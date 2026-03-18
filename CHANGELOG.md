## [0.17.2] — WS-N2 Robin Hood Invariant Proofs

- Completed Phase 2 (WS-N2) of the Robin Hood hashing workstream: invariant
  definitions, WF/distCorrect preservation, modular arithmetic helpers, loop
  count/correctness proofs, bundle preservation theorems, and lookup correctness
  signatures
- N2-A: Invariant definitions in `SeLe4n/Kernel/RobinHood/Invariant/Defs.lean`:
  `distCorrect` (probe distance accuracy), `noDupKeys` (key uniqueness),
  `robinHoodOrdered` (non-decreasing cluster distances), `RHTable.invariant`
  4-conjunct bundle; `empty_distCorrect`, `empty_noDupKeys`,
  `empty_robinHoodOrdered`, `empty_invariant` proofs
- N2-B: WF preservation in `SeLe4n/Kernel/RobinHood/Invariant/Preservation.lean`:
  `insertNoResize_preserves_wf`, `insert_preserves_wf`, `resize_preserves_wf`,
  `erase_preserves_wf`; modular arithmetic helpers `mod_succ_eq`,
  `dist_step_mod`; `countOccupied_le_size` bound proof
- N2-C: distCorrect preservation: `insertLoop_preserves_distCorrect` (full
  induction proof with modular arithmetic),
  `insertNoResize_preserves_distCorrect`, `insert_preserves_distCorrect`,
  `resize_preserves_distCorrect` (via fold induction)
- N2-D: Loop count and correctness: `insertLoop_countOccupied`,
  `backshiftLoop_countOccupied`, `findLoop_lt`, `findLoop_correct`
- N2-E: Bundle preservation: `insert_preserves_invariant`,
  `erase_preserves_invariant`, `resize_preserves_invariant`
- N2-F: Lookup correctness signatures in
  `SeLe4n/Kernel/RobinHood/Invariant/Lookup.lean`: `get_after_insert_eq`,
  `get_after_insert_ne`, `get_after_erase_eq`
- N2-G: Re-export hub `SeLe4n/Kernel/RobinHood/Invariant.lean`; updated
  `SeLe4n/Kernel/RobinHood.lean` to import Invariant; changed `private` to
  `protected` for `insertNoResize`, `insertNoResize_capacity`,
  `resize_fold_capacity` in `Core.lean`
- **Major finding:** `robinHoodOrdered` (non-decreasing dist within clusters)
  is NOT preserved by backshift-on-erase. `invExt` bundle restructured to use
  `probeChainDominant` instead, which IS preserved by all operations
- Additional helper lemmas proved: `noDupKeys_after_clear`,
  `backshiftLoop_preserves_noDupKeys`, `erase_preserves_noDupKeys`,
  `displacement_backward`, `backshiftLoop_preserves_distCorrect`,
  `erase_preserves_distCorrect`
- Preservation theorems complete: WF (all ops), distCorrect (all ops),
  noDupKeys (all ops)
- TPI-D1 completed: `insertLoop_preserves_noDupKeys` — full fuel induction
  proving noDupKeys for insertLoop result (zero sorry)
- TPI-D2 completed: `insertLoop_preserves_pcd` — full fuel induction proving
  probeChainDominant for insertLoop result (zero sorry)
- Helper infrastructure added: `offset_injective` (modular offset injectivity),
  `getElem_idx_eq` (array access proof irrelevance), `carried_key_absent`
  (key absent if probe reached empty/swap position), `getLoop_none_of_absent`
  (if key absent from all slots, getLoop returns none)
- D6 (`get_after_erase_eq`) structured via `getLoop_none_of_absent` +
  `erase_removes_key`
- Files: 4 new (`Invariant/Defs.lean`, `Invariant/Preservation.lean`,
  `Invariant/Lookup.lean`, `Invariant.lean`), 2 modified (`Core.lean`,
  `RobinHood.lean`)
- 4 TPI-D deferred items remaining (TPI-D3 through TPI-D6): erase PCD
  preservation and lookup correctness
- Zero `sorry`/`axiom` in completed proofs; zero warnings; all test tiers pass
- Bumped `lakefile.toml` version to `0.17.2`

## [0.17.1] — WS-N1 Core Robin Hood Types + Operations

- Completed Phase 1 (WS-N1) of the Robin Hood hashing workstream: core data
  types, fuel-bounded operations, and array-size preservation proofs
- N1-A: `RHEntry` (key, value, probe distance) and `RHTable` (single-
  representation `Array (Option (RHEntry α β))` with `hCapPos`/`hSlotsLen`
  invariants); `idealIndex`/`nextIndex` with `@[inline]`; `idealIndex_lt`/
  `nextIndex_lt` bound proofs via `Nat.mod_lt`
- N1-B: `RHTable.empty` constructor from `List.replicate`; `countOccupied`
  helper; 4-conjunct `RHTable.WF` predicate (slotsLen, capPos, sizeCount,
  sizeBound); `empty_wf` proof (zero sorry)
- N1-C: Fuel-bounded `insertLoop` with 5 branches (empty slot, key match,
  Robin Hood swap, continue probing, fuel exhausted); structural recursion on
  `fuel : Nat`; `insertLoop_preserves_len` by induction
- N1-D: `RHTable.insert` with 75% load-factor resize trigger; private
  `insertNoResize` helper to avoid resize/insert circularity;
  `insertNoResize_size_le` proof
- N1-E: Fuel-bounded `getLoop` with Robin Hood early termination (empty slot,
  dist < search dist); `RHTable.get?`; `RHTable.contains`
- N1-F: `findLoop` (locate target slot) + `backshiftLoop` (fill gap after
  removal, decrement dist); `backshiftLoop_preserves_len` proof;
  `RHTable.erase` composing both phases
- N1-G: `RHTable.fold`, `RHTable.toList`, `RHTable.resize` (double capacity,
  re-insert all via `insertNoResize`); `resize_preserves_len` proof
  (`slots.size = capacity * 2` via `Array.foldl_induction`);
  `resize_fold_capacity` proof; `Membership` instance;
  `GetElem`/`GetElem?` instances enabling `t[k]?` bracket notation
- N1-H: Re-export hub `SeLe4n/Kernel/RobinHood.lean`
- Files: `SeLe4n/Kernel/RobinHood/Core.lean` (379 lines),
  `SeLe4n/Kernel/RobinHood.lean` (15 lines)
- Zero `sorry`/`axiom`; zero warnings; all test tiers pass
- Bumped `lakefile.toml` version to `0.17.1`

## [0.16.18] — WS-M4 Test Coverage Expansion

- Completed Phase 4 (WS-M4) of the capability subsystem workstream: test
  coverage expansion for `resolveCapAddress` edge cases and `cspaceRevokeCdtStrict`
  stress scenarios
- M4-A: 6 `resolveCapAddress` edge case tests in `NegativeStateSuite.lean`:
  - M4-A1: Guard-only CNode (zero radixWidth, non-zero guardWidth) resolves
    to slot 0; wrong guard correctly rejected (SCN-RESOLVE-GUARD-ONLY)
  - M4-A2: 64-bit resolution across 8 CNodes (8 bits per hop) succeeds
    end-to-end; 65-bit overflow returns `.invalidCapability` due to bit-shift
    misalignment (SCN-RESOLVE-MAX-DEPTH)
  - M4-A3: Guard mismatch at intermediate level in 3-level CNode chain
    returns `.invalidCapability` (SCN-RESOLVE-GUARD-MISMATCH-MID)
  - M4-A4: Partial bit consumption (bitsRemaining < guardWidth + radixWidth)
    and zero bitsRemaining both return `.illegalState` (SCN-RESOLVE-PARTIAL-BITS)
  - M4-A5: Single-level leaf resolution with exact bit consumption
    (SCN-RESOLVE-SINGLE-LEVEL)
- M4-B: 3 `cspaceRevokeCdtStrict` stress tests in `OperationChainSuite.lean`:
  - M4-B1: 15-level deep chain strict revocation — all 15 descendants deleted,
    `deletedSlots.length = 15`, root slot preserved, CDT nodes detached
    (SCN-REVOKE-STRICT-DEEP)
  - M4-B2: Partial failure mid-traversal — corrupted CNode triggers
    `.objectNotFound`, `firstFailure` populated with correct context,
    `deletedSlots.length = 2` (exactly the nodes before the failure point),
    traversal halts at failure point (SCN-REVOKE-STRICT-PARTIAL-FAIL)
  - M4-B3: Branching tree (root→A→A1, root→B→B1→B2) — all 5 descendants
    deleted, set-membership verified, parent-before-child ordering verified
    for each sub-chain (SCN-REVOKE-STRICT-ORDER)
- Refined WS-M4 workstream plan with detailed subtask specifications,
  dependency graph, and execution order
- 9 new test scenarios; zero sorry/axiom; zero warnings
- All test tiers pass (test_full.sh Tier 0-3)
- Bumped `lakefile.toml` version to 0.16.18

## [0.16.17] — WS-M3 IPC Capability Transfer Implementation

- Completed Phase 3 (WS-M3) of the capability subsystem workstream: IPC
  capability transfer with seL4-aligned receive-side cap unwrapping
- M3-A: Added `CapTransferResult` inductive (`installed`/`noSlot`/`grantDenied`),
  `CapTransferSummary` structure, `DerivationOp.ipcTransfer` CDT variant
- M3-B: Implemented `CNode.findFirstEmptySlot` with structural recursion on
  `limit` parameter; `findFirstEmptySlot_spec` and `findFirstEmptySlot_zero`
  correctness theorems
- M3-C: Implemented `ipcTransferSingleCap` — single-cap transfer with CDT edge
  tracking via `.ipcTransfer` derivation op; `ipcTransferSingleCap_preserves_scheduler`
  and `ipcTransferSingleCap_preserves_capabilityInvariantBundle` preservation proofs
- M3-D: Implemented `ipcUnwrapCaps` batch cap unwrap with `ipcUnwrapCapsLoop`
  recursive helper (fuel-based structural recursion); Grant-right gate drops
  all caps when endpoint lacks Grant right; `ipcUnwrapCaps_preserves_scheduler`
  preservation proof by induction on fuel;
  `ipcUnwrapCaps_preserves_capabilityInvariantBundle_noGrant` proves bundle
  preservation when Grant right is absent (state unchanged)
- M3-E: Added `endpointSendDualWithCaps`, `endpointReceiveDualWithCaps`,
  `endpointCallWithCaps` wrapper operations composing existing IPC ops with
  cap transfer during rendezvous; `lookupCspaceRoot` helper reads receiver's
  CSpace root from TCB; `ipcUnwrapCaps_preserves_ipcInvariant`,
  `endpointSendDualWithCaps_preserves_ipcInvariant`,
  `endpointReceiveDualWithCaps_preserves_ipcInvariant`,
  `endpointCallWithCaps_preserves_ipcInvariant` preservation theorems
- M3-F: Added `decodeExtraCapAddrs` with determinism theorem; `resolveExtraCaps`
  pure fold over CPtr array; updated `dispatchWithCap` to use WithCaps wrappers
  for send/call paths; renamed theorems (`dispatchWithCap_send_uses_withCaps`,
  `dispatchWithCap_call_uses_withCaps`)
- M3-G: Added 4 test scenarios: SCN-IPC-CAP-TRANSFER-BASIC,
  SCN-IPC-CAP-TRANSFER-NO-GRANT, SCN-IPC-CAP-TRANSFER-FULL-CNODE,
  SCN-IPC-CAP-BADGE-COMBINED; `chain12`–`chain14` in OperationChainSuite +
  `runWSM3CapTransferNegativeChecks` in NegativeStateSuite
- New files: `SeLe4n/Kernel/IPC/Operations/CapTransfer.lean`,
  `SeLe4n/Kernel/IPC/DualQueue/WithCaps.lean`
- Resolves L-T03 (capability transfer during IPC — last WS-L deferred item)
- 12+ new proved declarations; zero sorry/axiom; zero warnings
- All test tiers pass (test_full.sh Tier 0-3)
- Bumped `lakefile.toml` version to 0.16.17

## [0.16.16] — WS-M3 IPC Capability Transfer Plan Refinement

- Refined and expanded Phase 3 (WS-M3) workstream plan for IPC capability
  transfer from 4 coarse tasks to 7 tasks with 20 atomic subtasks
- Corrected architectural alignment: cap unwrapping happens on the receive side
  (seL4 semantics), not the send side as originally planned
- Added `CapTransferResult`/`CapTransferSummary` type specifications with
  seL4-accurate `grantDenied` variant (replacing incorrect `attenuationFailed`)
- Added `DerivationOp.ipcTransfer` CDT variant for tracking IPC-transferred caps
- Designed `CNode.findFirstEmptySlot` with bounded iteration (structural
  recursion on `limit`) and correctness theorem specifications
- Specified `ipcTransferSingleCap` operation with CDT edge tracking and
  `ipcUnwrapCaps` batch operation with Grant-right gate
- Designed wrapper pattern (`endpointSendDualWithCaps`,
  `endpointReceiveDualWithCaps`, `endpointCallWithCaps`) preserving all existing
  IPC operation signatures and proofs
- Added `decodeExtraCapAddrs` and `resolveExtraCaps` specifications for wiring
  extra cap addresses from `SyscallDecodeResult.msgInfo.extraCaps` through
  `dispatchWithCap`
- Specified 4 test scenarios: positive transfer, grant-right gate, no-slot
  negative, badge+cap combined (SCN-IPC-CAP-TRANSFER-*)
- Full dependency graph with 9 sequential steps and parallelism opportunities
- Corrected Phase 4/5 target versions (0.16.17/0.16.18, consistent with patch
  version scheme)
- All tests pass (test_full.sh Tier 0-3); zero sorry/axiom; zero warnings
- Bumped `lakefile.toml` version to 0.16.16

## [0.16.15] — Capability Performance Optimization (WS-M2)

- Completed Phase 2 (WS-M2) of the capability subsystem workstream: performance
  optimization across CSpace revoke, CDT parent lookup, and proof infrastructure
- M2-A: Fused `revokeAndClearRefsState` single-pass revoke — eliminates
  intermediate `revokedRefs` list allocation and second O(m) traversal through
  `clearCapabilityRefsState`, cutting revoke hot path from two O(m) passes to one
- M2-A2: Added comprehensive field preservation lemmas for
  `revokeAndClearRefsState` — objects, scheduler, machine, services, irqHandlers,
  objectIndex, objectIndexSet, CDT fields — using `Std.HashMap.fold_eq_foldl_toList`
  bridge with list induction
- M2-B1: Added `parentMap : Std.HashMap CdtNodeId CdtNodeId` field to
  `CapDerivationTree` — child-indexed parent map symmetric to existing `childMap`
- M2-B2/B3: Rewrote `parentOf` to use `parentMap[node]?` (O(E) → O(1)),
  updated `addEdge` to maintain `parentMap` alongside `childMap` and `edges`
- M2-B4/B5: Updated `removeAsChild`, `removeAsParent`, `removeNode` for
  targeted `parentMap` erasure — `removeNode` childMap update goes from O(E)
  full rebuild to O(children.length) targeted splice
- M2-B6/B7: Defined `parentMapConsistent` invariant with proofs for `empty`,
  `addEdge`, and `removeNode` (requires `childMapConsistent` co-hypothesis)
- M2-C: Extracted `capabilityInvariantBundle_of_storeTcbAndEnsureRunnable`
  private theorem — shared reply-preservation proof body eliminating duplication
  across authorized and unrestricted dispatch branches
- Updated non-interference proofs (Helpers.lean, Operations.lean) to use
  `revokeAndClearRefsState_preserves_*` and `revokeAndClearRefsState_preserves_projectState`
- Added `cdtParentMapConsistentCheck` runtime invariant check in test harness
- Removed dead code: `clearCapabilityRefsState`, `clearCapabilityRefs`, and 11
  associated preservation theorems — fully superseded by `revokeAndClearRefsState`
- Net +1 proved declarations (12 added, 11 dead removed); zero sorry/axiom
- All test tiers pass (test_full.sh); 150/150 trace fixtures matched
- Bumped `lakefile.toml` version to 0.16.15

## [0.16.14] — Capability Proof Strengthening (WS-M1)

- Completed Phase 1 (WS-M1) of the capability subsystem workstream: proof
  strengthening and correctness improvements across CSpace resolution, CDT
  acyclicity, mint completeness, and revoke error consistency
- M1-A: Added `resolveCapAddress_guard_match` theorem — forward-direction
  companion proving that successful resolution implies guard bits match the
  CNode's stored guardValue (complements existing `resolveCapAddress_guard_reject`)
- M1-B1: Introduced `cdtMintCompleteness` predicate — every CDT node with a
  slot mapping either has a parent edge (derived node) or is completely isolated
  (root node with no edges at all)
- M1-B2: Added `cdtMintCompleteness_of_cdt_edges_nodeSlot_eq` transfer theorem
  for state transitions that preserve CDT edges and nodeSlot mappings
- M1-B3: Defined `capabilityInvariantBundleWithMintCompleteness` extended
  invariant bundle with extraction theorems
- M1-C1: Proved `addEdge_preserves_edgeWellFounded_fresh` — CDT edge addition
  preserves acyclicity when the child node is fresh (not in any existing edge),
  covering the common `ensureCdtNodeForSlot` kernel pattern
- M1-C2: Added `addEdgeWouldBeSafe` runtime acyclicity check (parent ≠ child ∧
  parent ∉ descendantsOf child)
- M1-D1: Added `cspaceRevokeCdt_swallowed_error_consistent` theorem — proves
  invariant preservation, object stability, and edge-set monotonicity through
  the error-swallowing path of `revokeCdtFoldBody`
- M1-D2/E: Updated `cspaceRevokeCdt` and `cspaceRevoke` docstrings with
  accurate cross-references and error-handling design rationale
- Refined Phase 1 workstream plan: split 5 high-level tasks into 10 atomic
  subtasks (M1-E, M1-A1/A2, M1-B1/B2/B3, M1-C1/C2, M1-D1/D2)
- 7 new proved declarations; zero sorry/axiom; all proofs machine-checked
- All test tiers pass (test_full.sh); production LoC: 38,556 across 69 files
- Bumped `lakefile.toml` version to 0.16.14

## [0.16.12] — IPC Test Coverage Expansion (WS-L4)

- Completed WS-L4 phase: filled all 4 IPC test coverage gaps (L-T01, L-T02,
  L-T04, L-T05) with 9 new scenario IDs (16 total across L4 test functions)
- L4-A2: Extended `runReplyRecvRoundtripTrace` with second-sender rendezvous
  path — verifies `endpointReplyRecv` replies to caller A AND immediately
  receives caller B's message in a single atomic operation (RRC-002, RRC-006);
  refined RRC-005 to verify server is `.ready` after rendezvous (not just
  not-blocked)
- L4-B: New `runEndpointLifecycleTrace` — endpoint retype while senders are
  blocked on sendQ, validates graceful-failure-by-guard model: senders retain
  stale `blockedOnSend` state, stale IPC operations rejected with
  `.invalidCapability` (ELC-001 through ELC-004)
- L4-D2/D3: Extended `runMultiEndpointInterleavingTrace` from 2 to 3 endpoints
  with out-of-order receive (EP3 before EP1) and FIFO verification on EP1
  second message round (MEI-004, MEI-005, MEI-006)
- L4-C: Extended blocked-thread IPC rejection tests with 2 cross-state
  scenarios (blocked-on-receive rejects send to different endpoint;
  blocked-on-send rejects receive from different endpoint) — 5 total rejection
  cases
- Refined WS-L4 workstream plan with detailed gap analysis, sub-step breakdown,
  and implementation status tracking
- Updated fixture files and scenario registry for all new scenario IDs
- Inter-transition invariant check count: 22 (up from 21)
- Bumped `lakefile.toml` version to 0.16.12
- Zero sorry/axiom; all proofs machine-checked; test_full.sh passes

## [0.16.11] — IPC Proof Strengthening (WS-L3)

- Added 22 new theorems and 1 new invariant definition strengthening formal
  assurance of the IPC dual-queue subsystem
- L3-A: Enqueue-dequeue round-trip theorem — proves that a thread enqueued
  into an empty queue can be successfully dequeued via popHead
  (`endpointQueueEnqueue_then_popHead_succeeds` + 2 postcondition lemmas)
- L3-B: Standalone `tcbQueueLinkIntegrity` preservation for popHead and
  enqueue, extracted from bundled `dualQueueSystemInvariant` preservation
- L3-C: New `ipcStateQueueConsistent` invariant (blocked → endpoint exists)
  with queue-operation preservation theorems; 3 forward endpoint preservation
  helpers (`storeTcbQueueLinks_endpoint_forward`, `endpointQueuePopHead_endpoint_forward`,
  `endpointQueueEnqueue_endpoint_forward`)
- L3-D: Tail consistency for `endpointQueueRemoveDual` — non-tail removal
  preserves tail, tail removal characterization
- L3-E: Identified as already resolved (pre-existing in `CallReplyRecv.lean:797`)
- Refined WS-L3 workstream plan with granular subtask breakdown
- L3-C3: high-level `ipcStateQueueConsistent` preservation theorems for
  `endpointSendDual`, `endpointReceiveDual`, `endpointReply` — plus 5
  sub-operation helpers (`ensureRunnable`, `removeRunnable`,
  `storeTcbIpcStateAndMessage`, `storeTcbIpcState`, `storeTcbPendingMessage`)
- Regenerated `docs/codebase_map.json` — 38,186 production LoC, 1,224 proved
  declarations
- Bumped `lakefile.toml` version to 0.16.11
- Zero sorry/axiom; all proofs machine-checked; test_full.sh passes

## [0.16.10] — Code Quality & HashMap.fold Migration (WS-L2)

- Eliminated all 4 `Std.HashMap.toList.foldl/foldr` anti-patterns across codebase,
  replacing with direct `HashMap.fold` calls that avoid intermediate list allocation
- L2-A: Migrated 3 fold patterns in `Testing/InvariantChecks.lean`
  (`cspaceSlotCoherencyChecks`, `capabilityRightsStructuralChecks`,
  `cdtChildMapConsistentCheck`) from `.toList.foldr` to `HashMap.fold`
- L2-B: Migrated `detachCNodeSlots` in `Kernel/Lifecycle/Operations.lean` from
  `.toList.foldl` to `HashMap.fold`; updated 3 preservation proofs
  (`_objects_eq`, `_lifecycle_eq`, `_scheduler_eq`) using
  `Std.HashMap.fold_eq_foldl_toList` bridge lemma
- Refined WS-L2 workstream plan: expanded scope from 1 site to 4, added
  sub-task breakdown with proof update strategy and risk assessment
- Regenerated `docs/codebase_map.json`
- Bumped `lakefile.toml` version to 0.16.10
- Zero sorry/axiom; all proofs machine-checked; test_full.sh passes

## [0.16.9] — IPC Performance Optimization (WS-L1)

- Eliminated 4 redundant TCB lookups on IPC hot paths (L-P01, L-P02, L-P03)
- Changed `endpointQueuePopHead` return type to `(ThreadId × TCB × SystemState)`,
  providing pre-dequeue TCB to callers (L1-A)
- Added `storeTcbIpcStateAndMessage_fromTcb` and `storeTcbIpcState_fromTcb`
  variants with equivalence theorems — zero new preservation lemmas needed (L1-B, L1-C)
- Added `lookupTcb_preserved_by_storeObject_notification` helper for cross-store
  TCB stability
- Updated all transport lemmas and preservation theorems for new PopHead return type
  (~18 mechanical pattern-match updates across 6 invariant files)
- Refined WS-L1 workstream plan with smaller task units and optimal implementation
  strategy (equivalence-theorem approach vs. duplicated lemmas)
- Regenerated `docs/codebase_map.json`
- Bumped `lakefile.toml` version to 0.16.9
- Zero sorry/axiom; all proofs machine-checked; test_full.sh passes

## [0.16.8] — Documentation Sync and Workstream Closeout (WS-K-H)

- Synchronized all project documentation with completed WS-K implementation
  (K-A through K-G): canonical root docs, GitBook mirrors, metrics, version
- Updated `docs/WORKSTREAM_HISTORY.md` with WS-K portfolio completion
  (v0.16.0–v0.16.8, all 8 phases)
- Updated `docs/spec/SELE4N_SPEC.md` with v0.16.8 current state snapshot,
  WS-K PORTFOLIO COMPLETE status, and updated metrics
- Updated `docs/DEVELOPMENT.md` with WS-K completion and RPi5 next priority
- Updated `docs/CLAIM_EVIDENCE_INDEX.md` with comprehensive WS-K claim row
  covering all deliverables and evidence commands
- Updated GitBook chapters: architecture module map (03), design deep dive (04),
  specification and roadmap (05), proof and invariant map (12)
- Added `SyscallArgDecode.lean` entry to architecture module map with WS-K-B/K-F
  annotations
- Added two-layer syscall argument decode section to design deep dive
- Documented WS-K proof surface (44+ theorems) in proof and invariant map
- Regenerated `docs/codebase_map.json` with current Lean source metrics
- Synced `README.md` metrics from regenerated codebase map
- Bumped `lakefile.toml` version to 0.16.8
- Zero code changes to Lean source — documentation-only workstream

## [0.16.7] — Comprehensive Testing for Syscall Dispatch Completion (WS-K-G)

- Refined WS-K-G workstream plan into 7 granular sub-phases (K-G1 through K-G7)
  with detailed test specifications, design rationale, and acceptance criteria
- Added 21 negative-state tests in `NegativeStateSuite.lean` (`runWSKGChecks`):
  K-G1 (6 tests) CSpace decode/dispatch error coverage, K-G2 (7 tests)
  lifecycle/VSpace error coverage, K-G3 (5 tests) service policy and boundary
  coverage, K-G4 (3 tests) determinism verification for decode pipeline
- Added 8 trace scenarios in `MainTraceHarness.lean` (`runSyscallDispatchTrace`):
  KSD-001 through KSD-008 covering CSpace mint/copy/delete, lifecycle retype,
  VSpace map, service start, IPC message population, and layer 1+2 round-trip;
  all scenarios exercise the full Layer-2 decode pipeline (SyscallDecodeResult →
  typed args → kernel operation)
- Added 34 Tier 3 invariant surface anchors (11 `rg` pattern checks + 23
  `#check` type-level validations) for K-F and K-G proof surface in
  `scripts/test_tier3_invariant_surface.sh`
- Updated scenario registry with KSD-001 through KSD-008 entries
- Updated fixture file with new trace output (134 lines, ITR-001 count 18→19)
- All tiers (0-3) pass; zero `sorry`, zero `axiom`

## [0.16.6] — Lifecycle NI Proof Completion and Deferred Proof Resolution (WS-K-G)

- Added `cspaceRevoke_preserves_projection` standalone theorem in
  `InformationFlow/Invariant/Operations.lean` — extracted from inline proof in
  Composition.lean for compositional reuse in lifecycle NI proofs
- Added `lifecycleRevokeDeleteRetype_preserves_projection` theorem — chains
  projection preservation across `cspaceRevoke`, `cspaceDeleteSlot`, and
  `lifecycleRetypeObject` sub-operations via their respective projection theorems
- Added `lifecycleRevokeDeleteRetype_preserves_lowEquivalent` two-run NI theorem
  — completes the previously deferred `lifecycleRevokeDeleteRetype` NI proof
  using compositional projection-preservation reasoning
- Extended `NonInterferenceStep` inductive with `lifecycleRevokeDeleteRetype`
  constructor (34 constructors total, up from 33) covering the composed
  revoke-delete-retype lifecycle operation
- Updated `step_preserves_projection` with the new constructor case using
  the standalone `lifecycleRevokeDeleteRetype_preserves_projection` theorem
- Updated `syscallNI_coverage_witness` documentation to reflect 34-constructor
  exhaustive match (verified by Lean exhaustiveness checker)
- Zero `sorry`, zero `axiom` — all proofs machine-checked

## [0.16.5] — Proofs: Round-Trip, Preservation, and NI Integration (WS-K-F)

- Added 7 encode functions in `SyscallArgDecode.lean` (`encodeCSpaceMintArgs`,
  `encodeCSpaceCopyArgs`, `encodeCSpaceMoveArgs`, `encodeCSpaceDeleteArgs`,
  `encodeLifecycleRetypeArgs`, `encodeVSpaceMapArgs`, `encodeVSpaceUnmapArgs`)
  completing the encode/decode symmetry for all layer-2 typed argument structures
- Proved 7 layer-2 round-trip theorems via structure eta reduction (`rcases + rfl`)
  with `decode_layer2_roundtrip_all` composed conjunction
- Added `extractMessageRegisters_roundtrip` in `RegisterDecode.lean` — proves
  encoding `Nat` values as `RegValue` then extracting recovers the originals
  (closes the layer-1 extraction round-trip gap)
- Added `dispatchWithCap_layer2_decode_pure` in `API.lean` — proves all 7
  layer-2 decode functions depend only on `msgRegs` (two `SyscallDecodeResult`
  values with identical `msgRegs` produce identical decode results)
- Added `dispatchWithCap_preservation_composition_witness` structural
  preservation theorem in `API.lean` — witnesses compositional invariant
  preservation through the syscall entry → decode → dispatch → subsystem pipeline
- Added `retypeFromUntyped_preserves_lowEquivalent` NI theorem in
  `InformationFlow/Invariant/Operations.lean` — completes the last deferred
  NI proof using two-stage `storeObject_at_unobservable_preserves_lowEquivalent`
  composition through intermediate untyped update state
- Added `syscallNI_coverage_witness` in `InformationFlow/Invariant/Composition.lean`
  — witnesses that (1) decode-error path produces a valid NI step, (2) every NI
  step composes into a trace, and (3) `step_preserves_projection` is total over
  all 33 `NonInterferenceStep` constructors
- Refined WS-K-F workstream plan into 6 granular sub-phases (K-F1 through K-F6)
  with detailed task breakdowns, proof patterns, and exit criteria
- Zero `sorry`, zero `axiom` — all proofs machine-checked

## [0.16.4] — Service Policy and IPC Message Population (WS-K-E)

- Replaced `(fun _ => true)` service policy stubs in `dispatchWithCap` with
  configuration-sourced predicates: `.serviceStart` reads
  `st.serviceConfig.allowStart`, `.serviceStop` reads `st.serviceConfig.allowStop`
- Added `ServiceConfig` structure in `Model/State.lean` with `Inhabited` default
  (permissive `fun _ => true`), preserving backward compatibility
- Extended `SystemState` with `serviceConfig : ServiceConfig := default` field
- Added `extractMessageRegisters` in `RegisterDecode.lean` — converts
  `Array RegValue` → `Array Nat` (matching `IpcMessage.registers : Array Nat`)
  with triple bound (`info.length`, `maxMessageRegisters`, `msgRegs.size`)
- Updated `.send`, `.call`, `.reply` IPC dispatch arms to populate message bodies
  from decoded registers instead of empty arrays (`registers := #[]`)
- Proved `extractMessageRegisters_length` (result size ≤ `maxMessageRegisters`),
  `extractMessageRegisters_ipc_bounded` (constructed `IpcMessage` satisfies
  `bounded`), `extractMessageRegisters_deterministic`
- 5 delegation theorems proved (`dispatchWithCap_serviceStart_uses_config`,
  `dispatchWithCap_serviceStop_uses_config`, `dispatchWithCap_send_populates_msg`,
  `dispatchWithCap_call_populates_msg`, `dispatchWithCap_reply_populates_msg`)
- All existing soundness theorems compile unchanged
- `BootstrapBuilder` extended with `serviceConfig` field and `withServiceConfig`
  combinator for test scenario configuration
- 11 Tier 3 invariant surface anchors (rg + #check) for all new definitions
- Refined WS-K-E workstream plan with 17 detailed subtasks (K-E.1–K-E.17)
- Zero `(fun _ => true)` policy stubs remain in `dispatchWithCap`
- Zero `registers := #[]` in IPC dispatch arms
- Zero `sorry`, zero `axiom` — all proofs machine-checked

## [0.16.3] — Lifecycle and VSpace Syscall Dispatch (WS-K-D)

- Wired all 3 remaining syscall stubs (`lifecycleRetype`, `vspaceMap`,
  `vspaceUnmap`) through `dispatchWithCap` using decoded message register
  arguments — zero `.illegalState` stubs remain; all 13 syscalls fully dispatch
- Added `objectOfTypeTag` helper mapping raw type tags (0–5) to default
  `KernelObject` constructors with dedicated `invalidTypeTag` error variant for
  unrecognized tags; includes type, error-exclusivity, and determinism theorems
- Added `lifecycleRetypeDirect` — companion to `lifecycleRetypeObject` for
  register-sourced dispatch where the authority cap is already resolved by
  `syscallInvoke`; avoids double capability lookup; includes equivalence theorem
  linking it to `lifecycleRetypeObject`
- Added `PagePermissions.ofNat`/`toNat` bitfield codec (bit 0=read, 1=write,
  2=execute, 3=user, 4=cacheable) with round-trip theorem
- `vspaceMap` dispatch uses `vspaceMapPageChecked` (bounds-checked variant,
  rejects `paddr ≥ 2^52`) for user-space entry safety
- 3 delegation theorems proved (`dispatchWithCap_lifecycleRetype_delegates`,
  `dispatchWithCap_vspaceMap_delegates`, `dispatchWithCap_vspaceUnmap_delegates`)
- All existing soundness theorems compile unchanged after dispatch changes
- Tier 3 invariant surface anchors added for all new definitions and theorems
- Refined WS-K-D workstream plan with 10 detailed subtasks (K-D.1–K-D.10)
- Zero `sorry`, zero `axiom` — all proofs machine-checked

## [0.16.2] — CSpace Syscall Dispatch (WS-K-C)

- Wired all 4 CSpace syscalls (`cspaceMint`, `cspaceCopy`, `cspaceMove`,
  `cspaceDelete`) through `dispatchWithCap` using decoded message register
  arguments from `SyscallArgDecode`
- Changed `dispatchWithCap` signature from `SyscallId` to `SyscallDecodeResult`
  so CSpace dispatch arms can extract per-syscall typed arguments from
  `decoded.msgRegs`
- `cspaceMint` dispatch: decodes srcSlot, dstSlot, rights bitmask, and badge
  from 4 message registers; badge=0 maps to `none` (seL4 convention)
- `cspaceCopy`/`cspaceMove` dispatch: decodes srcSlot and dstSlot from 2
  message registers; delegates to kernel-level copy/move with CDT integration
- `cspaceDelete` dispatch: decodes targetSlot from 1 message register
- 4 delegation theorems proved (`dispatchWithCap_cspaceMint_delegates`, etc.)
- All 3 existing soundness theorems (`dispatchSyscall_requires_right`,
  `syscallEntry_implies_capability_held`, `syscallEntry_requires_valid_decode`)
  compile unchanged after signature refactoring
- Refined WS-K-C workstream plan with 8 detailed subtasks (K-C.1–K-C.8)
- Zero `sorry`, zero `axiom` — all proofs machine-checked

## [0.16.1] — Per-Syscall Argument Decode Layer (WS-K-B)

- Added `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean` — layer 2 of the
  two-layer syscall decode architecture
- 7 per-syscall typed argument structures: `CSpaceMintArgs`, `CSpaceCopyArgs`,
  `CSpaceMoveArgs`, `CSpaceDeleteArgs`, `LifecycleRetypeArgs`, `VSpaceMapArgs`,
  `VSpaceUnmapArgs`
- 7 total decode functions with explicit `Except KernelError` error handling
- 7 determinism theorems (trivial `rfl`)
- 7 error-exclusivity theorems (`decode fails ↔ msgRegs.size < N`)
- Zero `sorry`, zero `axiom` — all proofs machine-checked
- Integrated into `API.lean` import graph

## [0.16.0] - 2026-03-14

### WS-K-A: Message Register Extraction into SyscallDecodeResult

- **SyscallDecodeResult extension**: Added `msgRegs : Array RegValue := #[]`
  field to `SyscallDecodeResult` in `Model/Object/Types.lean`. Default value
  ensures backward compatibility with all existing construction sites.
- **Decode function update**: Updated `decodeSyscallArgs` in
  `RegisterDecode.lean` to validate and read message registers (x2–x5 on
  ARM64) in a single pass via `Array.mapM`, replacing the previous
  bounds-only validation loop.
- **Encoding helper**: Added `encodeMsgRegs` identity encoder for round-trip
  proof surface completeness.
- **Length invariant**: Proved `decodeMsgRegs_length` — when decode succeeds,
  `decoded.msgRegs.size = layout.msgRegs.size`. Proved via novel
  `list_mapM_except_length` / `array_mapM_except_size` helper lemmas.
- **Round-trip lemma**: Proved `decodeMsgRegs_roundtrip` — encoding then
  decoding message register values is identity.
- **Extended composition**: Updated `decode_components_roundtrip` to include
  the `msgRegs` component (4-conjunct from 3-conjunct).
- **Test updates**: NegativeStateSuite J1-NEG-17 now verifies `msgRegs.size = 4`
  for ARM64 layout. MainTraceHarness RDT-002 trace output includes `msgRegs`
  count. Trace fixture updated. 4 new Tier 3 surface anchors added.
- **Workstream plan refinement**: WS-K-A section decomposed into 8 detailed
  subtasks (K-A.1 through K-A.8) with per-subtask acceptance criteria.
- **Build jobs:** 140. Zero sorry/axiom. Zero warnings.
- **Closes:** WS-K Phase A.

## [0.15.10] - 2026-03-14

### WS-J1-F: CdtNodeId Cleanup and Documentation Sync

- **Typed wrapper replacement**: Replaced `abbrev CdtNodeId := Nat` with
  `structure CdtNodeId where val : Nat` in `Model/Object/Structures.lean`,
  matching the typed wrapper pattern used by all 15 other kernel identifiers.
- **Instance suite**: Added `DecidableEq`, `Hashable`, `LawfulHashable`,
  `EquivBEq`, `LawfulBEq`, `Repr`, `ToString`, `Inhabited`, `ofNat`/`toNat`
  conversion functions — all co-located with the type definition in
  `Structures.lean`.
- **Downstream compilation fixes**: Updated `SystemState` field defaults
  (`cdtNextNode := ⟨0⟩`), monotone allocator (`⟨node.val + 1⟩`), and test
  literals in `NegativeStateSuite.lean` to use explicit constructor syntax.
- **Documentation synchronization**: Updated all canonical sources (README,
  SELE4N_SPEC, DEVELOPMENT, WORKSTREAM_HISTORY, CLAIM_EVIDENCE_INDEX) and
  GitBook chapters (03, 04, 05, 12) to reflect WS-J1-F completion.
- **Codebase map regeneration**: `docs/codebase_map.json` regenerated with
  updated declaration counts and version.
- **Build jobs:** 140. Zero sorry/axiom. Zero warnings.
- **Closes:** WS-J1 Phase F. **WS-J1 portfolio fully completed.**

## [0.15.7] - 2026-03-14

### WS-J1-C: Audit Refinements

- **CSpace/lifecycle/VSpace dispatch**: `dispatchWithCap` now returns
  `illegalState` for operations requiring message-register data (CSpace
  mint/copy/move/delete, lifecycle retype, VSpace map/unmap). Full MR-based
  argument extraction deferred to WS-J1-E.
- **Register count parameter**: `syscallEntry` accepts `regCount : Nat`
  (default 32 for ARM64) forwarded to `decodeSyscallArgs` for architectural
  register bounds validation.
- **Strengthened capability-held theorem**: `syscallEntry_implies_capability_held`
  now proves the full chain from entry success through TCB/CSpace lookup to
  capability resolution with the required access right, composing with
  `dispatchSyscall_requires_right`.
- **Stability table**: added `syscallEntry`, `lookupThreadRegisterContext`,
  `dispatchSyscall` entries.
- **Build jobs:** 140. Zero sorry/axiom. Zero warnings.

## [0.15.6] - 2026-03-14

### WS-J1-C: Syscall Entry Point and Dispatch

- **Syscall entry point**: `syscallEntry : SyscallRegisterLayout → Nat → Kernel Unit`
  — top-level user-space entry point that reads the current thread's register
  file, decodes raw register values via `decodeSyscallArgs` (with configurable
  `regCount`, default 32), and dispatches to the appropriate capability-gated
  kernel operation.
- **Register context lookup**: `lookupThreadRegisterContext : ThreadId → Kernel
  RegisterFile` — extracts the saved register context from the current thread's
  TCB, with `objectNotFound`/`illegalState` error paths.
- **Syscall dispatch**: `dispatchSyscall : SyscallDecodeResult → ThreadId →
  Kernel Unit` — constructs a `SyscallGate` from the caller's TCB and CSpace
  root CNode, then routes through `syscallInvoke` to the appropriate internal
  kernel operation based on the decoded `SyscallId`.
- **Per-syscall routing**: `dispatchWithCap` handles all 13 modeled syscalls.
  IPC ops (send/receive/call/reply) and service ops extract the target from the
  resolved capability's `CapTarget`. CSpace ops (mint/copy/move/delete),
  lifecycle retype, and VSpace ops (map/unmap) return `illegalState` as they
  require message-register data not yet available in the decode path.
- **Right mapping**: `syscallRequiredRight : SyscallId → AccessRight` — total
  function mapping each syscall to its required access right, matching the
  authority requirements of the existing `api*` wrappers.
- **MachineConfig field**: `registerCount` promoted from computed def to
  configurable structure field with default 32 (ARM64).
- **Soundness theorems**:
  - `syscallEntry_requires_valid_decode` — successful entry implies register
    decode succeeded.
  - `syscallEntry_implies_capability_held` — successful entry implies dispatch
    succeeded (capability was resolved and authorized).
  - `dispatchSyscall_requires_right` — dispatch success implies the caller held
    a capability with the required access right for the invoked syscall.
  - `lookupThreadRegisterContext_state_unchanged` — register context lookup is
    read-only.
  - `syscallRequiredRight_total` — every syscall maps to exactly one right.
- **Build jobs:** 140. Zero sorry/axiom. Zero warnings.
- **Closes:** WS-J1 Phase C.

## [0.15.5] - 2026-03-14

### WS-J1-B: Register Decode Layer

- **Syscall decode types**: `SyscallId` inductive (13 modeled syscalls with
  injective `toNat`/total `ofNat?` encoding, round-trip and injectivity
  theorems), `MessageInfo` structure (seL4 message-info word layout with
  bit-field encode/decode), `SyscallDecodeResult` (typed decode output
  consumed by syscall dispatch).
- **Register decode functions**: `decodeCapPtr` (total, unbounded CPtr address
  space), `decodeMsgInfo` (partial, validates length/extraCaps bounds),
  `decodeSyscallId` (partial, validates against modeled syscall set),
  `validateRegBound` (per-architecture register index bounds check),
  `decodeSyscallArgs` (entry point combining all register reads and decodes).
- **Platform configuration**: `SyscallRegisterLayout` structure mapping
  hardware registers to syscall arguments, `arm64DefaultLayout` constant
  (x0=capPtr, x1=msgInfo, x2–x5=msgRegs, x7=syscallNum),
  `MachineConfig.registerCount` field.
- **KernelError variants**: `invalidRegister`, `invalidSyscallNumber`,
  `invalidMessageInfo` for explicit decode failure reporting.
- **Correctness theorems**: `decodeCapPtr_roundtrip`, `decodeSyscallId_roundtrip`
  (encode-then-decode recovery), `decodeSyscallArgs_deterministic` (pure
  determinism), `decodeSyscallId_error_iff`, `decodeMsgInfo_error_iff` (error
  exclusivity), `validateRegBound_ok_iff`/`error_iff` (bounds iff-theorems),
  `decodeCapPtr_always_ok` (universal CPtr success), `SyscallId.toNat_injective`
  (encoding injectivity).
- **New file**: `SeLe4n/Kernel/Architecture/RegisterDecode.lean` — self-contained
  module importing only `Model.State`, no kernel subsystem dependencies.
- **Build jobs:** 140. Zero sorry/axiom. Zero warnings.
- **Closes:** WS-J1 Phase B.

## [0.14.10] - 2026-03-13

### WS-I1: Critical Testing Infrastructure

- **Part A (R-01): Inter-transition invariant assertions.** Added 17
  `checkInvariants` calls across all 13 trace functions in
  `MainTraceHarness.lean`, validating scheduler, CSpace, IPC, lifecycle,
  service, VSpace, and CDT invariants after each major transition group.
  Counter-based tracking via `IO.Ref Nat` prints summary count at trace end.
  Catches state corruption (CDT orphans, ASID mismatches, queue pointer
  corruption) that would previously pass silently.
- **Part B (R-02): Mandatory determinism validation.** Created
  `scripts/test_tier2_determinism.sh` executing `lake exe sele4n` twice and
  diffing output. Integrated into `test_smoke.sh` between trace fixture and
  negative state checks. Non-determinism bugs (HashMap iteration order, random
  scheduling) now caught immediately rather than at nightly Tier 4.
- **Part C (R-03): Scenario ID traceability.** Added `[PREFIX-NNN]` tags to all
  121 trace output lines across 15 prefixes (ENT, CAT, SST, LEP, CIC, IMT,
  IMB, DDT, ICS, BME, STD, UMT, SGT, RCF, ITR, PTY). Updated fixture file to
  pipe-delimited format (`SCENARIO_ID | SUBSYSTEM | fragment`). Created
  `tests/fixtures/scenario_registry.yaml` mapping each ID to source function
  and subsystem. Added `validate-registry` subcommand to `scenario_catalog.py`
  with Tier 0 hygiene integration. Developers can now answer coverage questions
  by grepping the registry.
- **Build jobs:** 138. Zero sorry/axiom. Zero warnings.
- **Recommendations closed:** R-01, R-02, R-03.

### WS-I2: Test Coverage and Memory domain ownership

- proof/validation depth completed: Tier 0 now runs semantic L-08 theorem-body
  analysis (`scripts/check_proof_depth.py` with regex fallback), Tier 3 now runs
  Lean `#check` correctness anchors across
  scheduler/capability/IPC/lifecycle/service/VSpace/IF preservation theorems,
  and IF projection now supports optional memory-domain ownership
  (`memoryOwnership`) with backward-compatible default (`none`).

### WS-I3: Test coverage expansion —

- new tests/OperationChainSuite.lean adds 6 multi-operation chain tests
  (retype→mint→revoke, send/send/receive FIFO, map/lookup/unmap/lookup,
  service start/stop dependency sequencing, copy/move/delete,   notification
  badge accumulation), scheduler stress coverage (16-thread repeated scheduling,
  same-priority determinism, multi-domain isolation), and Tier 2 integration via
  scripts/test_tier2_negative.sh; tests/InformationFlowSuite.lean now includes
  declassification runtime checks for authorized downgrade, normal-flow rejection,
  policy-denied rejection, and 3-domain lattice behavior. Closes R-06/R-07/R-08
  Declassification policy denial now reports a distinct declassificationDenied
   error in declassifyStore and suite expectations.
   
## [0.14.9] - 2026-03-11

### WS-F5: Model Fidelity

- **F5-D1 (CRIT-06): Word-bounded badge.** `Badge.val` is now logically bounded
  to 64-bit machine word size via `machineWordBits`/`machineWordMax` constants.
  New constructors: `Badge.ofNatMasked` (truncating), `Badge.bor` (word-bounded
  OR combiner). Theorems: `ofNatMasked_valid`, `bor_valid`, `bor_comm`,
  `bor_idempotent`, `ofNat_lt_valid`. `notificationSignal` uses `Badge.bor`
  for accumulation. Updated: `badge_merge_idempotent`,
  `notificationSignal_badge_stored_fresh`, `badge_notification_routing_consistent`.
- **F5-D2 (HIGH-04): Order-independent access rights.** `Capability.rights` is
  now `AccessRightSet` (bitmask) instead of `List AccessRight`. `AccessRightSet`
  provides O(1) membership, subset, union, intersection. `ofList` converts from
  list literals; `ofList_comm` proves order-independence. `rightsSubset_sound`
  re-proved via finite enumeration. All capability operations, invariant proofs,
  information-flow wrappers, and test fixtures migrated.
- **F5-D3 (MED-03): Deferred operations documented.** `setPriority`,
  `setMCPriority`, `suspend`, `resume`, `setIPCBuffer` explicitly documented in
  API.lean deferred operations table with rationale and prerequisites. Spec
  section 5.13 added. Claim evidence index updated.
- **Prior work acknowledged:** Per-thread register context (WS-H12c, v0.14.0)
  and multi-level CSpace resolution (WS-H13, v0.14.4) were already delivered
  and are marked as completed in the refined WS-F5 plan.
- **Workstream plan refined:** Original 5-deliverable plan replaced with
  detailed 3-deliverable plan (13 sub-tasks) reflecting actual remaining scope.
- **Build jobs:** 138. Zero sorry/axiom. Zero warnings.
- **Findings closed:** CRIT-06, HIGH-04, MED-03. Prior: HIGH-01 (WS-H13),
  HIGH-02 (WS-H12c).

## [0.14.8] - 2026-03-10

### WS-H16: Testing, Documentation & Cleanup

- **Part A (M-18):** Lifecycle negative tests — 10 new `expectError` tests in
  `NegativeStateSuite.lean` exercising error branches in `lifecycleRetypeObject`
  (non-existent target, metadata mismatch, insufficient authority, bad authority
  CNode), `lifecycleRevokeDeleteRetype` (authority = cleanup, bad cleanup CNode,
  non-existent retype target), and `retypeFromUntyped` (exhausted untyped,
  non-untyped source type mismatch, device untyped restriction).
- **Part B (A-43):** Semantic Tier 3 assertions — 13 new proof-surface anchors
  in `test_tier3_invariant_surface.sh` checking structural properties:
  `capabilityInvariantBundle` conjunct count, `schedulerInvariantBundleFull`
  component inclusion, `NonInterferenceStep` constructor count,
  `objectIndexLive` and `runQueueThreadPriorityConsistent` definitions and
  theorems, `runWSH16LifecycleChecks` test function, `schedule` O(1) RunQueue
  membership.
- **Part D (A-13):** `objectIndexLive` liveness invariant — new predicate in
  `Model/State.lean` with `objectIndexLive_default` theorem and
  `storeObject_preserves_objectIndexLive` preservation proof. Ensures every
  `objectIndex` entry resolves to a live object in the store.
- **Part D (A-19):** `runQueueThreadPriorityConsistent` predicate — new
  bi-directional consistency predicate in `Scheduler/Invariant.lean` with
  `runQueueThreadPriorityConsistent_default` theorem. Formalizes the invariant
  that every RunQueue member has a `threadPriority` entry and vice versa.
- **Part D (A-18):** O(n) membership check audit — confirmed `schedule` already
  uses O(1) `HashSet`-backed `RunQueue.contains` (not the O(n) `runnable` flat
  list alias). No code change required.
- **Documentation sync (M-21/A-45):** Updated `CLAUDE.md` file-size table,
  `README.md` metrics, `WORKSTREAM_HISTORY.md`, `CHANGELOG.md`, GitBook
  proof-and-invariant map.
- **Build jobs:** 138. Zero sorry/axiom.
- **Findings closed:** M-18, A-43, A-13, A-18, A-19, M-21/A-45.

## [0.14.7] - 2026-03-10

### WS-H15a–d: Platform & API Hardening

- **WS-H15a:** Added `Decidable` instance fields (`irqLineSupportedDecidable`,
  `irqHandlerMappedDecidable`) to `InterruptBoundaryContract`, enabling
  adapter code to branch on interrupt predicates using `if` without manual
  instance threading. Updated `simInterruptContract` and `rpi5InterruptContract`.
- **WS-H15b:** RPi5 platform contract hardening:
  - Added MMIO region definitions (`mmioRegions`) with disjointness proof
    (`mmioRegionDisjoint_holds`) via `native_decide`.
  - Proved `rpi5MachineConfig_wellFormed` (region sizes, overlaps, PA bounds).
  - Replaced `True` placeholder boot predicates with substantive checks
    (empty object store, empty capability refs at boot).
  - Strengthened `rpi5InterruptContract.irqHandlerMapped` from `True` to
    handler-map lookup validation.
  - Strengthened `rpi5RuntimeContract.registerContextStable` from `True` to
    SP-preservation-or-context-switch predicate.
- **WS-H15c:** Syscall capability-checking wrappers:
  - Added `SyscallGate` structure and `syscallLookupCap`/`syscallInvoke`
    combinators implementing the seL4 CSpace-lookup + rights-check pattern.
  - 3 soundness theorems: `syscallLookupCap_implies_capability_held`,
    `syscallLookupCap_state_unchanged`, `syscallInvoke_requires_right`.
  - 13 capability-gated `api*` wrappers: `apiEndpointSend`, `apiEndpointReceive`,
    `apiEndpointCall`, `apiEndpointReply`, `apiCspaceMint`, `apiCspaceCopy`,
    `apiCspaceMove`, `apiCspaceDelete`, `apiLifecycleRetype`, `apiVspaceMap`,
    `apiVspaceUnmap`, `apiServiceStart`, `apiServiceStop`.
  - Added `retype` variant to `AccessRight` enum.
- **WS-H15a (addendum):** Decidability consistency theorems:
  `irqLineSupported_decidable_consistent` and
  `irqHandlerMapped_decidable_consistent` proving `decide` agrees with the
  underlying predicate.
- **WS-H15d:** AdapterProofHooks concrete instantiation:
  - Generic `advanceTimerState_preserves_proofLayerInvariantBundle` theorem
    proving timer advancement preserves the full 7-conjunct invariant bundle.
  - `simRestrictiveAdapterProofHooks` concrete instance for the simulation
    restrictive runtime contract with 3 end-to-end theorems
    (`simRestrictive_adapterAdvanceTimer_preserves`,
    `simRestrictive_adapterWriteRegister_preserves`,
    `simRestrictive_adapterReadMemory_preserves`).
  - `rpi5RestrictiveAdapterProofHooks` concrete instance for the RPi5
    restrictive runtime contract (`rpi5RuntimeContractRestrictive`) with 3
    end-to-end theorems. Timer advancement uses the generic preservation
    lemma substantively; register write and memory read paths are vacuous
    (restrictive contract rejects all register writes).
  - Design note: production RPi5 contract (`rpi5RuntimeContract`) admits
    all register writes (because `writeReg` never modifies `sp`), making
    `contextMatchesCurrent` preservation unprovable for arbitrary writes.
    A future context-switch-aware adapter (WS-H3) will resolve this by
    combining register-file load with `scheduler.current` update atomically.
- **WS-H15e:** Testing and documentation:
  - 31 Tier 3 invariant surface anchors covering all WS-H15 additions.
  - Syscall capability-gating trace in `MainTraceHarness.lean` (5 scenarios:
    correct gate, bad root, insufficient rights, missing cap, retype gate).
  - 6 negative tests in `NegativeStateSuite.lean` exercising syscall
    capability-checking error paths.
  - 7 platform contract tests validating `rpi5MachineConfig.wellFormed`,
    `mmioRegionDisjointCheck`, GIC-400 IRQ boundary values (INTID 0, 223, 224),
    and boot contract predicates.
  - Stability table in `API.lean` updated with all 13 `api*` syscall wrappers.
  - Regenerated `docs/codebase_map.json`.
- **Build jobs:** 138 (up from 134). Zero sorry/axiom.

## [0.14.5] - 2026-03-10

### Codebase Module Restructuring

- **Module decomposition:** Decomposed 9 large monolithic files (1,000–5,800
  lines each) into 24 focused submodule files using the re-export hub pattern.
  Original files preserved as thin import hubs for full backward compatibility.
- **Model/Object.lean** → `Object/Types.lean` (core data types) +
  `Object/Structures.lean` (VSpaceRoot, CNode, KernelObject, CDT helpers).
- **Scheduler/Operations.lean** → `Operations/Selection.lean` (EDF predicates) +
  `Operations/Core.lean` (core transitions) +
  `Operations/Preservation.lean` (preservation theorems).
- **IPC/DualQueue.lean** → `DualQueue/Core.lean` (dual-queue operations) +
  `DualQueue/Transport.lean` (transport lemmas).
- **IPC/Operations.lean** → `Operations/Endpoint.lean` (core endpoint ops) +
  `Operations/SchedulerLemmas.lean` (scheduler preservation lemmas).
- **IPC/Invariant.lean** → `Invariant/Defs.lean` + `Invariant/EndpointPreservation.lean` +
  `Invariant/CallReplyRecv.lean` + `Invariant/NotificationPreservation.lean` +
  `Invariant/Structural.lean`.
- **Capability/Invariant.lean** → `Invariant/Defs.lean` + `Invariant/Authority.lean` +
  `Invariant/Preservation.lean`.
- **InformationFlow/Invariant.lean** → `Invariant/Helpers.lean` +
  `Invariant/Operations.lean` + `Invariant/Composition.lean`.
- **InformationFlow/Enforcement.lean** → `Enforcement/Wrappers.lean` +
  `Enforcement/Soundness.lean`.
- **Service/Invariant.lean** → `Invariant/Policy.lean` + `Invariant/Acyclicity.lean`.
- **Private definition visibility:** ~53 cross-module `private` definitions
  made non-private to support submodule access across file boundaries.
  Post-decomposition audit re-privatized 15 definitions that were only used
  within their own submodule file (11 CNode helper theorems, 4 projection
  preservation lemmas), tightening the API surface.
- **Tier 3 invariant surface tests:** Updated 209 anchor checks to reference
  new submodule file paths.
- **Build jobs:** Increased from 86 to 134 (finer-grained parallelism).
- **Zero sorry/axiom:** No regressions — all proof surface remains complete.

## [0.14.4] - 2026-03-10

### WS-H13: CSpace, Lifecycle & Service Model Enrichment

- **CSpace depth-consistency invariant (`cspaceDepthConsistent`):** Added to
  `capabilityInvariantBundle` as the 8th conjunct, ensuring every CNode has
  `depth ≤ maxCSpaceDepth` and well-formedness when `bitsConsumed > 0`. All
  preservation proofs updated for the expanded 8-tuple.
- **Multi-level `resolveCapAddress` theorems (Part A):**
  - `resolveCapAddress_deterministic` — pure function determinism.
  - `resolveCapAddress_zero_bits` — zero-bits returns `.error .illegalState`.
  - `resolveCapAddress_result_valid_cnode` — success implies the returned slot
    reference points to a valid CNode in the object store (proved by
    well-founded induction on `bitsRemaining`).
  - `resolveCapAddress_guard_reject` — guard mismatch at any CNode level
    returns `.error .invalidCapability` (attack surface coverage).
- **Service backing-object verification (Part C / A-29):**
  - `serviceStop` now verifies `st.objects[svc.identity.backingObject]? ≠ none`
    before allowing the transition. Returns `.backingObjectMissing` if absent.
  - Added `serviceStop_error_backingObjectMissing` theorem.
  - Updated `serviceStop_error_policyDenied` to require backing-object
    existence hypothesis.
  - All `serviceStop_preserves_*` theorems updated for the new branch.
  - `serviceStart` backing check already present from prior work.
- **`serviceGraphInvariant` preservation proofs (Part E / M-17):**
  - `serviceGraphInvariant` bundle (`serviceDependencyAcyclic ∧
    serviceCountBounded`) with preservation for `serviceRegisterDependency`,
    `serviceStart`, and `serviceStop`.
  - Added transfer lemmas: `serviceEdge_of_storeServiceState_sameDeps`,
    `serviceNontrivialPath_of_storeServiceState_sameDeps`,
    `serviceDependencyAcyclic_of_storeServiceState_sameDeps`,
    `bfsUniverse_of_storeServiceState_sameDeps`,
    `serviceCountBounded_of_storeServiceState_sameDeps`,
    `serviceGraphInvariant_of_storeServiceState_sameDeps`.
- **Capability move atomicity (Part B / A-21):**
  - `cspaceMove_error_no_state` — error-path exclusion: on error, no success
    state is reachable.
  - `cspaceMove_ok_implies_source_exists` — success-path: if move succeeds,
    the source slot had a valid capability.
  - Documented that the sequential kernel's `Except` monad provides implicit
    both-or-neither semantics: on error, no intermediate state is returned.
- **CNode field migration:** Updated `NegativeStateSuite.lean` CNode
  constructions from old `guard`/`radix` fields to new `depth`/`guardWidth`/
  `guardValue`/`radixWidth` fields.
- **Default-state proof updated:** `default_capabilityInvariantBundle` in
  `Architecture/Invariant.lean` extended to 8-tuple with
  `cspaceDepthConsistent` component.
- **`docs/codebase_map.json` regenerated.**
- **New negative tests (WS-H13):**
  - `MainTraceHarness`: service start with missing backing object
    (`backingObjectMissing` error).
  - `NegativeStateSuite`: `runWSH13Checks` — backing-object missing and
    restart start-stage failure (dependency violation).
- **Expected fixture updated:** `tests/fixtures/main_trace_smoke.expected`
  updated with 1 new output line (110 total).
- **Zero sorry/axiom, zero warnings.** Build: 86 jobs, zero errors.
- **All tests pass:** `test_full.sh` (Tier 0-3) clean.
- **Findings addressed:** H-01 (multi-level CSpace resolution), A-29 (service
  backing-object verification), A-21 (capability move atomicity), A-30
  (service restart implicit rollback via error monad), M-17/A-31
  (`serviceCountBounded` invariant).

## [0.14.3] - 2026-03-09

### WS-H12f: Test Harness Update & Documentation Sync

- **Dequeue-on-dispatch trace scenario:** Added `runDequeueOnDispatchTrace` to
  `MainTraceHarness.lean` exercising the full dequeue-on-dispatch lifecycle:
  schedule selects highest-priority thread and dequeues it from `runQueue`,
  non-dispatched thread remains in queue, and after preemption (timer tick
  expiry) the preempted thread is re-enqueued while a higher-priority thread
  takes over.
- **Inline context switch trace scenario:** Added `runInlineContextSwitchTrace`
  demonstrating that `handleYield` → `schedule` saves the outgoing thread's
  `machine.regs` into its TCB `registerContext` and restores the incoming
  thread's `registerContext` into `machine.regs`, establishing
  `contextMatchesCurrent` atomically.
- **Bounded message extended trace scenario:** Added
  `runBoundedMessageExtendedTrace` verifying boundary behavior: zero-length
  messages accepted, sub-boundary messages (119 registers) accepted, and
  max-cap messages (3 caps) accepted — complementing the existing WS-H12d
  rejection tests.
- **Legacy `endpointInvariant` comment cleanup:** Removed stale comments in
  `IPC/Invariant.lean` referencing the deleted legacy endpoint fields (`state`,
  `queue`, `waitingReceiver`) and `endpointQueueWellFormed`. Updated
  preservation theorem docstrings to reference `ipcInvariant` (notification
  well-formedness) instead of the removed `endpointInvariant`.
- **Expected fixture updated:** `tests/fixtures/main_trace_smoke.expected`
  updated to include all 11 new trace output lines (108 total, up from 98).
- **Tier 3 invariant surface anchors:** Added 9 new anchors to
  `test_tier3_invariant_surface.sh` for WS-H12f trace functions and fixture
  output lines.
- **Documentation synchronized:** CHANGELOG, SELE4N_SPEC, DEVELOPMENT,
  CLAIM_EVIDENCE_INDEX, codebase_map.json, README, and GitBook chapters
  updated to reflect WS-H12f completion and WS-H12 composite closure.
- **`docs/codebase_map.json` regenerated.**
- **Zero sorry/axiom, zero warnings.** Build: 86 jobs, zero errors.
- **Findings addressed:** Documentation component of all WS-H12 findings
  (A-08/M-01/A-25, H-04, H-03, A-09). Completes WS-H12 composite workstream.

## [0.14.2] - 2026-03-09

### WS-H12e: Cross-Subsystem Invariant Reconciliation

- **`schedulerInvariantBundleFull` expanded:** Added `contextMatchesCurrent`
  (from WS-H12c) as the 5th conjunct to the full scheduler invariant bundle.
  Previously the register-context coherence invariant was defined and preserved
  but orphaned from all composition bundles.
- **`coreIpcInvariantBundle` strengthened:** Updated from `ipcInvariant` to
  `ipcInvariantFull` (which composes `ipcInvariant ∧ dualQueueSystemInvariant ∧
  allPendingMessagesBounded`). The M3 seed bundle now includes dual-queue
  structural well-formedness and message payload bounds in the cross-subsystem
  proof surface.
- **`ipcSchedulerCouplingInvariantBundle` extended:** Added
  `contextMatchesCurrent` and `currentThreadDequeueCoherent` to the M3.5
  coupling bundle, ensuring register-context coherence and dequeue-on-dispatch
  predicates are composed into the cross-subsystem invariant.
- **`proofLayerInvariantBundle` upgraded:** Uses `schedulerInvariantBundleFull`
  (5-conjunct, with `contextMatchesCurrent`) instead of the bare
  `schedulerInvariantBundle` (3-conjunct). The top-level architecture proof
  surface now includes all WS-H12a–d invariant additions.
- **Extraction theorems:** Added `coreIpcInvariantBundle_to_ipcInvariant`,
  `coreIpcInvariantBundle_to_dualQueueSystemInvariant`,
  `coreIpcInvariantBundle_to_allPendingMessagesBounded`, and
  `schedulerInvariantBundleFull_to_contextMatchesCurrent` for backward-compatible
  proof composition.
- **`switchDomain_preserves_contextMatchesCurrent`:** New preservation theorem
  for `contextMatchesCurrent` through domain switches (vacuous when
  `current = none` after switch, unchanged in single-domain no-op).
- **Default state proof updated:** `default_system_state_proofLayerInvariantBundle`
  extended with proofs for `dualQueueSystemInvariant`, `allPendingMessagesBounded`,
  `contextMatchesCurrent`, `currentThreadDequeueCoherent`, and
  `schedulerInvariantBundleFull` on the default (empty) system state.
- **`contextMatchesCurrent` relocated:** Moved definition before
  `schedulerInvariantBundleFull` in `Scheduler/Invariant.lean` to resolve
  forward-reference issue in bundle composition.
- **Preservation theorem updates:** Updated all 4 `*_preserves_schedulerInvariantBundleFull`
  theorems (`schedule`, `handleYield`, `timerTick`, `switchDomain`) to include
  `contextMatchesCurrent` in destructuring and construction.
  Updated `lifecycleRetypeObject_preserves_coreIpcInvariantBundle` and
  `lifecycleRetypeObject_preserves_lifecycleCompositionInvariantBundle` for
  the enriched bundle signatures.
- **`allPendingMessagesBounded` frame lemmas:** Added 8 primitive-operation
  frame lemmas (`ensureRunnable`, `removeRunnable`, `storeTcbIpcState`,
  `storeTcbIpcStateAndMessage`, `storeTcbPendingMessage`, `storeObject_endpoint`,
  `storeTcbQueueLinks`, `storeObject_notification`) proving each operation
  preserves the `allPendingMessagesBounded` system invariant.
- **Compound `allPendingMessagesBounded` preservation:** Added
  `notificationSignal_preserves_allPendingMessagesBounded`,
  `notificationWait_preserves_allPendingMessagesBounded`, and
  `endpointReply_preserves_allPendingMessagesBounded` — full proofs composing
  frame lemmas for multi-step IPC operations.
- **Composed `ipcInvariantFull` preservation theorems:** Added 7 theorems
  (`notificationSignal`, `notificationWait`, `endpointReply`,
  `endpointSendDual`, `endpointReceiveDual`, `endpointCall`,
  `endpointReplyRecv`) each proving preservation of the full 3-conjunct
  `ipcInvariantFull` bundle.
- **Tier 3 invariant surface anchors:** Updated `coreIpcInvariantBundle` body
  anchor from `ipcInvariant` to `ipcInvariantFull`. Added 30 new anchors for
  WS-H12e invariant definitions, extraction theorems, frame lemmas, compound
  preservation theorems, and composed `ipcInvariantFull` preservation proofs.
- **`docs/codebase_map.json` regenerated.**
- **Zero sorry/axiom, zero warnings:** Full production proof surface verified
  clean. Build produces 86 jobs, zero errors and zero warnings.
- **Findings addressed:** Systemic invariant composition gaps from WS-H12a–d.
  Completed deferred `allPendingMessagesBounded` preservation from WS-H12d.

## [0.14.1] - 2026-03-09

### WS-H12d: IPC Message Payload Bounds

- **Bounded IPC message type:** Replaced unbounded `List Nat` / `List Capability`
  in `IpcMessage` with bounded `Array Nat` / `Array Capability`, matching seL4's
  `seL4_MsgMaxLength` (120) and `seL4_MsgMaxExtraCaps` (3) limits.
- **Message size constants:** Added `maxMessageRegisters` (120) and `maxExtraCaps`
  (3) to `Model/Object.lean`, matching seL4's standard configuration.
- **Bounds enforcement at send boundaries:** All four IPC send operations
  (`endpointSendDual`, `endpointCall`, `endpointReply`, `endpointReplyRecv`)
  and the policy-checked `endpointSendDualChecked` now validate payload size
  before proceeding. Oversized payloads return `ipcMessageTooLarge` or
  `ipcMessageTooManyCaps` errors.
- **New error variants:** Added `KernelError.ipcMessageTooLarge` and
  `KernelError.ipcMessageTooManyCaps` for bounds violation reporting.
- **`IpcMessage.bounded` predicate:** Formal proposition asserting registers
  and caps satisfy seL4 bounds. `IpcMessage.checkBounds` provides decidable
  runtime checking. `checkBounds_iff_bounded` bridges the two.
- **Send-produces-bounded-message theorems:** Proved `endpointSendDual_message_bounded`,
  `endpointCall_message_bounded`, `endpointReply_message_bounded`, and
  `endpointReplyRecv_message_bounded` — if the operation succeeds, the message
  satisfies `IpcMessage.bounded`.
- **`allPendingMessagesBounded` system invariant:** Added to `IPC/Invariant.lean`,
  asserting all pending messages in TCBs satisfy payload bounds. Integrated into
  `ipcInvariantFull` 3-conjunct bundle (ipcInvariant ∧ dualQueueSystemInvariant ∧
  allPendingMessagesBounded) — preservation theorems implemented in WS-H12e.
- **Enforcement theorem updates:** Updated `endpointSendDualChecked_flowDenied`
  to require `msg.checkBounds = true` (bounds checks precede flow checks).
  Updated `enforcement_sufficiency_endpointSendDual` to include bounds-error
  cases in the complete disjunction. Updated `enforcementSoundness_endpointSendDualChecked`
  with bounds-check elimination.
- **~40 invariant preservation proofs updated:** All IPC/capability/info-flow
  preservation theorems that unfold send operations now handle the new
  bounds-check if-branches via contradiction (error ≠ ok).
- **Trace verification:** Added 5 H12d trace scenarios verifying oversized
  registers/caps rejection, boundary acceptance, and cross-operation coverage.
- **Negative tests:** Added 10 negative tests in `NegativeStateSuite` for all
  four IPC send operations with oversized registers and oversized caps, plus
  boundary-exact message acceptance.
- **Zero sorry/axiom, zero warnings:** Full production proof surface verified
  clean. Build produces zero errors and zero warnings.
- **Finding closed:** A-09 (HIGH, IpcMessage unbounded payload).

## [0.14.0] - 2026-03-09

### WS-H12c: Per-TCB Register Context with Inline Context Switch

- **Per-TCB register save area:** Added `registerContext : RegisterFile`
  field to TCB structure (`Model/Object.lean`), with `default` initialization.
  Each thread now carries its own register file, matching seL4's per-TCB
  `tcbContext` (ARM `user_context_t`).
- **Inline context save/restore in `schedule`:** `schedule` now performs
  `saveOutgoingContext` (saves `machine.regs` into the outgoing TCB's
  `registerContext`) and `restoreIncomingContext` (loads the incoming TCB's
  `registerContext` into `machine.regs`) directly inline, matching seL4's
  `switchToThread` → `Arch_switchToThread` → `vcpu_switch`/`setVMRoot`
  context-switch path.
- **`saveOutgoingContext`/`restoreIncomingContext` functions:** Public
  definitions with `@[simp]` frame lemmas proving scheduler/objects
  preservation, enabling downstream proof automation.
- **`contextMatchesCurrent` invariant:** Added to `Scheduler/Invariant.lean`
  — states that `st.machine.regs = tcb.registerContext` when a thread is
  current, formalizing the register-context coherence property.
- **`endpointInvariant` removal:** Completely removed the deprecated
  `endpointInvariant` predicate and all references from `IPC/Invariant.lean`,
  `Capability/Invariant.lean`, and `Architecture/Invariant.lean`. Simplifies
  `ipcInvariant` to its essential predicates.
- **Information-flow projection update:** Modified `projectKernelObject` in
  `Projection.lean` to strip `registerContext` from TCBs (replacing with
  `default`), ensuring register contents don't leak through the information-flow
  projection.
- **Projection preservation proofs:** Added `saveOutgoingContext_preserves_projection`,
  `restoreIncomingContext_preserves_projection`, and
  `saveOutgoingContext_with_sched_preserves_projection` theorems in
  `InformationFlow/Invariant.lean`, proving context switch preserves
  low-equivalence.
- **Frame lemma suite:** Added `saveOutgoingContext_preserves_tcb`,
  `saveOutgoingContext_tcb_fields`, `saveOutgoingContext_preserves_non_tcb_lookup`,
  `saveOutgoingContext_preserves_timeSlicePositive`, and
  `restoreIncomingContext_preserves_timeSlicePositive`.
- **Scheduler preservation proofs:** Added `schedule_preserves_contextMatchesCurrent`,
  `handleYield_preserves_contextMatchesCurrent`, `timerTick_preserves_contextMatchesCurrent`,
  and `contextMatchesCurrent_frame` general frame theorem to `Scheduler/Operations.lean`.
- **IPC preservation proofs:** Added `storeObject_preserves_contextMatchesCurrent`,
  `storeTcbIpcState_preserves_contextMatchesCurrent`,
  `storeTcbIpcStateAndMessage_preserves_contextMatchesCurrent`,
  `storeTcbPendingMessage_preserves_contextMatchesCurrent`,
  `storeTcbQueueLinks_preserves_contextMatchesCurrent`,
  `ensureRunnable_preserves_contextMatchesCurrent`, and
  `removeRunnable_preserves_contextMatchesCurrent` to `IPC/Invariant.lean`.
- **Trace verification:** Added context switch trace scenario to `MainTraceHarness`
  verifying `machine.regs` matches the incoming thread's `registerContext` after
  `schedule`.
- **Zero sorry/axiom, zero warnings:** Full production proof surface verified
  clean. Build produces zero errors and zero warnings.
- **Finding closed:** H-03 (HIGH, no per-TCB register context).

## [0.13.9] - 2026-03-09

### WS-H12b: Dequeue-on-Dispatch Scheduler Semantics

- **Scheduler invariant inversion:** Changed `queueCurrentConsistent` from
  `current = some tid → tid ∈ runnable` to `current = some tid → tid ∉ runnable`,
  matching seL4's `switchToThread`/`tcbSchedDequeue` dequeue-on-dispatch
  semantics where the running thread is removed from the ready queue at
  dispatch time.
- **`schedule` dequeue-on-dispatch:** `schedule` now dequeues the chosen
  thread from the run queue before dispatching via `setCurrentThread`,
  mirroring seL4's `switchToThread` → `tcbSchedDequeue` path.
- **`handleYield` re-enqueue:** Since the current thread is not in the run
  queue, `handleYield` now inserts the current thread and rotates to back
  before calling `schedule`, matching seL4's `handleYield` →
  `tcbSchedDequeue` + `tcbSchedAppend` path.
- **`timerTick` re-enqueue on preemption:** On time-slice expiry,
  `timerTick` inserts the current thread back into the run queue before
  scheduling, mirroring seL4's `timerInterrupt` → `rescheduleRequired` →
  `tcbSchedEnqueue` → `schedule` path.
- **`switchDomain` re-enqueue:** `switchDomain` re-enqueues the current
  thread before the domain switch so the outgoing thread returns to the
  runnable pool for its next domain slot.
- **`currentTimeSlicePositive` predicate:** Added predicate to ensure the
  current thread's time slice is positive (not covered by `timeSlicePositive`
  since the current thread is no longer in the run queue).
  `schedulerInvariantBundleFull` extended to include `currentTimeSlicePositive`.
- **`schedulerPriorityMatch` predicate:** Added predicate and supporting
  theorems `RunQueue.insert_preserves_wellFormed` and
  `insert_threadPriority` for priority consistency.
- **IPC invariant updates:** Added `currentThreadIpcReady`,
  `currentNotEndpointQueueHead`, `currentNotOnNotificationWaitList`, and
  `currentThreadDequeueCoherent` predicates to `IPC/Invariant.lean`.
  Updated 23 cross-subsystem proof sites.
- **Information-flow invariant updates:** Updated 5 error sites in
  `InformationFlow/Invariant.lean` with new helper theorems for the
  inverted scheduler semantics.
- **Helper lemmas:** Added `ensureRunnable_not_mem_of_not_mem` and
  `removeRunnable_not_mem_of_not_mem` to `Scheduler/Operations.lean`;
  added `ThreadId.ext` theorem to `Prelude.lean`.
- **Test invariant checker:** Updated `Testing/InvariantChecks.lean` to
  verify dequeue-on-dispatch semantics at runtime.
- **~1800 lines of preservation proofs** re-proved across
  `Scheduler/Operations.lean`, `IPC/Invariant.lean`, and
  `InformationFlow/Invariant.lean`.
- **Finding closed:** H-04 (HIGH, running thread stays in ready queue).

## [0.13.8] - 2026-03-09

### WS-H12a: Legacy Endpoint Field & Operation Removal

- **Legacy endpoint fields removed:** Deleted `EndpointState` inductive type
  and three legacy fields (`state`, `queue`, `waitingReceiver`) from the
  `Endpoint` structure. Endpoint now contains only `sendQ`/`receiveQ`
  intrusive queues.
- **Legacy IPC operations deleted:** Removed `endpointSend`,
  `endpointAwaitReceive`, `endpointReceive` from `IPC/Operations.lean` and
  `endpointSendChecked` from `InformationFlow/Enforcement.lean`. All IPC now
  uses exclusively the O(1) dual-queue path (`endpointSendDual`/
  `endpointReceiveDual`).
- **Legacy KernelOperation entries removed:** Deleted `endpointSend`,
  `endpointAwaitReceive`, `endpointReceive` from `KernelOperation` inductive
  and `TransitionSurface` in `Architecture/Assumptions.lean`.
- **Legacy theorem cleanup:** Deleted ~60 legacy preservation theorems from
  `IPC/Invariant.lean`, `Capability/Invariant.lean`,
  `InformationFlow/Invariant.lean`, and `InformationFlow/Enforcement.lean`
  that proved preservation for deleted operations.
- **endpointInvariant rewrite:** Redefined `endpointInvariant` as vacuous
  (`True`) for structural compatibility. Actual dual-queue well-formedness
  is enforced system-wide via `dualQueueSystemInvariant` (per-endpoint
  `dualQueueEndpointWellFormed` + `tcbQueueLinkIntegrity`).
- **endpointReplyRecv fix:** Migrated `endpointReplyRecv` from legacy
  `endpointAwaitReceive` to `endpointReceiveDual`, completing the dual-queue
  transition for all compound IPC operations.
- **Test migration:** `NegativeStateSuite`, `InformationFlowSuite`, and
  `TraceSequenceProbe` updated to use dual-queue operations exclusively.
  All endpoint fixtures use only `sendQ`/`receiveQ` fields.
- **Tier-3 anchor updates:** Removed stale legacy anchors from
  `test_tier3_invariant_surface.sh`; updated counts and added new
  dual-queue-only anchors.
- **Findings closed:** A-08 (HIGH, redundant legacy endpoint fields), M-01
  (MEDIUM, redundant legacy endpoint fields), A-25 (MEDIUM, legacy O(n) IPC
  retained without deprecation path).

## [0.13.7] - 2026-03-08

### WS-H11: VSpace & Architecture Enrichment

- **Part A — PagePermissions & W^X enforcement:** `PagePermissions` struct with
  `wxCompliant` predicate; W^X enforced at insertion time in `vspaceMapPage`;
  enriched mappings `HashMap VAddr (PAddr × PagePermissions)` with
  `vspaceLookupFull` returning permissions alongside physical address.
- **Part B — Address bounds check:** `vspaceMapPageChecked` rejects physical
  addresses ≥ 2^52 (ARM64 52-bit PA bound); `physicalAddressBound` constant;
  `addressOutOfBounds` error variant; preservation theorem
  `vspaceMapPageChecked_success_preserves_vspaceInvariantBundle`.
- **Part C — ASID uniqueness & consistency:** `asidTableConsistent` and
  `vspaceAsidRootsUnique` in the 5-conjunct `vspaceInvariantBundle`;
  `resolveAsidRoot` extraction and characterization lemmas.
- **Part D — TLB/cache maintenance model:** `TlbEntry`, `TlbState`,
  `adapterFlushTlb`, `adapterFlushTlbByAsid`, `tlbConsistent`; abstract TLB
  model with full and per-ASID flush operations proven correct.
- **VSpaceBackend typeclass:** Platform-agnostic VSpace operations abstraction
  with `hashMapVSpaceBackend` instance; prepares for ARM page table backend.
- **ASID table composition:** Explicit `resolveAsidRoot` agreement theorems
  for `vspaceMapPage` and `vspaceUnmapPage`, proving ASID table consistency
  is preserved through page table modifications.
- **TLB selectivity:** `adapterFlushTlbByAsid_removes_matching` and
  `adapterFlushTlbByAsid_preserves_other` theorems proving per-ASID flush
  removes exactly matching entries and preserves all others.
- **Per-VAddr TLB flush:** `adapterFlushTlbByVAddr` operation (ARM64 `TLBI VAE1`)
  with preservation, selectivity, and composition theorems; targeted flush for
  single page table entry modifications.
- **Cross-ASID TLB isolation:** `cross_asid_tlb_isolation` theorem proving
  per-ASID flush on one ASID does not affect TLB entries belonging to a
  different ASID — key security property for multi-address-space systems.
- **Proof deduplication:** Extracted `VSpaceRoot.mapPage_mappings_insert`,
  `VSpaceRoot.unmapPage_mappings_erase`, and `HashMap_lookup_of_erase_lookup`
  helper lemmas, reducing duplicated proof code in VSpaceInvariant.lean.
- **Testing:** 19+ new negative-state tests covering W^X, address bounds, ASID
  errors, TLB flush (full, per-ASID, per-VAddr), permission round-trip,
  cross-ASID isolation, multiple concurrent mappings, and map-unmap-remap
  cycles; 3 new MainTraceHarness traces (VSPACE-05..07).

## [0.13.6] - 2026-03-08

### End-to-End Codebase Audit

- **Comprehensive audit:** Full end-to-end audit of all 40 production Lean
  files (29,351 LoC), 866 theorem/lemma declarations, 3 test suites (2,063
  LoC), build scripts, platform bindings, and documentation. Zero critical
  issues found. Zero sorry/axiom confirmed across the entire codebase.
- **A-v13.6-01 (MEDIUM): Stale theorem count in spec.** Fixed
  `docs/spec/SELE4N_SPEC.md` theorem count from 833 to 866.
- **A-v13.6-02 (MEDIUM): Stale metrics in gitbook.** Fixed
  `docs/gitbook/17-project-usage-value.md` LoC from 26,194 to 29,351 and
  theorem count from 753 to 866.
- **A-v13.6-06 (LOW): Stale milestone reference.** Fixed milestone
  progression reference from "WS-B..F" to "WS-B..H" in gitbook.
- **Documentation sync:** Updated README.md, SELE4N_SPEC.md, DEVELOPMENT.md,
  CLAIM_EVIDENCE_INDEX.md, and 5 GitBook chapters with audit workstream
  entry, latest audit reference, and corrected metrics.
- **Audit report:** Created `docs/audits/AUDIT_CODEBASE_v0.13.6.md` with
  detailed findings across all subsystems, security property verification,
  performance characteristic confirmation, and test coverage assessment.

### WS-H10: Security Model Foundations

- **C-05/A-38 (CRITICAL): MachineState projection in IF model.** Extended
  `ObservableState` with `machineRegs : Option RegisterFile` — the machine
  register file is projected through current-thread observability gating
  (visible only when the executing thread is observable). Machine timer is
  deliberately excluded to prevent covert timing channels. Machine memory
  projection deferred to WS-H11 (VSpace domain ownership model required).
  All 863 proved declarations updated — zero sorry/axiom.
- **A-34 (CRITICAL): Security lattice resolution.** Added formal threat model
  justification documenting the legacy integrity model as a valid "write-up"
  policy. Introduced `bibaIntegrityFlowsTo`, `bibaSecurityFlowsTo`, and
  `bibaPolicy` as standard BIBA alternatives with reflexivity/transitivity
  proofs. Added `securityLattice_reflexive` and `securityLattice_transitive`
  alias theorems confirming the legacy lattice forms a valid pre-order.
- **A-39 (MEDIUM): Declassification model.** Added `DeclassificationPolicy`
  structure with `canDeclassify` predicate, `DeclassificationPolicy.none`
  (strictest policy), and `isDeclassificationAuthorized` (base policy denial +
  declass authorization). Added `declassifyStore` operation in Enforcement.lean
  with 5 theorems: authorization equivalence, normal-flow rejection,
  declass-denied rejection, state preservation on denial, and enforcement
  soundness.
- **M-16 (MEDIUM): Endpoint flow policy well-formedness.** Added
  `endpointFlowPolicyWellFormed` predicate requiring both global and per-
  endpoint override policies to satisfy reflexivity + transitivity. Added
  `endpointFlowPolicyWellFormed_no_overrides`, `endpointFlowCheck_reflexive`,
  and `endpointFlowCheck_transitive` theorems.
- **Declassification NI theorem (C.10).** Added `declassifyStore_NI` — proves
  that declassification at a non-observable target preserves low-equivalence
  for non-target observers (the key NI property for controlled downgrade).
- **IF configuration invariant bundle.** Added `InformationFlowConfigInvariant`
  structure collecting global policy well-formedness, per-endpoint override
  well-formedness, and declassification consistency. Added
  `defaultConfigInvariant` existence proof. Kernel transitions trivially
  preserve the bundle since policies are external to `SystemState`.
- **Strengthened `declassifyStore_denied_no_state_change`.** Replaced
  the previously trivial (`True`) state preservation theorem with a proper
  proof that no successful result exists when the operation returns an error.
- **Version bump:** `lakefile.toml` version updated to 0.13.6.
- **Documentation sync:** Updated README.md, SELE4N_SPEC.md, DEVELOPMENT.md,
  CLAIM_EVIDENCE_INDEX.md, and GitBook chapters with current metrics and
  WS-H10 completion.
- **866 proved declarations. Zero sorry/axiom. Zero warnings. `test_full.sh` passes.**

## [0.13.5] - 2026-03-08

### Comprehensive Audit Remediation & WS-H Completion

- **WS-H8 gap closure:** Added `endpointReceiveDualChecked_NI` bridge theorem
  connecting the enforcement-checked receive wrapper to non-interference
  guarantees. All 5 enforced operations now have complete NI bridge theorems.
- **WS-H9 IPC NI completion:** Added `endpointReceiveDual_preserves_lowEquivalent`,
  `endpointCall_preserves_lowEquivalent`, and
  `endpointReplyRecv_preserves_lowEquivalent` theorems using the hypothesis-based
  bridge pattern. These close the remaining ~6% gap in NI coverage.
- **NonInterferenceStep extended to 31 constructors:** Added
  `endpointReceiveDualHigh`, `endpointCallHigh`, and `endpointReplyRecvHigh`
  constructors with projection preservation hypotheses. Up from 28 constructors.
- **WS-H7 BEq soundness lemmas:** Added `VSpaceRoot.beq_sound` and
  `CNode.beq_sound` theorems proving the fold-based HashMap comparison extracts
  correct structural fields (ASID, size, guard, radix).
- **Version bump:** `lakefile.toml` version updated to 0.13.5.
- **Documentation sync:** Updated README.md (28,713 LoC, 840 theorems), CLAUDE.md
  (large file sizes), SELE4N_SPEC.md, DEVELOPMENT.md, CLAIM_EVIDENCE_INDEX.md,
  and 5 GitBook chapters (overview, spec/roadmap, audit/quality, proof map,
  threat model) with current metrics, WS-H9 completion, and corrected next
  workstream references (WS-H10..H16).
- **Codebase map regenerated** to reflect new declarations.
- **840 proved declarations. Zero sorry/axiom. Zero warnings. `test_full.sh` passes.**

## [0.13.4] - 2026-03-07

### WS-H9: Non-Interference Coverage Extension

- **NI coverage extended from ~25% to >80% (C-02/A-40 CRITICAL):** Added 27
  new non-interference preservation theorems covering scheduler, IPC, CSpace,
  VSpace, and observable-state operations. Total NI theorems in
  `Invariant.lean`: 69 (up from ~19). Proof surface covers all kernel
  transitions that modify security-relevant state.
- **NonInterferenceStep inductive extended to 28 constructors (M-15 MEDIUM):**
  Up from 11 constructors. Covers: `chooseThread`, `endpointSend`,
  `cspaceMint`, `cspaceRevoke`, `lifecycleRetype`, `notificationSignal`,
  `notificationWait`, `cspaceInsertSlot`, `serviceStart`, `serviceStop`,
  `serviceRestart`, `schedule`, `vspaceMapPage`, `vspaceUnmapPage`,
  `vspaceLookup`, `cspaceCopy`, `cspaceMove`, `cspaceDeleteSlot`,
  `endpointReply`, `storeObjectHigh`, `setCurrentThread`,
  `ensureRunnableHigh`, `removeRunnableHigh`,
  `storeTcbIpcStateAndMessageHigh`, `storeTcbQueueLinksHigh`,
  `cspaceMutateHigh`, `handleYield`, `timerTick`.
- **Scheduler NI proofs (Part A):** `schedule_preserves_projection` (with
  high-current and all-runnable-high side conditions),
  `setCurrentThread_preserves_projection`,
  `ensureRunnable_preserves_projection`,
  `removeRunnable_preserves_projection`,
  `rotateToBack_preserves_projection`,
  `handleYield_preserves_projection` / `_lowEquivalent`,
  `insert_tick_preserves_projection`,
  `timerTick_preserves_projection` / `_lowEquivalent`.
- **IPC NI proofs (Part B):** `endpointReply_preserves_projection` /
  `_lowEquivalent`, `storeTcbIpcStateAndMessage_preserves_projection`,
  `storeTcbQueueLinks_preserves_projection`,
  `storeTcbPendingMessage_preserves_projection`.
- **CSpace NI proofs (Part C):** `cspaceCopy_preserves_projection` /
  `_lowEquivalent`, `cspaceMove_preserves_projection` / `_lowEquivalent`,
  `cspaceDeleteSlot_preserves_projection` / `_lowEquivalent`,
  `cspaceMutate` handled via `cspaceMutateHigh` constructor.
- **VSpace NI proofs (Part D):** `vspaceMapPage_preserves_projection` /
  `_lowEquivalent`, `vspaceUnmapPage_preserves_projection` /
  `_lowEquivalent`, `vspaceLookup_preserves_state` / `_lowEquivalent`.
- **Observable-state NI (Part E):** `storeObject_preserves_projection`,
  `storeCapabilityRef_preserves_projection`, CDT-only helpers
  (`cdt_only_preserves_projection`, `ensureCdtNodeForSlot_preserves_projection`,
  `attachSlotToCdtNode_preserves_projection`).
- **switchDomain two-sided NI (Part A supplement):**
  `switchDomain_preserves_lowEquivalent` — domain switching modifies scheduler
  globals so one-sided projection is NOT preserved, but two-sided
  low-equivalence IS preserved since both states see the same domain change.
- **RunQueue filter_erase_of_false fix:** Corrected Bool/Prop coercion in
  `SeLe4n/Kernel/Scheduler/RunQueue.lean`.
- **827 proved declarations. Zero sorry/axiom. `test_full.sh` passes.**

## [0.13.3] - 2026-03-07

### WS-H6: EDF Scheduler Proof Completion

- **EDF bridge theorem completed (A-14/H-06 CRITICAL):** `chooseBestInBucket_edf_bridge` —
  proves that `chooseBestInBucket` result is EDF-optimal among all domain-eligible
  runnable threads at the same priority level. Handles both bucket-success and
  full-scan-fallback paths using RunQueue well-formedness and priority-match
  external predicates.
- **RunQueue well-formedness predicate (H-06):** `RunQueue.wellFormed` — external
  predicate capturing the implicit invariant maintained by insert/remove/rotate
  API: forward (bucket→membership+threadPriority) and reverse
  (membership→bucket) consistency.
- **RunQueue well-formedness lemmas (H-06):** `maxPriorityBucket_subset`,
  `maxPriorityBucket_threadPriority`, `mem_maxPriorityBucket_of_threadPriority`
  — bridge lemmas connecting well-formedness to bucket-first EDF scheduling.
- **Rotation preserves well-formedness (H-06):** `rotateToBack_preserves_wellFormed`
  and 6 field-preservation lemmas (`rotateToBack_membership`,
  `rotateToBack_threadPriority`, `rotateToBack_maxPriority`,
  `rotateToBack_contains`, `rotateToBack_mem_iff`,
  `rotateToBack_flat_subset`, `rotateToBack_flat_superset`) — proves that
  `rotateToBack` preserves `wellFormed` and all RunQueue structural fields.
- **External priority-match predicate (H-06):** `schedulerPriorityMatch` —
  bridges RunQueue's internal `threadPriority` to authoritative TCB priority
  in the object store.
- **Full EDF preservation chain (H-06):**
  `schedule_preserves_edfCurrentHasEarliestDeadline`,
  `handleYield_preserves_edfCurrentHasEarliestDeadline`,
  `timerTick_preserves_edfCurrentHasEarliestDeadline` — all sorry-free.
- **Full bundle composition (H-06):**
  `schedule_preserves_schedulerInvariantBundleFull`,
  `handleYield_preserves_schedulerInvariantBundleFull`,
  `timerTick_preserves_schedulerInvariantBundleFull`.
- **Fold result membership lemma (H-06):**
  `chooseBestRunnableBy_result_mem_aux` and `chooseBestRunnableBy_result_mem` —
  proves that `chooseBestRunnableBy` result is drawn from the scanned list.
- **Zero sorry/axiom.** `test_full.sh` passes (Tier 0-3).

## [0.13.2] - 2026-03-07

### WS-H8: Enforcement-NI Bridge & Missing Wrappers

- **Enforcement-NI bridge connected (A-35/H-07 CRITICAL):** Added enforcement
  soundness meta-theorems (`enforcementSoundness_endpointSendDualChecked`,
  `enforcementSoundness_notificationSignalChecked`,
  `enforcementSoundness_cspaceCopyChecked`,
  `enforcementSoundness_cspaceMoveChecked`,
  `enforcementSoundness_endpointReceiveDualChecked`) proving that checked
  operation success implies the `securityFlowsTo` check passed. These form the
  foundational bridge connecting the enforcement layer to non-interference
  hypotheses.
- **4 new enforcement wrappers (H-07 HIGH):** `notificationSignalChecked`,
  `cspaceCopyChecked`, `cspaceMoveChecked`, `endpointReceiveDualChecked` —
  each gates on `securityFlowsTo` before delegating to the unchecked operation.
  Enforcement boundary extended from 3 to 8 policy-gated operations.
- **NI bridge theorems:** `endpointSendDualChecked_NI`,
  `notificationSignalChecked_NI`, `cspaceCopyChecked_NI`,
  `cspaceMoveChecked_NI` — each proves that if the checked wrapper succeeds,
  low-equivalence is preserved (cspaceCopy/Move take underlying NI as
  hypothesis pending WS-H9 decomposition lemmas).
- **Projection hardening (A-36/A-37/H-11 HIGH):** Extended `ObservableState`
  with `domainTimeRemaining`, `domainSchedule`, `domainScheduleIndex` fields.
  Added projection helpers and updated all 19 NI theorems in Invariant.lean.
  `activeDomain` kept always-visible as deliberate scheduling transparency.
- **Correctness theorems:** `*_eq_*_when_allowed` (4), `*_flowDenied` (4),
  `*_denied_preserves_state` (4), `enforcement_sufficiency_*` (4) for all
  new wrappers.
- **Extended enforcement boundary:** `enforcementBoundaryExtended` — 8
  policy-gated operations (up from 3 in `enforcementBoundary`).
- **Test coverage:** 12 new executable tests in `InformationFlowSuite.lean`
  covering same-domain match, cross-domain denial, boundary classification,
  and domain timing metadata projection.
- **26 new theorems.** Zero sorry/axiom. `test_full.sh` passes (Tier 0-3).
  779 proved theorems total.

## [0.13.1] - 2026-03-07

### WS-H6: Scheduler Proof Completion (partial)

- **Time-slice positivity fully proven (A-15/H-08 CRITICAL):** Added preservation
  theorems for `timeSlicePositive` across all scheduler operations:
  `setCurrentThread_preserves_timeSlicePositive`,
  `chooseThread_preserves_timeSlicePositive`,
  `schedule_preserves_timeSlicePositive`,
  `handleYield_preserves_timeSlicePositive`,
  `switchDomain_preserves_timeSlicePositive`,
  `timerTick_preserves_timeSlicePositive`. Previously defined but with zero proofs.
- **Candidate selection optimality proven (A-17/M-05/M-06 HIGH):**
  `isBetterCandidate_transitive` (strict partial order completion),
  `isBetterCandidate_not_better_trans` (negation transitivity),
  `chooseBestRunnableBy_optimal_combined` and `chooseBestRunnableBy_optimal`
  (fold-based selection produces no strictly better alternative).
- **EDF invariant definition fixed (A-14 design gap):**
  `edfCurrentHasEarliestDeadline` previously quantified over all runnable threads
  regardless of scheduling domain, which was unprovable for the domain-aware
  scheduler. Added `tcb.domain = curTcb.domain` constraint to align the invariant
  with `chooseBestRunnableInDomain` semantics.
- **EDF bridge lemma:** `noBetter_implies_edf` — converts `isBetterCandidate = false`
  at equal priority to the deadline-comparison form used by the EDF invariant.
- **EDF trivial preservation:** `setCurrentThread_none_preserves_edfCurrentHasEarliestDeadline`,
  `switchDomain_preserves_edfCurrentHasEarliestDeadline`.
- **Full scheduler bundle:** `schedulerInvariantBundleFull` (5-tuple extending the
  structural triad with `timeSlicePositive` and `edfCurrentHasEarliestDeadline`),
  `schedulerInvariantBundleFull_to_base` (projection),
  `switchDomain_preserves_schedulerInvariantBundleFull` (composition).
- **Refactoring:** Extracted `threadId_ne_objId_beq_false` helper to deduplicate
  recurring ObjId inequality proofs in `timerTick_preserves_timeSlicePositive`.
  Made `noBetter_implies_edf` private (internal bridge lemma).
- **Linker hardening:** Added CRT startup file verification (`crti.o`, `crt1.o`,
  `Scrt1.o`) to `setup_lean_env.sh` with automatic toolchain re-download on
  incomplete extraction. Prevents `ld: cannot find crti.o` linker errors.
- **14 new theorems.** Zero sorry/axiom. `test_full.sh` passes (Tier 0-3).
  753 proved theorems total.

## [0.13.0] - 2026-03-03

### WS-H5 audit: documentation sync and Tier 3 surface anchors

- **Documentation sync:** Fixed stale version and metric references across 7 documentation files — SELE4N_SPEC.md theorem count (575 -> 627), GitBook README/navigation_manifest version (0.12.15 -> 0.12.19), development workflow WS-H reference (H1..H3 -> H1..H5), kernel performance chapter theorem count (400+ -> 627), project usage value LoC/module/theorem counts (16,485/34/400+ -> 21,340/40/627).
- **Tier 3 invariant surface anchors:** Added 18 WS-H5 anchor checks to `test_tier3_invariant_surface.sh` covering all 5 predicate definitions (`intrusiveQueueWellFormed`, `tcbQueueLinkIntegrity`, `dualQueueEndpointWellFormed`, `dualQueueSystemInvariant`, `ipcInvariantFull`), 5 safety/closure theorems (A-23/A-24), and 8 preservation theorems for all dual-queue operations.
- **Testing milestone:** Added WS-H5 bullet to `07-testing-and-ci.md` milestone testing trajectory.
- **Zero sorry/axiom.** `test_full.sh` passes (Tier 0-3). 627 proved theorems total.

## [0.12.19] - 2026-03-03

### WS-H5: IPC Dual-Queue Structural Invariant (completed)

- **C-04 / A-22 (CRITICAL): Formal well-formedness predicate for intrusive dual-queue IPC.** The dual-queue structure (`sendQ`/`receiveQ`, TCB `queueNext`/`queuePrev`/`queuePPrev` linkage) previously had zero formal well-formedness guarantees. Defined `intrusiveQueueWellFormed` (head/tail emptiness iff, head has prev=none, tail has next=none, TCB existence) and `dualQueueEndpointWellFormed` composing both queues. Integrated as `dualQueueSystemInvariant` covering all endpoints and `tcbQueueLinkIntegrity` (doubly-linked forward/reverse consistency).
- **A-23 (HIGH): Link dereference safety in `endpointQueuePopHead`.** Under `dualQueueSystemInvariant`, `headTcb.queueNext` is guaranteed to be either `none` (tail) or a valid TCB. Proved via `endpointQueuePopHead_preserves_dualQueueSystemInvariant`.
- **A-24 (HIGH): Message lookup after dequeue.** Under `dualQueueSystemInvariant`, the TCB existence guarantee ensures `lookupTcb` after `popHead` succeeds. Proved via `endpointReceiveDual_preserves_dualQueueSystemInvariant`.
- **Predicate definitions in `IPC/Invariant.lean`:** `intrusiveQueueWellFormed`, `dualQueueEndpointWellFormed`, `tcbQueueLinkIntegrity`, `dualQueueSystemInvariant`.
- **13 preservation theorems:** `ensureRunnable_preserves_dualQueueSystemInvariant`, `removeRunnable_preserves_dualQueueSystemInvariant`, `storeTcbIpcState_preserves_dualQueueSystemInvariant`, `storeTcbIpcStateAndMessage_preserves_dualQueueSystemInvariant`, `storeTcbPendingMessage_preserves_dualQueueSystemInvariant`, `endpointReply_preserves_dualQueueSystemInvariant`, `endpointAwaitReceive_preserves_dualQueueSystemInvariant`, `endpointReplyRecv_preserves_dualQueueSystemInvariant`, `endpointQueuePopHead_preserves_dualQueueSystemInvariant`, `endpointQueueEnqueue_preserves_dualQueueSystemInvariant`, `endpointSendDual_preserves_dualQueueSystemInvariant`, `endpointReceiveDual_preserves_dualQueueSystemInvariant`, `endpointCall_preserves_dualQueueSystemInvariant`.
- **Helper infrastructure:** `storeTcbQueueLinks_result_tcb`, `storeTcbQueueLinks_preserves_iqwf`, `storeTcbQueueLinks_clearing_preserves_linkInteg`, `storeTcbQueueLinks_none_prevnext_preserves_linkInteg` — transport lemmas for queue link mutations.
- **Zero sorry/axiom.** `test_full.sh` passes (Tier 0-3). 627 proved theorems total.

## [0.12.18] - 2026-03-02

### WS-H4: Capability Invariant Redesign (completed)

- **capabilityInvariantBundle extended from 4-tuple to 7-tuple (C-03 CRITICAL):** The `capabilityInvariantBundle` previously contained only `cspaceSlotUnique ∧ cspaceLookupSound ∧ cspaceAttenuationRule ∧ lifecycleAuthorityMonotonicity` — all trivially true or structural. Replaced with a meaningful 7-conjunct bundle adding: `cspaceSlotCountBounded` (every CNode has bounded slot count), `cdtCompleteness` (every CDT node-slot mapping references an existing object), and `cdtAcyclicity` (CDT derivation forest is well-founded via path-based acyclicity).
- **New predicates in Model/Object.lean:** `CNode.slotCountBounded` (slot count ≤ maxCNodeSlots), `CapDerivationTree.edgeWellFounded` (no non-empty path from a node to itself), `edgeWellFounded_sub` (edge-subset preserves well-foundedness), `removeNode_edges_sub` (removeNode produces edge subset), `CNode.remove_slotCountBounded` and `CNode.revokeTargetLocal_slotCountBounded` (CNode operations preserve bounds).
- **New predicates in Capability/Invariant.lean:** `cspaceSlotCountBounded st`, `cdtCompleteness st`, `cdtAcyclicity st` — formalized as quantified propositions over system state.
- **Transfer theorem infrastructure:** Added ~20 helper theorems for propagating the 3 new predicates through state transitions: `cspaceSlotCountBounded_of_objects_eq`, `cdtCompleteness_of_storeObject`, `cdtAcyclicity_of_cdt_eq`, `cdtPredicates_through_blocking_path`, `cdtPredicates_through_handshake_path`, `cdtPredicates_through_reply_path`, `cdtPredicates_of_detachSlotFromCdt`, `boundedCompleteness_of_cdt_only_update`, `capabilityInvariantBundle_of_cdt_update`, and more.
- **All preservation theorems re-proved:** Every `_preserves_capabilityInvariantBundle` theorem (cspaceInsertSlot, cspaceMint, cspaceCopy, cspaceMove, cspaceMintWithCdt, cspaceMutate, cspaceDeleteSlot, cspaceRevoke, revokeCdtFoldBody, revokeCdtFold, endpointReply, endpointSend, endpointReceive, endpointAwaitReceive, lifecycleRetypeObject, storeServiceState) re-proved against the non-trivial 7-conjunct bundle.
- **CDT-modifying operations:** For `cspaceCopy`, `cspaceMove`, `cspaceMintWithCdt` (which add CDT edges that could break acyclicity), cdtCompleteness and cdtAcyclicity of the post-state are taken as hypotheses. For CDT-shrinking operations (removeNode in revoke), acyclicity is proven via `edgeWellFounded_sub` and `removeNode_edges_sub`.
- **CNode insertion operations:** A `hSlotCapacity` / `hDstCapacity` hypothesis added to `cspaceInsertSlot`, `cspaceMint`, `cspaceCopy`, `cspaceMove`, `cspaceMintWithCdt`, `cspaceMutate` since no HashMap size_insert lemma is available.
- **Downstream callers updated:** Architecture/Invariant.lean default-state proofs, Service/Invariant.lean `storeServiceState_preserves`, and lifecycle composition theorems all updated for the 7-tuple.
- **Zero sorry/axiom.** `test_full.sh` passes (Tier 0-3).

### WS-H4 refinement: audit, optimization, and documentation sync

- **Architecture/Invariant.lean proof deduplication:** Extracted `default_capabilityInvariantBundle` helper theorem, eliminating 4x duplication of the 7-tuple default-state construction in `default_system_state_proofLayerInvariantBundle`.
- **API.lean M-08/A-20 annotation:** Added untracked-capability warning to `cspaceMint` API table entry — capabilities created via the non-CDT mint path are not tracked by CDT-based revocation; `cspaceMintWithCdt` should be preferred for tracked derivation.
- **Docstring refinements:** Updated `cdtCompleteness` docstring to clarify node-slot reachability scope vs. spec-intended mint-based completeness. Updated `capabilityInvariantBundle` docstring with WS-H4 design decision rationale (hCdtPost hypothesis pattern, edgeWellFounded_sub strategy, slotsUnique retention).
- **GitBook sync:** Updated 6 GitBook chapters (01-project-overview, 05-specification-and-roadmap, 07-testing-and-ci, 12-proof-and-invariant-map, 19-end-to-end-audit, 22-next-slice-development-path) with WS-H4 completion references, bundle redefinition details, and transfer theorem documentation.
- **Spec/CLAUDE.md sync:** Updated `SELE4N_SPEC.md` portfolio table, `CLAUDE.md` workstream context, and `docs/DEVELOPMENT.md` with WS-H4 (v0.12.18) completion status.

## [0.12.17] - 2026-03-02

### WS-H3: Build/CI Infrastructure Fixes (completed)

- **run_check return value fix (H-12 HIGH):** `run_check` in `scripts/test_lib.sh` previously fell through to an implicit `return 0` after recording a failure when `CONTINUE_MODE=1`, causing callers to receive success even on failure. Fixed by adding explicit `return 1` in the failure path. In continue mode, `set -e` is now disabled after `parse_common_args` so that `run_check` can return non-zero without aborting the script; failure tracking is managed by `record_failure`/`finalize_report`.
- **Documentation sync CI integration (M-19 MEDIUM):** `test_docs_sync.sh` was previously available only as a standalone local tool. Now integrated into both the `test_smoke.sh` entrypoint (local runs) and the `lean_action_ci.yml` smoke CI job (automated PR checks). Documentation navigation/link drift is now caught automatically on every PR.
- **Tier 3 rg availability guard (M-20 MEDIUM):** `test_tier3_invariant_surface.sh` has ~440 `rg` invocations. Previously, a missing `rg` produced hundreds of command-not-found errors. Added a guard at script entry that checks for `rg` availability. If absent, a `grep -P` fallback shim is created on PATH (handling both direct calls and `bash -lc` subshell invocations). If neither `rg` nor `grep -P` is available, the script fails with a single clear diagnostic message.
- **Full integration:** `test_full.sh` passes (Tier 0-3). Zero sorry/axiom.

### WS-H2/B-5: Lifecycle hFresh Auto-Derivation (audit gap closure)

- **retypeFromUntyped_ok_childId_ne:** New theorem proving `childId ≠ untypedId` is automatically derivable from successful `retypeFromUntyped` execution (H-06 self-overwrite guard).
- **retypeFromUntyped_ok_childId_fresh:** New theorem proving childId freshness among existing untyped children is automatically derivable from successful `retypeFromUntyped` execution (A-27 collision guard).
- **retypeFromUntyped_preserves_untypedMemoryInvariant_auto:** New auto-derivation wrapper that eliminates the manual `hNe` and `hFresh` proof obligations from `retypeFromUntyped_preserves_untypedMemoryInvariant`. Callers need only supply the invariant precondition, new-object well-formedness, and success hypothesis — both safety conditions are derived from the operation semantics.
- **Documentation updates:** GitBook chapters updated to v0.12.17 (19-end-to-end-audit, 22-next-slice-development-path, 07-testing-and-ci, README). Audit lineage table extended with WS-H portfolio entry. Theorem count updated to 575+.

## [0.12.16] - 2026-03-02

### WS-H1: IPC Call-Path Semantic Fix (completed)

- **blockedOnCall IPC state (C-01 CRITICAL):** Added `blockedOnCall` variant to `ThreadIpcState` enum in `Model/Object.lean`. A Call sender blocked on the send queue now carries `blockedOnCall endpointId` (distinct from `blockedOnSend endpointId`), signaling that upon dequeue by `endpointReceiveDual`, the sender transitions to `blockedOnReply` (not `.ready`). This fixes the semantic bug where a blocked Call sender was erroneously unblocked as if it were a plain Send, violating the Call contract.
- **Receiver-side call/send dispatch (C-01):** `endpointReceiveDual` now inspects the dequeued sender's `ipcState` to determine post-dequeue transition: `blockedOnCall` senders transition to `blockedOnReply` (caller stays blocked awaiting reply), while plain `blockedOnSend` senders transition to `.ready` (sender unblocked). The `let senderWasCall` conditional dispatches between the two paths.
- **Reply-target scoping (M-02 MEDIUM):** Added optional `replyTarget : Option ThreadId` field to the `blockedOnReply` state, recording which server thread is authorized to reply. `endpointReply` and `endpointReplyRecv` now validate that the replier matches `replyTarget` (when set), preventing confused-deputy attacks where any thread could reply to any blocked caller.
- **endpointCall updates:** Blocking path uses `blockedOnCall endpointId` instead of `blockedOnSend`; handshake path populates `blockedOnReply endpointId (some receiver)` with the receiver's ThreadId.
- **ipcSchedulerContractPredicates expanded:** Predicate bundle extended from 3 to 5 conjuncts with `blockedOnCallNotRunnable` and `blockedOnReplyNotRunnable`, ensuring threads in call/reply blocking states are not in the runnable queue.
- **Invariant proof maintenance:** All IPC invariant preservation theorems re-proved for the updated state transitions, including `endpointReceiveDual` dual-path proofs (call path and send path), `endpointCall` blocking/handshake proofs, and all `endpointReplyRecv` chain proofs.
- **Trace and test coverage:** Updated trace harness with WS-H1 blocking-path scenarios (H1-01 through H1-05) verifying call/reply lifecycle. Updated `NegativeStateSuite` pattern matches for the new `blockedOnReply` signature.
- **Code quality refinement:** Refactored `endpointReply` to use `let authorized := ...` pattern matching `endpointReplyRecv`, eliminating duplicated reply-delivery logic. Consolidated dual `lookupTcb` calls in `endpointReceiveDual` into a single lookup returning `(senderMsg, senderWasCall)`. Proof duplication in `endpointReply_preserves_ipcSchedulerContractPredicates` and `endpointReply_preserves_capabilityInvariantBundle` eliminated via `suffices` abstraction.
- **Full proof migration:** zero sorry/axiom across all modified files. `test_full.sh` passes (Tier 0-3).

### WS-H2: Lifecycle Safety Guards (completed)

- **childId self-overwrite guard (H-06 CRITICAL):** `retypeFromUntyped` now rejects calls where `childId = untypedId`, preventing the untyped object from being overwritten by its own child. Returns new `KernelError.childIdSelfOverwrite` error.
- **childId collision guards (A-26/A-27 HIGH):** `retypeFromUntyped` rejects calls where `childId` collides with an existing object in `st.objects` or with an existing child in the untyped's `children` list. Returns new `KernelError.childIdCollision` error.
- **TCB retype scheduler cleanup (H-05 CRITICAL):** New `cleanupTcbReferences` helper removes a TCB's ThreadId from the scheduler run queue before retype. New `detachCNodeSlots` helper clears CDT slot mappings when a CNode is replaced by a non-CNode object. Both composed in `lifecyclePreRetypeCleanup`.
- **Safe retype wrapper (H-05):** `lifecycleRetypeWithCleanup` wraps `lifecyclePreRetypeCleanup` + `lifecycleRetypeObject`, providing the recommended entry point with safety guarantees. Original `lifecycleRetypeObject` is unchanged to preserve all downstream invariant proofs.
- **Theorem: no dangling runnable after TCB retype:** `lifecycleRetypeWithCleanup_ok_runnable_no_dangling` proves that after a successful TCB retype via the safe wrapper, the old ThreadId is not in the run queue.
- **Atomic retype (A-28):** `retypeFromUntyped` computes both the updated untyped and the new child object before any state mutation, preventing partial-update inconsistencies.
- **Preservation proofs:** Field-orthogonality theorems for all cleanup operations (`*_objects_eq`, `*_lifecycle_eq`, `*_scheduler_eq`). Fold induction proofs for `detachCNodeSlots` CDT traversal.
- **Trace coverage:** F2-09/F2-10 trace scenarios for childId guards, LIFE-10 scenario for `lifecycleRetypeWithCleanup` with TCB cleanup verification. 3 new scenario catalog entries.
- **Negative test coverage:** H2-NEG-01 through H2-NEG-03 in `NegativeStateSuite.lean` testing childIdSelfOverwrite, childIdCollision (existing object), and childIdCollision (untyped child).
- **Full proof migration:** zero sorry/axiom. `test_smoke.sh` passes (86/86 trace, all negative checks).

## [0.12.15] - 2026-03-02

### WS-G Refinement: Scheduler optimization, validation hardening, and audit coverage expansion

- **RunQueue.remove bucket precomputation (WS-G4 refinement):** `RunQueue.remove` previously computed the filtered bucket twice — once for `byPriority` update and once for `maxPriority` update. Refactored to compute the filtered bucket once and reuse for both, eliminating redundant `List.filter` evaluation on every thread removal. Structural invariant documentation added explaining the implicit `membership` ↔ `threadPriority` consistency maintained by the insert/remove API.
- **MachineConfig.wellFormed page-size validation hardened:** Added `isPowerOfTwo` helper using bitwise characterization (`n > 0 ∧ n &&& (n - 1) == 0`). `MachineConfig.wellFormed` now validates `pageSize` as a positive power of two instead of merely positive, catching misconfigured platforms with non-standard page sizes (e.g., `pageSize = 3`).
- **Dead code removal:** Removed unused `filterByDomain` function from `Scheduler/Operations.lean` — dead code since WS-G4 replaced domain filtering with bucket-first scheduling via `chooseBestInBucket`. Added performance documentation note to `schedule` explaining the O(n) `List.Mem` membership check vs deferred O(1) HashSet alternative.
- **Phantom object cleanup:** Removed phantom object ID 200 from `bootstrapInvariantObjectIds` in `MainTraceHarness.lean` — this ID had no corresponding object in the bootstrap state and added false positive invariant check passes.
- **Runtime invariant checks expanded:** Added `runQueueThreadPriorityConsistentB` verifying that every thread in the RunQueue flat list has a corresponding `threadPriority` entry (structural API safety net). Added `cdtChildMapConsistentCheck` verifying bidirectional consistency between `CapDerivationTree.childMap` HashMap and `edges` list (both forward and backward directions).
- **StateBuilder TCB priority integration (WS-G4 fix):** `BootstrapBuilder.build` now uses actual TCB priorities from the builder's object list for RunQueue bucketing via `lookupThreadPriority`, instead of defaulting all threads to priority 0. This ensures test states have correctly bucketed run queues matching their thread priority configuration.
- **Audit test coverage expansion:** Added `runAuditCoverageChecks` to `NegativeStateSuite.lean` with comprehensive `endpointReplyRecv` coverage (2 negative checks: non-existent target, target not in blockedOnReply state; 1 positive flow via endpointCall→endpointReplyRecv chain verifying caller unblock) and `cspaceMutate` coverage (2 negative checks: non-existent CNode, rights escalation; 2 positive checks: rights attenuation, badge override).
- **Full proof migration:** zero sorry/axiom across all 7 modified files. `test_full.sh` passes (Tier 0-3).

## [0.12.14] - 2026-03-01

### WS-G9: Information-Flow Projection Optimization (completed)

- **Precomputed observable set (F-P09):** `projectState` previously evaluated `objectObservable` redundantly across `projectObjects`, `projectIrqHandlers`, and `projectObjectIndex` — repeated `securityFlowsTo` label comparisons for every object at each sub-projection call site. New `computeObservableSet` builds a `Std.HashSet ObjId` via single `foldl` pass over `st.objectIndex`; `projectObjectsFast`, `projectIrqHandlersFast`, `projectObjectIndexFast` now use O(1) `contains` lookups instead of re-evaluating `objectObservable`.
- **`@[csimp]`-ready design:** Original `projectState` definition kept unchanged to preserve all existing non-interference proofs in `Invariant.lean` (1448 lines, untouched). New `projectStateFast` is an optimized alternative with `projectObjectsFast`, `projectIrqHandlersFast`, `projectObjectIndexFast` — all using the precomputed HashSet. Top-level equivalence theorem `projectStateFast_eq` proves `projectStateFast = projectState` under standard state synchronization invariants, ready for `@[csimp]` compiler substitution.
- **HashSet bridge lemmas:** 3 new `List.foldl` monotonicity/preservation lemmas in `Prelude.lean`: `foldl_preserves_contains`, `foldl_not_contains_when_absent`, `foldl_preserves_when_pred_false`. Core induction lemma `foldl_observable_set_mem` in `Projection.lean` proves membership equivalence for the observable set.
- **Zero downstream proof breakage:** All non-interference theorems, enforcement wrappers, and invariant proofs remain unchanged. `projectState` definition is untouched; `projectStateFast` provides the performance path.
- **Full proof migration:** zero sorry/axiom across all 2 modified files. `test_full.sh` passes (Tier 0-3).
- Closes finding F-P09 (information-flow projection redundant observability evaluation).

## [0.12.13] - 2026-03-01

### WS-G8: Graph Traversal Optimization (completed)

- **Service dependency DFS with HashSet (Phase A / F-P08):** `serviceHasPathTo` rewritten from O(n²) BFS with `List ServiceId` visited set to O(n+e) DFS with `Std.HashSet ServiceId`. Visited-set membership checks now O(1) amortized. Frontier ordering changed from BFS (`rest ++ newDeps`) to DFS (`newDeps ++ rest`) for stack-friendly traversal. Three HashSet bridge lemmas added to `Prelude.lean`: `HashSet_contains_insert_iff`, `HashSet_not_contains_insert`, `HashSet_contains_insert_self`.
- **CDT childMap index (Phase B / F-P14):** `CapDerivationTree` extended with `childMap : Std.HashMap CdtNodeId (List CdtNodeId)` parent-indexed edge index. `childrenOf` rewritten from O(E) edge-list scan to O(1) HashMap lookup. `descendantsOf` BFS complexity reduced from O(N×E) to O(N+E). `addEdge`, `removeAsChild`, `removeAsParent`, `removeNode` all maintain `childMap` alongside `edges`.
- **Consistency invariant:** `childMapConsistent` defines bidirectional correspondence between `childMap` and `edges`. `empty_childMapConsistent` and `addEdge_childMapConsistent` proved; `edges` remains the proof anchor.
- **Invariant proofs re-proved:** `bfsClosed`, `bfsClosed_init`, `bfsClosed_skip`, `bfsClosed_expand`, `bfs_boundary_lemma`, `filter_vis_decrease`, `go_tgt_eq`, `go_skip_eq`, `go_expand_eq`, `go_complete`, `bfs_complete_for_nontrivialPath` all migrated to HashSet-based visited set in `Service/Invariant.lean`.
- **Test infrastructure updated:** `NegativeStateSuite.lean` CDT construction migrated from raw struct literals to `addEdge` API calls, ensuring `childMap` consistency.
- **Full proof migration:** zero sorry/axiom across all 5 modified files. `test_full.sh` passes (Tier 0-3).
- Closes findings F-P08 (service dependency BFS O(n²)) and F-P14 (CDT descendantsOf BFS O(N×E)).

## [0.12.12] - 2026-03-01

### WS-G7: IPC Queue Completion & Notification (completed)

- **Legacy endpoint deprecation (Phase A / F-P04):** Trace harness and sequence probe migrated from legacy `endpointSend`/`endpointReceive`/`endpointAwaitReceive` to O(1) dual-queue `endpointSendDual`/`endpointReceiveDual`. Legacy operations marked deprecated with docstring annotations. New `endpointSendDualChecked` enforcement wrapper provides information-flow gating for the dual-queue send path, matching the legacy `endpointSendChecked` pattern.
- **Notification wait optimization (Phase B / F-P11):** `notificationWait` O(n) duplicate check `waiter ∈ ntfn.waitingThreads` replaced with O(1) TCB `ipcState` check via `lookupTcb`. O(n) append `ntfn.waitingThreads ++ [waiter]` replaced with O(1) prepend `waiter :: ntfn.waitingThreads`.
- **New `notificationWaiterConsistent` invariant:** Bridges TCB `ipcState` to notification queue membership, ensuring the O(1) TCB-based duplicate check is sound. Bridge lemma `not_mem_waitingThreads_of_ipcState_ne` enables `uniqueWaiters` preservation under prepend. Base case `default_notificationWaiterConsistent` proved. Runtime `notificationWaiterConsistentChecks` added to invariant check surface with Tier-3 anchor.
- **Invariant proofs re-proved:** `notificationWait_preserves_uniqueWaiters`, `notificationWait_preserves_ipcInvariant`, `notificationWait_preserves_schedulerInvariantBundle`, `notificationWait_preserves_ipcSchedulerContractPredicates` all re-proved against new O(1) logic. `notificationWait_recovers_pending_badge` (Capability) and `notificationWait_projection_preserved` (InformationFlow) updated for `lookupTcb` match structure.
- **`endpointSendDualChecked` enforcement:** New checked dual-queue send in `Enforcement.lean` with correctness theorems `endpointSendDualChecked_eq_endpointSendDual_when_allowed` and `endpointSendDualChecked_flowDenied`.
- **API stability table updated:** Legacy `endpointSend`/`endpointReceive`/`endpointAwaitReceive` and `endpointSendChecked` marked `Deprecated (WS-G7)`. `endpointSendDualChecked` added as stable entry point.
- **Structured fixture updated:** Trace fixture migrated to dual-queue output (IPC-03 updated, legacy-only IPC-05/IPC-06 removed). Tier-3 surface anchors updated for `endpointReceiveDual`.
- **Full proof migration:** zero sorry/axiom across all 9 modified files. `test_full.sh` passes (Tier 0-3).
- Closes findings F-P04 (legacy endpoint queue O(n) append) and F-P11 (notification duplicate wait O(n) check).

## [0.12.11] - 2026-03-01

### WS-G6: VSpace Mapping HashMap (completed)

- **VSpace mapping HashMap migration:** `VSpaceRoot.mappings` changed from `List (VAddr × PAddr)` to `Std.HashMap VAddr PAddr`. All page lookups (`VSpaceRoot.lookup`), inserts (`VSpaceRoot.mapPage`), and erasures (`VSpaceRoot.unmapPage`) now O(1) amortized instead of O(m) linear scan.
- **`noVirtualOverlap` trivially true:** HashMap enforces key uniqueness by construction. `noVirtualOverlap` reformulated from list membership to `lookup`-based semantics. Universal `noVirtualOverlap_trivial` theorem proves the property for *all* VSpaceRoots; `noVirtualOverlap_empty`, `mapPage_noVirtualOverlap`, and `unmapPage_noVirtualOverlap` delegate to it.
- **Round-trip theorems re-proved:** `lookup_mapPage_eq`, `lookup_unmapPage_eq_none`, `lookup_mapPage_ne`, `lookup_unmapPage_ne` all re-proved using `HashMap_getElem?_insert`/`HashMap_getElem?_erase` bridge lemmas. `lookup_eq_none_iff` replaces `lookup_eq_none_not_mem` with bidirectional HashMap membership characterization.
- **BEq instance:** Manual `BEq VSpaceRoot` (entry-wise HashMap comparison) replaces lost `DecidableEq VSpaceRoot` derivation, matching the `BEq CNode` pattern from WS-G5.
- **VSpaceBackend updated:** `listVSpaceBackend` renamed to `hashMapVSpaceBackend`; docstring updated to reflect HashMap backing.
- **`boundedAddressTranslation` reformulated:** From list membership `(v, p) ∈ root.mappings` to HashMap lookup `root.mappings[v]? = some p`.
- **Test infrastructure updated:** `MainTraceHarness.lean`, `NegativeStateSuite.lean` use `mappings := {}` for VSpaceRoot construction. All test suites pass (Tier 0-3).
- **Full proof migration:** zero sorry/axiom across all 7 modified files. `test_full.sh` passes (Tier 0-3).
- Closes finding F-P05 (VSpace mapping linear scan).

## [0.12.10] - 2026-03-01

### WS-G5: CNode Slot HashMap (completed)

- **CNode slot HashMap migration:** `CNode.slots` changed from `List (Slot × Capability)` to `Std.HashMap Slot Capability`. All capability lookups (`CNode.lookup`), inserts (`CNode.insert`), and deletes (`CNode.remove`) now O(1) amortized instead of O(m) linear scan.
- **`slotsUnique` invariant trivially true:** HashMap enforces key uniqueness by construction. `CNode.slotsUnique` redefined as `True`, and all three preservation theorems (`insert_slotsUnique`, `remove_slotsUnique`, `revokeTargetLocal_slotsUnique`) now prove `trivial`.
- **Bridge lemmas:** `HashMap_filter_preserves_key` (single-filter key preservation for `revokeTargetLocal`) and `HashMap_filter_filter_getElem?` (double-filter idempotency for projection) in `Prelude.lean`. Both avoid `Std.HashMap`'s `Option.pfilter` dependent types by working at the membership level.
- **Projection idempotency reformulated:** `projectKernelObject_idempotent` in `Projection.lean` reformulated from structural equality to slot-level lookup equality, because `Std.HashMap.filter` reverses internal `AssocList` bucket ordering making `(m.filter f).filter f ≠ m.filter f` structurally.
- **BEq instances for runtime tests:** Manual `BEq CNode` (entry-wise HashMap comparison) and `BEq KernelObject` instances replace the lost `DecidableEq KernelObject` derivation.
- **CSpace invariant proofs migrated:** `cspaceRevoke_local_target_reduction` rewritten with HashMap-level reasoning (`mem_filter`, `getKey_beq`, `getElem_filter`). `cspaceLookupSound_of_cspaceSlotUnique` simplified (HashMap lookup is direct). `revokedRefs` computed via `HashMap.fold` in a single O(m) pass (no intermediate `.toList` allocation).
- **Test infrastructure updated:** `InvariantChecks.lean` uses `cn.slots.toList.foldr`. `MainTraceHarness.lean` and all test suites use `Std.HashMap.ofList` for CNode construction. `InformationFlowSuite.lean` uses `cn.slots.contains` for O(1) key-existence checks and `cn.slots.size` for slot counts.
- **Full proof migration:** zero sorry/axiom across all 10 modified files. `test_full.sh` passes (Tier 0-3).
- Closes finding F-P03 (CNode slot linear scan).

## [0.12.9] - 2026-03-01

### WS-G4: Run Queue Restructure (completed)

- **Priority-bucketed RunQueue:** New `RunQueue` structure in `Scheduler/RunQueue.lean` replaces flat `List ThreadId` runnable queue. Backed by `Std.HashMap Priority (List ThreadId)` for priority bucketing, `Std.HashSet ThreadId` for O(1) membership, and `Std.HashMap ThreadId Priority` for O(1) priority lookup. `flat : List ThreadId` maintained for proof/projection compatibility.
- **O(1) scheduler hot-path operations:** `insert`, `remove`, `contains`, `rotateHead`, `rotateToBack` all O(1) amortized. `maxPriority` cached and maintained incrementally (recomputed only on bucket exhaustion).
- **Bucket-first scheduling (F-P07):** `chooseBestInBucket` scans only the max-priority bucket for domain-eligible threads, reducing best-candidate selection from O(t) to O(k) where k is the bucket size (typically 1-3). Falls back to full-list scan when max-priority bucket has no eligible thread in the active domain.
- **Structural invariant `flat_wf`:** `∀ tid, tid ∈ flat → membership.contains tid = true` — Prop field that formally bridges HashSet and flat list membership. Maintained by inline proofs in every RunQueue mutation.
- **SchedulerState restructured:** `runQueue : RunQueue` replaces `runnable : List ThreadId`. Eliminated `runnableHead`, `runnableTail` cache fields. Eliminated `withRunnableQueue` helper (subsumed by RunQueue structure). Dead `rotateCurrentToBack` private function removed.
- **IPC operations rewritten:** `removeRunnable` uses `RunQueue.remove`; `ensureRunnable` uses `RunQueue.contains` + `RunQueue.insert`. `handleYield`/`timerTick` use `RunQueue.rotateToBack` directly.
- **13 RunQueue bridge lemmas:** `mem_insert`, `mem_remove`, `mem_rotateHead`, `mem_rotateToBack`, `not_mem_empty`, `toList_insert_not_mem`, `toList_filter_insert_neg`, `toList_filter_remove_neg`, `not_mem_toList_of_not_mem`, `not_mem_remove_toList`, `mem_toList_rotateToBack_self`, `toList_rotateToBack_nodup`, `mem_toList_rotateToBack_ne`.
- **IPC invariant migration:** 30+ proofs in `IPC/Invariant.lean` migrated to flat-list variants (`removeRunnable_runnable_mem`, `ensureRunnable_runnable_mem_old`). `ensureRunnable_nodup` simplified (no longer needs `hWF` parameter).
- **Information-flow preservation:** `ensureRunnable_preserves_projection` re-proved via `congr 1` + `RunQueue.toList_filter_insert_neg`.
- **Full proof migration:** zero sorry/axiom across all 7 modified files. `test_full.sh` passes (Tier 0-3).
- Closes findings F-P02 (runnable queue O(n) ops), F-P07 (scheduler best-candidate O(t) scan), F-P12 (`withRunnableQueue` tail recomputation).

## [0.12.8] - 2026-03-01

### WS-G3: ASID Resolution Table (completed)

- **ASID resolution O(1) via HashMap:** `resolveAsidRoot` rewritten from O(n) `objectIndex.findSome?` linear scan to O(1) `Std.HashMap ASID ObjId` lookup with object-store validation. New `asidTable` field in `SystemState`.
- **asidTable maintenance in storeObject:** erase-before-insert pattern ensures old ASID entries are cleaned up when overwriting a VSpaceRoot. Three bridge lemmas: `storeObject_asidTable_vspaceRoot`, `storeObject_asidTable_vspaceRoot_ne`, `storeObject_asidTable_non_vspaceRoot`.
- **asidTableConsistent invariant:** bidirectional soundness + completeness agreement between `asidTable` and VSpaceRoot objects. `vspaceInvariantBundle` extended from 2-conjunct to 3-conjunct (+ `asidTableConsistent`).
- **Preservation proofs updated:** both map/unmap success-path theorems prove `asidTableConsistent` preservation via shared `asidTableConsistent_of_storeObject_vspaceRoot` helper (deduplicates ~50 lines). All 4 round-trip theorems simplified (no longer need `objectIndexSetSync` hypothesis).
- **StateBuilder + InvariantChecks:** test state builder auto-populates `asidTable` from VSpaceRoot objects. Runtime `asidTableConsistencyChecks` added to invariant check surface with Tier-3 anchor.
- **Tier-3 test anchors:** `objectIndex.findSome?` exit criterion (expect NOT found in VSpace.lean), `st.asidTable` positive anchor, `asidTableConsistencyChecks` runtime check anchor, updated theorem name anchors.
- **Full proof migration:** zero sorry/axiom. `test_full.sh` passes (Tier 0-3).
- Closes finding F-P06 (ASID resolution linear scan).

## [0.12.7] - 2026-03-01

### WS-G2: Object Store & ObjectIndex HashMap (completed)

- **Object store HashMap migration:** `SystemState.objects` changed from closure-chain `ObjId → Option KernelObject` to `Std.HashMap ObjId KernelObject`. All object lookups now O(1) amortized instead of O(k) chain-walking. `storeObject` uses `HashMap.insert` directly.
- **ObjectIndex shadow HashSet:** new `objectIndexSet : Std.HashSet ObjId` field enables O(1) membership checks for `storeObject`'s index-deduplication guard. New `objectIndexSetSync` invariant ensures consistency between `objectIndex` and `objectIndexSet`.
- **Lifecycle metadata HashMap:** `LifecycleMetadata.objectTypes` migrated to `Std.HashMap ObjId KernelObjectType` for O(1) type metadata lookups.
- **Bridge lemmas:** `HashMap_getElem?_insert`, `HashMap_getElem?_empty`, `HashMap_getElem?_eq_get?`, `HashMap_get?_eq_getElem?` in `Prelude.lean`. `LawfulHashable` and `EquivBEq` instances for all key types.
- **Full proof migration:** all 400+ theorems re-verified. Zero sorry/axiom. `test_full.sh` passes (Tier 0-3).
- **Closure elimination:** all `fun oid => if oid = X then ... else st.objects[oid]?` patterns replaced with `st.objects.insert`.
- Closes findings F-P01 (object store closure chain), F-P10 (objectIndex linear scan), F-P13 (lifecycle metadata linear scan).

## [0.12.6] - 2026-03-01

### WS-G1: Hashable/BEq Infrastructure (completed)

- **Hashable instances for all 13 typed identifiers:** `ObjId`, `ThreadId`, `DomainId`, `Priority`, `Deadline`, `Irq`, `ServiceId`, `CPtr`, `Slot`, `Badge`, `ASID`, `VAddr`, `PAddr` — all marked `@[inline]` for zero runtime overhead, delegating to `Nat` hash. BEq is provided by the existing `DecidableEq` derivations via `instBEqOfDecidableEq`.
- **Hashable instance for composite key `SlotRef`:** uses `mixHash` to combine `cnode` and `slot` hashes for uniform distribution in HashMap/HashSet.
- **Std imports:** `Std.Data.HashMap` and `Std.Data.HashSet` imported in `Prelude.lean`, making O(1) hash-based data structures available to all kernel modules.
- **Zero behavioral change:** all existing tests pass identically (Tier 0-3). Zero sorry/axiom.
- **Foundation for WS-G2..G9:** every subsequent performance workstream depends on these instances for HashMap/HashSet usage.

## [0.12.5] - 2026-03-01

### WS-F4: Proof Gap Closure (completed)

- **timerTick preservation (F-03):** `timerTick_preserves_schedulerInvariantBundle` and `timerTick_preserves_kernelInvariant` — covers `queueCurrentConsistent`, `runQueueUnique`, `currentThreadValid`, `currentThreadInActiveDomain`. Expired-timeslice path delegates to `schedule_preserves_*`; non-expired path proves scheduler unchanged directly.
- **cspaceMutate preservation (F-06):** `cspaceMutate_preserves_capabilityInvariantBundle` — uses `revert/unfold` decomposition through capability lookup, rights check, and storeObject.
- **cspaceRevokeCdt/cspaceRevokeCdtStrict preservation (F-06):** Fold induction via extracted `revokeCdtFoldBody` with error propagation lemmas (`revokeCdtFoldBody_foldl_error`). CDT-only state updates handled by `capabilityInvariantBundle_of_cdt_update`.
- **Notification preservation (F-12):** `notificationSignal_preserves_ipcInvariant`, `notificationSignal_preserves_schedulerInvariantBundle`, `notificationWait_preserves_ipcInvariant`, `notificationWait_preserves_schedulerInvariantBundle`. Compositional through new `storeObject_notification_preserves_ipcInvariant` helper. Wake/merge/badge-consume/wait paths fully covered with existing well-formedness lemmas.
- **Notification contract predicate preservation:** `notificationSignal_preserves_ipcSchedulerContractPredicates` and `notificationWait_preserves_ipcSchedulerContractPredicates` — closes the gap where notification operations lacked proof of scheduler-IPC coherence (M3.5). Wake/badge-consume paths use backward TCB transport through storeObject + storeTcbIpcState with ensureRunnable. Merge path uses `contracts_of_same_scheduler_ipcState`. Wait path handles `.blockedOnNotification` (not covered by `blockedOnSend`/`blockedOnReceive` predicates) with removeRunnable.
- **Testing:** 11 Tier-3 surface anchors. `test_full.sh` passes (Tier 0-3). Zero sorry/axiom.
- **Fix:** Capability invariant proof comments corrected from F-03 to F-06 (F-03 is timerTick; F-06 is cspaceMutate/revoke).
- Closes F-03 (timerTick no proofs), F-06 (cspaceMutate etc.), F-12 (notification preservation).

## [0.12.4] - 2026-03-01

### Audit hardening: F1-A silent data loss fix and O-3 allocSize validation

- **F1-A fix (IPC):** `endpointReceiveDual` now propagates `storeTcbPendingMessage` errors instead of silently succeeding when the receiver TCB doesn't exist, preventing a data loss path where the sender's message is cleared but never delivered.
- **O-3 fix (Untyped memory):** `retypeFromUntyped` validates `allocSize >= objectTypeAllocSize` for the target object type before attempting allocation. New error variant `untypedAllocSizeTooSmall`, error theorem `retypeFromUntyped_error_allocSizeTooSmall`, negative test F2-NEG-06, trace anchor F2-08.
- **Proof updates:** 3 IPC invariant proofs simplified (error branch now contradiction). Decomposition theorem `retypeFromUntyped_ok_decompose` extended with allocSize bound conjunct. Downstream invariant proofs updated.
- **Testing:** 80 trace expectations (was 68), 6 WS-F2 negative tests (was 5), 4 new Tier-3 surface anchors.

## [0.12.3] - 2026-02-28

### WS-F2: Untyped Memory Model (completed)

- **UntypedObject data model:** `UntypedObject` structure with `regionBase`, `regionSize`, `watermark`, `children`, and `isDevice` fields. `UntypedChild` tracks carved child objects with `objId`, `offset`, and `size`. Added `.untyped` variant to `KernelObject` and `KernelObjectType`.
- **retypeFromUntyped operation:** carves a typed kernel object from an untyped memory region, advancing the watermark. Enforces authority via `cspaceLookupSlot`, region bounds via `canAllocate`, and device restrictions (device untypeds can only produce more untypeds).
- **Error variants:** `untypedRegionExhausted`, `untypedTypeMismatch`, `untypedDeviceRestriction`, `untypedAllocSizeTooSmall` added to `KernelError`.
- **Proof surface:** `allocate_some_iff` decomposition lemma, `allocate_watermark_advance/monotone`, `allocate_preserves_watermarkValid/region`, `reset_wellFormed`, `empty_wellFormed`, `canAllocate_implies_fits`. Decomposition theorem `retypeFromUntyped_ok_decompose` and error characterization theorems.
- **Invariants:** `untypedWatermarkInvariant`, `untypedChildrenBoundsInvariant`, `untypedChildrenNonOverlapInvariant`, `untypedChildrenUniqueIdsInvariant`, `untypedMemoryInvariant`. Default-state theorem. Preservation through `retypeFromUntyped` for both `lifecycleMetadataConsistent` and `lifecycleInvariantBundle`.
- **Testing:** 8 trace scenarios (F2-01..F2-08), 6 negative-state tests, runtime watermark invariant checks, 27 Tier-3 surface anchors.
- Closes CRIT-04 (No Untyped memory).

### WS-F3: Information-Flow Completeness (completed)

- **ObservableState extension (CRIT-02):** 3 new security-relevant fields — `activeDomain` (scheduling transparency, always visible), `irqHandlers` (filtered by target object observability), `objectIndex` (filtered by object observability). All NI theorems extended to preserve the 7-field projection.
- **CNode slot filtering (F-22):** `projectKernelObject` redacts CNode capability slots whose targets reference high-domain objects. `capTargetObservable` gate covers `.object`, `.cnodeSlot`, and `.replyCap` target variants. Safety theorems: `projectKernelObject_idempotent` and `projectKernelObject_objectType`.
- **NI theorem coverage (CRIT-03):** 12 standalone `_preserves_lowEquivalent` theorems (endpointSend, chooseThread, cspaceMint, cspaceRevoke, lifecycleRetypeObject, notificationSignal, notificationWait, cspaceInsertSlot, serviceStart, serviceStop, serviceRestart, storeObject). 3 enforcement-NI bridge theorems (endpointSendChecked_NI, cspaceMintChecked_NI, serviceRestartChecked_NI).
- **Enforcement-NI bridge (F-20):** Bool case-splitting pattern connects checked operations to NI domain-separation hypotheses. Each bridge theorem extracts the flow-allowed proof, rewrites to the unchecked operation, and delegates to the standalone NI theorem.
- **Composed NI framework (H-05):** `NonInterferenceStep` inductive with 11 constructors (storeObject is standalone infrastructure, not an API constructor), `step_preserves_projection` one-sided theorem, `composedNonInterference_step/trace` two-sided bundle theorems, `preservesLowEquivalence` abstract predicate with sequential composition and error-action helpers.
- **Testing:** 39 WS-F3 tests in InformationFlowSuite covering activeDomain projection, IRQ handler filtering, object index filtering, CNode slot filtering (all 3 CapTarget variants), 7-field low-equivalence, serviceRestartChecked enforcement. 22 Tier-3 surface anchors.
- Closes CRIT-02 (incomplete projection), CRIT-03 (NI 5→12 operations), F-20 (enforcement-NI gap), F-21 (notificationSignal NI), F-22 (CNode projection leak).

### WS-F1: IPC message transfer and dual-queue verification (completed)

- **IPC message transfer:** `endpointSendDual`, `endpointReceiveDual`, `endpointCall`, `endpointReply`, and `endpointReplyRecv` now carry `IpcMessage` payloads (registers, caps, badge) through send/receive rendezvous. Messages are staged in sender's `TCB.pendingMessage` while blocked and transferred to the receiver's TCB on handshake/dequeue. `endpointReceiveDual` propagates message delivery errors (receiver TCB not found) instead of silently swallowing them, preventing silent data loss.
- **TCB.pendingMessage field:** new `Option IpcMessage` field on TCB for staging message content during IPC transfers.
- **Combined state+message helpers:** `storeTcbIpcStateAndMessage` and `storeTcbPendingMessage` update IPC state and pending message in a single `storeObject` call, simplifying both implementation and proof tracking.
- **Invariant preservation theorems:** 14 new theorems for dual-queue and compound operations (`endpointSendDual`, `endpointReceiveDual`, `endpointQueueRemoveDual`, `endpointCall`, `endpointReplyRecv`, `endpointReply`) preserving `ipcInvariant`, `schedulerInvariantBundle`, and `ipcSchedulerContractPredicates`. Tracked as TPI-D08/TPI-D09 for mechanical unfolding through private multi-step `storeObject` chains.
- **Supporting proof lemmas:** backward endpoint/notification preservation, scheduler equality, IPC state readback, and TCB existence lemmas for `storeTcbIpcStateAndMessage`, `storeTcbPendingMessage`, and `storeTcbQueueLinks`.
- **Trace harness scenarios:** 7 new fixture anchors (F1-01a..F1-03b) demonstrating actual data transfer: send-then-receive with registers/badge, rendezvous delivery, and call/reply roundtrip.
- Closes CRIT-01 (no message transfer), CRIT-05 (dual-queue unverified), F-10, F-11.

## [0.12.2] - 2026-02-27

### Optimization work continues

- **Node-stable CDT model:** capability derivation edges are tracked over stable CDT node IDs while CSpace slots map to nodes (`cdtSlotNode`/`cdtNodeSlot`); `cspaceMove` performs slot→node pointer transfer plus backpointer fixup instead of global edge rewrite, and `cspaceDeleteSlot` detaches slot↔node mappings to prevent stale CDT aliasing on slot reuse.
- Provide an opt-in strict variant of CDT-aware revoke that does not swallow deletion errors but surfaces the first descendant deletion failure for auditability and debugging.
- Record precise failing context (CDT node, projected slot when present, and concrete KernelError) so tooling/tests can assert and report offending slot/state.

## [0.12.1] - 2026-02-27

### Optimization work begins

- **Intrusive endpoint queues:** dual-queue wait lists now track `queuePrev`/`queuePPrev`/`queueNext` per waiting TCB to support O(1) arbitrary removal (`endpointQueueRemoveDual`).
- **Domain-aware scheduler policy:** selection is unified under active-domain filtering (`chooseThread`/`chooseThreadInDomain`), `kernelInvariant`/`canonicalSchedulerInvariantBundle` enforce `currentThreadInActiveDomain`, and regression coverage includes mixed runnable-set filtering plus `scheduleDomain` switch/tick consistency checks.

## [0.12.0] - 2026-02-26

### WS-E6 Model completeness and documentation (completed)

All 10 WS-E6 findings resolved with zero sorry/axiom. Synthesized from analysis of PRs #223, #224, and #225, selecting the best approach for each finding. This closes the entire WS-E portfolio.

- **M-03 (EDF tie-breaking):** Three-level scheduling comparison via `isBetterCandidate` (priority > deadline > FIFO). `Deadline` typed identifier. `TCB.deadline` field. `isBetterCandidate_irrefl` FIFO stability and `isBetterCandidate_asymm` strict ordering theorems. `edfCurrentHasEarliestDeadline` invariant predicate.
- **M-04 (Time-slice preemption):** `TCB.timeSlice` field (default 5). `defaultTimeSlice` constant. `timerTick` operation with decrement/reset+reschedule. `timeSlicePositive` invariant predicate.
- **M-05 (Domain scheduling):** `DomainScheduleEntry`, `filterByDomain`, `chooseThreadInDomain` (with fallback), `switchDomain`, `scheduleDomain`. `currentThreadInActiveDomain` invariant. Preservation theorems.
- **M-08 (Architecture assumption consumption):** Three consumption bridge theorems connecting structural axioms to adapter proofs. 4-step consumption chain documented.
- **F-17 (O(n) design decision ADR):** `docs/ON_DESIGN_DECISION_ADR.md` with rationale, scope note, complexity comparison, migration path.
- **L-01 (Unified API surface):** `apiInvariantBundle` alias, `apiInvariantBundle_default` theorem, entry-point stability table (30+ operations).
- **L-02 (Memory zero-default):** Comprehensive documentation and 4 theorems (`default_memory_returns_zero`, `default_registerFile_pc_zero`, `default_registerFile_sp_zero`, `default_timer_zero`).
- **L-03 (Monad helpers):** `KernelM.get/set/modify/liftExcept/throw` with 6 correctness theorems.
- **L-04 (toObjId documentation):** Design rationale documented. `toObjIdChecked` safe variant with `toObjIdChecked_eq_some_of_not_reserved` theorem.
- **L-05 (objectIndex monotonicity):** Design rationale documented. `storeObject_objectIndex_monotone` theorem.
- WS-E6 trace scenarios: EDF tie-breaking, timer tick, domain switching. 7 new fixture anchors.
- All documentation synchronized. WS-E6 marked COMPLETED across all surfaces.
- Bumped package version to **`0.12.0`** (minor version bump for WS-E portfolio completion).

## [0.11.12] - 2026-02-26

### WS-E5 Information-flow maturity (completed)

All 3 WS-E5 findings resolved with zero sorry/axiom. Synthesized from analysis of PRs #218, #219, and #220, selecting the best approach for each finding.

- **H-04 (Parameterized security labels):** Introduced `SecurityDomain` (Nat-indexed), `DomainFlowPolicy` with `canFlow`/`isReflexive`/`isTransitive`/`wellFormed` fields, and proofs `domainFlowsTo_refl`/`domainFlowsTo_trans`. Built-in policies: `allowAll` and `linearOrder` with well-formedness proofs. `GenericLabelingContext` with embedded policy field. `EndpointFlowPolicy` for per-endpoint flow overrides. `embedLegacyLabel` mapping legacy 2x2 lattice to 4-domain system with `embedLegacyLabel_preserves_flow` correctness proof. `threeDomainExample` with 3 validation theorems.
- **H-05 (Composed bundle-level non-interference):** `NonInterferenceStep` inductive with 5 constructors (`chooseThread`, `endpointSend`, `cspaceMint`, `cspaceRevoke`, `lifecycleRetype`). `step_preserves_projection` and `composedNonInterference_step` (primary IF-M4 theorem). `NonInterferenceTrace` for multi-step lift with `composedNonInterference_trace`. Abstract composition via `preservesLowEquivalence`/`compose_preservesLowEquivalence`. Error path preservation via `errorAction_preserves_lowEquiv`.
- **M-07 (Enforcement boundary specification):** `EnforcementClass` inductive (`policyGated`/`capabilityOnly`/`readOnly`). Exhaustive `enforcementBoundary` table (17 entries covering all kernel operations). `denied_preserves_state_*` for all 3 checked operations. `enforcement_sufficiency_*` complete-disjunction coverage proofs.
- Extended information-flow test suite with 24 new WS-E5 checks (H-04 + M-07 coverage). Total: 54 checks passing.
- Updated all canonical documentation: workstream plan, README, SELE4N_SPEC, DEVELOPMENT.md, CLAIM_EVIDENCE_INDEX, INFORMATION_FLOW_ROADMAP, GitBook chapters (01, 05, 12, 24, 32, README).
- Bumped package version to **`0.11.12`**.

## [0.11.11] - 2026-02-25

### Documentation and release metadata synchronization
- Bumped patch version to **`0.11.11`** in `lakefile.toml`.
- Updated version badges and current-version references in canonical docs (`README.md`, `docs/spec/SELE4N_SPEC.md`).
- Updated contributor guidance mirrors (`AGENTS.md`, `CLAUDE.md`) so project metadata matches the codebase.

## [0.11.10] - 2026-02-25

### WS-E4 preparation — proof infrastructure and documentation accuracy

Synthesized from analysis of PRs #207 and #208, selecting the best ideas from each. All changes maintain zero sorry/axiom.

- **CPtr sentinel infrastructure:** Added `CPtr.isReserved`, `CPtr.sentinel`, `CPtr.default_eq_sentinel`, `CPtr.sentinel_isReserved` to `Prelude.lean`, paralleling the existing ObjId/ThreadId/ServiceId sentinel convention (H-06). Prepares for seL4_CapNull (CPtr 0) modeling in WS-E4 capability operations.
- **ServiceId sentinel completion:** Added `ServiceId.sentinel`, `ServiceId.default_eq_sentinel`, `ServiceId.sentinel_isReserved` to `Prelude.lean`, closing a gap where ServiceId had `isReserved` but lacked the full sentinel infrastructure.
- **Machine-layer frame lemmas:** Added 13 read-after-write and frame theorems to `Machine.lean`: `readReg_writeReg_eq/ne`, `readMem_writeMem_eq/ne`, `writeReg_preserves_pc/sp`, `writeMem_preserves_regs/timer`, `setPC_preserves_memory/timer`, `tick_preserves_regs/memory`, `tick_timer_succ`. Foundation for architecture-boundary proofs in WS-E4.
- **State-layer frame lemmas:** Added `storeObject_irqHandlers_eq` and `storeObject_machine_eq` to `Model/State.lean`, proving `storeObject` preserves IRQ handler mappings and machine state.
- **Notification well-formedness theorems:** Added `notificationSignal_result_wellFormed_wake`, `notificationSignal_result_wellFormed_merge`, `notificationWait_result_wellFormed_badge`, `notificationWait_result_wellFormed_wait` to `IPC/Invariant.lean`. Building blocks for notification ipcInvariant preservation in WS-E4.
- **Strengthened `serviceRestart_error_discards_state`:** Upgraded from trivial `True` to invariant-preservation statement (proves `serviceLifecycleCapabilityInvariantBundle` preservation on error path).
- **`boundedAddressTranslation` docstring:** Annotated as forward declaration for WS-E6 (not yet integrated into `vspaceInvariantBundle`).
- **Documentation accuracy audit:** Fixed stale references in `docs/gitbook/README.md` (pointed to v0.11.0 baseline instead of v0.11.6), `CONTRIBUTING.md` (workstream plan link), and `docs/gitbook/05-specification-and-roadmap.md` (phase status). Updated `CLAUDE.md` known-large-file entries to accurate line counts.

### WS-E3 Kernel semantic hardening (completed)

All 6 WS-E3 findings resolved with zero sorry/axiom. Synthesized from analysis of PRs #201–#203, selecting the best approach for each finding.

- **H-06 (Sentinel IDs):** Established ID 0 as reserved sentinel for all identifier types. Added `isReserved`, `sentinel`, and `ObjId.valid` predicates on `ObjId`, `ThreadId`, `ServiceId`. Proved `ObjId.default_eq_sentinel`, `ThreadId.default_eq_sentinel`, `ObjId.sentinel_isReserved`, `ThreadId.sentinel_isReserved`, `ObjId.valid_iff_not_reserved`. Added `ThreadId.toObjId_injective` in Prelude for canonical placement.
- **H-07 (VSpace in composed bundle):** Added `vspaceInvariantBundle` as 7th conjunct to `proofLayerInvariantBundle` in `Architecture/Invariant.lean`. Added adapter preservation theorems (`advanceTimerState_preserves_vspaceInvariantBundle`, `writeRegisterState_preserves_vspaceInvariantBundle`).
- **H-08 (BFS fuel exhaustion):** Changed `serviceHasPathTo.go` fuel-exhaustion base case from `false` to `true` (conservative for cycle detection). Added soundness theorems: `serviceHasPathTo_fuel_zero_is_true`, `serviceHasPathTo_false_implies_not_fuel_exhaustion`, `serviceBfsFuel_adequate`, `serviceRegisterDependency_rejects_if_path_or_fuel_exhausted`.
- **H-09 (Thread blocking in IPC):** Endpoint operations now perform compound 3-step transitions: `storeObject` (endpoint update) → `storeTcbIpcState` (thread IPC state) → `removeRunnable`/`ensureRunnable` (scheduler). `removeRunnable` also clears `scheduler.current` when removing current thread. All IPC invariant preservation proofs, capability bundle proofs, scheduler bundle proofs, and information-flow non-interference proofs rewritten for compound transitions. Added comprehensive frame lemmas for `storeTcbIpcState`, `removeRunnable`, `ensureRunnable`.
- **M-09 (Metadata sync):** Proved `storeObject_metadata_sync_type_change` and `storeObject_metadata_sync_capref_at_stored` in `Model/State.lean`.
- **L-06 (Initialization proof):** Proved `default_systemState_lifecycleConsistent` and `default_system_state_proofLayerInvariantBundle` showing the empty state satisfies all composed invariants.
- Updated all canonical documentation: workstream plan, README, SELE4N_SPEC, DEVELOPMENT.md, CLAIM_EVIDENCE_INDEX, GitBook chapters (01, 05, 24, 32).
- Bumped package version to **`0.11.10`**.

## [0.11.7] - 2026-02-24

### WS-E1 Test infrastructure and CI hardening (completed)
- **F-14:** SHA-pinned all GitHub Actions across 4 workflow files (`lean_action_ci`, `nightly_determinism`, `lean_toolchain_update_proposal`, `platform_security_baseline`) to full 40-character commit hashes with version comments.
- **M-10:** Added parameterized test topologies in `MainTraceHarness.lean` — 3 configurations (minimal/medium/large) varying thread count, priority, CNode radix, and ASID count, exercised during `lake exe sele4n`.
- **M-11:** Added 5 runtime invariant check families to `InvariantChecks.lean`: CSpace slot coherency, capability rights structure, lifecycle metadata consistency, service graph acyclicity (BFS-based), and VSpace ASID uniqueness.
- **L-07:** Converted `main_trace_smoke.expected` fixture to structured `scenario_id | risk_class | expected_fragment` format. Backward-compatible with existing substring matching in `test_tier2_trace.sh`.
- **L-08:** Added theorem-body spot-check validation to `test_tier0_hygiene.sh` (verifies no `sorry` in invariant proof surface) and F-14 SHA-pin regression guard.
- Updated Tier 3 invariant surface script with WS-E1 anchor checks for new check families, topology builders, structured fixture format, and hygiene additions.
- Updated all canonical documentation surfaces: workstream plan, README, SELE4N_SPEC, DEVELOPMENT.md, CI_POLICY.md, GitBook chapters (07, 24, README).

### Lean toolchain upgrade (WS-B10, closes #182)
- Bumped Lean toolchain from `leanprover/lean4:v4.27.0` to `leanprover/lean4:v4.28.0` in `lean-toolchain`.
- Updated Lean version badge in `README.md`, toolchain reference in `CLAUDE.md`, and package version in `docs/spec/SELE4N_SPEC.md`.
- Bumped patch version to **`0.11.7`**.

## [0.11.6] - 2026-02-22

### Documentation optimization and context-pressure reduction
- Added `CLAUDE.md` with focused project guidance: build commands, source layout, key conventions, documentation rules, active workstream context, and PR checklist. Provides a concise onboarding surface that avoids requiring full documentation traversal.
- Added `--quiet`/`-q` flag to `scripts/setup_lean_env.sh` to suppress informational output during automated runs while preserving error messages. SessionStart hook updated to use `--quiet`.
- Fixed stale workstream status in `docs/DOCUMENTATION_SYNC_AND_COVERAGE_MATRIX.md`: WS-D4 now correctly listed as completed.
- Fixed stale canonical source reference in `docs/DOCS_DEDUPLICATION_MAP.md`: "Current execution workstreams" row now points to the active `AUDIT_v0.11.0_WORKSTREAM_PLAN.md` instead of the historical `AUDIT_v0.9.32` plan.
- Tightened `CONTRIBUTING.md` to remove redundant prose and consolidate validation guidance.
- Bumped patch version to **`0.11.6`**.

## [0.11.5] - 2026-02-22

### Build environment hardening
- Fixed `scripts/setup_lean_env.sh` to work in proxy-restricted environments (e.g. Claude Code web sessions behind an egress gateway). The setup script now falls back to a manual `curl`-based download of the elan binary and Lean toolchain when elan's internal HTTP client cannot negotiate CONNECT tunnels through an egress proxy.
- Made `shellcheck` and `ripgrep` installation non-fatal in `setup_lean_env.sh`; both tools are optional for building and their absence is already handled gracefully by `test_tier0_hygiene.sh` fallback paths.
- Made `apt_update_once` tolerant of complete apt repository unavailability so the script continues to elan/lean installation instead of aborting.
- Added `.claude/settings.json` with a `SessionStart` hook that automatically runs `setup_lean_env.sh --build` on new Claude Code sessions, ensuring the Lean environment is provisioned and built without manual intervention.
- Bumped patch version to **`0.11.5`**.

## [0.11.3] - 2026-02-21

### WS-D3 proof gap closure (F-06, F-08, F-16)
- **F-06 (Badge-override safety):** Added three badge-safety theorems to `SeLe4n/Kernel/Capability/Invariant.lean`: `mintDerivedCap_rights_attenuated_with_badge_override` (rights attenuation holds regardless of badge), `mintDerivedCap_target_preserved_with_badge_override` (target identity preserved regardless of badge), and `cspaceMint_badge_override_safe` (composed kernel-operation-level proof that badge override cannot escalate privilege). TPI-D04 closed.
- **F-08 (VSpace success preservation):** Added `vspaceMapPage_success_preserves_vspaceInvariantBundle` and `vspaceUnmapPage_success_preserves_vspaceInvariantBundle` to `SeLe4n/Kernel/Architecture/VSpaceInvariant.lean`. Supporting infrastructure: `resolveAsidRoot_some_implies`, `resolveAsidRoot_of_unique_root`, `storeObject_objectIndex_eq_of_mem`, and `vspaceAsidRootsUnique` moved to `VSpace.lean`; seven VSpaceRoot helper theorems added to `Model/Object.lean` (`mapPage_asid_eq`, `unmapPage_asid_eq`, `lookup_eq_none_not_mem`, `mapPage_noVirtualOverlap`, `unmapPage_noVirtualOverlap`, `lookup_mapPage_ne`, `lookup_unmapPage_ne`). TPI-D05 closed.
- **TPI-001 (VSpace round-trip theorems):** Four round-trip theorems proved in `VSpaceInvariant.lean`: `vspaceLookup_after_map`, `vspaceLookup_map_other`, `vspaceLookup_after_unmap`, `vspaceLookup_unmap_other`. All proved without `sorry`. TPI-001 obligation from WS-C fully discharged.
- **F-16 (Proof classification docstrings):** Added module-level `/-! ... -/` docstrings to all seven `Invariant.lean` files (Scheduler, IPC, Capability, Lifecycle, InformationFlow, Service, Architecture) and `VSpaceInvariant.lean`, classifying every theorem as substantive, error-case (trivially true), non-interference, badge-safety, structural/bridge, or round-trip.
- Updated Tier-3 invariant surface script with 20 new anchor checks for WS-D3 theorem symbols and docstring presence.
- Updated all canonical planning docs, tracked proof issues, claim-evidence index, development guide, spec, GitBook chapters (12, 32), and documentation sync matrix to reflect WS-D3 completion.
- Bumped patch version to **`0.11.3`**.

## [0.11.1] - 2026-02-19

### WS-D2 information-flow enforcement and proof completion
- Implemented policy-checked kernel operation wrappers in `SeLe4n/Kernel/InformationFlow/Enforcement.lean`: `endpointSendChecked`, `cspaceMintChecked`, `serviceRestartChecked` (F-02), with correctness theorems for allowed/denied cases and reflexive self-domain flow.
- Extended non-interference proof surface in `SeLe4n/Kernel/InformationFlow/Invariant.lean` with five transition-level theorems (F-05): `chooseThread_preserves_lowEquivalent` (TPI-D01), `cspaceMint_preserves_lowEquivalent`, `cspaceRevoke_preserves_lowEquivalent` (TPI-D02), `lifecycleRetypeObject_preserves_lowEquivalent` (TPI-D03), plus shared `storeObject_at_unobservable_preserves_lowEquivalent` infrastructure.
- Added `flowDenied` error variant to `KernelError` and preservation helper lemmas to `Model/State.lean` and `Capability/Operations.lean` supporting the new proof decompositions.
- Extended `tests/InformationFlowSuite.lean` with 4 enforcement boundary tests covering same-domain pass-through and cross-domain flow denial for `endpointSendChecked` and `cspaceMintChecked`.
- Closed proof obligations TPI-D01, TPI-D02, TPI-D03; marked WS-D2 and Phase P2 as completed across all canonical planning, spec, and GitBook documentation.
- Bumped patch version to **`0.11.1`**.

## [0.11.0] - 2026-02-19

### WS-C8 post-merge audit refinement and minor release
- Performed an end-to-end documentation/codebase synchronization audit after WS-C8 completion and corrected residual status drift in the seLe4n spec (`WS-C portfolio` summary now consistently states WS-C1..WS-C8 completed).
- Refined carried-forward proof-issue tracker wording to reflect that WS-C execution is complete and obligations remain intentionally tracked post-closeout.
- Revalidated docs automation + smoke/full/nightly experimental gates to confirm runtime, proof-surface, and documentation anchors are synchronized.
- Bumped minor version to **`0.11.0`** and synchronized version markers in root/spec metadata.

## [0.10.8] - 2026-02-19

### WS-C8 documentation and GitBook consolidation completion
- Marked WS-C8 as completed across canonical planning docs, root guides, and GitBook mirrors so active portfolio status is consistently closed (WS-C1..WS-C8 complete).
- Added a canonical claim/evidence audit index (`docs/CLAIM_EVIDENCE_INDEX.md`) plus a GitBook pointer chapter (`docs/gitbook/31-claim-vs-evidence-index.md`).
- Refreshed documentation ownership/synchronization matrices and planning companion links to include the new claim/evidence index.
- Bumped patch version to **`0.10.8`** and synchronized version markers.

## [0.10.7] - 2026-02-19

### Documentation correctness and WS-C7 refinement follow-up
- Audited and corrected remaining ADR/GitBook drift where WS-B1 material still implied bounded ASID discovery is current behavior.
- Amended VSpace ADR + GitBook mirror to explicitly record WS-C7 superseding the bounded scan with `SystemState.objectIndex` traversal in `resolveAsidRoot`.
- Synchronized root/spec version markers to **`0.10.7`**.
- Re-ran docs sync + full + nightly experimental validation to confirm end-to-end consistency.

## [0.10.6] - 2026-02-19

### Added
- Added WS-C7 architecture decision record for finite object-store migration staging and compatibility notes (`docs/FINITE_OBJECT_STORE_ADR.md`) with a synced GitBook completion chapter.

### Changed
- Migrated `ServiceId` from a `Nat` alias to a typed wrapper in `SeLe4n/Prelude.lean` to restore identifier-domain separation.
- Added finite `objectIndex` tracking to `SystemState` and `BootstrapBuilder`, and rewired VSpace ASID-root resolution to use indexed object discovery instead of bounded range scanning.
- Consolidated shared store-object helper lemmas into `Model/State.lean` and reused them from lifecycle invariant helpers.
- Updated active portfolio docs/GitBook to mark WS-C7 completed.
- Bumped patch version to **`0.10.6`** and synchronized version markers.

## [0.10.5] - 2026-02-19

### WS-C6 refinement follow-up: status precision + telemetry/doc anchor tightening
- Refined active-portfolio wording in root/spec docs so WS-C7 is explicitly marked as planned while WS-C8 remains in progress.
- Synchronized GitBook telemetry mirror wording to reflect nightly smoke flake probing defaulting to 3 attempts.
- Tightened Tier-3 documentation anchor check for `docs/DOCUMENTATION_SYNC_AND_COVERAGE_MATRIX.md` to require the current WS-C baseline string instead of broad historical alternates.
- Re-ran Tier 0-4 validation (`test_full` + `test_nightly`) to confirm full-codebase/docs/gitbook consistency after refinement.
- Bumped patch version to **`0.10.5`** and synchronized version markers.

## [0.10.4] - 2026-02-19

### WS-C6 CI and supply-chain hardening completion
- Hardened GitHub Actions cache isolation in the primary Lean CI and nightly workflows by adding `runner.arch` to cache keys/restore prefixes.
- Added defensive Lean release-tag format validation in `.github/workflows/lean_toolchain_update_proposal.yml` before using upstream tags in issue-search/query logic.
- Strengthened flake telemetry defaults by updating `scripts/ci_flake_probe.sh` to default to 3 attempts (with optional explicit override) and wiring nightly to use the stronger default.
- Tightened Tier-0 hygiene marker scanning to word-boundary matching so incidental substrings no longer trigger false positives.
- Marked WS-C6 as completed across the active workstream dashboard plus development/spec/README/GitBook/matrix mirrors and synchronized Tier-3 documentation anchors.
- Bumped patch version to **`0.10.4`** and synchronized version markers.

## [0.10.3] - 2026-02-19

### WS-C5 information-flow assurance completion
- Added service-level visibility control to the IF labeling context (`serviceLabelOf`) and updated observer projection so service status is filtered by clearance policy instead of being globally visible.
- Added `SeLe4n.Kernel.InformationFlow.Invariant.endpointSend_preserves_lowEquivalent`, a nontrivial endpoint-send preservation theorem over `lowEquivalent` under hidden sender/endpoint assumptions.
- Extended IF regression checks in `tests/InformationFlowSuite.lean` to cover service-visibility filtering and an executable theorem witness for endpoint-send low-equivalence preservation.
- Marked WS-C5 as completed in the active workstream plan, tracked-proof obligations, development guide, root README, documentation sync matrix, and GitBook workstream status chapter.
- Bumped patch version to **`0.10.3`** and synchronized root version markers.

## [0.10.2] - 2026-02-19

### WS-C4 hardening follow-up: invariant precision and negative-fixture cleanup
- Refined invariant utility API with `stateInvariantChecksFor`/`assertStateInvariantsFor` so suites can validate exact fixture object inventories instead of relying only on a broad discovery window.
- Removed negative-suite `invariantView` masking and reworked the empty-send endpoint case into a dedicated malformed test state, preserving strict invariant checks for all success-path fixtures.
- Updated generative and trace harness callers to use explicit invariant object sets for stronger test validity guarantees and clearer intent.
- Re-ran smoke/full/tier4 candidate gates to confirm deterministic behavior and documentation/test synchronization after the hardening refactor.
- Bumped patch version to **`0.10.2`** and synchronized root version markers.

## [0.10.1] - 2026-02-19

### WS-C4 test validity hardening + workstream status sync
- Added executable invariant check utilities for scheduler + IPC validity and reusable state assertions used by runtime suites.
- Hardened negative and generative trace suites with post-success invariant assertions while preserving explicit invalid-fixture negative coverage.
- Added baseline invariant assertions at main trace harness entry points.
- Marked WS-C4 as completed across the active audit plan, root docs, and GitBook mirrors; synchronized Tier-3 documentation anchors accordingly.
- Bumped patch version to **`0.10.1`** and synchronized root version markers.

## [0.10.0] - 2026-02-18

### WS-C3 completion hardening + docs-sync reliability + portfolio synchronization
- Finalized WS-C3 proof-surface cleanup by removing tautological determinism theorems from VSpace and IF projection modules, while preserving tracked semantic obligations in TPI-001/TPI-002.
- Added module-level WS-C3 notes in affected Lean modules to clarify determinism-as-meta-property guidance and prevent future tautological theorem regressions.
- Hardened Tier 3 anchors to assert both removal of deprecated tautological theorems and presence of WS-C3 proof-surface notes, alongside synchronized active-slice status anchors.
- Improved docs-sync reliability in non-login shells by sourcing `${HOME}/.elan/env` when available before probing `lake`, reducing unnecessary setup churn and external mirror warnings when Lean is already installed.
- Synchronized root docs and GitBook status text to reflect WS-C3 completion and current P1 continuation focus on WS-C4.
- Bumped minor version to **`0.10.0`** and synchronized root version marker in `README.md`.

## [0.9.29] - 2026-02-18

### WS-B10 docs-sync offline/restricted-environment fallback fix
- Updated `scripts/test_docs_sync.sh` to treat `setup_lean_env.sh` as **best-effort** by default when `lake` is missing, so docs-sync still validates navigation/link consistency on offline or restricted environments where Lean setup cannot complete.
- Added explicit strict mode: `DOCS_SYNC_REQUIRE_LEAN_SETUP=1` now makes setup failure fatal for environments that require Lean setup enforcement during docs-sync.
- Kept existing explicit opt-out: `DOCS_SYNC_SKIP_LEAN_SETUP=1` skips Lean setup and doc-gen4 probing intentionally.
- Synchronized testing docs (`docs/TESTING_FRAMEWORK_PLAN.md`, `docs/gitbook/07-testing-and-ci.md`) to describe best-effort vs strict behavior.
- Bumped patch version to **`0.9.29`** and synchronized root version marker in `README.md`.

## [0.9.28] - 2026-02-18

### WS-B10 docs-sync reliability refinement
- Refined `scripts/test_docs_sync.sh` so it now auto-runs `scripts/setup_lean_env.sh` when `lake` is missing (unless `DOCS_SYNC_SKIP_LEAN_SETUP=1`), making docs-sync behavior more deterministic in pre-build environments.
- Kept doc-gen behavior explicit: navigation/link checks remain mandatory, while doc-gen4 remains optional when the executable is unavailable.
- Synchronized testing documentation language in `docs/TESTING_FRAMEWORK_PLAN.md` and GitBook chapter 07 to reflect docs-sync auto-setup semantics.
- Bumped patch version to **`0.9.28`** and synchronized root version marker in `README.md`.

## [0.9.27] - 2026-02-18

### WS-B10 CI maturity upgrades completion
- Completed WS-B10 by codifying CI governance in `docs/CI_POLICY.md`, including explicit CodeQL informational/non-blocking policy rationale, toolchain automation references, and telemetry artifact expectations.
- Added automated dependency/update cadence controls via `.github/dependabot.yml` (GitHub Actions updates) and `.github/workflows/lean_toolchain_update_proposal.yml` (weekly Lean release drift proposals as issues).
- Implemented CI timing and flake telemetry capture using `scripts/ci_capture_timing.sh` and `scripts/ci_flake_probe.sh`, wired into `.github/workflows/lean_action_ci.yml`, `.github/workflows/nightly_determinism.yml`, and `.github/workflows/platform_security_baseline.yml`.
- Published telemetry baseline documentation in `docs/CI_TELEMETRY_BASELINE.md` with GitBook mirror `docs/gitbook/29-ci-maturity-and-telemetry-baseline.md`, and synchronized active-slice/workstream completion status across README/spec/development/workstream-plan/GitBook docs.
- Bumped patch version to **`0.9.27`** and synchronized root version marker in `README.md`.

## [0.9.26] - 2026-02-18

### WS-B9 bootstrap reproducibility fix (immutable elan installer URL)
- Fixed `scripts/setup_lean_env.sh` to use a commit-pinned `ELAN_INSTALLER_URL` for `elan-init.sh` instead of the moving `master` branch URL.
- Kept `ELAN_INSTALLER_SHA256` aligned with the pinned commit artifact so fresh bootstrap remains reproducible and does not break when upstream `master` changes.
- Clarified the hardening anchor comment to require intentional paired updates of installer URL and checksum.
- Bumped patch version to **`0.9.26`** and synchronized root version marker in `README.md`.

## [0.9.25] - 2026-02-18

### WS-B9 post-audit documentation synchronization hardening
- Corrected documentation-sync baseline drift by updating `docs/DOCUMENTATION_SYNC_AND_COVERAGE_MATRIX.md` to reflect WS-B9 completion in the active planning baseline summary.
- Updated GitBook chapter 25 (`docs/gitbook/25-documentation-sync-and-coverage-matrix.md`) to explicitly call out WS-B9 synchronization expectations.
- Extended Tier 3 anchor enforcement in `scripts/test_tier3_invariant_surface.sh` to require the updated documentation-sync baseline marker and added a targeted ShellCheck suppression (`SC2016`) for the literal regex line.
- Re-ran full validation gates (`test_fast`, `test_full`, default + experimental `test_nightly`) to verify end-to-end consistency.
- Bumped patch version to **`0.9.25`** and synchronized root version marker in `README.md`.

## [0.9.24] - 2026-02-18

### WS-B9 threat model and security hardening completion
- Published the canonical security baseline document at `docs/THREAT_MODEL.md` and added GitBook mirror chapter `docs/gitbook/28-threat-model-and-security-hardening.md`.
- Hardened bootstrap supply-chain behavior in `scripts/setup_lean_env.sh` by replacing remote `curl | sh` execution with temporary-file download + SHA-256 verification (`ELAN_INSTALLER_SHA256`) before installer execution.
- Expanded `.gitignore` to block common local secret/config files and scanner outputs from being committed.
- Synchronized active-slice/workstream status across README/spec/development/workstream-plan/GitBook pages to mark WS-B9 completed.
- Extended Tier 3 invariant/doc anchors to enforce WS-B9 security surfaces (threat model presence + setup checksum markers).
- Bumped patch version to **`0.9.24`** and synchronized root version marker in `README.md`.

## [0.9.23] - 2026-02-18

### WS-B8 post-review refinement and CI/doc-policy synchronization
- Refined CI branch-protection policy documentation (`docs/CI_POLICY.md`) so required checks now include `Docs Automation / Navigation + Links + DocGen Probe`, matching the live `lean_action_ci` workflow.
- Updated testing contract docs (`docs/TESTING_FRAMEWORK_PLAN.md`, `docs/gitbook/07-testing-and-ci.md`) to explicitly document Tier 0 docs-sync automation (`scripts/test_docs_sync.sh`) and its role in required CI coverage.
- Expanded Tier 3 doc anchors in `scripts/test_tier3_invariant_surface.sh` to enforce the new docs-automation required-check and testing-doc synchronization surfaces.
- Bumped patch version to **`0.9.23`** and synchronized root version marker in `README.md`.

## [0.9.22] - 2026-02-18

### WS-B8 documentation automation + consolidation completion
- Added deterministic documentation automation tooling: `scripts/generate_doc_navigation.py` (manifest-driven GitBook navigation generation), `scripts/check_markdown_links.py` (local markdown link validation), and `scripts/test_docs_sync.sh` (single docs-sync execution entrypoint).
- Added `docs/gitbook/navigation_manifest.json` as the single source for generated handbook navigation and regenerated `docs/gitbook/README.md` + `docs/gitbook/SUMMARY.md` from that manifest.
- Wired documentation automation into required validation surfaces by invoking `scripts/test_docs_sync.sh` from `scripts/test_tier0_hygiene.sh`, and by adding a `Docs Automation / Navigation + Links + DocGen Probe` CI lane in `.github/workflows/lean_action_ci.yml`.
- Published root↔GitBook dedup ownership guidance in `docs/DOCS_DEDUPLICATION_MAP.md` and GitBook chapter mirror `docs/gitbook/27-documentation-deduplication-map.md`.
- Added planning-doc synchronization checklist enforcement via `.github/pull_request_template.md` and synchronized active-slice/workstream status docs to mark WS-B8 completed.
- Bumped patch version to **`0.9.22`** and synchronized root version marker in `README.md`.

## [0.9.21] - 2026-02-18

### WS-B7 synchronization audit follow-up
- Corrected remaining GitBook planning drift for WS-B7 completion by updating chapter 24 Phase P2 status to include WS-B7 completion state.
- Extended Tier 3 doc anchors to enforce this chapter-24 Phase P2 synchronization in `scripts/test_tier3_invariant_surface.sh`, preventing regression in future doc updates.
- Re-ran full and nightly validation/audit lanes to confirm repository-wide determinism and documentation consistency remain intact.
- Bumped patch version to **`0.9.21`** and synchronized root version marker in `README.md`.

## [0.9.20] - 2026-02-18

### WS-B7 audit optimization and IF-M1 test-surface hardening
- Added executable IF-M1 runtime assertions in `tests/InformationFlowSuite.lean` and wired them into Tier 2 negative validation via `lake exe information_flow_suite` in `scripts/test_tier2_negative.sh`, strengthening regression coverage for label-flow and observer-projection behavior.
- Expanded Tier 3 invariant anchors to enforce the new IF runtime suite presence and Tier 2 wiring (`scripts/test_tier3_invariant_surface.sh`).
- Synchronized testing/docs/GitBook evidence for the strengthened WS-B7 validation surface (`docs/TESTING_FRAMEWORK_PLAN.md`, `docs/gitbook/07-testing-and-ci.md`, `docs/audits/AUDIT_v0.9.0_WORKSTREAM_PLAN.md`, `docs/gitbook/24-comprehensive-audit-2026-workstream-planning.md`).
- Bumped patch version to **`0.9.20`** and synchronized root version marker in `README.md`.

## [0.9.19] - 2026-02-18

### WS-B7 information-flow proof-track start completion
- Implemented IF-M1 formal baseline modules in `SeLe4n/Kernel/InformationFlow/Policy.lean` and `SeLe4n/Kernel/InformationFlow/Projection.lean`, including security-label lattice primitives, flow-relation algebraic lemmas, observer projection helpers, and low-equivalence scaffolding.
- Wired information-flow modules into the aggregate kernel API (`SeLe4n/Kernel/API.lean`) and expanded Tier 3 invariant/doc anchors in `scripts/test_tier3_invariant_surface.sh` to continuously enforce IF-M1 surface and WS-B7 status synchronization.
- Published IF-M1 theorem targets + assumptions ledger in `docs/IF_M1_BASELINE_PACKAGE.md`, marked WS-B7 complete in canonical planning/spec/development/README/GitBook pages, and added WS-B7 closure evidence sections in planning mirrors.
- Bumped patch version to **`0.9.19`** and synchronized root version marker in `README.md`.

## [0.9.18] - 2026-02-18

### WS-B6 audit hardening follow-up
- Hardened Tier 3 documentation-synchronization guards in `scripts/test_tier3_invariant_surface.sh` so active-slice/phase-status wording for WS-B6 completion is continuously checked across README/spec/development guide/GitBook pages.
- Re-ran fast/full/nightly validation lanes to confirm no behavioral regressions and deterministic test stability under the tightened documentation anchors.
- Bumped patch version to **`0.9.18`** and synchronized root version marker in `README.md`.

## [0.9.17] - 2026-02-18

### WS-B6 post-merge synchronization audit
- Performed a full repository audit pass after WS-B6 merge and revalidated all quality tiers, including nightly default and nightly experimental determinism lanes.
- Fixed remaining documentation/GitBook status drift so WS-B6 completion is reflected consistently in:
  - `docs/gitbook/01-project-overview.md`,
  - `docs/gitbook/06-development-workflow.md`,
  - `docs/DEVELOPMENT.md`.
- Updated next-workstream guidance to point to WS-B7 as the next unfinished stream.
- Bumped patch version to **`0.9.17`** and synchronized the root version marker in `README.md`.

## [0.9.16] - 2026-02-18

### WS-B6 IPC completeness with notifications
- Added notification-object IPC model coverage in `SeLe4n/Model/Object.lean`: `NotificationState`, `Notification`, `KernelObject.notification`, `KernelObjectType.notification`, and `ThreadIpcState.blockedOnNotification`.
- Implemented executable notification transitions in `SeLe4n/Kernel/IPC/Operations.lean` with `notificationWait`/`notificationSignal` semantics and explicit scheduler runnable-queue interactions.
- Extended IPC invariant surfaces (`SeLe4n/Kernel/IPC/Invariant.lean`) so global `ipcInvariant` now covers both endpoint and notification object classes.
- Expanded regression evidence with notification paths in `SeLe4n/Testing/MainTraceHarness.lean`, `tests/NegativeStateSuite.lean`, and `tests/fixtures/main_trace_smoke.expected`, and added WS-B6 Tier 3 anchors in `scripts/test_tier3_invariant_surface.sh`.
- Marked WS-B6 as completed across root docs/spec/development guide and GitBook planning mirrors.
- Bumped patch version to **`0.9.16`** and synchronized root version marker in `README.md`.

## [0.9.15] - 2026-02-18

### WS-B5 semantic-correctness refinement
- Corrected `CNode.resolveSlot` semantics so `depth` is interpreted as consumed bits with `depth >= radix`, guard width `depth - radix`, and guard comparison against extracted guard bits; removed the unreachable `slotOutOfRange` branch.
- Updated `cspaceResolvePath` error mapping to the refined `ResolveError` space and realigned WS-B5 negative tests (`tests/NegativeStateSuite.lean`) to validate true depth-mismatch and guard-mismatch paths under the corrected semantics.
- Refined main trace WS-B5 coverage to assert meaningful behaviors only: removed impossible radix-0 depth-mismatch source branch and strengthened deep CNode success/guard-mismatch paths with valid pointers/depths.
- Bumped patch version to **`0.9.15`** and synchronized root version marker in `README.md`.

## [0.9.14] - 2026-02-18

### WS-B5 trace/invariant hardening follow-up
- Fixed WS-B5 trace semantics to avoid misleading "unexpected" alias output by making alias-path behavior explicit in `SeLe4n/Testing/MainTraceHarness.lean` and anchoring deep-path success with a valid guard/radix CPtr.
- Expanded Tier 2 fixture coverage by adding source/deep CSpace path expectations in `tests/fixtures/main_trace_smoke.expected` so WS-B5 path traversal outputs are regression-checked.
- Added Tier 3 invariant/doc anchors for WS-B5 (`ResolveError`, `resolveSlot`, `cspaceResolvePath`, `cspaceLookupPath`, and canonical WS-B5 completion header) in `scripts/test_tier3_invariant_surface.sh`.
- Bumped package patch version to **`0.9.14`** and synchronized root version marker in `README.md`.

## [0.9.13] - 2026-02-18

### WS-B5 CSpace guard/radix semantics completion
- Implemented executable guard/radix pointer traversal for CNodes via `CNode.resolveSlot` in `SeLe4n/Model/Object.lean`, including explicit depth mismatch and guard mismatch failure branches.
- Added path-addressed CSpace APIs (`CSpacePathAddr`, `cspaceResolvePath`, `cspaceLookupPath`) in `SeLe4n/Kernel/Capability/Operations.lean` so resolution semantics are exercised independently from direct slot lookup.
- Extended malformed-state coverage in `tests/NegativeStateSuite.lean` with WS-B5 path-resolution success + failure checks, and synchronized active-slice status/closure evidence in README/spec/development/workstream-plan/GitBook docs.
- Bumped package patch version to **`0.9.13`** and synchronized root version marker in `README.md`.

## [0.9.12] - 2026-02-18

### WS-B documentation/test-sync audit hardening
- Audited and corrected stale testing/hardware-direction status language so active-slice references consistently describe Comprehensive Audit 2026-02 WS-B execution rather than post-M7 next-slice wording.
- Added Tier 3 WS-B4 closure anchors in `scripts/test_tier3_invariant_surface.sh` that assert wrapper-structure presence for `DomainId`, `Priority`, `Irq`, `Badge`, `ASID`, `VAddr`, and `PAddr`.
- Bumped package patch version to **`0.9.12`** and synchronized root version marker in `README.md`.

## [0.9.11] - 2026-02-18

### Documentation synchronization hardening (WS-B4 follow-through)
- Audited and corrected stale GitBook/archive status language so active-slice references now consistently point to the Comprehensive Audit 2026-02 WS-B portfolio and mark older M7/post-M7 transition pages as historical context.
- Updated historical audit metadata pointers in `docs/audits/AUDIT_v0.9.0.md` so readers are directed to the current comprehensive-audit baseline and workstream execution backbone.
- Bumped package patch version to **`0.9.11`** and synchronized root version marker in `README.md`.

## [0.9.10] - 2026-02-18

### WS-B4 completion / remaining wrapper migration
- Upgraded `DomainId`, `Priority`, `Irq`, `Badge`, `ASID`, `VAddr`, and `PAddr` in `SeLe4n/Prelude.lean` from `Nat` aliases to dedicated wrapper structures with explicit migration helpers (`ofNat`/`toNat`) and compatibility instances (`OfNat`, `ToString`).
- Added a Tier 0 WS-B4 regression guard in `scripts/test_tier0_hygiene.sh` that fails if any of the migrated wrappers regress to `abbrev ... := Nat`.
- Synchronized active-slice status across root docs/spec/development guide/GitBook and canonical workstream planning docs to mark WS-B4 complete.

# Changelog

## 2026-02-19 — WS-C4 test validity hardening + documentation sync

- Completed **WS-C4 (Test validity hardening)** by adding executable invariant checks, asserting invariant validity at test fixture entry points, and enforcing post-success invariant checks in the negative state suite and trace probe.
- Hardened `MainTraceHarness` by asserting baseline and post-schedule invariant validity before running the smoke trace sequence.
- Updated active workstream status references across root docs and GitBook pages to mark WS-C4 as completed and reflect the next active execution focus.
- Bumped patch version to **`0.10.1`** and synchronized root version markers.

## [0.9.9] - 2026-02-17

### WS-B3 scenario-function decomposition and end-to-end sync audit
- Refined `SeLe4n/Testing/MainTraceHarness.lean` by decomposing the large monolithic `runMainTraceFrom` body into dedicated scenario functions (`runCapabilityAndArchitectureTrace`, `runServiceAndStressTrace`, `runLifecycleAndEndpointTrace`) while preserving stable trace output ordering and semantics.
- Re-ran complete repository validation (fast/smoke/full/nightly default+experimental and `audit_testing_framework`) to verify deterministic trace behavior and full documentation/test anchor consistency.
- Bumped package patch version to **`0.9.9`** and synchronized root version markers.

## [0.9.8] - 2026-02-17

### WS-B3 post-merge audit and synchronization hardening
- Removed an unused `TraceStep` alias from `SeLe4n/Testing/MainTraceHarness.lean` to keep the extracted harness surface minimal and intentional.
- Synchronized remaining GitBook active-slice status text (`docs/gitbook/README.md`) so WS-B3 completion state matches README/spec/development/workstream-plan snapshots.
- Re-ran full validation coverage (`test_fast`, `test_smoke`, `test_full`, default+experimental `test_nightly`, and `audit_testing_framework`) to verify full-repository consistency.
- Bumped package patch version to **`0.9.8`** and synchronized root version markers.

## [0.9.7] - 2026-02-17

### WS-B3 main trace harness refactor completion
- Refactored the executable trace harness by extracting orchestration from `Main.lean` into `SeLe4n/Testing/MainTraceHarness.lean`, keeping scenario execution composable and auditable while retaining deterministic behavior.
- Replaced ad hoc bootstrap state construction with list-driven builder composition using `SeLe4n/Testing/StateBuilder.lean` in the main harness bootstrap path.
- Updated audit/spec/development/README/GitBook status tracking to mark WS-B3 completed and record closure evidence.
- Bumped package patch version to **`0.9.7`** and synchronized root version markers.

## [0.9.6] - 2026-02-17

### WS-B2 negative-suite correctness hardening
- Refined `tests/NegativeStateSuite.lean` endpoint coverage to test both `.endpointStateMismatch` (idle endpoint receive) and `.endpointQueueEmpty` (send-state empty queue) on explicit fixtures, removing the prior mislabeled assertion gap.
- Re-ran full repository validation (`test_fast`, `test_smoke`, `test_full`, default/experimental `test_nightly`, and `audit_testing_framework`) to ensure code/docs/gitbook/test contracts remain synchronized and deterministic.
- Bumped package patch version to **`0.9.6`** and synchronized root version markers.

## [0.9.5] - 2026-02-17

### WS-B2 generative + negative testing expansion completion
- Added reusable bootstrap-state builder DSL in `SeLe4n/Testing/StateBuilder.lean` and a dedicated malformed-state executable suite in `tests/NegativeStateSuite.lean` (wired as `lake exe negative_state_suite`).
- Extended smoke/full gates with `scripts/test_tier2_negative.sh` so negative-path assertions are required alongside trace fixtures.
- Expanded nightly experimental candidates to persist per-seed stochastic probe logs and a replay manifest (`tests/artifacts/nightly/trace_sequence_probe_manifest.csv`) for deterministic triage.
- Synchronized active-slice documentation and GitBook mirrors to mark WS-B2 as completed and record closure evidence in the comprehensive-audit workstream plan.
- Bumped package patch version to **`0.9.5`** and synchronized root version markers.

## [0.9.4] - 2026-02-17

### Bootstrap reliability + doc-sync hardening follow-up
- Hardened `scripts/setup_lean_env.sh` apt bootstrap behavior: if `apt-get update` fails due an unavailable third-party source, the script now retries using primary distro sources only so required setup dependencies can still install deterministically.
- Updated developer workflow docs and GitBook mirror to document the new setup fallback behavior and keep contributor guidance aligned with executable setup semantics.
- Bumped package patch version to **`0.9.4`** and synchronized root version marker.

## [0.9.3] - 2026-02-17

### WS-B1 audit hardening and repository-wide synchronization pass
- Corrected WS-B1 ASID/root modeling by replacing the previous malformed `asidBoundToRoot` relation with a proper existential relation and documenting the explicit bounded discovery-window assumption in code and ADR.
- Added VSpace soundness/determinism anchors (`resolveAsidRoot_sound`, `vspaceLookup_deterministic`) and strengthened Tier-3 invariant-surface guards accordingly.
- Performed a full documentation/GitBook consistency pass so phase sequencing and active-slice wording consistently reflect `WS-B1 completed` status across spec/development/workflow pages.
- Updated audit index wording to align with the current `0.9.3` baseline and synchronized package version markers.

## [0.9.2] - 2026-02-17

### WS-B1 VSpace + memory model foundation completion
- Implemented first-class VSpace modeling with `VSpaceRoot` kernel objects, deterministic map/unmap/lookup transitions, and explicit failure modes for ASID binding, mapping conflicts, and translation faults.
- Added WS-B1 architecture invariant surface (`vspaceInvariantBundle`) and bounded translation predicate scaffold to anchor follow-on proof work.
- Extended `Main.lean` executable trace and Tier 2 fixture expectations with deterministic VSpace map→lookup→unmap→fault coverage.
- Published VSpace/memory abstraction ADR (`docs/VSPACE_MEMORY_MODEL_ADR.md`) and synchronized GitBook/state-tracking docs to mark WS-B1 completed in the active comprehensive-audit slice.
- Bumped package patch version from `0.9.1` to **`0.9.2`**.

## [0.9.1] - 2026-02-17

### Comprehensive-audit workstream execution kickoff readiness
- Expanded `docs/audits/AUDIT_v0.9.0_WORKSTREAM_PLAN.md` into a detailed execution contract with per-workstream goals, prerequisites, implementation slices, evidence contracts, and exit criteria for WS-B1..WS-B11.
- Added explicit portfolio readiness gates (G0 kickoff readiness and G1 hardware-entry readiness) and clarified that the current slice is centered on WS-B execution kickoff.
- Synchronized root README, audit index, and GitBook planning chapter wording so active-slice status consistently reflects comprehensive-audit workstream execution readiness.
- Bumped package patch version from `0.9.0` to **`0.9.1`**.

## [0.9.0] - 2026-02-17

### CI security-scan reliability follow-up
- Fixed Gitleaks shallow-clone ambiguous revision failures by setting `actions/checkout` `fetch-depth: 0` in the security baseline scan job.
- Fixed `Platform and Security Baseline` workflow permissions by adding `pull-requests: read`, resolving Gitleaks pull-request commit enumeration failures (`Resource not accessible by integration`) in the `Security Signal / Secret + Dependency + CodeQL` job.
- Updated `docs/CI_POLICY.md` to document the `pull-requests: read` requirement and rationale for the Gitleaks PR scan path.
- Made CodeQL analyze upload non-blocking (`continue-on-error: true`) to avoid failing the security lane when repository Code Scanning is not enabled.
- Added Tier 3 invariant/doc anchor coverage to ensure the workflow retains `pull-requests: read` in future refactors.
- Version marker remains `0.9.0` as the canonical minor-release target for this slice.


### M7 exit-gate closeout and next-slice activation
- Published formal M7 closeout artifact `docs/M7_CLOSEOUT_PACKET.md` and GitBook mirror `docs/gitbook/23-m7-remediation-closeout-packet.md`, including dependency owners, accepted residual risks, and exit-gate checklist evidence.
- Synchronized root docs/spec/development/testing/GitBook stage markers so M7 is completed baseline and post-M7 hardware-oriented next-slice execution is active.
- Expanded Tier-3 documentation anchors to validate closeout packet presence and stage-state synchronization as part of required full-suite checks.
- Bumped project version from `0.8.22` to **`0.9.0`** for the post-remediation minor release transition.

## [0.8.22] - 2026-02-17

### WS-A8 validation hardening and CI robustness
- Hardened `.github/workflows/platform_security_baseline.yml` so security scanning is skipped for fork-origin pull requests where `security-events: write` is unavailable, while keeping the ARM64 fast-gate lane active.
- Expanded test/docs synchronization by adding WS-A8 artifact anchor checks to `scripts/test_tier3_invariant_surface.sh` (workflow/job names, roadmap milestones, and cross-doc references).
- Updated testing docs (`docs/TESTING_FRAMEWORK_PLAN.md` and `docs/gitbook/07-testing-and-ci.md`) to explicitly include WS-A8 platform/security baseline automation in the CI/test contract narrative.
- Bumped package patch version to `0.8.22` and synchronized README version marker.

## [0.8.21] - 2026-02-17

### WS-A8 platform/security maturity completion
- Added `.github/workflows/platform_security_baseline.yml` to operationalize WS-A8 gates: an ARM64 architecture-targeted fast lane (`ubuntu-24.04-arm`) and automated baseline security scanning (Gitleaks, Trivy, CodeQL for workflow analysis).
- Published `docs/INFORMATION_FLOW_ROADMAP.md` with staged IF-M1..IF-M5 milestones, deliverables, and exit-evidence expectations for post-M7 information-flow proofs.
- Updated remediation/development/GitBook tracking docs to mark WS-A8 completed and synchronized CI policy/README references with the new security and roadmap artifacts.
- Bumped package patch version to `0.8.21` and synchronized the root README version marker.

## [0.8.20] - 2026-02-17

### Validation and documentation synchronization follow-up
- Refined nightly-testing documentation (`docs/TESTING_FRAMEWORK_PLAN.md` and `docs/gitbook/07-testing-and-ci.md`) to match mode-aware Tier 4 status behavior in `scripts/test_nightly.sh` (default extension-point guidance vs executed signal when `NIGHTLY_ENABLE_EXPERIMENTAL=1`).
- Re-validated smoke/full/nightly test tiers (default + experimental) to confirm repository and GitBook/testing docs remain synchronized with current M7 progress state.
- Bumped package patch version to `0.8.20` and synchronized the root README version marker.

## [0.8.19] - 2026-02-17

### Audit hardening follow-up
- Optimized `scripts/test_nightly.sh` reporting so Tier 4 status messaging is environment-aware: it now reports staged execution when `NIGHTLY_ENABLE_EXPERIMENTAL=1` and reports extension-point guidance only in default mode.
- Re-ran full validation coverage (`test_smoke`, `test_full`, default `test_nightly`, experimental `test_nightly`, `lake build`, and executable trace run) to confirm repository, docs, and GitBook remain synchronized with current M7/WS-A7 status.
- Bumped package patch version to `0.8.19` and synchronized the root README version marker.

## [0.8.18] - 2026-02-17

### WS-A7 proof maintainability completion
- Completed WS-A7 by introducing shared helper theorem `endpoint_store_preserves_schedulerInvariantBundle` in `SeLe4n/Kernel/IPC/Invariant.lean`, reducing repeated scheduler-bundle proof blocks across endpoint send/await/receive preservation theorems.
- Added concise theorem-purpose docstrings for the shared helper and endpoint scheduler-bundle preservation theorem entrypoints to improve proof-surface legibility for reviewers.
- Updated development guide and GitBook workstream status pages to mark WS-A7 completed and move active focus to WS-A8.
- Bumped package patch version to `0.8.18` and synchronized the root README version marker.

## [0.8.17] - 2026-02-17

### Documentation/GitBook sync audit hardening
- Closed remaining WS-A6-era documentation drift by marking WS-A4 as completed in `docs/M7_CLOSEOUT_PACKET.md` to match existing closure evidence and the active-slice status pages.
- Updated `docs/gitbook/13-future-slices-and-delivery-plan.md` so M7 workstream statuses are synchronized with current slice reality (WS-A1..WS-A6 completed, WS-A7 in progress, WS-A8 planned).
- Bumped package patch version to `0.8.17` and synchronized the root README version marker.

## [0.8.16] - 2026-02-17

### WS-A6 documentation IA completion
- Marked WS-A6 as completed across remediation planning and active-slice GitBook chapters with explicit closure evidence and DoD status updates.
- Added a contributor-first 5-minute onboarding path in `CONTRIBUTING.md`, synchronized root `README.md` start-here ordering, and mirrored the same quickstart flow in `docs/gitbook/README.md`.
- Updated M7 completion snapshot in `docs/DEVELOPMENT.md` to reflect WS-A6 closure and move active focus to WS-A7.

## [0.8.15] - 2026-02-17

### WS-A5 regression-guard refinement
- Added Tier 3 invariant/doc anchors for WS-A5 closure evidence: fixture-module presence, `Main.lean` fixture import, and hardware-boundary policy guard language.
- Preserved full Tier 0–4 validation after extending regression anchors.

## [0.8.14] - 2026-02-17

### WS-A5 audit follow-up hardening
- Hardened Tier 0 import-boundary hygiene to include a non-`rg` fallback scan path, preventing false failures in environments where ripgrep is unavailable.
- Tightened `docs/HARDWARE_BOUNDARY_CONTRACT_POLICY.md` wording so policy scope matches enforcement (`SeLe4n/Kernel`).

## [0.8.13] - 2026-02-17

### Hardware-boundary safety / WS-A5 completion
- Isolated permissive runtime contract fixtures into `SeLe4n/Testing/RuntimeContractFixtures.lean` and updated `Main.lean` to consume them from a testing-only module.
- Added Tier 0 hygiene boundary enforcement to fail if production modules under `SeLe4n/` reference test-only runtime contract fixtures.
- Added `docs/HARDWARE_BOUNDARY_CONTRACT_POLICY.md` and synchronized remediation/GitBook workstream status to mark WS-A5 complete.

## [0.8.12] - 2026-02-17

### Testing / WS-A4 completion hardening
- Expanded Tier 2 fixture-backed trace coverage in `Main.lean` + `tests/fixtures/main_trace_smoke.expected` to explicitly cover all audit-recommended scale categories: deep CNode radix shape, large runnable queue (10+), multiple IPC endpoints, service dependency chain depth-5, and boundary memory addresses.
- Kept Tier 2 scenario/risk tagging format for audit traceability while adding new WS-A4 scale scenarios under `WS-A4-SCALE-*` IDs.
- Revalidated Tier 0–4 scripts (including seeded `trace_sequence_probe`) with the expanded scenarios and refreshed M7 workstream documentation evidence.

All notable changes to this project are documented in this file.

## [0.8.10] - 2026-02-17

### WS-A3 regression-guard hardening
- Added Tier-3 invariant-surface guards that require explicit `ThreadId.toObjId` conversion entrypoint presence and fail if an implicit `ThreadId -> ObjId` coercion is reintroduced.
- Revalidated full Tier 0-4 test coverage (`test_fast`, `test_smoke`, `test_full`, `test_nightly` with experimental candidates) after introducing the new guard.

## [0.8.9] - 2026-02-17

### WS-A3 audit follow-up hardening
- Removed implicit `ThreadId -> ObjId` coercion and replaced it with explicit `ThreadId.toObjId` conversions at object-store boundaries to preserve stronger compile-time domain separation.
- Updated scheduler and IPC proof/operation call sites to use explicit conversion points and kept all invariant bundles compiling without placeholder debt.
- Synchronized GitBook planning chapters so WS-A3 completion state is consistent across current-slice and remediation overview pages.

## [0.8.8] - 2026-02-17

### M7 WS-A3 type-safety uplift
- Migrated `ThreadId`, `ObjId`, `CPtr`, and `Slot` from raw `Nat` aliases to dedicated wrapper types with migration helpers (`ofNat`/`toNat`) and typed bridge instances where object-store indexing is intentional.
- Updated scheduler/IPC invariant surfaces to keep thread-domain membership obligations typed as `ThreadId` while preserving object-store key discipline through `ObjId`.
- Updated active-slice docs/GitBook to mark WS-A3 completed and synced current development status snapshots.

## [0.8.7] - 2026-02-17

### Tooling setup optimization
- Refactored `scripts/setup_lean_env.sh` to share package-manager helpers and perform `apt-get update` at most once even when both `shellcheck` and `ripgrep` are missing.
- Preserved all existing installer behavior while reducing duplicated setup work/noise in cold environments.

## [0.8.6] - 2026-02-17

### Audit/Sync hardening
- Performed full post-WS-A2 repository validation sweep (`test_fast`, `test_smoke`, `test_full`, `test_nightly`) and confirmed all tiers pass without regressions.
- Synchronized roadmap and audit-context docs so M7 status explicitly reflects WS-A1/WS-A2 as completed while preserving historical audit snapshot intent.
- Clarified historical audit caveat language so architecture criticisms about IPC split are interpreted as pre-remediation findings, not current-state defects.

## [0.8.5] - 2026-02-17

### Architecture / API modularity (WS-A2)
- Split IPC transition semantics into `SeLe4n/Kernel/IPC/Operations.lean` and retained invariant/proof obligations in `SeLe4n/Kernel/IPC/Invariant.lean` to restore operations/invariant symmetry.
- Kept `SeLe4n/Kernel/API.lean` as the stable external facade while explicitly exporting IPC operations and invariant surfaces.
- Updated development documentation and GitBook architecture maps/workstream tracking to mark WS-A2 complete with closure evidence.

## [0.8.4] - 2026-02-17

### CI / Tooling reliability
- Updated `scripts/setup_lean_env.sh` to install `ripgrep` (`rg`) when missing, matching Tier-3/Tier-4 script requirements and preventing CI failures where `rg` is unavailable.

## [0.8.3] - 2026-02-17

### CI / Tooling reliability
- Fixed `scripts/setup_lean_env.sh` to source existing elan env before probing/installing, preventing redundant reinstall attempts in CI shells that do not persist PATH changes.
- Fixed `scripts/setup_lean_env.sh` to treat already-installed Lean toolchains as a success path, preventing CI failures when `leanprover/lean4:v4.27.0` is present.

## [0.8.2] - 2026-02-17

### Documentation
- Added root `CONTRIBUTING.md` pointer to canonical contributor workflow in `docs/DEVELOPMENT.md`.
- Added root `CHANGELOG.md` for chronological release notes and milestone-delivery traceability.
- Added post-audit remediation note in `docs/audits/AUDIT_v0.8.0.md` clarifying WS-A1 CI hardening landed after the audit snapshot.

### CI / Quality Gates
- Added Tier 3/WS-A1 documentation anchor checks for CI policy/workflow artifacts and root contributor/changelog discoverability in `scripts/test_tier3_invariant_surface.sh`.

## [0.8.1] - 2026-02-17

### CI / Quality Gates (WS-A1)
- Promoted Tier 3 (`test_full.sh`) into CI merge-gate flow.
- Added nightly determinism workflow running `NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh`.
- Added canonical branch-protection policy doc `docs/CI_POLICY.md`.
- Added Lean/Lake cache restoration in CI workflows.

## [0.8.0] - 2026-02-17

### Baseline
- M6 complete / M7 active audit-remediation baseline.
