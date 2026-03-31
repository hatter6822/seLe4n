# Proof and Invariant Map

This chapter summarizes how theorem surfaces are organized and how they compose across milestones.

## 1. Layered invariant philosophy

seLe4n invariants are intentionally layered:

1. **component invariants** describe one focused safety condition,
2. **subsystem bundles** combine related components,
3. **cross-subsystem bundles** compose milestone contracts.

This keeps proof scripts reviewable and reduces blast radius when adding new transitions.

**WS-Q2 migration note (v0.17.8):** All `Std.HashMap` fields in kernel state
have been replaced with verified `RHTable` (Robin Hood hash table), and all
`Std.HashSet` fields with `RHSet`. Historical references to `Std.HashMap`/
`Std.HashSet` below describe the pre-Q2 architecture. The global invariant
`allTablesInvExt` (State.lean) ensures all 16 map + 2 set fields satisfy
`invExt` (WF + distCorrect + noDupKeys + probeChainDominant). Algorithm-local
`Std.HashSet` usage (BFS visited sets in Acyclicity.lean, observable filtering
in Projection.lean) is intentionally retained.

**WS-T/T3 additions (v0.20.3) — Rust ABI Hardening:**

- `MessageInfo::encode()` now returns `Result<u64, KernelError>` with 20-bit
  label bound check (`MAX_LABEL = 2^20 - 1`, seL4 convention; V2-E/H tightened
  from 55-bit), preventing silent truncation (M-NEW-9). Propagated through
  `encode_syscall()` and `invoke_syscall()`.
- `VSpaceMapArgs.perms` changed from raw `u64` to typed `PagePerms` with
  decode-time validation via `PagePerms::try_from()` (M-NEW-10).
- `ServiceRegisterArgs.requires_grant` decode changed from permissive `!= 0`
  to strict `match { 0 => false, 1 => true, _ => error }` (M-NEW-11).
- 24 pre-existing clippy `double_must_use` warnings resolved in `sele4n-sys`.

**WS-T/T2 additions (v0.20.1):**

- `AccessRightSet.ofList_valid` — proves `ofList` always produces a valid
  rights set (H-1).
- `CapDerivationTree.mk` constructor is now `private`; external code must use
  `empty` or `mk_checked` (which requires `cdtMapsConsistent` witness) (H-2).
- `FrozenSystemState.tlb` field added; `freeze_preserves_tlb` correctness
  theorem proves TLB state is preserved across freeze (M-NEW-1).
- `storeObject_preserves_allTablesInvExtK` — bundled theorem composing 16+
  component preservation proofs for `storeObject` using `invExtK` (M-NEW-2, V3-B).
- `capabilityRefs_filter_preserves_invExt` + `capabilityRefs_fold_preserves_invExt`
  — filter-then-fold chain in `storeObject` preserves `invExt` (M-NEW-3).
- `CNode.guardBounded` predicate added to `CNode.wellFormed` — guard value
  must fit in guard width bits. `resolveSlot_guardMismatch_of_not_guardBounded`
  proves `resolveSlot` always fails for unbounded guards (L-NEW-4).
- `Builder.createObject` now maintains `objectIndex`/`objectIndexSet` (M-BLD-1).

**WS-T/T4 additions (v0.20.3) — IPC & Capability Proof Closure:**

- `ipcStateQueueConsistent` preservation for `endpointCall`, `endpointReplyRecv`,
  `notificationSignal`, `notificationWait` (M-IPC-1).
- `endpointQueueRemoveDual_preserves_dualQueueSystemInvariant` — 1023-line
  sorry-free proof covering all 4 paths with `tcbQueueChainAcyclic` (M-IPC-2).
- `ipcInvariantFull` preservation for WithCaps wrapper operations (M-IPC-3).
- `descendantsOf_fuel_sufficiency` with 8 BFS lemmas (M-CAP-2).
- `buildCNodeRadix_lookup_equiv` bidirectional equivalence (M-DS-3).
- `insert_maxPriority_consistency` for RunQueue (M-SCH-1).

**WS-T/T5 additions (v0.20.4) — Lifecycle & Cross-Subsystem:**

- `KernelObject.wellFormed` decidable predicate for structural validation (M-NEW-5).
- `spliceOutMidQueueNode` intrusive queue mid-node removal with link patching (M-LCS-1).
- `noStaleEndpointQueueReferences` extended to interior queue members via
  bounded `collectQueueMembers` traversal (M-CS-1).
- `noStaleNotificationWaitReferences` added to `crossSubsystemInvariant` (L-NEW-3).
- `threadPriority_membership_consistent` with insert/remove preservation (M-SCH-3).

**WS-T/T6 additions (v0.20.5) — Architecture & Hardware:**

- `checkedDispatch_flowDenied_preserves_state` — proves all 3 policy-gated
  wrappers preserve state on flow denial (M-IF-1).
- `mmioRead`/`mmioWrite` with 4 correctness theorems (M-NEW-7/8).
- `MmioReadOutcome` inductive encoding volatile/ram/w1c/fifo read-kind constraints (X1-D).
- `mkMmioSafe_uart`/`mkMmioSafe_gicDist`/`mkMmioSafe_gicCpu` witness generators (X1-E).
- `tlbFlushByASID`/`tlbFlushByPage`/`tlbFlushAll` with state frame proofs (M-ARCH-4).
- `contextSwitchState` atomic operation preserving `contextMatchesCurrent` (X1-F/G).
- `AdapterProofHooks.preserveContextSwitch` + `adapterContextSwitch_ok_preserves_proofLayerInvariantBundle` (X1-F/G).
- `RegisterWriteInvariant` predicate for context-switch awareness (H-3).

**WS-T/T7 additions (v0.20.6) — Test & Build Infrastructure:**

- `buildChecked` migration ensures runtime structural invariant validation.
- 31 post-mutation invariant checks across all major transition families.
- `decodeVSpaceMapArgs_error_iff` theorem (Tier 3 invariant surface anchor).

## 2. Scheduler invariants (M1)

Component level:

- `runQueueUnique`
- `currentThreadValid`
- `queueCurrentConsistent` (WS-H12b: inverted to `current ∉ runnable`, matching seL4 dequeue-on-dispatch)
- `currentTimeSlicePositive` (WS-H12b: current thread time slice positive, since current is not in run queue)
- `schedulerPriorityMatch` (WS-H12b: priority consistency for run queue threads)
- `runQueueThreadPriorityConsistent` (WS-H16/A-19: bi-directional consistency between RunQueue membership and `threadPriority` mapping, with `runQueueThreadPriorityConsistent_default` theorem)

Data structure:

- `RunQueue` (`Scheduler/RunQueue.lean`, WS-G4 + WS-H6) — priority-bucketed run queue with bidirectional structural invariants `flat_wf` and `flat_wf_rev`, plus bridge lemmas `membership_implies_flat` and `mem_toList_iff_mem` between O(1) `Std.HashSet` membership and `flat : List ThreadId`/`toList` reasoning. `chooseBestInBucket` bucket-first scheduling: O(k) max-priority bucket scan with full-list fallback. `remove` computes filtered bucket once for both `byPriority` and `maxPriority` (v0.12.15 refinement). Implicit `membership` ↔ `threadPriority` consistency maintained by insert/remove API (runtime-verified by `runQueueThreadPriorityConsistentB`).
- 13 bridge lemmas: `mem_insert`, `mem_remove`, `mem_rotateHead`, `mem_rotateToBack`, `not_mem_empty`, `toList_insert_not_mem`, `toList_filter_insert_neg`, `toList_filter_remove_neg`, `not_mem_toList_of_not_mem`, `not_mem_remove_toList`, `mem_toList_rotateToBack_self`, `toList_rotateToBack_nodup`, `mem_toList_rotateToBack_ne`.

Bundle level:

- `schedulerInvariantBundle` (alias over `kernelInvariant`)
- `schedulerInvariantBundleFull` (9-conjunct: `schedulerInvariantBundle ∧ timeSlicePositive ∧ currentTimeSlicePositive ∧ edfCurrentHasEarliestDeadline ∧ contextMatchesCurrent ∧ runnableThreadsAreTCBs ∧ schedulerPriorityMatch ∧ domainTimeRemainingPositive ∧ domainScheduleEntriesPositive`, R6-D/L-12/V5-H/X2-A)

Extraction theorems:

- `schedulerInvariantBundleFull_to_contextMatchesCurrent` — extracts `contextMatchesCurrent` from the 9-conjunct bundle (WS-H12e + WS-F6/D3)
- `schedulerInvariantBundleFull_to_priorityMatch` — extracts `schedulerPriorityMatch` from the 9-conjunct bundle (R6-D/L-12)
- `schedulerInvariantBundleFull_to_domainTimeRemainingPositive` — extracts `domainTimeRemainingPositive` from the 9-conjunct bundle (V5-H)
- `schedulerInvariantBundleFull_to_domainScheduleEntriesPositive` — extracts `domainScheduleEntriesPositive` from the 9-conjunct bundle (X2-A)

Preservation shape:

- `chooseThread_preserves_*`
- `schedule_preserves_*`
- `handleYield_preserves_*`
- `timerTick_preserves_schedulerInvariantBundle` (WS-F4 / F-03)
- `timerTick_preserves_kernelInvariant` (WS-F4 / F-03)
- `scheduleDomain_preserves_schedulerInvariantBundleFull` (S3-E / U-M08)
- `schedule_preserves_runQueueWellFormed` (S3-G / U-M09)
- `remove_preserves_wellFormed` (S3-F / U-M09 — RunQueue.lean)
- `isBetterCandidate_transitive` (WS-H6 / A-17)
- `bucketFirst_fullScan_equivalence` (WS-H6 / A-17)

Documented semantics:

- `chooseThread` uses EDF tie-breaking with FIFO ordering: among threads with the
  earliest deadline in the highest-priority bucket, the thread at the head of the
  bucket list (longest-waiting) is selected (S5-I / U-M22).

## 3. Capability invariants (M2)

Component level:

- `cspaceSlotUnique` — structural CNode slot-index uniqueness (reformulated in WS-E2; WS-G5: trivially true with `Std.HashMap` key uniqueness),
- `cspaceLookupSound` — lookup completeness grounded in slot membership (reformulated in WS-E2; non-tautological),
- `cspaceAttenuationRule` — minted capabilities attenuate rights,
- `lifecycleAuthorityMonotonicity` — authority only decreases through lifecycle operations.

Bridge theorem: `cspaceLookupSound_of_cspaceSlotUnique` derives lookup soundness from slot uniqueness.

Bundle level:

- `capabilityInvariantBundle` (WS-H4 + WS-H13 + WS-F6/D1: 6-tuple conjunction — `cspaceSlotUnique`, `cspaceLookupSound`, `cspaceSlotCountBounded`, `cdtCompleteness`, `cdtAcyclicity`, `cspaceDepthConsistent`; 2 tautological predicates removed by WS-F6)
- `capabilityInvariantBundleWithCdtMaps` (S3-D: base bundle + `cdtMapsConsistent`)
- `capabilityInvariantBundleFull` (S3-D: base bundle + `cdtMapsConsistent` + `cdtMintCompleteness`)

CDT edge operations (S3-B/C):

- `addEdge_preserves_cdtMapsConsistent` — composite: addEdge preserves both childMap and parentMap consistency
- `removeEdge` (private) — single-edge removal from edges, childMap, parentMap
- `removeEdge_surviving_child_ne` — surviving edges have child ≠ removed child (forest property)
- `removeEdge_preserves_cdtMapsConsistent` — removal preserves consistency (postcondition pattern)
- `revokeDerivationEdge` — public CDT wrapper for removeEdge
- `severDerivationEdge` — kernel-level operation for fine-grained single-edge CDT revocation

CDT maps consistency preservation (S3-D):

- `cdtMapsConsistent_of_cdt_eq` — transfer through state changes preserving CDT
- `cdtMapsConsistent_of_storeObject` — frame through object store
- `cspaceInsertSlot_preserves_cdtMapsConsistent` — insert preserves (CDT unchanged)
- `cspaceMint_preserves_cdtMapsConsistent` — mint preserves (via insert)
- `cspaceDeleteSlot_preserves_cdtMapsConsistent` — delete preserves (CDT unchanged)
- `cspaceCopy_preserves_cdtMapsConsistent` — copy preserves (postcondition hypothesis, matching `cdtCompleteness`/`cdtAcyclicity` pattern)
- `cspaceMove_preserves_cdtMapsConsistent` — move preserves (postcondition hypothesis)
- `cspaceRevoke_preserves_cdtMapsConsistent` — revoke preserves (CDT unchanged)
- `capabilityInvariantBundle_of_slotUnique` (constructor; requires all CNodes satisfy `slotsUnique` plus WS-H4 components)

Preservation shape:

- operation-level `*_preserves_capabilityInvariantBundle` for insert/delete/revoke (compositional: pre-state → post-state),
- `cspaceMutate_preserves_capabilityInvariantBundle` (WS-F4 / F-06),
- `cspaceRevokeCdt_preserves_capabilityInvariantBundle` (WS-F4 / F-06),
- `cspaceRevokeCdtStrict_preserves_capabilityInvariantBundle` (WS-F4 / F-06),
- `streamingRevokeBFS_step_preserves` (WS-M5 / M-P04 — single BFS level invariant maintenance),
- `streamingRevokeBFS_preserves` (WS-M5 / M-P04 — composed multi-level BFS preservation),
- `cspaceRevokeCdtStreaming_preserves_capabilityInvariantBundle` (WS-M5 / M-P04 — streaming BFS revoke top-level bundle preservation),
- IPC-level preservation for endpoint send/receive/await-receive/reply (compositional),
- lifecycle preservation with `hNewObjCNodeUniq` + `hNewObjCNodeBounded` hypotheses (WS-H4).

CDT acyclicity discharge patterns **(V3-D/E/F, M-PRF-1)**:

- CDT-expanding ops (`cspaceCopy`, `cspaceMove`, `cspaceMint`) externalize `hCdtPost` hypothesis — caller supplies post-state `cdtAcyclicity` witness since these add CDT edges.
- CDT-shrinking ops (`cspaceDeleteSlotCore`, `cspaceRevokeCdt`) prove acyclicity internally via `edgeWellFounded_sub` — removing edges preserves well-foundedness.
- `cdtExpandingOp_preserves_bundle_with_hypothesis` — documents the externalized hypothesis pattern for CDT-expanding operations.
- `cdtShrinkingOps_preserve_acyclicity` — machine-checked proof that CDT-shrinking operations preserve acyclicity via `edgeWellFounded_sub` edge-removal argument.
- `ipcTransferSingleCap_preserves_capabilityInvariantBundle` — machine-checked per-step theorem for IPC capability transfer. `ipcUnwrapCapsLoop_preserves_capabilityInvariantBundle` — fuel-indexed induction composing per-step preservation across all loop iterations, threading slot capacity and CDT postcondition hypotheses. `ipcUnwrapCaps_preserves_capabilityInvariantBundle` — unified Bool-parametric theorem covering both Grant=true (loop induction) and Grant=false (state unchanged) paths. Full capability transfer preservation chain is machine-checked **(V3-E, M-PRF-2)**.
- `resolveCapAddress_callers_check_rights` — machine-checked theorem proving all `syscallInvoke` dispatch arms pass through `syscallLookupCap` rights gate before operations. Located in `API.lean` **(V3-F, M-PRF-3)**.

WS-H4 transfer theorems (new):

- `cdtPredicates_through_blocking_path` — storeObject(.endpoint) → storeTcbIpcState → removeRunnable,
- `cdtPredicates_through_handshake_path` — storeObject(.endpoint) → storeTcbIpcState → ensureRunnable,
- `cdtPredicates_through_reply_path` — storeTcbIpcStateAndMessage → ensureRunnable.

Badge routing chain (H-03, WS-F5/D1):

- `mintDerivedCap_badge_propagated` → `cspaceMint_child_badge_preserved` → `notificationSignal_badge_stored_fresh` → `notificationWait_recovers_pending_badge`
- End-to-end: `badge_notification_routing_consistent` (word-bounded)
- Merge property: `badge_merge_idempotent` (via `Badge.bor`)
- Word-bounding: `Badge.ofNatMasked_valid`, `Badge.bor_valid`, `Badge.bor_comm`, `Badge.ofNatMasked_lt_eq` (R6-B/L-01)
- **R6-B/S1-A**: `Badge.ofNat` removed entirely (WS-S/S1-A); all callers use `Badge.ofNatMasked`
- Access rights: `AccessRightSet.ofList_comm` (order-independence), `rightsSubset_sound`
- **S1-G**: `AccessRightSet.valid` (bits < 2^5), `ofNat` masked constructor, `ofNat_valid`, `ofNat_idempotent`

**WS-M audit findings** (v0.16.13 — Phase 1 at v0.16.14; Phase 2 at v0.16.15; Phase 3 at v0.16.17; Phase 4 at v0.16.18; Phase 5 at v0.16.19–v0.17.0 — **PORTFOLIO COMPLETE**):

- M-G01: ~~proof incomplete~~ → **RESOLVED** (v0.16.14): existing proof was complete; added forward-direction `resolveCapAddress_guard_match` companion theorem,
- M-G02: ~~`cdtMintCompleteness` gap~~ → **RESOLVED** (v0.16.14): `cdtMintCompleteness` predicate + transfer theorem + extended bundle `capabilityInvariantBundleWithMintCompleteness`,
- M-G03: ~~CDT acyclicity hypotheses deferred~~ → **RESOLVED** (v0.18.1): `addEdge_preserves_edgeWellFounded_fresh` for fresh nodes + `isAncestor` decidable predicate + `addEdgeWouldBeSafe` runtime cycle check. General no-parent theorem (`addEdge_preserves_edgeWellFounded_noParent`) requires descendant hypothesis,
- M-G04: ~~unnamed error-swallowing pattern~~ → **RESOLVED** (v0.18.1): Error-swallowing eliminated in R2-A/R2-B. `processRevokeNode` now propagates errors. `cspaceRevokeCdt_error_propagation_consistent` replaces `cspaceRevokeCdt_swallowed_error_consistent`. `streamingRevokeBFS` returns `.error .resourceExhausted` on fuel exhaustion,
- M-P01: ~~`cspaceRevokeCdt` double-pass revoke fold~~ → **RESOLVED** (v0.16.15): `revokeAndClearRefsState` fuses revoke and clear-refs into a single-pass fold (M2-A),
- M-P02: ~~CDT parent lookup O(E) scan~~ → **RESOLVED** (v0.16.15): `parentMap : Std.HashMap CdtNodeId CdtNodeId` index added to `CapDerivationTree`; `parentOf` now O(1) HashMap lookup; `parentMapConsistent` invariant with runtime check (M2-B),
- M-P03: ~~reply lemma duplication~~ → **RESOLVED** (v0.16.15): reply lemmas extracted as shared infrastructure; new field preservation lemmas for NI proofs (M2-C),
- M-P05: ~~`endpointReply_preserves_capabilityInvariantBundle` proof duplication~~ → **RESOLVED** (v0.16.15): unified via extracted lemmas from M2-C,
- M-D01: ~~IPC capability transfer not modeled~~ → **RESOLVED** (v0.16.17): `CapTransferResult`/`CapTransferSummary` types, `ipcTransferSingleCap`/`ipcUnwrapCaps` operations with preservation proofs, Grant-right gate, CDT `.ipcTransfer` edge tracking, `endpointSendDualWithCaps`/`endpointReceiveDualWithCaps`/`endpointCallWithCaps` wrappers with IPC invariant + `dualQueueSystemInvariant` preservation, `ipcUnwrapCaps_preserves_capabilityInvariantBundle_noGrant`, `ipcUnwrapCaps_preserves_dualQueueSystemInvariant`, `ipcUnwrapCaps_preserves_cnode_at_root`, `ipcTransferSingleCap_receiverRoot_stays_cnode`, `decodeExtraCapAddrs`/`resolveExtraCaps` API wiring,
- M-T03: ~~capability transfer during IPC untested~~ → **RESOLVED** (v0.16.17): 4 test scenarios implemented (SCN-IPC-CAP-TRANSFER-BASIC, SCN-IPC-CAP-TRANSFER-NO-GRANT, SCN-IPC-CAP-TRANSFER-FULL-CNODE, SCN-IPC-CAP-BADGE-COMBINED) in OperationChainSuite and NegativeStateSuite.
- M-P04: ~~`descendantsOf` materializes full set upfront~~ → **RESOLVED** (v0.16.19–v0.17.0): `processRevokeNode` shared per-node step (DRY), `streamingRevokeBFS` BFS loop, `cspaceRevokeCdtStreaming` top-level operation. `processRevokeNode_preserves_capabilityInvariantBundle` shared proof, `streamingRevokeBFS_preserves` induction, `cspaceRevokeCdtStreaming_preserves_capabilityInvariantBundle` composition. 4 test scenarios.

All 14 WS-M findings resolved. See [WS-M workstream plan](../dev_history/audits/AUDIT_v0.16.13_CAPABILITY_SUBSYSTEM_WORKSTREAM_PLAN.md).

**WS-N proof surface** (v0.17.0+, **ACTIVE** — Robin Hood hashing verified implementation):

**N1 delivered proof surface** (v0.17.1, `SeLe4n/Kernel/RobinHood/Core.lean`):
- `idealIndex_lt`/`nextIndex_lt` — index bound proofs via `Nat.mod_lt`
- `RHTable.WF` — 4-conjunct well-formedness predicate (slotsLen, capPos,
  sizeCount, sizeBound)
- `RHTable.empty_wf` — well-formedness of empty table (zero sorry)
- `insertLoop_preserves_len` — array size preservation through insertion loop
  (by induction on fuel)
- `backshiftLoop_preserves_len` — array size preservation through backward-shift
  erasure (by induction on fuel)
- `RHTable.insertNoResize_size_le` — insertion increases size by at most 1
- `RHTable.resize_fold_capacity` — resize output capacity equals `t.capacity * 2`
  (via `Array.foldl_induction`)
- `RHTable.resize_preserves_len` — resize output `slots.size = t.capacity * 2`

**N2 delivered proof surface** (v0.17.2, `SeLe4n/Kernel/RobinHood/Invariant/`):

Invariant definitions (`Invariant/Defs.lean`):
- `distCorrect` — probe distance accuracy for all occupied slots
- `noDupKeys` — key uniqueness across the table
- `robinHoodOrdered` — non-decreasing cluster distances (Robin Hood property)
- `RHTable.invariant` — 4-conjunct bundle: `wf ∧ distCorrect ∧ noDupKeys ∧ robinHoodOrdered`
- `empty_distCorrect`, `empty_noDupKeys`, `empty_robinHoodOrdered`, `empty_invariant`

WF preservation (`Invariant/Preservation.lean`):
- `insertNoResize_preserves_wf`, `insert_preserves_wf`, `resize_preserves_wf`,
  `erase_preserves_wf`
- `mod_succ_eq` — modular arithmetic increment helper
- `dist_step_mod` — displacement step for probe distance
- `countOccupied_le_size` — count bound

distCorrect preservation (`Invariant/Preservation.lean`):
- `insertLoop_preserves_distCorrect` — full induction proof with modular arithmetic
- `insertNoResize_preserves_distCorrect`, `insert_preserves_distCorrect`
- `resize_preserves_distCorrect` — via fold induction

Loop correctness (`Invariant/Preservation.lean`):
- `insertLoop_countOccupied`, `backshiftLoop_countOccupied`
- `findLoop_lt`, `findLoop_correct`

Bundle preservation (`Invariant/Preservation.lean`):
- `insert_preserves_invariant`, `erase_preserves_invariant`,
  `resize_preserves_invariant`

noDupKeys preservation (`Invariant/Preservation.lean`):
- `noDupKeys_after_clear`, `backshiftLoop_preserves_noDupKeys`,
  `erase_preserves_noDupKeys`
- `insertLoop_preserves_noDupKeys` — full fuel induction proving noDupKeys for
  insertLoop result (TPI-D1, zero sorry)

Erase distCorrect preservation (`Invariant/Preservation.lean`):
- `displacement_backward`, `backshiftLoop_preserves_distCorrect`,
  `erase_preserves_distCorrect`

probeChainDominant preservation (`Invariant/Preservation.lean`):
- `insertLoop_preserves_pcd` — full fuel induction proving probeChainDominant
  for insertLoop result (TPI-D2, zero sorry)
- `erase_preserves_probeChainDominant` — relaxedPCD framework: clear creates
  relaxedPCD gap, `backshiftStep_relaxedPCD` advances gap,
  `relaxedPCD_to_pcd_at_termination` recovers full PCD (TPI-D3, zero sorry)
- `insert_preserves_invExt`, `erase_preserves_invExt`, `resize_preserves_invariant`
  — composite bundle preservation for all operations
- `invExtFull` — extended invariant plus load factor bound (V3-A, H-RH-1)
- `invExtFull_implies_size_lt_capacity` — strict size bound from load factor (V3-A)
- `erase_preserves_invExtFull` — erase without redundant `hSize` hypothesis (V3-B)
- `invExtK` — kernel-level bundle: `invExt ∧ size < capacity ∧ 4 ≤ capacity` (V3-B)
- `erase_preserves_invExtK`, `insert_preserves_invExtK`, `filter_preserves_invExtK`,
  `getElem?_erase_ne_K`, `ofList_invExtK`, `empty_invExtK` — kernel wrappers (V3-B)

Helper infrastructure (`Invariant/Preservation.lean`):
- `offset_injective` — injectivity of modular offsets from same base
- `getElem_idx_eq` — array access proof irrelevance
- `carried_key_absent` — key absent if probe reached empty/swap position
- `displacement_backward` — backshift displacement decrement
- `relaxedPCD` — gap-excused PCD invariant for erase proofs

Lookup correctness (`Invariant/Lookup.lean`):
- `getLoop_none_of_absent` — if key absent from all slots, getLoop returns none
- `getLoop_finds_present` — if key present, getLoop returns its value
- `get_after_insert_eq` — insert lookup correctness (TPI-D4, zero sorry)
- `get_after_insert_ne` — insert non-interference (TPI-D5, zero sorry)
- `get_after_erase_eq` — erase lookup correctness (TPI-D6, zero sorry)
- `insertLoop_absent_ne_key`, `insertLoop_output_source`,
  `resize_preserves_key_absence`, `erase_removes_key` — helper lemmas

**invExt bundle restructuring:** Discovery: `robinHoodOrdered` (non-decreasing
dist within clusters) is NOT preserved by backshift-on-erase. The `invExt`
bundle was restructured to use `probeChainDominant` instead, which IS preserved
by all operations. Preservation theorems proved: WF (all ops), distCorrect
(all ops), noDupKeys (all ops), probeChainDominant (all ops). All 6 TPI-D
items complete (D1–D6), ~4,655 LoC, zero sorry/axiom. **WS-N2 COMPLETE.**

**N3 delivered proof surface** (v0.17.3, `SeLe4n/Kernel/RobinHood/Bridge.lean`):

- **Typeclass instances**: `Inhabited (RHTable α β)`, `BEq (RHTable α β)`
- **Bridge lemmas** (10 core): `getElem?_empty`, `getElem?_insert_self/ne`,
  `getElem?_erase_self/ne`, `size_erase_le`, `size_insert_le`,
  `mem_iff_isSome_getElem?`, `getElem?_eq_some_getElem`, `fold_eq_slots_foldl`
- **Filter support**: `RHTable.filter`, `size_filter_le_capacity`, `size_filter_le_size`
- **Convenience**: `RHTable.ofList`, `empty_invExt'`
- **Lookup.lean additions**: `get_after_erase_ne` + 3 helper lemmas
  (`backshiftLoop_output_has_input_key_value`, `backshiftLoop_preserves_entry_presence`,
  `erase_preserves_ne_entry`)

~307 LoC Bridge.lean + ~247 LoC Lookup.lean additions, ~15 proved declarations,
zero sorry/axiom. **WS-N3 COMPLETE.**

**WS-N4 (v0.17.4) — COMPLETED:** Kernel integration (CNode.slots migration):
- `filter_fold_absent_by_pred` — predicate-gated fold induction: if entries
  matching key `k` fail predicate `f`, filter result has `get? k = none`
- `filter_get_pred` — filter lookup implies predicate holds: if
  `(t.filter f).get? k = some v` then `f k v = true`
- `filter_filter_getElem?` — filter idempotence: `((t.filter f).filter f).get? k
  = (t.filter f).get? k` (used for `projectKernelObject_idempotent`)
- `slotsUnique` repurposed from `True` to substantive invariant
  `invExt ∧ size < capacity ∧ 4 ≤ capacity`, propagated via `cspaceSlotUnique`
  through Capability and InformationFlow subsystem theorems
- 20+ files updated, zero sorry/axiom. **WS-N4 COMPLETE.**

**WS-N5 (v0.17.5) — COMPLETED:** Test coverage + documentation:
- 12 standalone Robin Hood test scenarios (`tests/RobinHoodSuite.lean`): empty
  table, insert/get roundtrip, erase, overwrite, multi-key correctness, collision
  handling, Robin Hood swap verification, backward-shift after erase, resize
  trigger at 75% load, post-resize correctness, large-scale stress (200 inserts +
  100 erases), fold/toList utility
- 6 CNode integration regression tests: lookup/insert/remove, revokeTargetLocal
  filter, findFirstEmptySlot, slotCountBounded, CSpace resolution, BEq comparison
- `robin_hood_suite` executable + Tier 2 integration + 18 scenario IDs
- Full documentation sync. **WS-N portfolio COMPLETE** (v0.17.0–v0.17.5).
- See [WS-N workstream plan](../dev_history/audits/AUDIT_v0.17.0_IPC_CAPABILITY_WORKSTREAM_PLAN.md)
  for full proof strategies, expanded pseudocode, and 122-subtask breakdown.

CDT structural invariants (WS-G8):

- `childMapConsistent` — bidirectional consistency between `edges` and `childMap : Std.HashMap CdtNodeId (List CdtNodeId)` parent-indexed index,
- `empty_childMapConsistent` — empty CDT satisfies `childMapConsistent`,
- `addEdge_childMapConsistent` — `addEdge` preserves `childMapConsistent`,
- `removeNode_childMapConsistent` — `removeNode` preserves `childMapConsistent` (R3/R2-C, closing CDT consistency gap),
- `childrenOf` — O(1) HashMap lookup replacing O(E) edge-list scan,
- `descendantsOf` — O(N+E) total via `childrenOf`-backed BFS traversal.
- `descendantsOf_fuel_sufficiency` — **(T4-G, M-CAP-2)** direct children of any
  CDT node are included in the BFS result, providing the foundation for
  revocation completeness. Supported by 8 proven lemmas: `go_cons`, `go_nil`,
  `go_acc_subset`, `go_children_found`, `children_subset`, `go_fuel_mono`,
  `go_head_children_found`, `fuel_bound`.
- `descendantsOf_go_queue_pos_children_found` — **(U4-N)** positional queue
  lemma: if a node sits behind `n` entries in the BFS queue and fuel > `n`,
  every child of that node appears in the result.
- `descendantsOf_go_mem_children_found` — **(U4-N)** queue membership variant:
  if a node is anywhere in the BFS queue and fuel ≥ queue length, every child
  appears in the result.
- `cdtChildMapConsistentCheck` — runtime verification of `childMapConsistent` invariant (v0.12.15), checking both forward (childMap→edges) and backward (edges→childMap) directions.

## 4. IPC invariants (M3)

Module structure:

- `IPC/Operations.lean` (re-export hub) — core endpoint/notification ops (`Operations/Endpoint.lean`) and scheduler preservation lemmas (`Operations/SchedulerLemmas.lean`),
- `IPC/DualQueue.lean` (re-export hub) — dual-queue operations (`DualQueue/Core.lean`: queue links, PopHead/Enqueue/RemoveDual, SendDual, ReceiveDual, Call, Reply, ReplyRecv) and transport lemmas (`DualQueue/Transport.lean`),
- `IPC/Invariant.lean` (re-export hub) — definitions (`Invariant/Defs.lean`), endpoint preservation (`Invariant/EndpointPreservation.lean`), call/replyRecv preservation (`Invariant/CallReplyRecv.lean`), notification preservation (`Invariant/NotificationPreservation.lean`), structural invariants and composition (`Invariant/Structural.lean`).

### 4.1 Dual-queue structural invariant (WS-H5)

`dualQueueSystemInvariant st` — system-wide structural invariant for intrusive dual-queue endpoints:

- `dualQueueEndpointWellFormed` — per-endpoint: both `sendQ` and `receiveQ` satisfy `intrusiveQueueWellFormed` (head/tail emptiness iff, head.prev=none, tail.next=none),
- `tcbQueueLinkIntegrity` — per-TCB: forward link consistency (`a.next=b → b.prev=a`) and reverse link consistency (`b.prev=a → a.next=b`).

Primitive preservation:

- `endpointQueuePopHead_preserves_dualQueueSystemInvariant`,
- `endpointQueueEnqueue_preserves_dualQueueSystemInvariant`.

Frame lemmas (non-queue-mutating operations):

- `ensureRunnable_preserves_dualQueueSystemInvariant`, `removeRunnable_preserves_dualQueueSystemInvariant`,
- `storeObject_tcb_preserves_dualQueueSystemInvariant`, `storeObject_endpoint_preserves_dualQueueSystemInvariant`,
- `storeTcbIpcState_preserves_dualQueueSystemInvariant`, `storeTcbIpcStateAndMessage_preserves_dualQueueSystemInvariant`, `storeTcbPendingMessage_preserves_dualQueueSystemInvariant`.

Composite preservation (all 6 compound IPC operations):

- `endpointSendDual_preserves_dualQueueSystemInvariant`,
- `endpointReceiveDual_preserves_dualQueueSystemInvariant`,
- `endpointCall_preserves_dualQueueSystemInvariant`,
- `endpointReply_preserves_dualQueueSystemInvariant`,
- ~~`endpointAwaitReceive_preserves_dualQueueSystemInvariant`~~ (removed in WS-H12a),
- `endpointReplyRecv_preserves_dualQueueSystemInvariant`,
- `ipcUnwrapCaps_preserves_dualQueueSystemInvariant` (M3-E4: CNode precondition, composes per-step ep/tcb preservation),
- `endpointSendDualWithCaps_preserves_dualQueueSystemInvariant` (M3-E4: composes send + ipcUnwrapCaps),
- `endpointReceiveDualWithCaps_preserves_dualQueueSystemInvariant` (M3-E4: composes receive + ipcUnwrapCaps).

Helper lemmas: `storeTcbQueueLinks_noprevnext_preserves_linkInteg`, `storeTcbQueueLinks_append_tail_preserves_linkInteg`, `storeTcbQueueLinks_endpoint_backward`.

Bundle level:

- `ipcInvariantFull` (9-conjunct: `ipcInvariant ∧ dualQueueSystemInvariant ∧ allPendingMessagesBounded ∧ badgeWellFormed ∧ waitingThreadsPendingMessageNone ∧ endpointQueueNoDup ∧ ipcStateQueueMembershipConsistent ∧ queueNextBlockingConsistent ∧ queueHeadBlockedConsistent`, WS-H12c + WS-H12d + WS-F5 + V3-G6 + V3-K + V3-J + V3-J-cross)
- `badgeWellFormed` (WS-F5/D1d): `notificationBadgesWellFormed ∧ capabilityBadgesWellFormed` — all badge values in notification pending badges and capability slots satisfy word-boundedness

Cross-subsystem composition (WS-H12e + WS-F5):

- `coreIpcInvariantBundle` — upgraded from `ipcInvariant` to `ipcInvariantFull` (9-conjunct), closing the gap where `dualQueueSystemInvariant`, `allPendingMessagesBounded`, `badgeWellFormed`, `waitingThreadsPendingMessageNone`, `endpointQueueNoDup`, `ipcStateQueueMembershipConsistent`, `queueNextBlockingConsistent`, and `queueHeadBlockedConsistent` were defined but not composed into the cross-subsystem proof surface
- Backward-compatible extraction theorems: `coreIpcInvariantBundle_to_ipcInvariant`, `coreIpcInvariantBundle_to_dualQueueSystemInvariant`, `coreIpcInvariantBundle_to_allPendingMessagesBounded`, `coreIpcInvariantBundle_to_badgeWellFormed`, `coreIpcInvariantBundle_to_waitingThreadsPendingMessageNone`, `coreIpcInvariantBundle_to_endpointQueueNoDup`, `coreIpcInvariantBundle_to_ipcStateQueueMembershipConsistent`, `coreIpcInvariantBundle_to_queueNextBlockingConsistent`, `coreIpcInvariantBundle_to_queueHeadBlockedConsistent`

Component level:

- `ipcInvariant` — notification queue well-formedness across object store,
- `dualQueueSystemInvariant` — per-endpoint dual-queue well-formedness + system-wide TCB link integrity,
- `allPendingMessagesBounded` — all pending IPC messages satisfy payload bounds.

V3 proof chain hardening predicates **(v0.22.2)**:

- `waitingThreadsPendingMessageNone` — **(V3-G, M-PRF-5)** threads in blocked receiver states (`blockedOnReceive`, `blockedOnNotification`) have `pendingMessage = none`. Note: `blockedOnSend` and `blockedOnCall` are excluded because these states legitimately carry outgoing messages in `pendingMessage`. **Integrated as 5th conjunct of `ipcInvariantFull` (V3-G6).** Seven machine-checked primitive preservation lemmas (`removeRunnable`, `ensureRunnable`, `storeObject_nonTcb`, `storeTcbIpcState`, `storeTcbIpcStateAndMessage`, `storeTcbQueueLinks`, `storeTcbPendingMessage`) in `Structural.lean`. Full operation-level machine-checked proofs: `notificationWait_preserves_*`, `notificationSignal_preserves_*`, `endpointSendDual_preserves_*`, `endpointReceiveDual_preserves_*`, `endpointCall_preserves_*`, `endpointReply_preserves_*`, `endpointReplyRecv_preserves_*`. `notificationWake_pendingMessage_was_none` proves blocking-state implies `pendingMessage = none`. Two backward lemmas added: `storeTcbQueueLinks_tcb_pendingMessage_backward` (Core.lean) and `endpointQueueEnqueue_tcb_pendingMessage_backward` (Transport.lean).
- `ipcStateQueueMembershipConsistent` — **(V3-J, L-IPC-3)** bidirectional consistency: threads claiming blocked-on-endpoint state are reachable from the corresponding endpoint queue (via `head` or `queueNext` linkage). Predicate definition in `Defs.lean`. Primitive frame lemmas in `QueueMembership.lean`: `storeObject_non_ep_non_tcb_preserves_ipcStateQueueMembershipConsistent`, scheduler frame helpers (`ensureRunnable`/`removeRunnable`), and `ipcStateQueueMembershipConsistent_of_objects_eq`. TCB-store primitives: `storeTcbIpcStateAndMessage_preserves_*`, `storeTcbIpcState_preserves_*` (with non-blocking precondition), `storeTcbIpcStateAndMessage_fromTcb_preserves_*`. Per-operation proofs: `notificationSignal_preserves_*`, `notificationWait_preserves_*`, `endpointReply_preserves_*`. **Integrated as 7th conjunct of `ipcInvariantFull`.**
- `endpointQueueNoDup` — **(V3-K, L-LIFE-1)** intrusive queue no-cycle and disjointness: no thread's `queueNext` points to itself, and `sendQ.head ≠ receiveQ.head` when both are non-empty. Predicate definition in `Defs.lean`. Primitive frame lemmas in `QueueNoDup.lean`: `storeObject_non_ep_non_tcb_preserves_endpointQueueNoDup`, `storeTcbQueueLinks_preserves_endpointQueueNoDup`, `storeObject_endpoint_preserves_endpointQueueNoDup`. TCB-store primitives: `storeTcbIpcStateAndMessage_preserves_*`, `storeTcbIpcState_preserves_*`, `storeTcbPendingMessage_preserves_*`. Per-operation proofs: `notificationSignal_preserves_*`, `notificationWait_preserves_*`, `endpointReply_preserves_*`. **Integrated as 6th conjunct of `ipcInvariantFull`.**

Preservation shape:

- transition-level `endpointSendDual_preserves_ipcInvariant`, etc.
- WS-F1 dual-queue: `endpointSendDual_preserves_ipcInvariant`, `endpointReceiveDual_preserves_ipcInvariant`, `endpointQueueRemoveDual_preserves_ipcInvariant` (TPI-D08).
- WS-F1 compound: `endpointCall_preserves_ipcInvariant`, `endpointReplyRecv_preserves_ipcInvariant`, `endpointReply_preserves_ipcSchedulerContractPredicates` (TPI-D09).
- WS-F4 notification: `notificationSignal_preserves_ipcInvariant`, `notificationSignal_preserves_schedulerInvariantBundle`, `notificationWait_preserves_ipcInvariant`, `notificationWait_preserves_schedulerInvariantBundle` (F-12).
- WS-F4 notification contract predicates: `notificationSignal_preserves_ipcSchedulerContractPredicates`, `notificationWait_preserves_ipcSchedulerContractPredicates` (M3.5 gap closure).
- WS-H5 dual-queue structural invariant: 13 `*_preserves_dualQueueSystemInvariant` theorems covering `endpointQueuePopHead`, `endpointQueueEnqueue`, `endpointSendDual`, `endpointReceiveDual`, `endpointCall`, `endpointReply`, `endpointReplyRecv`, plus 5 state-only ops (`ensureRunnable`, `removeRunnable`, `storeTcbIpcState`, `storeTcbIpcStateAndMessage`, `storeTcbPendingMessage`).
- WS-L1 IPC performance optimization (v0.16.9): `endpointQueuePopHead` returns pre-dequeue TCB in 3-tuple `(ThreadId × TCB × SystemState)`, eliminating redundant lookups. `storeTcbIpcStateAndMessage_fromTcb` and `storeTcbIpcState_fromTcb` bypass internal lookup with equivalence theorems (`storeTcbIpcStateAndMessage_fromTcb_eq`, `storeTcbIpcState_fromTcb_eq`). `lookupTcb_preserved_by_storeObject_notification` proves cross-store TCB stability. 4 redundant O(log n) lookups eliminated; zero new preservation lemmas needed.
- R3-B/M-18 `ipcInvariantFull` internalization (v0.18.2): Notification operations (`notificationSignal`, `notificationWait`) and `endpointReply` now have **self-contained** `ipcInvariantFull` preservation theorems with zero externalized hypotheses. New infrastructure: `storeObject_notification_preserves_dualQueueSystemInvariant`, `notificationSignal_preserves_dualQueueSystemInvariant`, `notificationWait_preserves_dualQueueSystemInvariant`, `endpointReply_preserves_badgeWellFormed`.
- U4-K `ipcInvariantFull` internalization for dual-queue ops (v0.21.3): `endpointSendDual`, `endpointReceiveDual`, `endpointCall`, `endpointReplyRecv` now have self-contained `ipcInvariantFull` preservation, deriving `allPendingMessagesBounded` and `badgeWellFormed` internally. New primitives: `storeTcbQueueLinks_preserves_badgeWellFormed`, `storeTcbPendingMessage_preserves_badgeWellFormed`, `storeObject_endpoint_preserves_badgeWellFormed`. 4 queue-level + 8 endpoint-level composed theorems.
- R3-A/M-16 notification badge delivery (v0.18.2): `notificationSignal` wake path now delivers the signaled badge to the woken thread via `storeTcbIpcStateAndMessage` with `{ IpcMessage.empty with badge := some badge }`. All preservation proofs updated to use `storeTcbIpcStateAndMessage` instead of `storeTcbIpcState`.
- R3-C/M-19 `notificationWaiterConsistent` preservation: `storeObject_notification_preserves_notificationWaiterConsistent` (subset waiting list), `storeObject_nonNotification_preserves_notificationWaiterConsistent` (frame for TCB stores), `storeTcbIpcStateAndMessage_preserves_notificationWaiterConsistent` (TCB ipc state change with wait-list exclusion), `notificationSignal_preserves_notificationWaiterConsistent` (wake path + merge path), `frame_preserves_notificationWaiterConsistent` (general frame lemma for endpoint operations), `endpointReply_preserves_notificationWaiterConsistent` (reply path).
- R3-E/L-08 linter: `set_option linter.all false` removed from `Structural.lean`; replaced with targeted `set_option linter.unusedVariables false`.

### 4.2 IPC message payload bounds (WS-H12d)

`IpcMessage` registers and caps bounded to `Array` with `maxMessageRegisters` (120) and `maxExtraCaps` (3), matching seL4's `seL4_MsgMaxLength` and `seL4_MsgMaxExtraCaps`.

Predicate level:

- `IpcMessage.bounded` — `registers.size ≤ maxMessageRegisters ∧ caps.size ≤ maxExtraCaps`,
- `IpcMessage.checkBounds` — decidable runtime check,
- `checkBounds_iff_bounded` — decidability bridge theorem,
- `empty_bounded` — base case theorem.

System invariant:

- `allPendingMessagesBounded` — all pending messages in TCBs satisfy `bounded`.

Bounds enforcement (at all 4 send boundaries):

- `endpointSendDual`, `endpointCall`, `endpointReply`, `endpointReplyRecv` — early-exit with `ipcMessageTooLarge` / `ipcMessageTooManyCaps` errors.

Message-bounded theorems:

- `endpointSendDual_message_bounded`, `endpointCall_message_bounded`, `endpointReply_message_bounded`, `endpointReplyRecv_message_bounded` — any successfully sent message satisfies `bounded`.

Information-flow:

- `endpointSendDualChecked` — bounds checks precede flow checks; `enforcement_sufficiency_endpointSendDual` expanded to 4-way disjunction.
- **X3-A (v0.22.20)**: `serviceOrchestrationOutsideNiBoundary` — formal exclusion boundary documenting that service orchestration internals are outside NI scope. `serviceRegistryAffectsProjection` predicate.
- **X3-B (v0.22.20, extended Y2-E v0.22.24)**: `enforcementBridge_to_NonInterferenceStep` — unified 11-conjunct bridge theorem connecting enforcement soundness (all 11 checked wrappers) to NI composition framework. Y2-E added `endpointCallChecked`, `endpointReplyChecked`, `cspaceMintChecked`, `notificationWaitChecked`, `endpointReplyRecvChecked`.
- **X3-E (v0.22.20)**: `integrityFlowsTo_prevents_escalation` — privilege escalation prevention theorem for the non-BIBA integrity direction. `securityFlowsTo_prevents_label_escalation` — label-level denial.

## 5. IPC-scheduler coherence (M3.5)

Component level:

- runnable threads should be IPC-ready,
- blocked-on-send threads should not remain runnable,
- blocked-on-receive threads should not remain runnable,
- blocked-on-call threads should not remain runnable (WS-H1),
- blocked-on-reply threads should not remain runnable (WS-H1).

Bundle level:

- `ipcSchedulerContractPredicates` (6 conjuncts: ready, send, receive, call, reply, notification; WS-F6/D2)
- `ipcSchedulerCoherenceComponent`
- `ipcSchedulerCouplingInvariantBundle` (WS-H12e: extended from 2 to 4 conjuncts — `coreIpcInvariantBundle ∧ ipcSchedulerCoherenceComponent ∧ contextMatchesCurrent ∧ currentThreadDequeueCoherent`)

Preservation shape:

- local component preservation theorem per transition,
- composed contract preservation theorem per transition,
- bundle preservation theorem per transition.

## 6. Naming conventions and why they matter

Preferred shape:

- `<transition>_preserves_<componentOrBundle>`

Why:

- searchable theorem entrypoints,
- stable doc/test anchors,
- predictable maintainability under milestone growth.

## 7. M4 lifecycle invariant layering (M4-A complete, M4-B WS-B complete)

Current M4-A lifecycle invariant structure now follows the existing layered style:

1. identity/aliasing components (`lifecycleIdentityTypeExact`, `lifecycleIdentityNoTypeAliasConflict`),
2. identity bundle (`lifecycleIdentityAliasingInvariant`),
3. capability-reference components (`lifecycleCapabilityRefExact`, `lifecycleCapabilityRefObjectTargetBacked`),
4. capability-reference bundle (`lifecycleCapabilityReferenceInvariant`),
5. composed lifecycle bundle (`lifecycleInvariantBundle`),
6. stale-reference hardening family (`lifecycleStaleReferenceExclusionInvariant`),
7. lifecycle+stale bridge (`lifecycleIdentityStaleReferenceInvariant`).

This explicit split now includes transition-local lifecycle helper lemmas in `Lifecycle/Operations`,
local and composed lifecycle preservation entrypoints (`lifecycleRetypeObject_preserves_lifecycleInvariantBundle`,
`lifecycleRetypeObject_preserves_lifecycleStaleReferenceExclusionInvariant`,
`lifecycleRetypeObject_preserves_lifecycleIdentityStaleReferenceInvariant`,
`lifecycleRetypeObject_preserves_coreIpcInvariantBundle`, and
`lifecycleRetypeObject_preserves_lifecycleCompositionInvariantBundle`), and fixture-backed executable trace evidence
for unauthorized/illegal-state/success lifecycle retype outcomes plus composed lifecycle+capability behavior.

## 8. M5 policy-surface layering (WS-M5-C complete) — seLe4n extension

> **Note:** The Service subsystem is a seLe4n-specific extension with no
> analogue in real seL4. See `Service/Operations.lean` for design rationale.

Policy surface entrypoints now live in `SeLe4n/Kernel/Service/Invariant.lean` and are explicitly
kept mutation-free:

- reusable components: `policyBackingObjectTyped`, `policyOwnerAuthorityRefRecorded`,
  `policyOwnerAuthoritySlotPresent`,
- bundle entrypoint: `servicePolicySurfaceInvariant`,
- bridge lemmas: lifecycle/capability assumptions can discharge policy authority obligations,
- composed bridge: `servicePolicySurfaceInvariant_of_lifecycleInvariant` lifts lifecycle contracts
  (plus backing-object existence assumptions) into the service policy bundle,
- check-vs-mutation separation: policy-denial theorem surfaces remain explicit and deterministic.

## 9. M5 proof package layering (WS-M5-D complete; updated WS-Q1)

*(WS-Q1: Service lifecycle transitions (`serviceStart`/`serviceStop`/`serviceRestart`) removed.
The M5 policy surface now covers registry operations only.)*

Proof-package entrypoints extend the M5 policy surface to registry preservation:

- composed bundle entrypoint: `serviceLifecycleCapabilityInvariantBundle`,
- registry preservation:
  - `storeServiceState_preserves_servicePolicySurfaceInvariant`,
  - `storeServiceState_preserves_lifecycleInvariantBundle`,
  - `storeServiceState_preserves_capabilityInvariantBundle`,
  - `serviceRegisterDependency_preserves_serviceGraphInvariant`.

## 9.1 R4 cross-subsystem invariant completion (WS-R/R4 complete)

*(R4: Lifecycle & Service Coherence cross-subsystem preservation)*

Cross-subsystem consistency between lifecycle, service, and IPC subsystems:

- **Lifecycle/IPC coupling** (`cleanupTcbReferences` extensions):
  - `removeFromAllEndpointQueues` — removes TCB from all endpoint sender/receiver queues
  - `removeFromAllNotificationWaitLists` — removes TCB from all notification wait lists
  - `removeThreadFromQueue` advances head/tail to TCB's `queueNext`/`queuePrev` (preserves queue accessibility for remaining threads, instead of clearing to `none`)
  - Existing scheduler preservation theorems updated for new intermediate states

- **Lifecycle/Service coupling** (`cleanupEndpointServiceRegistrations`):
  - `cleanupEndpointServiceRegistrations` — revokes all service registrations backing a retyped endpoint
  - `registryEndpointValid` preservation through retype
  - Integrated into `lifecyclePreRetypeCleanup` in `Lifecycle/Operations.lean`

- **Service operation hardening**:
  - `registerService` validates target exists and is an endpoint BEFORE checking Write right authority (defense-in-depth ordering prevents authority probing on invalid targets)
  - Endpoint object type verification — target must be an actual endpoint (L-09)

- **Service revocation completeness**:
  - `revokeService` cleans dependency graph via `removeDependenciesOf`
  - Erases service entry and filters from all other entries' dependency lists

- **Cross-subsystem invariant bundle** (`CrossSubsystem.lean`):
  - `noStaleEndpointQueueReferences` — every endpoint queue head/tail and interior member has a live TCB (T5-I: extended from head/tail-only to full `collectQueueMembers` traversal)
  - `noStaleNotificationWaitReferences` — every ThreadId in notification `waitingThreads` has a live TCB (T5-H)
  - `registryDependencyConsistent` — every dependency edge references a registered service
  - `crossSubsystemInvariant` — composed 5-predicate bundle added to `proofLayerInvariantBundle` (T5-J: extended from 3-tuple, U4-G: serviceGraphInvariant added)
  - **X3-C/X3-D (v0.22.20)**: 10 predicate interaction pairs fully covered:
    - 6 disjoint pairs with field-disjointness witnesses (V6-A3)
    - 4 sharing pairs with frame theorems (`sharingPair1_objects_frame`, `sharingPair23_objects_frame`, `sharingPair4_services_frame`)
    - `crossSubsystemInvariant_composition_complete` — 10-conjunct tightness witness
    - `crossSubsystemInvariant_objects_frame` / `crossSubsystemInvariant_services_change` — composite preservation

## 9.2 S5-G/H: Page-alignment check for VSpace-bound retype (S5 complete)

*(S5-G/S5-H: Page-alignment enforcement in `retypeFromUntyped` for VSpace roots and CNodes)*

`retypeFromUntyped` now enforces page-aligned allocation bases for object types
that require it:

- **`requiresPageAlignment`** — predicate identifying `KernelObjectType` values
  requiring page-aligned allocation (VSpace roots, CNodes).
- **`allocationBasePageAligned`** — checks 4 KiB alignment of the allocation base.
- **`allocationMisaligned`** — new `KernelError` variant returned when the
  alignment check fails.
- **Lifecycle invariant preservation**: all existing lifecycle preservation proofs
  updated to account for the new error branch (trivially preserving — error returns
  unchanged state).

## 10. VSpace proof completion (WS-D3 / F-08 / TPI-001 CLOSED X1-K; WS-G3 / F-P06; WS-G6 / F-P05 updated)

VSpace invariant bundle preservation is now proven for both success and error paths:

- **Error-path preservation** (trivially true, error returns unchanged state):
  - `vspaceMapPage_error_asidNotBound_preserves_vspaceInvariantBundle`
  - `vspaceUnmapPage_error_translationFault_preserves_vspaceInvariantBundle`
- **Success-path preservation** (substantive — prove invariant preservation over changed state):
  - `vspaceMapPage_success_preserves_vspaceInvariantBundle`
  - `vspaceUnmapPage_success_preserves_vspaceInvariantBundle`
- **Round-trip / functional-correctness theorems** (TPI-001 closure; WS-G6: re-proved with HashMap bridge lemmas):
  - `vspaceLookup_after_map`: map then lookup yields mapped address
  - `vspaceLookup_map_other`: map at vaddr doesn't affect lookup at different vaddr'
  - `vspaceLookup_after_unmap`: after unmap, lookup fails with translationFault
  - `vspaceLookup_unmap_other`: unmap at vaddr doesn't affect lookup at different vaddr'

Data structure (WS-G6 / F-P05):

- `VSpaceRoot.mappings : RHTable VAddr (PAddr × PagePermissions)` — O(1) amortized lookup/insert/erase (WS-G6, enriched by WS-H11 with per-page permissions). Robin Hood key uniqueness makes `noVirtualOverlap` trivially true. `BEq VSpaceRoot` uses size + fold containment (order-independent equality). `VSpaceRoot.beq_refl` (Y2-D+, v0.22.25): machine-checked BEq reflexivity under `invExt`. `LawfulBEq VSpaceRoot` is provably impossible (non-canonical Robin Hood layouts); reflexivity is the strongest achievable result (L-FND-3 closed).

VSpace invariant bundle structure (7-conjunct, WS-G3/WS-H11/WS-F6/U2-C):
- `vspaceAsidRootsUnique` — no two VSpaceRoot objects share the same ASID
- `vspaceRootNonOverlap` — VSpaceRoot mapping ranges do not overlap (trivially true with HashMap, WS-G6)
- `asidTableConsistent` — bidirectional soundness + completeness between `asidTable` HashMap and VSpaceRoot objects
- `wxExclusiveInvariant` — no mapping is both writable and executable (W^X, WS-H11)
- `boundedAddressTranslation` — all translated physical addresses are within `[0, bound)` (WS-H11)
- `vspaceCrossAsidIsolation` — distinct VSpaceRoot objects have distinct ASIDs (WS-F6/D6)
- `canonicalAddressInvariant` — all virtual addresses in mappings are canonical (U2-C)

Supporting infrastructure in `VSpace.lean`:
- `resolveAsidRoot_some_implies_obj` — extracts asidTable + object-store facts from successful ASID resolution (WS-G3: O(1) HashMap lookup)
- `resolveAsidRoot_of_asidTable_entry` — characterization lemma enabling round-trip proofs (WS-G3: no uniqueness/objectIndex needed)

TLB/cache maintenance model (`TlbModel.lean`, WS-H11/H-10):
- `TlbEntry` — cached `(ASID, VAddr, PAddr, PagePermissions)` translation entry
- `TlbState` — abstract collection of cached entries (list-backed)
- `adapterFlushTlb` — full TLB invalidation (ARM64 `TLBI ALLE1`)
- `adapterFlushTlbByAsid` — per-ASID invalidation (ARM64 `TLBI ASIDE1`)
- `adapterFlushTlbByVAddr` — per-(ASID,VAddr) invalidation (ARM64 `TLBI VAE1`)
- `tlbConsistent` — invariant: all TLB entries match current page tables
- R7-A: `TlbState` integrated into `SystemState`; `tlbConsistent` added to `proofLayerInvariantBundle`
- `vspaceMapPageWithFlush`, `vspaceUnmapPageWithFlush` — composed page-table + TLB-flush operations
- 13 TLB theorems: `tlbConsistent_empty`, `adapterFlushTlb_restores_tlbConsistent`, `adapterFlushTlbByAsid_preserves_tlbConsistent`, `vspaceMapPage_then_flush_preserves_tlbConsistent`, `vspaceUnmapPage_then_flush_preserves_tlbConsistent`, `adapterFlushTlbByAsid_removes_matching`, `adapterFlushTlbByAsid_preserves_other`, `adapterFlushTlbByVAddr_preserves_tlbConsistent`, `adapterFlushTlbByVAddr_removes_matching`, `cross_asid_tlb_isolation`, `vspaceMapPageWithFlush_preserves_tlbConsistent`, `vspaceUnmapPageWithFlush_preserves_tlbConsistent`, `tlbConsistent_of_objects_eq`

## 11. Badge-override safety (WS-D3 / F-06 / TPI-D04 complete)

Badge-override safety in `cspaceMint` is now fully proven:

- `mintDerivedCap_rights_attenuated_with_badge_override` — rights attenuation holds regardless of badge
- `mintDerivedCap_target_preserved_with_badge_override` — target identity preserved regardless of badge
- `cspaceMint_badge_override_safe` — composed kernel-operation-level safety witness

The core insight: `mintDerivedCap` checks `rightsSubset` and sets `target := parent.target`
unconditionally — the `badge` parameter only affects the `.badge` field of the child capability,
which is notification-signaling metadata, not authority scope.

## 12. Proof classification docstrings (WS-D3 / F-16 complete)

All seven `Invariant.lean` files now contain module-level `/-! ... -/` docstrings that classify
every theorem into one of these categories:

| Category | Assurance level |
|---|---|
| **Substantive preservation** | High — proves invariant preservation over changed state |
| **Error-case preservation** | Low — trivially true (unchanged state) |
| **Non-interference** | Critical — proves high-domain operations don't leak to low observers |
| **Badge-safety** | High — proves badge override cannot escalate privilege |
| **Structural / bridge** | High — proves decomposition/composition relationships |
| **Round-trip / functional-correctness** | High — proves semantic contracts between operations |

## 13. Kernel design hardening (WS-D4 complete)

### F-07: Service dependency cycle detection

Service dependency registration now includes DFS-based cycle detection (WS-G8: migrated from BFS with `List` visited to DFS with `Std.HashSet` visited for O(n+e) complexity):

- `serviceBfsFuel` — fuel computation for bounded DFS (objectIndex.length + 256)
- `serviceHasPathTo` — bounded DFS reachability check in the dependency graph (WS-G8: `Std.HashSet ServiceId` visited set)
- `serviceRegisterDependency` — deterministic registration with self-loop, idempotency, and cycle checks
- `serviceRegisterDependency_error_self_loop` — self-dependency rejection theorem (no `sorry`)
- `serviceDependencyAcyclic` — acyclicity invariant definition
- `serviceRegisterDependency_preserves_acyclicity` — preservation theorem (no `sorry`; BFS bridge `bfs_complete_for_nontrivialPath` formally proven — TPI-D07-BRIDGE resolved, see §14)

### F-11: Service graph invariant preservation (updated WS-Q1)

*(WS-Q1: `serviceRestart` partial-failure semantics removed — lifecycle transitions eliminated.
Replaced by registry graph invariant preservation.)*

- `serviceRegisterDependency_preserves_serviceGraphInvariant` — dependency registration preserves acyclicity + bounded count
- `serviceRegisterDependency_preserves_acyclicity` — acyclicity preserved through new edge insertion

### F-12: Double-wait prevention and uniqueness invariant

Notification waiting lists now enforce uniqueness:

- `notificationWait` — checks `waiter ∈ ntfn.waitingThreads` before appending; returns `alreadyWaiting` on duplicate
- `notificationWait_error_alreadyWaiting` — rejection theorem (no `sorry`)
- `notificationWait_badge_path_notification` — decomposition: badge-consumed path post-state notification
- `notificationWait_wait_path_notification` — decomposition: wait path post-state notification
- `uniqueWaiters` — invariant: notification waiting list has no duplicates (`List.Nodup`)
- `notificationWait_preserves_uniqueWaiters` — preservation theorem (no `sorry`)

Supporting infrastructure:

- `storeTcbIpcState_preserves_objects_ne` — storeTcbIpcState preserves objects at other IDs
- `storeTcbIpcState_preserves_notification` — storeTcbIpcState preserves notification objects
- `removeRunnable_preserves_objects` — removeRunnable preserves all objects

## 14. TPI-D07 acyclicity proof infrastructure (Risk 0 resolved, TPI-D07 closed, TPI-D07-BRIDGE resolved)

The vacuous BFS-based acyclicity invariant (Risk 0) has been resolved via Strategy B:
the invariant definition was corrected and a genuine 4-layer proof infrastructure was
implemented in `SeLe4n/Kernel/Service/Invariant.lean`.

**Problem:** The original `serviceDependencyAcyclic` was defined as
`∀ sid, ¬ serviceHasPathTo st sid sid fuel = true`, but `serviceHasPathTo` returns `true`
immediately for self-queries (BFS starts with `[src]` in frontier, immediately finds
`src = target`), making the invariant equivalent to `False` — trivially unsatisfiable.

**Resolution:** Replaced with declarative acyclicity using `serviceNontrivialPath`
(an inductive `Prop`-valued path relation of length ≥ 1).

Implemented proof layers:

- **Layer 0 (Definitions):** `serviceEdge`, `serviceReachable`, `serviceNontrivialPath`,
  revised `serviceDependencyAcyclic` (declarative, non-vacuous)
- **Layer 1 (Structural lemmas):** `serviceReachable_trans`, `serviceReachable_of_edge`,
  `serviceReachable_of_nontrivialPath`, `serviceNontrivialPath_of_edge_reachable`,
  `serviceNontrivialPath_of_reachable_ne`, `serviceNontrivialPath_trans`,
  `serviceNontrivialPath_step_right`. Frame lemmas: `serviceEdge_storeServiceState_ne`,
  `serviceEdge_storeServiceState_updated`, `serviceEdge_post_insert`
- **Layer 2 (BFS bridge):** `bfs_complete_for_nontrivialPath` — BFS completeness
  bridge connecting declarative paths to the executable BFS check. Formally proven
  (TPI-D07-BRIDGE resolved); no `sorry` remains
- **Layer 3 (Path decomposition):** `nontrivialPath_post_insert_cases` — decomposes
  any post-insertion nontrivial path into either a pre-state path or a composition
  using the new edge with pre-state reachability
- **Layer 4 (Closure):** `serviceRegisterDependency_preserves_acyclicity` — genuine
  preservation proof via post-insertion path decomposition and contradiction with the
  BFS cycle-detection check. The main theorem is sorry-free

**Sub-obligation resolved (TPI-D07-BRIDGE):** The `bfs_complete_for_nontrivialPath`
lemma has been formally proven, establishing that the BFS with `serviceBfsFuel` fuel
is complete enough to detect all nontrivial paths between distinct services. No
`sorry` obligations remain in the TPI-D07 proof infrastructure.

### 14.1 BFS completeness proof (TPI-D07-BRIDGE completed)

The formal proof eliminating the `bfs_complete_for_nontrivialPath` sorry has been
completed following the M2 milestone roadmap
([`M2_BFS_SOUNDNESS.md`](../dev_history/audits/execution_plans/milestones/M2_BFS_SOUNDNESS.md))
and four sub-documents (M2A–M2D).

**Proof decomposition:**

1. **Equational theory ([M2A](../dev_history/audits/execution_plans/milestones/M2A_EQUATIONAL_THEORY.md)):**
   A `lookupDeps` helper bridges the executable BFS dependency lookup to the
   declarative `serviceEdge` relation (`serviceEdge_iff_lookupDeps`). Five BFS
   unfolding lemmas (EQ1-EQ5) provide rewrite rules for each branch of the `go`
   function.

2. **Completeness invariant ([M2B](../dev_history/audits/execution_plans/milestones/M2B_COMPLETENESS_INVARIANT.md)):**
   A named `bfsClosed` definition captures the visited-set closure property. Four
   lemmas (CB1-CB4) establish the invariant initially, preserve it across skip and
   expansion steps, and prove the critical boundary lemma: if a visited node reaches
   target and target is not visited, some frontier node also reaches target.

3. **Fuel adequacy ([M2C](../dev_history/audits/execution_plans/milestones/M2C_FUEL_ADEQUACY.md)):**
   A `serviceCountBounded` precondition bounds the BFS universe by `serviceBfsFuel st`
   (Approach A). `serviceCountBounded_preserved_by_registerDependency` proves the
   precondition is maintained across dependency registration.
   **X4-E:** `serviceBfsFuel_sufficient` and `serviceBfsFuel_sound` provide
   bi-directional correctness: nontrivial paths are detected (sufficient) and
   `false` results are genuine (sound). `serviceBfsFuel_has_margin` proves
   the `+ 256` margin is strictly conservative.

4. **Core completeness ([M2D](../dev_history/audits/execution_plans/milestones/M2D_COMPLETENESS_PROOF.md)):**
   `go_complete` (CP1) carries the four-part invariant (I1: target not visited,
   I2: closure, I3: frontier witness, I4: fuel adequate) through strong induction
   on fuel with structural induction on the frontier list. The sorry is eliminated.

**Implemented scope:** 17 private lemmas + 4 definitions + 3 public theorems.

Frozen operational files (M0 semantics freeze):

| File | SHA-256 |
|---|---|
| `Operations.lean` | `a61fa6c1...42ffff44` |
| `State.lean` | `6f6f87d8...d1cbc1e6` |
| `Object.lean` | `db228ed6...14594f32` |
| `Prelude.lean` | `bffc93fe...d47b30fe` |

Full execution plan: [`docs/dev_history/audits/execution_plans/00_INDEX.md`](../dev_history/audits/execution_plans/00_INDEX.md)

## 15. Information-flow layering (WS-B7 baseline + WS-D2 enforcement and non-interference)

### Readers' guide: 3-layer IF architecture (WS-L5-A)

The information-flow subsystem is organized in three architectural layers:

1. **Policy layer** (`InformationFlow/Policy.lean`): Defines security labels
   (confidentiality + integrity lattice), domain flow policies, observer
   projection, and the `lowEquivalent` relation. This is the *specification* —
   it says which information flows are allowed.

2. **Enforcement layer** (`InformationFlow/Enforcement/Wrappers.lean`,
   `Enforcement/Soundness.lean`): Implements policy-gated wrappers (e.g.,
   `endpointSendDualChecked`) that check flow authorization before delegating
   to the underlying operation. Soundness theorems prove that if the checked
   wrapper succeeds, the underlying operation was authorized.

3. **Invariant layer** (`InformationFlow/Invariant/Operations.lean`,
   `Invariant/Composition.lean`, `Invariant/Helpers.lean`): Contains
   per-operation non-interference (NI) proofs showing that kernel transitions
   preserve `lowEquivalent` for unobservable state changes. The composition
   layer (`composedNonInterference_trace`) chains single-step NI proofs into
   trace-level non-interference using the `NonInterferenceStep` inductive type
   (34 constructors as of v0.16.8).

### IF-M1 baseline (WS-B7 complete)

Policy and projection primitives:

- policy lattice/labels:
  - `Confidentiality`, `Integrity`, `SecurityLabel`,
  - `confidentialityFlowsTo`, `integrityFlowsTo`, `securityFlowsTo`,
  - algebraic lemmas: `securityFlowsTo_refl`, `securityFlowsTo_trans`.
- observer projection helpers:
  - `projectState`, `projectObjects`, `projectRunnable`, `projectCurrent`,
  - relation scaffold: `lowEquivalent` with `refl/symm/trans` lemmas.

### Enforcement layer (WS-D2 / F-02 complete)

Policy checks wired into kernel operations via `Enforcement.lean`:

- `endpointSendDualChecked` — enforces `securityFlowsTo` before IPC send,
- `cspaceMintChecked` — enforces `securityFlowsTo` before capability minting.
*(WS-Q1: `serviceRestartChecked` removed — service lifecycle simplified to registry model.)*

### Non-interference theorems (WS-D2 baseline + WS-F3 expansion)

Transition-level non-interference proofs in `InformationFlow/Invariant.lean`:

WS-D2 baseline (5 theorems):
- `chooseThread_preserves_lowEquivalent` — scheduler non-interference (TPI-D01),
- `endpointSendDual_preserves_lowEquivalent` — IPC endpoint non-interference,
- `cspaceMint_preserves_lowEquivalent` — capability mint non-interference (TPI-D02),
- `cspaceRevoke_preserves_lowEquivalent` — capability revoke non-interference (TPI-D02),
- `lifecycleRetypeObject_preserves_lowEquivalent` — lifecycle non-interference (TPI-D03).

WS-F3 additions (4 new theorems; WS-Q1: 3 service lifecycle NI proofs removed):
- `notificationSignal_preserves_lowEquivalent` — notification signal NI (F-21),
- `notificationWait_preserves_lowEquivalent` — notification wait NI (F-21),
- `cspaceInsertSlot_preserves_lowEquivalent` — capability insert NI (CRIT-03),
- `storeObject_at_unobservable_preserves_lowEquivalent` — generic infrastructure.

WS-F3 enforcement-NI bridges (2 theorems; WS-Q1: `serviceRestartChecked_NI` removed):
- `endpointSendDualChecked_NI` — bridges checked send to NI,
- `cspaceMintChecked_NI` — bridges checked mint to NI.

WS-H8 enforcement-NI bridges (4 theorems):
- `endpointSendDualChecked_NI` — bridges dual-queue checked send to NI,
- `notificationSignalChecked_NI` — bridges checked signal to NI,
- `cspaceCopyChecked_NI` — bridges checked copy to NI (underlying NI as hypothesis),
- `cspaceMoveChecked_NI` — bridges checked move to NI (underlying NI as hypothesis).

WS-H8 enforcement soundness (5 theorems):
- `enforcementSoundness_endpointSendDualChecked`,
- `enforcementSoundness_notificationSignalChecked`,
- `enforcementSoundness_cspaceCopyChecked`,
- `enforcementSoundness_cspaceMoveChecked`,
- `enforcementSoundness_endpointReceiveDualChecked`.

### IF-M4 bundle-level non-interference (WS-E5 complete)

**H-04 — Parameterized security labels (≥3 domains):**

- `SecurityDomain` (Nat-indexed), `DomainFlowPolicy` with `canFlow`/`isReflexive`/`isTransitive`/`wellFormed`,
- `domainFlowsTo` with `domainFlowsTo_refl`/`domainFlowsTo_trans` proofs,
- Built-in policies: `DomainFlowPolicy.allowAll`, `DomainFlowPolicy.linearOrder` with well-formedness proofs,
- `GenericLabelingContext` with embedded policy field,
- `EndpointFlowPolicy` for per-endpoint flow overrides,
- `embedLegacyLabel` mapping legacy 2x2 lattice to 4-domain system,
- `embedLegacyLabel_preserves_flow` correctness proof,
- `threeDomainExample` with 3 named validation theorems.

**H-05 — Composed bundle-level non-interference:**

- `NonInterferenceStep` inductive (32 constructors; extended from 31 by R5-B/M-02: added `registerServiceChecked`. Extended from 28 by v0.13.5 audit: added `endpointReceiveDualHigh`, `endpointCallHigh`, `endpointReplyRecvHigh`. Added `syscallDecodeError`, `syscallDispatchHigh` by WS-J1-D. Original 28 from WS-H9),
- `step_preserves_projection` — single-step projection preservation (all 32 constructors),
- `composedNonInterference_step` — primary IF-M4 single-step theorem,
- `NonInterferenceTrace` inductive (`nil`/`cons`),
- `trace_preserves_projection`, `composedNonInterference_trace` — multi-step lift,
- `preservesLowEquivalence`, `compose_preservesLowEquivalence` — abstract composition,
- `errorAction_preserves_lowEquiv` — error path preservation.

WS-H9 new NI preservation theorems (21 theorems):
- `schedule_preserves_projection` — scheduler NI (high-current + all-runnable-high conditions),
- `setCurrentThread_preserves_projection` — thread switch NI,
- `ensureRunnable_preserves_projection` / `removeRunnable_preserves_projection` — run queue NI,
- `vspaceMapPage_preserves_projection` / `_lowEquivalent` — VSpace map NI,
- `vspaceUnmapPage_preserves_projection` / `_lowEquivalent` — VSpace unmap NI,
- `vspaceLookup_preserves_state` / `_lowEquivalent` — VSpace lookup NI,
- `cspaceCopy_preserves_projection` / `_lowEquivalent` — CSpace copy NI,
- `cspaceMove_preserves_projection` / `_lowEquivalent` — CSpace move NI,
- `cspaceDeleteSlot_preserves_projection` / `_lowEquivalent` — CSpace delete NI,
- `endpointReply_preserves_projection` / `_lowEquivalent` — IPC reply NI,
- `storeTcbIpcStateAndMessage_preserves_projection` — IPC state NI,
- `storeTcbQueueLinks_preserves_projection` — queue links NI,
- `storeObject_preserves_projection` / `storeCapabilityRef_preserves_projection` — observable-state NI,
- `switchDomain_preserves_lowEquivalent` — domain switch two-sided NI.

v0.13.5 gap closure (3 theorems + 1 bridge):
- `endpointReceiveDualChecked_NI` — enforcement-NI bridge for dual-queue receive (WS-H8 gap),
- `endpointReceiveDual_preserves_lowEquivalent` — IPC receive-dual NI (hypothesis-based),
- `endpointCall_preserves_lowEquivalent` — IPC call NI (hypothesis-based),
- `endpointReplyRecv_preserves_lowEquivalent` — IPC reply-recv NI (hypothesis-based).

**M-07 — Enforcement boundary specification:**

- `EnforcementClass` inductive (`policyGated`/`capabilityOnly`/`readOnly`),
- `enforcementBoundary` — exhaustive 22-entry classification table (11 policy-gated, 7 capability-only, 4 read-only),
- `enforcementBoundaryExtended` — definitional alias of `enforcementBoundary` (W2-G, previously duplicate list),
- `enforcementBoundaryExtended_eq_canonical` — element-wise equality proof (W2-G),
- `enforcementBoundaryComplete_counts` — compile-time count witness (11+7+4=22, V6-F),
- `enforcementBoundary_names_nonempty` — all boundary handler names non-empty (V6-F),
- `denied_preserves_state_*` — denial preservation for all 11 policy-gated operations,
- `enforcement_sufficiency_*` — complete-disjunction coverage proofs for all 11 policy-gated operations.

**WS-H8/A-36 — Projection hardening:**

- `ObservableState` extended with `domainTimeRemaining`, `domainSchedule`, `domainScheduleIndex`, `serviceRegistry` (V6-E),
- `projectDomainTimeRemaining`, `projectDomainSchedule`, `projectDomainScheduleIndex`, `projectServiceRegistry` projection helpers,
- All 19 NI theorems updated to handle new fields (including V6-E serviceRegistry ripple fixes).

**V6 — Information flow & cross-subsystem formalization:**

- `bibaIntegrityFlowsTo` reference model (standalone: `dst ≥ src`; drop-in for `securityFlowsTo` swapped-argument position) + `integrityFlowsTo_is_not_biba` / `integrityFlowsTo_denies_write_up_biba_allows` comparison theorems (V6-C),
- `LabelingContextValid` predicate with `defaultLabelingContext_valid` — NI deployment requirements (V6-D),
- `endpointPolicyRestricted` — per-endpoint policy subset of global policy well-formedness (V6-G),
- `DeclassificationEvent` structure with `authorizationBasis` field and `recordDeclassification` audit trail (V6-H),
- `kernelOperationNiConstructor` — 32-variant operation→constructor mapping (V6-I),
- `niStepCoverage_operational`, `niStepCoverage_injective`, `niStepCoverage_count` — NI coverage documentation (V6-I),
- `acceptedCovertChannel_scheduling` — documented scheduling covert channel (V6-J),
- `defaultLabelingContext_insecure` — warning that default labeling provides no security (V6-K),
- `StateField` enum + 10 pairwise disjointness/overlap witnesses (6 disjoint + 4 non-disjoint) + `registryDependencyConsistent_frame`, `serviceGraphInvariant_frame` (V6-A),
- `serviceCountBounded_of_eq`, `serviceCountBounded_monotone`, `serviceGraphInvariant_monotone` (V6-B).

**WS-H10/C-05/A-38 — MachineState projection & security lattice:**

- `ObservableState` extended with `machineRegs : Option RegisterFile` (domain-gated via current thread observability),
- Machine timer deliberately excluded (covert timing channel prevention),
- `projectMachineRegs` projection helper with observability gating,
- `bibaIntegrityFlowsTo` / `bibaSecurityFlowsTo` standard BIBA flow checks,
- `bibaPolicy` generic `DomainFlowPolicy` with standard BIBA ordering,
- `bibaPolicy_reflexive`, `bibaPolicy_transitive`, `bibaPolicy_wellFormed`,
- `securityLattice_reflexive`, `securityLattice_transitive` — legacy lattice pre-order confirmation,
- `DeclassificationPolicy` with `isDeclassificationAuthorized`, `isDeclassificationAuthorized_not_reflexive`,
- `declassifyStore` operation with 5 theorems (authorization, rejection, state preservation, enforcement soundness),
- `endpointFlowPolicyWellFormed` predicate with `endpointFlowCheck_reflexive`, `endpointFlowCheck_transitive`,
- All NI theorems updated for `machineRegs` field.

## 12. Untyped memory invariants (WS-F2)

Component level:

- `untypedWatermarkInvariant` — watermark does not exceed region size,
- `untypedChildrenBoundsInvariant` — all children lie within the watermark,
- `untypedChildrenNonOverlapInvariant` — children do not overlap,
- `untypedChildrenUniqueIdsInvariant` — children have unique object IDs.

Bundle level:

- `untypedMemoryInvariant` (conjunction of all four components)

Object-level theorems:

- `allocate_some_iff` — decomposition biconditional for successful allocation,
- `allocate_watermark_advance` / `allocate_watermark_monotone` — watermark progression,
- `allocate_preserves_watermarkValid` / `allocate_preserves_region` — structural preservation,
- `reset_wellFormed`, `empty_wellFormed`, `canAllocate_implies_fits`.

Operation-level theorems:

- `retypeFromUntyped_ok_decompose` — success decomposition into existential witnesses,
- `retypeFromUntyped_error_typeMismatch` — non-untyped source returns type mismatch,
- `retypeFromUntyped_error_allocSizeTooSmall` — undersized allocation rejected,
- `retypeFromUntyped_error_regionExhausted` — oversized allocation fails,
- `retypeFromUntyped_preserves_lifecycleMetadataConsistent` — metadata preservation,
- `retypeFromUntyped_preserves_lifecycleInvariantBundle` — full bundle preservation,
- `default_systemState_untypedMemoryInvariant` — default state satisfies invariant.

Auto-derivation theorems (WS-H2/B-5 — eliminates manual `hNe`/`hFresh` proof obligations):

- `retypeFromUntyped_ok_childId_ne` — success implies `childId ≠ untypedId` (derived from H-06 self-overwrite guard),
- `retypeFromUntyped_ok_childId_fresh` — success implies childId fresh among untyped's existing children (derived from A-27 collision guard),
- `retypeFromUntyped_preserves_untypedMemoryInvariant_auto` — composed variant that auto-derives both `hNe` and `hFresh` from a success hypothesis; callers need only supply the invariant precondition, new-object well-formedness, and success hypothesis.

## 16. WS-F1 IPC message transfer and dual-queue verification

IPC operations now carry `IpcMessage` payloads (registers, caps, badge):

- `endpointSendDual` / `endpointReceiveDual` — dual-queue IPC with message staging in `TCB.pendingMessage` (errors propagated, never silently swallowed),
- `endpointCall` — send + block-for-reply compound with message,
- `endpointReply` / `endpointReplyRecv` — reply + receive compound with message.

Preservation theorems (TPI-D08/TPI-D09):
- `endpointSendDual_preserves_ipcInvariant` / `_schedulerInvariantBundle` / `_ipcSchedulerContractPredicates`,
- `endpointReceiveDual_preserves_ipcInvariant` / `_schedulerInvariantBundle` / `_ipcSchedulerContractPredicates`,
- `endpointQueueRemoveDual_preserves_ipcInvariant` / `_schedulerInvariantBundle` / `_ipcSchedulerContractPredicates`,
- `endpointCall_preserves_ipcInvariant` / `_schedulerInvariantBundle` / `_ipcSchedulerContractPredicates`,
- `endpointReplyRecv_preserves_ipcInvariant` / `_schedulerInvariantBundle` / `_ipcSchedulerContractPredicates`,
- `endpointReply_preserves_ipcSchedulerContractPredicates`.

Supporting lemmas: `storeTcbIpcStateAndMessage`, `storeTcbPendingMessage`, `storeTcbQueueLinks`
backward-preservation and frame lemmas.

## 17. WS-F3 information-flow completeness

**CRIT-02 — ObservableState extension** (`Projection.lean`):

- `activeDomain` — scheduling transparency, always visible to all observers,
- `irqHandlers` — filtered by target notification object observability,
- `objectIndex` — filtered by object observability.

**F-22 — CNode slot filtering** (`Projection.lean`):

- `capTargetObservable` — observability gate for `.object`, `.cnodeSlot`, `.replyCap` targets,
- `projectKernelObject` — redacts high-domain capability slot contents from CNodes,
- `projectKernelObject_idempotent` — safety: double-filtering is idempotent (WS-G5: reformulated to slot-level lookup equality for `Std.HashMap` compatibility),
- `projectKernelObject_objectType` — safety: filtering preserves object type.

**Enforcement-NI bridges** (`Invariant.lean`):

- `endpointSendDualChecked_NI` — bridges checked send to NI domain-separation,
- `cspaceMintChecked_NI` — bridges checked mint to NI domain-separation,
- `registerServiceChecked_NI` — bridges checked service registration to NI domain-separation.
*(WS-Q1: replaces `serviceRestartChecked_NI` — service lifecycle simplified to registry model.)*

## 18. WS-F4 proof gap closure

### F-03: timerTick preservation (`Scheduler/Operations.lean`)

`timerTick` now preserves the complete scheduler invariant bundle and kernel invariant:

- `timerTick_preserves_schedulerInvariantBundle` — covers `queueCurrentConsistent`, `runQueueUnique`, `currentThreadValid`
- `timerTick_preserves_kernelInvariant` — extends to include `currentThreadInActiveDomain`

Proof strategy: case split on `scheduler.current` (none/some), object lookup (none/tcb/other), and time-slice expiry (`tcb.timeSlice ≤ 1`). Expired path delegates to existing `schedule_preserves_*` infrastructure; non-expired path proves scheduler unchanged directly.

### F-06: cspaceMutate, cspaceRevokeCdt, cspaceRevokeCdtStrict preservation (`Capability/Invariant.lean`)

- `cspaceMutate_preserves_capabilityInvariantBundle` — uses `revert/unfold` decomposition pattern; case-splits on capability lookup, rights check, and storeObject
- `cspaceRevokeCdt_preserves_capabilityInvariantBundle` — fold induction via extracted `revokeCdtFoldBody` with error propagation lemmas (`revokeCdtFoldBody_foldl_error`). CDT-only state updates handled by `capabilityInvariantBundle_of_cdt_update`
- `cspaceRevokeCdtStrict_preserves_capabilityInvariantBundle` — `suffices` with inline fold induction over total function; case-splits on `firstFailure`, `lookupCdtSlotOfNode`, `cspaceDeleteSlot`

Supporting infrastructure:
- `capabilityInvariantBundle_of_cdt_update` — CDT-only state changes preserve capability invariants (WS-H4: requires `edgeWellFounded` witness for new CDT)
- `revokeCdtFoldBody` — extracted fold body for named step preservation
- `revokeCdtFoldBody_preserves` — single-step preservation through fold body (WS-H4: uses `CapDerivationTree.edgeWellFounded_sub` + `removeNode_edges_sub` for CDT-shrinking acyclicity)
- `revokeCdtFoldBody_error` / `revokeCdtFoldBody_foldl_error` — error propagation through fold

### WS-H4: Capability invariant bundle redesign (`Capability/Invariant.lean`, `Model/Object.lean`)

Three new predicates added to `capabilityInvariantBundle` (4-tuple → 7-tuple, later extended to 8-tuple by WS-H13, then reduced to 6-tuple by WS-F6/D1):
- `cspaceSlotCountBounded` — every CNode has at most `2^radixBits` occupied slots
- `cdtCompleteness` — every CDT node points to an existing object (node-slot coherence)
- `cdtAcyclicity` — CDT edge-well-foundedness (no cycles via `edgeWellFounded`)

Foundation lemmas in `Model/Object.lean`:
- `CNode.slotCountBounded`, `empty_slotCountBounded`, `remove_slotCountBounded`, `revokeTargetLocal_slotCountBounded`
- `CapDerivationTree.edgeWellFounded`, `empty_edgeWellFounded`, `edgeWellFounded_sub`, `removeNode_edges_sub`

Transfer theorem strategy:
- **Non-CNode stores**: `cspaceSlotCountBounded_of_storeObject_nonCNode` + `cdtCompleteness_of_storeObject` + `cdtAcyclicity_of_cdt_eq`
- **CNode stores**: `cspaceSlotCountBounded_of_storeObject_cnode` with `hSlotCapacity`/`hDstCapacity` hypotheses
- **CDT-modifying ops** (copy/move/mintWithCdt): `hCdtPost` hypothesis pattern defers acyclicity obligation to caller
- **CDT-shrinking ops** (revoke fold): `edgeWellFounded_sub` + `removeNode_edges_sub`

### F-12: Notification ipcInvariant + schedulerInvariantBundle preservation (`IPC/Invariant.lean`)

- `notificationSignal_preserves_ipcInvariant` — wake path (storeObject → storeTcbIpcState → ensureRunnable) and merge path (storeObject only)
- `notificationSignal_preserves_schedulerInvariantBundle` — compositional through `scheduler_unchanged_through_store_tcb` + ensureRunnable helpers
- `notificationWait_preserves_ipcInvariant` — badge-consume path (storeObject → storeTcbIpcState) and wait path (storeObject → storeTcbIpcState → removeRunnable)
- `notificationWait_preserves_schedulerInvariantBundle` — badge-consume scheduler unchanged; wait path through removeRunnable with currentThread safety
- `notificationSignal_preserves_ipcSchedulerContractPredicates` — M3.5 contract predicate closure: wake path follows endpointReply pattern (storeTcbIpcState → ensureRunnable); merge path via `contracts_of_same_scheduler_ipcState` (no TCB/scheduler change)
- `notificationWait_preserves_ipcSchedulerContractPredicates` — M3.5 contract predicate closure: badge-consume path (scheduler unchanged, waiter set to .ready); wait path (.blockedOnNotification not covered by blockedOnSend/blockedOnReceive predicates, waiter removed from runnable)

Supporting infrastructure:
- `storeObject_notification_preserves_ipcInvariant` — dual of `storeObject_endpoint_preserves_ipcInvariant`; new helper for notification-storing operations
- Existing well-formedness lemmas: `notificationSignal_result_wellFormed_wake/merge`, `notificationWait_result_wellFormed_badge/wait`

## 19. WS-G9 information-flow projection optimization (F-P09)

**Precomputed observable set** (`Projection.lean`):

- `computeObservableSet` — builds `Std.HashSet ObjId` via single `foldl` pass over `st.objectIndex`, using `objectObservable` as predicate. All sub-projection functions use O(1) `contains` lookups instead of redundant `objectObservable` re-evaluation (~12,800 comparisons → N lookups).

**`@[csimp]`-ready fast projection** (`Projection.lean`):

- `projectStateFast` — optimized `projectState` using precomputed observable set,
- `projectObjectsFast` — O(1) observability via `observableOids.contains`,
- `projectIrqHandlersFast` — O(1) observability via `observableOids.contains`,
- `projectObjectIndexFast` — O(1) observability via `observableOids.contains`.

**Equivalence proofs** (`Projection.lean`):

- `foldl_observable_set_mem` — core induction lemma: HashSet membership ↔ list membership ∧ predicate,
- `computeObservableSet_mem` — membership in computed set ↔ `objectObservable` for indexed ObjIds,
- `computeObservableSet_not_mem` — non-indexed ObjIds are not in the observable set,
- `projectObjectsFast_eq` — fast variant equals original `projectObjects`,
- `projectIrqHandlersFast_eq` — fast variant equals original `projectIrqHandlers`,
- `projectObjectIndexFast_eq` — fast variant equals original `projectObjectIndex` (via `List.filter_congr`),
- `projectStateFast_eq` — top-level equivalence: `projectStateFast = projectState` under state synchronization invariants.

**HashSet bridge lemmas** (`Prelude.lean`):

- `List.foldl_preserves_contains` — monotonicity: elements already in the set remain after foldl,
- `List.foldl_not_contains_when_absent` — elements not in the list are unaffected by foldl,
- `List.foldl_preserves_when_pred_false` — elements with false predicate are unaffected by foldl.

**Design invariant:** Original `projectState` definition is unchanged — all existing NI theorems in `Invariant.lean` (1448 lines) remain untouched. `projectStateFast` provides the performance path with proven equivalence.

## 21. WS-H14 type safety & Prelude foundations

**Typeclass instance hardening (A-03):**

- `EquivBEq` instances for all 16 typed identifier types (13 in `Prelude.lean` + `SecurityDomain` in `Policy.lean` + `RegName`/`RegValue` in `Machine.lean` via WS-J1-A + `CdtNodeId` in `Structures.lean` via WS-J1-F).
- `LawfulBEq` instances for all 16 typed identifier types.
- These close the gap where HashMap bridge lemmas required `EquivBEq` constraints that identifier types did not satisfy.

**KernelM monad law proofs (A-04/M-11):**

- `KernelM.pure_bind_law` — left identity for the state-error monad.
- `KernelM.bind_pure_law` — right identity (bind with pure is identity).
- `KernelM.bind_assoc_law` — associativity (sequential composition is associative).
- `LawfulMonad (KernelM σ ε)` — registered instance enabling equational reasoning about chained kernel transitions.

**isPowerOfTwo correctness (A-06):**

- `isPowerOfTwo_spec` — definitional unfolding: `isPowerOfTwo n = true → n > 0 ∧ n &&& (n - 1) = 0`.
- `isPowerOfTwo_pos` — positivity extraction.
- `isPowerOfTwo_of_pow2_k` — concrete verification for k = 0..5, 12, 16, 21 (covers all platform page sizes).

**Identifier roundtrip & injectivity proofs (WS-H14d):**

For each of the 16 identifier types:
- `toNat_ofNat` — roundtrip: construct then project yields the original value.
- `ofNat_toNat` — roundtrip: project then reconstruct yields the original identifier.
- `ofNat_injective` — distinct values produce distinct identifiers.
- `ext` — extensionality: equal underlying values imply equal identifiers.

**OfNat instance removal (A-02/M-10):**

- All `OfNat` instances removed for 16 typed identifier types.
- Numeric literals can no longer implicitly coerce to typed identifiers.
- All construction sites migrated to explicit `⟨n⟩` or `TypeName.ofNat n` syntax (including `CdtNodeId` literals in tests via WS-J1-F).

**Sentinel predicate completion (A-01):**

- `ThreadId.valid` / `ServiceId.valid` / `CPtr.valid` — nonzero value predicates.
- `*.valid_iff_not_reserved` — equivalence between validity and non-reservation.
- `*.sentinel_not_valid` — sentinel is never valid (for all 4 sentinel-bearing types).

## 20. WS-H10 security model foundations

**MachineState projection (C-05/A-38):**

- `ObservableState.machineRegs : Option RegisterFile` — domain-gated register file projection, visible only when the current thread is observable.
- `projectMachineRegs` — projects register file through current-thread observability gate. Machine timer deliberately excluded (covert timing channel).
- All existing NI theorems updated with `machineRegs` branch proofs.

**Security lattice (A-34):**

- `securityLattice_reflexive` / `securityLattice_transitive` — legacy lattice forms a valid pre-order.
- `bibaIntegrityFlowsTo` / `bibaSecurityFlowsTo` / `bibaPolicy` — standard BIBA alternatives with reflexivity/transitivity proofs.

**Declassification model (A-39):**

- `DeclassificationPolicy` — authorized downgrade paths with `isDeclassificationAuthorized` gate.
- `declassifyStore` — enforcement operation gating on base-policy denial + declassification authorization.
- `enforcementSoundness_declassifyStore` — if operation succeeds, both authorization checks passed.
- `declassifyStore_NI` — declassification at a non-observable target preserves low-equivalence for non-target observers. Delegates to `storeObject_at_unobservable_preserves_lowEquivalent`.

**Endpoint policy well-formedness (M-16):**

- `endpointFlowPolicyWellFormed` — global + per-endpoint override policies must be reflexive + transitive.
- `endpointFlowCheck_reflexive` / `endpointFlowCheck_transitive` — well-formedness inheritance proofs.

**IF configuration invariant bundle:**

- `InformationFlowConfigInvariant` — structure collecting global policy WF, endpoint policy WF, and declassification consistency. Trivially preserved by kernel transitions (policies are external to `SystemState`).
- `defaultConfigInvariant` — existence proof for the default configuration.

## 22. Cross-subsystem invariant reconciliation (WS-H12e)

WS-H12e reconciles all subsystem invariant compositions after WS-H12a–d changes,
closing gaps where invariants were defined but not composed into the top-level proof surface.

### Changes to bundle compositions

| Bundle | Change | Effect |
|---|---|---|
| `schedulerInvariantBundleFull` | Extended from 4 to 7 conjuncts (+ `contextMatchesCurrent` WS-H12e, + `runnableThreadsAreTCBs` WS-F6/D3, + `schedulerPriorityMatch` R6-D/L-12) | Machine registers match current thread's saved context; all runnable threads are valid TCBs; RunQueue priority index matches TCB priority |
| `coreIpcInvariantBundle` | Upgraded from `ipcInvariant` to `ipcInvariantFull` (5-conjunct) | `dualQueueSystemInvariant`, `allPendingMessagesBounded`, `badgeWellFormed`, and `waitingThreadsPendingMessageNone` now composed into cross-subsystem proof surface |
| `ipcSchedulerCouplingInvariantBundle` | Extended from 2 to 4 conjuncts (+ `contextMatchesCurrent`, `currentThreadDequeueCoherent`) | Running thread dequeue coherence and context consistency compose through IPC-scheduler boundary |
| `proofLayerInvariantBundle` | Uses `schedulerInvariantBundleFull` instead of `schedulerInvariantBundle` | Top-level proof surface includes all 7 scheduler conjuncts |

### New proofs and definitions

Scheduler preservation (4 updated theorems):
- `schedule_preserves_schedulerInvariantBundleFull` — 7-conjunct preservation (incl. `runnableThreadsAreTCBs` WS-F6/D3, `schedulerPriorityMatch` R6-D/L-12)
- `handleYield_preserves_schedulerInvariantBundleFull` — 7-conjunct preservation
- `timerTick_preserves_schedulerInvariantBundleFull` — 7-conjunct preservation
- `switchDomain_preserves_schedulerInvariantBundleFull` — 7-conjunct preservation (+ `switchDomain_preserves_schedulerPriorityMatch`)

Backward-compatible extraction theorems (3):
- `coreIpcInvariantBundle_to_ipcInvariant`
- `coreIpcInvariantBundle_to_dualQueueSystemInvariant`
- `coreIpcInvariantBundle_to_allPendingMessagesBounded`

Frame lemmas for `allPendingMessagesBounded` (8):
- `ensureRunnable_preserves_allPendingMessagesBounded`, `removeRunnable_preserves_allPendingMessagesBounded`
- `storeTcbIpcState_preserves_allPendingMessagesBounded`, `storeTcbIpcStateAndMessage_preserves_allPendingMessagesBounded`
- `storeTcbPendingMessage_preserves_allPendingMessagesBounded`, `storeObject_endpoint_preserves_allPendingMessagesBounded`
- `storeTcbQueueLinks_preserves_allPendingMessagesBounded`, `storeObject_notification_preserves_allPendingMessagesBounded`

Compound `allPendingMessagesBounded` preservation (3):
- `notificationSignal_preserves_allPendingMessagesBounded`, `notificationWait_preserves_allPendingMessagesBounded`
- `endpointReply_preserves_allPendingMessagesBounded`

Composed `ipcInvariantFull` preservation (7):
- `notificationSignal_preserves_ipcInvariantFull`, `notificationWait_preserves_ipcInvariantFull`
- `endpointReply_preserves_ipcInvariantFull`, `endpointSendDual_preserves_ipcInvariantFull`
- `endpointReceiveDual_preserves_ipcInvariantFull`, `endpointCall_preserves_ipcInvariantFull`
- `endpointReplyRecv_preserves_ipcInvariantFull`

Default-state proofs (7):
- `default_dualQueueSystemInvariant`, `default_allPendingMessagesBounded`, `default_badgeWellFormed`, `default_waitingThreadsPendingMessageNone`, `default_ipcInvariantFull`
- `default_contextMatchesCurrent`, `default_currentThreadDequeueCoherent`, `default_schedulerInvariantBundleFull`

Badge well-formedness preservation (WS-F5/D1d):
- `notificationSignal_preserves_badgeWellFormed`, `notificationWait_preserves_badgeWellFormed`
- `cspaceMint_preserves_badgeWellFormed`, `cspaceMutate_preserves_badgeWellFormed`
- Helper lemmas: `storeObject_cnode_preserves_notificationBadgesWellFormed`, `storeObject_cnode_preserves_capabilityBadgesWellFormed`
- `storeObject_notification_preserves_notificationBadgesWellFormed`, `storeObject_nonNotification_preserves_notificationBadgesWellFormed`
- `storeObject_nonCNode_preserves_capabilityBadgesWellFormed`
- Transfer: `badgeWellFormed_of_objects_eq`

## 23. WS-H13: CSpace enrichment, service hardening & serviceCountBounded (v0.14.4)

WS-H13 closes 5 findings: H-01 (HIGH), A-29 (HIGH), A-21 (MEDIUM), A-30 (MEDIUM), M-17/A-31 (MEDIUM).

### Part A — Type-indexed CSpace with compressed-path CNodes (H-01)

CNode structure enriched with multi-level resolution fields:

- `depth` — CNode depth in CSpace hierarchy
- `guardWidth` — number of guard bits
- `guardValue` — guard bit pattern to match
- `radixWidth` — log₂ of slot count at this level

Multi-level resolver (`Capability/Operations.lean`):

- `resolveCapAddress` — recursive CSpace address resolver; walks CNode chain consuming `guardWidth + radixWidth` bits per hop. `termination_by bitsRemaining` with `hProgress : guardWidth + radixWidth ≥ 1` ensuring strict decrease.
- `resolveCapAddressK` — kernel monad wrapper
- `resolveCapAddressAndLookup` — composition with slot lookup

**CNode Radix Tree** (Q4, v0.17.10 — `SeLe4n/Kernel/RadixTree/`):

`CNodeRadix` is a verified flat radix array for CNode capability slots. Each
CNode has a single radix level with `2^radixWidth` entries, addressed by
`extractBits` (pure bitwise index computation — zero hashing). Operations:

- `CNodeRadix.empty` — create empty tree with all slots `none`
- `CNodeRadix.lookup` — O(1) via `extractBits slot.toNat 0 radixWidth` + direct array access
- `CNodeRadix.insert` / `erase` — O(1) array set
- `CNodeRadix.fold` / `toList` / `size` — O(2^radixWidth) traversal

Correctness proofs (`RadixTree/Invariant.lean`):

- `lookup_empty` — empty tree returns `none` for all slots
- `lookup_insert_self` / `lookup_insert_ne` — insert roundtrip
- `lookup_erase_self` / `lookup_erase_ne` — erase correctness
- `insert_idempotent` — double insert = single insert
- `insert_erase_cancel` — erase then insert = insert
- `empty_wf` / `insert_wf` / `erase_wf` — WF preservation
- `insert_guardWidth` / `insert_radixWidth` / etc. — parameter invariance

Builder equivalence bridge (`RadixTree/Bridge.lean`):

- `buildCNodeRadix` — fold RHTable entries into CNodeRadix
- `buildCNodeRadix_guardWidth/guardValue/radixWidth` — parameter preservation
- `buildCNodeRadix_wf` — built tree is well-formed
- `CNodeRadix.ofCNode` — convenience conversion from CNode
- `buildCNodeRadix_lookup_equiv` — **(T4-I, M-DS-3)** bidirectional lookup
  equivalence: `(buildCNodeRadix rt config).lookup slot = rt.get? slot`.
  Proved via 3 private fold lemmas (foldl_preserves_none, foldl_preserves_some,
  foldl_establishes_some) with list induction over the hash table's slot array.
  Preconditions: `invExt`, `UniqueRadixIndices`, and `hNoPhantom` (no radix
  index collision between absent keys and present keys).
- `uniqueRadixIndices_sufficient` — **(V3-C, H-RAD-1)** bounded-key injectivity
  for `extractBits`: when all present keys satisfy `s.toNat < 2^radixWidth`,
  `extractBits` is injective over distinct keys, discharging `UniqueRadixIndices`.
- `buildCNodeRadix_hNoPhantom_auto_discharge_note` — **(V3-H)** documentation-only
  theorem. Documents auto-discharge pattern for bounded-key CNodes; requires
  `extractBits_identity` lemma (not yet formally proven) to complete the chain.

Resolution theorems:

- `resolveCapAddress_deterministic` — trivial (functional equality)
- `resolveCapAddress_zero_bits` — zero remaining bits → `.error .illegalState`
- `resolveCapAddress_result_valid_cnode` — success implies valid CNode exists at returned reference. Proved via `Nat.strongRecOn` (well-founded induction on `bits`) with nested `split at hOk` through all branches.

CSpace depth invariant:

- `cspaceDepthConsistent` — added to `capabilityInvariantBundle` (WS-H13; later WS-F6/D1 reduced bundle to 6-tuple by removing 2 tautological predicates)
- `default_capabilityInvariantBundle` — updated for current 6-tuple (vacuous for empty object store)

### Part B — Atomic capability move (A-21)

- `cspaceMove_error_no_state` — error-path exclusion: on error, no success state is reachable.
- `cspaceMove_ok_implies_source_exists` — success-path: if move succeeds, the source capability existed.
- `resolveCapAddress_guard_reject` — guard mismatch at any CNode level returns `.error .invalidCapability` (primary CSpace attack surface coverage).
- Error monad (`Except`) provides implicit atomicity: error paths discard intermediate state, returning original state unchanged.

### Part C — Service backing-object verification (A-29)

`serviceStop` now checks backing-object existence before allowing transition:

- `serviceStop` — added `st.objects[svc.identity.backingObject]? = none` → `.error .backingObjectMissing` branch before policy check
- `serviceStop_error_backingObjectMissing` — rejection theorem
- `serviceStop_error_policyDenied` — updated with `hBacking` hypothesis (backing-object existence is a precondition for reaching the policy-denial branch)
- All downstream preservation theorems updated with extra `split at hStep` for new backing-object check branch

### Part D — Service graph invariant preservation (updated WS-Q1)

*(WS-Q1: `serviceRestart` atomicity removed — lifecycle transitions eliminated.)*

### Part E — serviceCountBounded invariant (M-17/A-31)

`serviceGraphInvariant` extended to 2-conjunct: `serviceDependencyAcyclic ∧ serviceCountBounded`.

Transfer lemma suite (6 lemmas for `storeServiceState` where `entry.dependencies = svc.dependencies`):

- `serviceEdge_of_storeServiceState_sameDeps` — edge relation preserved
- `serviceNontrivialPath_of_storeServiceState_sameDeps` — path relation preserved
- `serviceDependencyAcyclic_of_storeServiceState_sameDeps` — acyclicity preserved
- `bfsUniverse_of_storeServiceState_sameDeps` — BFS universe preserved
- `serviceCountBounded_of_storeServiceState_sameDeps` — count bound preserved
- `serviceGraphInvariant_of_storeServiceState_sameDeps` — composed invariant preserved

Preservation theorems:

- `serviceRegisterDependency_preserves_serviceGraphInvariant` — `serviceCountBounded` transfer through dependency insertion

## WS-H15: Platform & API Hardening (v0.14.7)

### Syscall capability-checking (WS-H15c)

Introduces the seL4-style capability-gated syscall entry pattern:

- **`SyscallGate`** — structure encoding caller identity, CSpace root, capability
  address, depth, and required access right.
- **`syscallLookupCap`** — resolves a capability through `resolveCapAddress` and
  validates the required access right.
- **`syscallInvoke`** — gated combinator that composes lookup with an operation.
- **Soundness theorems**: `syscallLookupCap_implies_capability_held` (successful
  lookup implies capability held with required right), `syscallLookupCap_state_unchanged`
  (lookup is read-only), `syscallInvoke_requires_right` (successful invocation
  implies caller held required capability).
- **13 `api*` wrappers**: capability-gated entry points for IPC, CSpace, lifecycle,
  VSpace, and service operations.

### Decidability consistency (WS-H15a)

- **`irqLineSupported_decidable_consistent`** — `decide` agrees with the
  `irqLineSupported` predicate for any `InterruptBoundaryContract`.
- **`irqHandlerMapped_decidable_consistent`** — same for `irqHandlerMapped`.

### Adapter proof hooks (WS-H15d)

- **`advanceTimerState_preserves_proofLayerInvariantBundle`** — generic theorem
  proving timer advancement preserves the full 7-conjunct invariant bundle,
  applicable to any `RuntimeBoundaryContract`.
- **Simulation platform** (`Platform/Sim/ProofHooks.lean`):
  - `simRestrictiveAdapterProofHooks` — concrete `AdapterProofHooks` instance
    for the restrictive contract (all predicates `False`).
  - 3 end-to-end theorems: `simRestrictive_adapterAdvanceTimer_preserves`,
    `simRestrictive_adapterWriteRegister_preserves`,
    `simRestrictive_adapterReadMemory_preserves`.
- **RPi5 platform** (`Platform/RPi5/ProofHooks.lean`):
  - `rpi5RuntimeContractRestrictive` — restrictive variant of the RPi5
    runtime contract. Shares production timer/memory predicates; denies
    all register writes. Needed because the production contract's SP-only
    check admits all `writeReg` calls (which never modify `sp`), making
    `contextMatchesCurrent` preservation unprovable for arbitrary writes.
  - `rpi5RestrictiveAdapterProofHooks` — concrete `AdapterProofHooks`
    instance. Timer preservation uses the generic lemma substantively;
    register write is vacuous (restrictive contract rejects all writes).
  - 3 end-to-end theorems: `rpi5Restrictive_adapterAdvanceTimer_preserves`,
    `rpi5Restrictive_adapterWriteRegister_preserves`,
    `rpi5Restrictive_adapterReadMemory_preserves`.
- **SimRestrictive platform** (`Platform/Sim/RuntimeContract.lean`, `Platform/Sim/Contract.lean`, `Platform/Sim/ProofHooks.lean` — S5-D):
  - `simRuntimeContractSubstantive` — substantive simulation contract with timer
    monotonicity validation, memory access restricted to 256 MiB RAM, register
    writes denied.
  - `SimRestrictivePlatform` — `PlatformBinding` instance using the substantive
    contract.
  - Substantive proof hooks in `Platform/Sim/ProofHooks.lean` for the restrictive
    simulation variant.

### Testing (WS-H15e)

- **Trace harness**: 5 syscall gate scenarios (correct gate, bad root,
  insufficient rights, missing cap, retype gate) in `MainTraceHarness.lean`.
- **Negative tests**: 6 tests in `NegativeStateSuite.lean` exercising
  `syscallLookupCap` and `apiEndpointSend` error paths.
- **Platform contract tests**: 7 tests in `NegativeStateSuite.lean` validating
  `rpi5MachineConfig.wellFormed`, `mmioRegionDisjointCheck`,
  `mmioRegionsPairwiseDisjointCheck` (X4-D inter-device disjointness), GIC-400 IRQ
  boundary values (INTID 0, 223, 224), and boot contract predicates.
- **Tier 3 anchors**: 31 anchors covering all WS-H15 additions.

## WS-H16: Testing, Documentation & Cleanup (v0.14.8)

WS-H16 closes 6 findings: M-18 (MEDIUM), A-43 (LOW), A-13 (MEDIUM), A-18 (MEDIUM), A-19 (LOW), M-21/A-45 (LOW).

### Object store liveness invariant (A-13)

New predicate in `Model/State.lean`:

- `objectIndexLive` — every entry in `objectIndex` resolves to a live object
  in the store (`∀ id ∈ st.objectIndex, st.objects[id]? ≠ none`).
- `objectIndexLive_default` — holds trivially for the default system state.
- `storeObject_preserves_objectIndexLive` — preservation through `storeObject`,
  the atomic object store mutation primitive. Proved by case-splitting on
  `objectIndexSet.contains` (new vs existing object) with `HashMap.getElem?_insert`.

### RunQueue threadPriority consistency (A-19)

New predicate in `Scheduler/Invariant.lean`:

- `runQueueThreadPriorityConsistent` — bi-directional consistency:
  (1) every RunQueue member has a `threadPriority` entry, and
  (2) every `threadPriority` entry is a RunQueue member.
- `runQueueThreadPriorityConsistent_default` — holds for empty default state.
- Standalone predicate (not in `schedulerInvariantBundleFull`) following the
  pattern of `schedulerPriorityMatch`, to avoid cascading proof breakage.

### O(1) membership audit (A-18)

Confirmed that `schedule` (`Operations/Core.lean:235`) uses O(1) `RunQueue.contains`
via `tid ∈ st'.scheduler.runQueue` (backed by `HashSet`), not the O(n)
`runnable` flat-list alias. No code change required.

### Lifecycle negative tests (M-18)

10 new `expectError` tests in `NegativeStateSuite.lean` (`runWSH16LifecycleChecks`):

- H16-NEG-01..04: `lifecycleRetypeObject` error branches (non-existent target,
  metadata mismatch, insufficient authority, bad authority CNode).
- H16-NEG-05..06: `lifecycleRevokeDeleteRetype` error branches (authority = cleanup,
  bad cleanup CNode).
- H16-NEG-07: `retypeFromUntyped` with exhausted untyped region.
- H16-NEG-08: `retypeFromUntyped` with non-untyped source (type mismatch).
- H16-NEG-09: `retypeFromUntyped` with device untyped restriction.
- H16-NEG-10: `lifecycleRevokeDeleteRetype` with non-existent retype target.

### Semantic Tier 3 assertions (A-43)

13 new proof-surface anchors in `test_tier3_invariant_surface.sh` verifying
structural properties rather than just symbol existence:

- `capabilityInvariantBundle` has ≥5 conjuncts
- `schedulerInvariantBundleFull` includes `timeSlicePositive`, `edfCurrentHasEarliestDeadline`, `contextMatchesCurrent`
- `NonInterferenceStep` has ≥20 constructors
- `objectIndexLive` definition and theorems exist
- `runQueueThreadPriorityConsistent` definition and default theorem exist
- `runWSH16LifecycleChecks` test function exists
- `schedule` uses O(1) `runQueue` membership

## 30. WS-J1 Register-indexed authoritative namespaces

WS-J1 introduces a register decode layer and typed register wrappers,
closing the gap between the abstract model and real ARM64 syscall argument
delivery. See [`AUDIT_v0.14.10_REGISTER_NAMESPACE_WORKSTREAM_PLAN.md`](../dev_history/audits/AUDIT_v0.14.10_REGISTER_NAMESPACE_WORKSTREAM_PLAN.md).

**Completed types (WS-J1-A, v0.15.4):**

- `RegName` — typed wrapper structure with `DecidableEq`, `Hashable`, `LawfulHashable`, `EquivBEq`, `LawfulBEq`, `Repr`, `ToString`, `ofNat`/`toNat`, roundtrip/injectivity proofs
- `RegValue` — typed wrapper structure with identical instance suite
- `RegisterFile.gpr` — updated from `Nat → Nat` to `RegName → RegValue`
- All 10 machine lemmas (`readReg_writeReg_eq/ne`, `writeReg_preserves_pc/sp`, etc.) re-proved for typed wrappers

**R7 hardware preparation (R7-B/C/D/E, v0.18.6):**

- `RegName.arm64GPRCount` — ARM64 GPR count constant (32), `RegName.isValid`/`isValidDec` bounds predicate (L-02)
- `isWord64` / `isWord64Dec` — 64-bit word-boundedness predicate for `Nat` (L-03)
- `RegValue.valid`/`isValid`, `VAddr.valid`/`isValid`, `PAddr.valid`/`isValid` — type-specific 64-bit bounds (L-03)
- `machineWordBounded` — machine-state invariant asserting all registers are word-bounded (L-03)
- `TCB.faultHandler : Option CPtr`, `TCB.boundNotification : Option ObjId` — seL4 TCB fidelity fields (L-06)
- `KernelObjectType.toNat`/`ofNat?` — type tag encoding with `ofNat_toNat` / `toNat_injective` proofs (L-10)
- `LifecycleRetypeArgs.newType` — typed as `KernelObjectType` instead of raw `Nat` (L-10)
- `objectOfKernelType` — typed retype constructor with `objectOfKernelType_type` proof (L-10)

**Completed decode layer (WS-J1-B, v0.15.5):**

Types:
- `SyscallId` — inductive covering 13 modeled syscalls with `toNat`/`ofNat?` encoding, `toNat_injective`/`ofNat_toNat`/`toNat_ofNat` proofs
- `MessageInfo` — seL4 message-info word bit-field layout with `encode`/`decode`
- `SyscallRegisterLayout` — ARM64 register-to-argument mapping with `arm64DefaultLayout` (x0–x7), `DecidableEq` (provides `BEq` implicitly)
- `SyscallDecodeResult` — typed decode output consumed by syscall dispatch
- `MachineConfig.registerCount` — bounded register space per architecture

Decode functions (`RegisterDecode.lean`):
- `decodeCapPtr` — total decode (every register value is a valid CPtr)
- `decodeMsgInfo` — partial decode, validates length/extraCaps bounds
- `decodeSyscallId` — partial decode, validates against modeled syscall set
- `validateRegBound` — per-architecture register index bounds check
- `decodeSyscallArgs` — entry point combining all register reads + bounds validation + decoding

Round-trip theorems:
- `decodeCapPtr_roundtrip` — `decodeCapPtr (encodeCapPtr c) = .ok c`
- `decodeSyscallId_roundtrip` — `decodeSyscallId (encodeSyscallId s) = .ok s`
- `decodeMsgInfo_roundtrip` — `decodeMsgInfo (encodeMsgInfo mi) = .ok mi` (requires `mi.length ≤ maxMessageRegisters ∧ mi.extraCaps ≤ maxExtraCaps`; delegates to `MessageInfo.encode_decode_roundtrip` bitwise proof)
- `decode_components_roundtrip` — composite: all three per-component round-trips hold simultaneously for any well-formed `SyscallDecodeResult` (capPtr, msgInfo, syscallId). Message registers need no round-trip (identity in the abstract model). Originally 4-conjunct in WS-K-A v0.16.0; reduced to 3-conjunct in W3-H v0.22.14 when `encodeMsgRegs` was removed as dead code.
- `decodeMsgRegs_length` — when `decodeSyscallArgs` succeeds, `decoded.msgRegs.size = layout.msgRegs.size` (proved via `list_mapM_except_length` / `array_mapM_except_size` helper lemmas, WS-K-A v0.16.0)
- `MessageInfo.encode_decode_roundtrip` — bit-field round-trip: `MessageInfo.decode (MessageInfo.encode mi) = some mi` (proved via `Nat.testBit` extensionality with three bitwise extraction helper lemmas: `and_mask_127`, `shift7_and_mask_3`, `shift9_extracts_label`)

Determinism & error exclusivity:
- `decodeSyscallArgs_deterministic` — identical inputs produce identical results
- `decodeSyscallId_error_iff` — fails iff `SyscallId.ofNat?` returns `none`
- `decodeMsgInfo_error_iff` — fails iff `MessageInfo.decode` returns `none`
- `decodeCapPtr_ok_iff` — S4-K: decodeCapPtr succeeds iff register value is word64-bounded
- `decodeCapPtr_ok_of_word64` — S4-K: decodeCapPtr succeeds for word64-bounded values
- `validateRegBound_ok_iff` / `validateRegBound_error_iff` — bounds iff-theorems

**Completed syscall entry point and dispatch (WS-J1-C, v0.15.6; refinements v0.15.7):**

Functions:
- `lookupThreadRegisterContext` — extracts saved register context from current thread's TCB
- `syscallRequiredRight` — total mapping from `SyscallId` to `AccessRight` (13 cases)
- `dispatchCapabilityOnly` — shared helper for 6 capability-only syscall arms (cspaceDelete, lifecycleRetype, vspaceMap, vspaceUnmap, serviceRevoke, serviceQuery) used by both checked and unchecked dispatch paths (V8-H)
- `dispatchWithCap` — per-syscall routing: IPC send/receive/call/reply and service start/stop extract targets from resolved capability's `CapTarget`; delegates capability-only arms to `dispatchCapabilityOnly`
- `dispatchSyscall` — constructs `SyscallGate` from caller's TCB and CSpace root CNode, routes through `syscallInvoke`
- `syscallEntry` — top-level register-sourced entry point: reads `scheduler.current`, extracts registers, decodes (with configurable `regCount`, default 32), dispatches
- `MachineConfig.registerCount` — promoted from computed def to configurable structure field (default 32)

Soundness theorems:
- `syscallEntry_requires_valid_decode` — successful entry implies `decodeSyscallArgs` returned `.ok`
- `syscallEntry_implies_capability_held` — successful entry implies full capability-resolution chain: TCB/CSpace root lookup succeeded, capability with required access right resolved from decoded `capAddr`
- `dispatchSyscall_requires_right` — dispatch success implies capability with required access right was held (threads through `syscallInvoke_requires_right`)
- `lookupThreadRegisterContext_state_unchanged` — register context lookup is read-only
- `syscallRequiredRight_total` — every `SyscallId` maps to exactly one `AccessRight`
- `dispatchCapabilityOnly_some_iff` — characterizes the 6 syscall IDs handled by the shared capability-only dispatch path (V8-H)

**Completed invariant and information-flow integration (WS-J1-D, v0.15.8):**

Invariant predicate:
- `registerDecodeConsistent` — current thread (if any) has a valid TCB, bridging the decode layer to the kernel object store; implied by `schedulerInvariantBundleFull` via `currentThreadValid`
- `default_registerDecodeConsistent` — vacuously true for empty system state
- `registerDecodeConsistent_of_proofLayerInvariantBundle` — extraction from top-level invariant bundle
- `advanceTimerState_preserves_registerDecodeConsistent` — timer-only changes do not affect object store or scheduler
- `writeRegisterState_preserves_registerDecodeConsistent` — register-only changes do not affect object store or scheduler

Invariant preservation:
- `syscallEntry_preserves_proofLayerInvariantBundle` — compositional: if the dispatched operation preserves the bundle, `syscallEntry` preserves it (decode is pure, lookup is read-only)
- `syscallEntry_error_preserves_proofLayerInvariantBundle` — trivial (state unchanged on error)
- `lookupThreadRegisterContext_preserves_proofLayerInvariantBundle` — read-only operation

Non-interference:
- `decodeSyscallArgs_preserves_lowEquivalent` — pure function, NI trivial
- `lookupThreadRegisterContext_preserves_lowEquivalent` — read-only, low-equivalence preserved across paired lookups
- `lookupThreadRegisterContext_preserves_projection` — read-only, projection unchanged
- `syscallLookupCap_preserves_projection` — read-only capability lookup, projection unchanged
- `syscallEntry_preserves_projection` — compositional projection preservation
- `NonInterferenceStep.syscallDecodeError` — decode failure step (state unchanged, `st' = st`)
- `NonInterferenceStep.syscallDispatchHigh` — high-domain dispatch step (carries projection preservation proof)
- `step_preserves_projection` extended with new constructor cases
- `syscallEntry_error_yields_NI_step` — bridge: failed `syscallEntry` → `syscallDecodeError` NI step
- `syscallEntry_success_yields_NI_step` — bridge: successful high-domain `syscallEntry` → `syscallDispatchHigh` NI step

**Completed testing and trace evidence (WS-J1-E, v0.15.9):**

Negative decode tests (`tests/NegativeStateSuite.lean`):
- `validateRegBound` out-of-bounds and boundary-pass (register index 32 ≥ 32, 31 < 32)
- `decodeSyscallId` invalid number and boundary-pass (99 not modeled, 0 = send)
- `decodeMsgInfo` oversized length and boundary-pass (127 > maxMessageRegisters, valid info)
- `decodeCapPtr` zero-valued register (total, always succeeds)
- `decodeSyscallArgs` bad layout, bad msgReg, invalid syscall in register, malformed msgInfo in register, all-zero valid decode
- `syscallEntry` no current thread (returns `objectNotFound`)

Register-decode trace scenarios (`SeLe4n/Testing/MainTraceHarness.lean`):
- RDT-002: standalone decode success (syscall=send, capAddr=0)
- RDT-003: full `syscallEntry` send via register decode (endpoint has sender)
- RDT-006: invalid syscall number decode error
- RDT-008: malformed msgInfo decode error
- RDT-010: out-of-bounds register layout error

Operation-chain tests (`tests/OperationChainSuite.lean`):
- `chain10RegisterDecodeMultiSyscall` — multi-syscall sequence (send then receive) via register decode
- `chain11RegisterDecodeIpcTransfer` — register decode with badge-carrying capability and IPC transfer

Tier 3 invariant surface anchors:
- 5 definition anchors (`decodeCapPtr`, `decodeMsgInfo`, `decodeSyscallId`, `validateRegBound`, `decodeSyscallArgs`)
- 11 theorem anchors (round-trip ×4 including `decodeMsgInfo_roundtrip`, `decode_components_roundtrip`, `encode_decode_roundtrip`; determinism; error-iff ×2; always-ok; bounds-iff ×2)
- WS-K-A additions (v0.16.0): `decodeMsgRegs_length` theorem, `msgRegs` field grep in Types.lean; `#check` anchors for length/composition. Note: `encodeMsgRegs` definition and `decodeMsgRegs_roundtrip` theorem were removed in W3-H (v0.22.14) as dead code.

**Completed CdtNodeId cleanup (WS-J1-F, v0.15.10):**

- `CdtNodeId` — typed wrapper structure (replacing `abbrev CdtNodeId := Nat`) with full instance suite (`DecidableEq`, `Hashable`, `LawfulHashable`, `EquivBEq`, `LawfulBEq`, `Repr`, `ToString`, `Inhabited`, `ofNat`/`toNat`)
- All 16 kernel identifiers are now typed wrappers with explicit HashMap/HashSet instances
- `SystemState` field defaults updated (`cdtNextNode := ⟨0⟩`), monotone allocator updated (`⟨node.val + 1⟩`)
- Test literals in `NegativeStateSuite.lean` migrated from bare `Nat` to explicit constructor syntax
- **WS-J1 portfolio fully completed**

**WS-K full syscall dispatch completion (v0.16.0–v0.16.8, PORTFOLIO COMPLETE):**

WS-K extends the WS-J1 decode layer to complete the full syscall surface.

**Completed — K-A (v0.16.0):** `SyscallDecodeResult.msgRegs` field added with
`Array RegValue` type and `#[]` default. `decodeSyscallArgs` updated to
validate-and-read message registers in a single `Array.mapM` pass.
`decodeMsgRegs_length` theorem proves output size equals layout size.
`decodeMsgRegs_roundtrip` and extended `decode_components_roundtrip` proved.
`encodeMsgRegs` identity helper was added for proof surface completeness (removed in W3-H v0.22.14 as dead code).

**Completed — K-B (v0.16.1), extended WS-Q1:** `SyscallArgDecode.lean` defines per-syscall typed
argument structures (`CSpaceMintArgs`, `CSpaceCopyArgs`, `CSpaceMoveArgs`,
`CSpaceDeleteArgs`, `LifecycleRetypeArgs`, `VSpaceMapArgs`, `VSpaceUnmapArgs`,
`ServiceRegisterArgs`, `ServiceRevokeArgs`, `ServiceQueryArgs`)
and total decode functions via shared `requireMsgReg` bounds-checked helper.
7 determinism theorems (trivially `rfl`), 7 error-exclusivity theorems
(decode fails iff `msgRegs.size < required`), `requireMsgReg_error_iff` and
`requireMsgReg_ok_iff` helper theorems. Zero sorry/axiom.

**Completed — K-C (v0.16.2):** All 4 CSpace syscalls (`cspaceMint`,
`cspaceCopy`, `cspaceMove`, `cspaceDelete`) wired through `dispatchWithCap`
using decoded message register arguments from `SyscallArgDecode`. Signature
of `dispatchWithCap` changed from `SyscallId` to `SyscallDecodeResult`.
4 delegation theorems proved: `dispatchWithCap_cspaceMint_delegates`,
`dispatchWithCap_cspaceCopy_delegates`, `dispatchWithCap_cspaceMove_delegates`,
`dispatchWithCap_cspaceDelete_delegates`. All 3 existing soundness theorems
compile unchanged. Zero sorry/axiom.

**Completed — K-D (v0.16.3):** Lifecycle and VSpace syscall dispatch —
all 3 remaining `.illegalState` stubs in `dispatchWithCap` replaced with full
dispatch logic. `objectOfTypeTag` (6-arm match, type tag → default
`KernelObject`, dedicated `invalidTypeTag` error variant for unrecognized tags)
with determinism and error-exclusivity theorems.
`lifecycleRetypeDirect` accepts pre-resolved capability (avoiding double
`cspaceLookupSlot`), with equivalence theorem to `lifecycleRetypeObject`.
`PagePermissions.ofNat`/`toNat` bitfield codec with `native_decide` round-trip
proof. `vspaceMapPageChecked` used for bounds-safe dispatch. 3 delegation
theorems proved: `dispatchWithCap_lifecycleRetype_delegates`,
`dispatchWithCap_vspaceMap_delegates`, `dispatchWithCap_vspaceUnmap_delegates`.
All 13 syscalls now fully dispatch. Zero sorry/axiom. 18 new Tier 3 anchors.

**K-E (v0.16.4; updated WS-Q1) — IPC message population:**
*(WS-Q1: `ServiceConfig` and service start/stop dispatch removed — registry-only model.)*
`extractMessageRegisters` converts `Array RegValue` → `Array Nat` (matching
`IpcMessage.registers` type) with triple bound (`info.length`, `maxMessageRegisters`,
`msgRegs.size`). IPC dispatch arms (`.send`, `.call`, `.reply`) populate message
bodies from decoded registers. Proved: `extractMessageRegisters_length` (result
size ≤ `maxMessageRegisters`), `extractMessageRegisters_ipc_bounded` (constructed
`IpcMessage` satisfies `bounded`), `extractMessageRegisters_deterministic`. 3
delegation theorems: `dispatchWithCap_send_uses_withCaps`,
`dispatchWithCap_call_uses_withCaps`, `dispatchWithCap_reply_populates_msg`. All
existing soundness theorems compile unchanged. Zero sorry/axiom.

**Completed — K-F (v0.16.5) — Proofs: round-trip, preservation, and NI integration:**
7 encode functions (`encodeCSpaceMintArgs` through `encodeVSpaceUnmapArgs`) completing
encode/decode symmetry. 7 round-trip theorems via structure eta reduction (`rcases + rfl`)
with `decode_layer2_roundtrip_all` composed conjunction. `extractMessageRegisters_roundtrip`
closes layer-1 extraction gap. `dispatchWithCap_layer2_decode_pure` proves decode
functions depend only on `msgRegs` (two results with same `msgRegs` produce same decode).
`dispatchWithCap_preservation_composition_witness` structural preservation theorem.
`retypeFromUntyped_preserves_lowEquivalent` NI theorem (two-stage store composition).
`syscallNI_coverage_witness` witnesses decode-error NI step availability, step→trace
composition, and `step_preserves_projection` totality over all 33 constructors.
Zero sorry/axiom.

**Completed — K-G (v0.16.7) — Lifecycle NI proof completion and deferred proof resolution:**
`cspaceRevoke_preserves_projection` extracted as standalone theorem for compositional reuse.
`lifecycleRevokeDeleteRetype_preserves_projection` chains projection preservation across
three sub-operations (`cspaceRevoke`, `cspaceDeleteSlot`, `lifecycleRetypeObject`).
`lifecycleRevokeDeleteRetype_preserves_lowEquivalent` two-run NI theorem completes the
deferred `lifecycleRevokeDeleteRetype` NI proof. `NonInterferenceStep` extended with
`lifecycleRevokeDeleteRetype` constructor (34 total). `syscallNI_coverage_witness` updated
to reflect 34-constructor exhaustive match. Zero sorry/axiom.

**Completed — K-H (v0.16.8) — Documentation sync and workstream closeout:**
All project documentation synchronized with WS-K implementation. Metrics
regenerated (`docs/codebase_map.json`). Version bumped to v0.16.8.
WS-K portfolio fully complete (K-A through K-H, v0.16.0–v0.16.8).
See [workstream plan](../dev_history/audits/AUDIT_v0.15.10_SYSCALL_COMPLETION_WORKSTREAM_PLAN.md).

### WS-K proof surface summary

The WS-K portfolio delivered 44+ new theorems across 4 proof categories:

**Layer-2 round-trip proofs** (SyscallArgDecode.lean, K-F):
- `encodeCSpaceMintArgs`/`decodeCSpaceMintArgs` round-trip (requires `rights.valid` + `badge.valid`; Y1-D: `ofNat` decode masks at boundary) (and 9 analogous pairs, WS-Q1: +`ServiceRegisterArgs`, `ServiceRevokeArgs`, `ServiceQueryArgs`)
- `decode_layer2_roundtrip_all` — composed conjunction of all 10 round-trips

**Layer-1 extraction round-trip** (RegisterDecode.lean, K-F):
- `extractMessageRegisters_roundtrip` — closes layer-1 extraction gap

**Delegation theorems** (API.lean, K-C/K-D/K-E):
- 4 CSpace: `dispatchWithCap_cspaceMint_delegates`, `_cspaceCopy_delegates`, `_cspaceMove_delegates`, `_cspaceDelete_delegates`
- 3 Lifecycle/VSpace: `dispatchWithCap_lifecycleRetype_delegates`, `_vspaceMap_delegates`, `_vspaceUnmap_delegates`
- 3 IPC: `dispatchWithCap_send_uses_withCaps`, `_call_uses_withCaps`, `_reply_populates_msg`
*(WS-Q1: 2 service delegation theorems removed — `dispatchWithCap_serviceStart_uses_config`, `_serviceStop_uses_config`.)*

**Preservation and NI** (API.lean, Operations.lean, Composition.lean, K-F/K-G):
- `dispatchWithCap_layer2_decode_pure` — decode depends only on `msgRegs`
- `dispatchWithCap_preservation_composition_witness` — structural preservation
- `retypeFromUntyped_preserves_lowEquivalent` — NI for untyped retype
- `cspaceRevoke_preserves_projection` — standalone revoke projection preservation
- `lifecycleRevokeDeleteRetype_preserves_projection` — chained 3-op projection
- `lifecycleRevokeDeleteRetype_preserves_lowEquivalent` — two-run NI
- `syscallNI_coverage_witness` — exhaustive 34-constructor match

**Error-exclusivity theorems** (SyscallArgDecode.lean, K-B):
- 10 theorems: `decodeCSpaceMintArgs_error_iff` through `decodeServiceQueryArgs_error_iff` (WS-Q1: +3 service decode structures)

**Type tag and permissions** (Lifecycle/Operations.lean, Structures.lean, K-D):
- `objectOfTypeTag_type`, `objectOfTypeTag_error_iff`, `objectOfTypeTag_deterministic`
- `PagePermissions_ofNat_toNat_roundtrip`
- `lifecycleRetypeDirect_equivalence`, `lifecycleRetypeDirect_error`

## 30. WS-L3 IPC proof strengthening (v0.16.11)

WS-L3 added 22 new theorems and 1 new invariant definition to strengthen
formal assurance of the IPC dual-queue subsystem.

**L3-A: Enqueue-dequeue round-trip** (`DualQueue/Core.lean`):

- `endpointQueueEnqueue_empty_sets_head` — enqueue into empty queue sets head to enqueued thread.
- `endpointQueueEnqueue_empty_queueNext_none` — enqueue into empty queue leaves `queueNext` as `none`.
- `endpointQueueEnqueue_then_popHead_succeeds` — successfully enqueued thread can be dequeued without error.

**L3-B: Queue link integrity preservation** (`DualQueue/Core.lean`, `DualQueue/Transport.lean`):

- `endpointQueuePopHead_preserves_tcbQueueLinkIntegrity` — pop-head preserves doubly-linked list integrity.
- `endpointQueueEnqueue_preserves_tcbQueueLinkIntegrity` — enqueue preserves doubly-linked list integrity.

**L3-C: ipcState-queue consistency invariant** (`Invariant/Defs.lean`, `Invariant/Structural.lean`):

Definition:
- `ipcStateQueueConsistent` — if a thread is `blockedOnSend epId` or `blockedOnReceive epId`, then the endpoint `epId` exists in the object store.

Queue-operation preservation (L3-C1/C2):
- `endpointQueuePopHead_preserves_ipcStateQueueConsistent`
- `endpointQueueEnqueue_preserves_ipcStateQueueConsistent`
- `storeTcbQueueLinks_endpoint_forward`
- `endpointQueuePopHead_endpoint_forward`
- `endpointQueueEnqueue_endpoint_forward`

High-level IPC operation preservation (L3-C3):
- `ensureRunnable_preserves_ipcStateQueueConsistent`
- `removeRunnable_preserves_ipcStateQueueConsistent`
- `storeTcbIpcStateAndMessage_preserves_ipcStateQueueConsistent`
- `storeTcbIpcState_preserves_ipcStateQueueConsistent`
- `storeTcbPendingMessage_preserves_ipcStateQueueConsistent`
- `endpointSendDual_preserves_ipcStateQueueConsistent`
- `endpointReceiveDual_preserves_ipcStateQueueConsistent`
- `endpointReply_preserves_ipcStateQueueConsistent`

**T4-A/B/C: Compound operation ipcStateQueueConsistent preservation** (`Structural.lean`):

- `endpointCall_preserves_ipcStateQueueConsistent` — handshake + blocking paths
- `endpointReplyRecv_preserves_ipcStateQueueConsistent` — reply + receive composition
- `notificationSignal_preserves_ipcStateQueueConsistent` — wake + badge accumulation
- `notificationWait_preserves_ipcStateQueueConsistent` — consume + blocking paths
- `storeObject_notification_preserves_ipcStateQueueConsistent` — notification store helper
- `ipcInvariantFull_compositional` — convenience 5-component composition

**T4-D: endpointQueueRemoveDual dualQueueSystemInvariant preservation** (`Structural.lean`):

- `endpointQueueRemoveDual_preserves_dualQueueSystemInvariant` — **(T4-D, M-IPC-2)**
  complete sorry-free proof (1023 lines) covering all 4 paths: endpointHead+none
  (Path A), endpointHead+some (Path B), tcbNext+none (Path C, tail removal),
  tcbNext+some (Path D, mid-queue removal). Proves `dualQueueEndpointWellFormed`,
  `tcbQueueLinkIntegrity`, and `tcbQueueChainAcyclic` preservation for each path.
  Path D handles 3 simultaneously modified TCBs with 4-way case analysis in both
  forward and reverse link integrity directions.

**T4-L: Scheduler maxPriority consistency** (`RunQueue.lean`):

- `insert_maxPriority_consistency` — after insert, maxPriority = max(old, prio)

**L3-D: Tail consistency** (`DualQueue/Core.lean`):

- `endpointQueueRemoveDual_preserves_tail_of_nonTail` — removing a non-tail element preserves tail pointer.
- `endpointQueueRemoveDual_tail_update` — removing the tail element correctly updates the tail pointer.

## 31. Information-flow architecture readers' guide (WS-L5-A)

The information-flow subsystem is organized in three layers. Each layer has a
clear responsibility, and the layers compose to deliver the IF-M4 multi-step
non-interference theorem.

### Layer 1 — Policy (`InformationFlow/Policy.lean`)

The policy layer is the declarative security specification. It defines:

- **`SecurityLabel`** — a product of `Confidentiality` (low | high) and
  `Integrity` (untrusted | trusted).
- **`securityFlowsTo`** — a decidable Boolean predicate: information may flow
  from label A to label B only when both `confidentialityFlowsTo A.conf B.conf`
  and `integrityFlowsTo A.integrity B.integrity` hold.
- **`LabelingContext`** — assigns security labels to kernel objects, threads,
  endpoints, services, and (optionally) memory domains.
- **BIBA alternatives** — `bibaIntegrityFlowsTo`, `bibaSecurityFlowsTo`,
  `bibaPolicy` with reflexivity and transitivity proofs.

The policy layer contains **no state mutation and no theorems about kernel
transitions**. It is a pure, mechanically-checkable specification of who may
talk to whom.

### Layer 2 — Enforcement (`InformationFlow/Enforcement/`)

The enforcement layer wraps kernel operations with policy checks.

**Wrappers** (`Enforcement/Wrappers.lean`): each wrapper embeds a single
`securityFlowsTo` check before delegating to the underlying unchecked operation.
If the policy denies the flow, the wrapper returns `KernelError.flowDenied`
without mutating state. Seven operations are wrapped:

| Wrapper | Underlying operation | Policy check |
|---------|---------------------|--------------|
| `endpointSendDualChecked` | `endpointSendDual` | sender → endpoint |
| `notificationSignalChecked` | `notificationSignal` | signaler → notification |
| `cspaceMintChecked` | `cspaceMint` | source CNode → destination |
| `cspaceCopyChecked` | `cspaceCopy` | source CNode → destination |
| `cspaceMoveChecked` | `cspaceMove` | source CNode → destination |
| `endpointReceiveDualChecked` | `endpointReceiveDual` | receiver → endpoint |
*(WS-Q1: `serviceRestartChecked` row removed — service lifecycle simplified.)*

**Soundness** (`Enforcement/Soundness.lean`): for each wrapper, two theorems:

1. **Transparency**: when policy allows, the wrapper produces the same result
   as the unchecked operation (e.g., `notificationSignalChecked_eq_notificationSignal_when_allowed`).
2. **Safety**: when policy denies, the wrapper returns `flowDenied` and the
   state is unchanged (e.g., `notificationSignalChecked_flowDenied`).

### Layer 3 — Invariant (`InformationFlow/Projection.lean`, `Invariant/`)

The invariant layer proves that all kernel operations respect non-interference.

**Projection** (`Projection.lean`): defines `ObservableState` — what a
security-cleared observer can see. Fields include filtered objects, runnable
threads, current thread, services, active domain, IRQ handlers, object index,
domain timing metadata, and machine registers. Machine timer and memory are
deliberately excluded (covert timing channel risk and pending VSpace domain
ownership model, respectively).

**Operations** (`Invariant/Operations.lean`): per-operation NI proofs. Each
kernel primitive (CSpace CRUD, lifecycle retype/revoke, IPC send/receive/reply,
scheduler transitions, notification signal/wait, service start/stop) has a
`*_preserves_lowEquivalent` theorem proving that operating on a non-observable
target does not change the observable state for any observer.

**Composition** (`Invariant/Composition.lean`): the `NonInterferenceStep`
inductive (34 constructors, one per kernel operation with domain-separation
hypotheses) plus the primary theorems:

- `composedNonInterference_step` — single-step IF-M4.
- `composedNonInterference_trace` — multi-step IF-M4 over arbitrary traces.

**Helpers** (`Invariant/Helpers.lean`): shared proof infrastructure. The core
pattern is `storeObject_at_unobservable_preserves_lowEquivalent` — mutations to
objects outside the observer's clearance are filtered out by projection.

### Cross-layer connections

```
┌─────────────────────────────────────────────────────┐
│ Layer 1: Policy.lean                                │
│   SecurityLabel, securityFlowsTo, LabelingContext   │
│   (pure decidable specification)                    │
└────────────────────┬────────────────────────────────┘
                     │ embeds securityFlowsTo check
                     ▼
┌─────────────────────────────────────────────────────┐
│ Layer 2: Enforcement/Wrappers.lean + Soundness.lean │
│   7 policy-gated wrappers (incl. registerServiceChecked) │
│   theorems (only safe calls proceed)                │
└────────────────────┬────────────────────────────────┘
                     │ safe calls reach the kernel
                     ▼
┌─────────────────────────────────────────────────────┐
│ Layer 3: Projection.lean + Invariant/*              │
│   ObservableState projection → per-op NI proofs →   │
│   composedNonInterference_trace (IF-M4)             │
└─────────────────────────────────────────────────────┘
```

**Source files** (relative to `SeLe4n/Kernel/`):

- `InformationFlow/Policy.lean` — security label lattice
- `InformationFlow/Enforcement/Wrappers.lean` — policy-gated wrappers
- `InformationFlow/Enforcement/Soundness.lean` — wrapper correctness
- `InformationFlow/Projection.lean` — observable state definition
- `InformationFlow/Invariant/Helpers.lean` — shared frame lemmas
- `InformationFlow/Invariant/Operations.lean` — per-operation NI proofs
- `InformationFlow/Invariant/Composition.lean` — trace-level IF-M4

## 32. WS-Q3 IntermediateState formalization (v0.17.9)

WS-Q3 introduces the builder-phase state model: a dependently-typed wrapper
around `SystemState` that carries four invariant witnesses through every
construction step, ensuring all hash tables, per-object structures, and
lifecycle metadata are well-formed at all times during boot.

### Q3-A: IntermediateState type (`Model/IntermediateState.lean`)

Definitions:

- `perObjectSlotsInvariant` — for all CNodes in `objects`, `cn.slotsUnique` holds
  (invExt + size < capacity + 4 ≤ capacity).
- `perObjectMappingsInvariant` — for all VSpaceRoots in `objects`,
  `vs.mappings.invExt` holds.
- `IntermediateState` — structure carrying `SystemState` + 4 proof witnesses:
  `hAllTables` (16 maps + 2 sets satisfy `invExt`), `hPerObjectSlots`,
  `hPerObjectMappings`, `hLifecycleConsistent`.
- `mkEmptyIntermediateState` — constructs empty `IntermediateState` from
  `default` SystemState with all invariants proved vacuously
  (`RHTable.getElem?_empty`).
- `mkEmptyIntermediateState_valid` — 4-conjunct validity theorem for the empty state.

### Q3-B: Builder operations (`Model/Builder.lean`)

Seven builder operations, each taking and returning `IntermediateState` with
all four invariant witnesses preserved:

| Builder Op | Mutates | Key proof obligation |
|-----------|---------|---------------------|
| `Builder.registerIrq` | `irqHandlers` | `allTablesInvExt` via `RHTable_insert_preserves_invExt` |
| `Builder.registerService` | `services` | `allTablesInvExt` via `RHTable_insert_preserves_invExt` |
| `Builder.addServiceGraph` | `services` | `allTablesInvExt` via `RHTable_insert_preserves_invExt` |
| `Builder.createObject` | `objects`, `lifecycle.objectTypes` | `allTablesInvExt` + per-object by-cases on id equality |
| `Builder.deleteObject` | `objects`, `lifecycle.objectTypes` | `allTablesInvExt` via `RHTable_erase_preserves_invExt` |
| `Builder.insertCap` | `objects` (CNode update) | per-object `slotsUnique` + capacity ≥ 4 after insert |
| `Builder.mapPage` | `objects` (VSpaceRoot update) | per-object `mappings.invExt` preservation |

Helper theorem: `insert_capacity_ge4` — capacity bound monotonicity through
`RHTable.insert` (via `insertNoResize_capacity` + `resize_fold_capacity`).

Per-object proof pattern: by-cases on `id = oid` with `RHTable_getElem?_eq_get?`
normalization to convert between `[k]?` and `.get?` notations.

### Q3-C: Boot sequence (`Platform/Boot.lean`)

- `PlatformConfig` — platform configuration: `irqTable : Array IrqEntry`,
  `initialObjects : Array ObjectEntry`.
- `IrqEntry` — `(irq : Irq, handler : ObjId)`.
- `ObjectEntry` — `(id : ObjId, obj : KernelObject)` + proof obligations for
  CNode `slotsUnique` and VSpaceRoot `mappings.invExt`.
- `bootFromPlatform` — folds IRQs then objects over empty `IntermediateState`.
- `bootFromPlatform_valid` — master validity: all 4 invariant witnesses hold
  after boot.
- `bootFromPlatform_deterministic` — determinism: identical configs produce
  identical states.
- `bootFromPlatform_empty` — identity: empty config yields empty state.

### Q5: FrozenSystemState + Freeze (`Model/FrozenState.lean`)

Phase Q5 defines the frozen execution-phase state representation and the
`freeze` transformation from `IntermediateState` (builder phase) to
`FrozenSystemState` (execution phase).

#### Q5-A: FrozenMap and FrozenSet

- `FrozenMap κ ν` — dense `Array ν` value store + `RHTable κ Nat` index
  mapping. Runtime bounds-checked `get?` (safe-by-construction), `set`
  (update existing key only), `contains`, `fold`.
- `FrozenSet κ` — `FrozenMap κ Unit` with `FrozenSet.mem` membership check.
- `freezeMap` — converts `RHTable κ ν` to `FrozenMap κ ν` via fold over
  `RHTable.toList`, building dense array + index simultaneously.

Key theorems:
- `toList_empty` — `toList` on an empty RHTable yields `[]`,
- `freezeMap_empty` — freezing empty RHTable yields empty FrozenMap (via `toList_empty`),
- `freezeMap_data_size` — `fm.data.size = rt.toList.length`,
- `frozenMap_set_preserves_size` — `set` preserves `data.size`.

#### Q5-B: Per-object frozen types

- `FrozenCNode` — uses `CNodeRadix` (from Q4) for O(1) zero-hash slot lookup,
- `FrozenVSpaceRoot` — uses `FrozenMap VAddr (PAddr × PagePermissions)`,
- `FrozenKernelObject` — 7-variant inductive matching `KernelObject` (incl. `schedContext`),
- `FrozenSchedulerState` — FrozenMap-based RunQueue fields + scalar metadata
  including `configDefaultTimeSlice` (Y1-A, preserves platform-tuned value),
- `FrozenSystemState` — 19 fields mirroring `SystemState` with all `RHTable`
  fields replaced by `FrozenMap`.

Key theorem:
- `freezeObject_preserves_type` — frozen object type matches source object type.

#### Q5-C: Freeze function

- `freezeObject` — per-object freeze (CNode→CNodeRadix via Q4 bridge,
  VSpaceRoot→FrozenMap, others pass-through),
- `freezeScheduler` — scheduler state freeze,
- `freeze` — full 19-field `IntermediateState → FrozenSystemState` conversion.

Key theorems:
- `freeze_deterministic` — same input yields same output,
- `freeze_preserves_machine` — machine state unchanged,
- `freeze_preserves_objectIndex` — object index list preserved,
- `freeze_preserves_cdtEdges` — CDT edge list preserved,
- `freeze_preserves_configDefaultTimeSlice` — platform time-slice config preserved (Y1-B).

#### Q5-D: Capacity planning

- `minObjectSize` — minimum object size constant (16),
- `objectCapacity` — `currentObjects + untypedMemory / minObjectSize`.

Key theorem:
- `objectCapacity_ge_size` — capacity ≥ current object count.

### Q6: Freeze Correctness Proofs (`Model/FreezeProofs.lean`)

Phase Q6 provides machine-checked proofs that the `freeze` function preserves
lookup semantics, structural properties, and kernel invariants across the
builder→execution phase transition.

#### Q6-A: Per-Map Lookup Equivalence

- `freezeMap_get?_eq` — core theorem: `rt.get? k = (freezeMap rt).get? k` for
  any key `k` when `invExt` holds.
- 13 per-field theorems (`lookup_freeze_objects`, `lookup_freeze_objectIndexSet`,
  `lookup_freeze_irqHandlers`, `lookup_freeze_asidTable`, etc.) instantiating
  the core theorem for every `RHTable`/`RHSet` field in `SystemState`.
- Helper theorems: `toList_contains_of_get` (get? some → toList membership),
  `toList_absent_of_get_none` (get? none → toList absence),
  `toList_noDupKeys` (pairwise distinct keys in toList).

#### Q6-B: CNode Radix Lookup Equivalence

- `lookup_freeze_cnode_slots_some` — forward: `cn.slots.get? slot = some cap →
  (freezeCNodeSlots cn).lookup slot = some cap`.
- `lookup_freeze_cnode_slots_none` — backward: `cn.slots.get? slot = none →
  (freezeCNodeSlots cn).lookup slot = none`.
- Three generic fold helpers (`foldl_generic_preserves_lookup`,
  `foldl_generic_preserves_none`, `foldl_generic_establishes_lookup`)
  parameterized over the fold step function to work around Lean 4 match
  compilation identity differences.

#### Q6-C: Structural Properties

- `freeze_deterministic'` — idempotent output,
- `freezeMap_preserves_size` — data array size = toList length,
- `freezeMap_preserves_membership` — isSome agreement between source and frozen,
- `freezeMap_no_duplicates` — pairwise distinct keys in toList,
- `freezeMap_total_coverage` — every source key has valid data index.

#### Q6-D: Invariant Transfer

- `apiInvariantBundle_frozen` — existential definition: frozen state was produced
  by `freeze` from an `IntermediateState` whose `apiInvariantBundle` held.
- `freeze_preserves_invariants` — **keystone theorem**: builder-phase
  `apiInvariantBundle` transfers to frozen `apiInvariantBundle_frozen`.
- `frozen_lookup_transfer` — enabling lemma for per-invariant transfer proofs.

### Q7: Frozen Kernel Operations (`Kernel/FrozenOps/`)

**Q7-A**: `FrozenKernel` monad (`Core.lean`) — execution-phase monad over
`FrozenSystemState` with `KernelError`. Core primitives: `frozenLookupObject`,
`frozenStoreObject`, `frozenLookupTcb`, `frozenStoreTcb`, scheduler context
switch helpers. Theorems: `frozenLookupObject_state_unchanged`,
`frozenStoreObject_preserves_scheduler`, `frozenStoreObject_preserves_machine`.

**Q7-B/C**: 14 per-subsystem frozen operations (`Operations.lean`) across 5
subsystems: Scheduler (`frozenSchedule`, `frozenHandleYield`, `frozenTimerTick`),
IPC (`frozenNotificationSignal/Wait`, `frozenEndpointSend/Receive/Call/Reply`),
Capability (`frozenCspaceLookup/Mint/Delete`), VSpace (`frozenVspaceLookup`),
Service (`frozenLookupServiceByCap`).

**Q7-D**: FrozenMap set/get? commutativity proofs (`Commutativity.lean`) —
roundtrip properties, frame lemmas, structural composition theorems.

**Q7-E**: 18 frozenStoreObject frame/preservation theorems (`Invariant.lean`).

**T1-A**: `frozenQueuePushTail` queue enqueue primitive (`Core.lean`) — appends
a thread to the tail of a frozen endpoint's intrusive send or receive queue.
Two-layer architecture: `frozenQueuePushTailObjects` computes the updated
`FrozenMap` (objects only), `frozenQueuePushTail` wraps in `{ st with objects }`.
Dual-queue invariant enforced via precondition check (reject if thread already
has queue links). Structural lemma: `frozenQueuePushTail_only_modifies_objects`.

**T1-B/C/D**: Frozen IPC queue enqueue integration (`Operations.lean`) —
`frozenEndpointSend`, `frozenEndpointReceive`, and `frozenEndpointCall` now call
`frozenQueuePushTail` in the "no counterpart" blocking path, ensuring blocked
threads are visible to subsequent matching operations (fixes M-FRZ-1/2/3).

**T1-E**: 7 `frozenQueuePushTail` preservation theorems (`Commutativity.lean`) —
`scheduler`, `machine`, `asidTable`, `serviceRegistry`, `cdtEdges`,
`irqHandlers`. All derived from `frozenQueuePushTail_only_modifies_objects`.

### Q9: Integration Testing (`tests/TwoPhaseArchSuite.lean`)

14 integration tests (41 checks) verifying the full builder→freeze→execution
pipeline:

- **TPH-001**: Builder pipeline (`mkEmptyIntermediateState` → `createObject` →
  `registerIrq`), invariant preservation verified at each step.
- **TPH-003**: Freeze populated state with multiple object types, lookup
  equivalence for objects and IRQ handlers, object type preservation.
- **TPH-005**: Frozen IPC (send blocks, receive blocks, call with reply).
- **TPH-006**: Frozen scheduler tick (time slice decrement, preemption on expiry).
- **TPH-010**: Commutativity — builder mutation→freeze ≈ freeze→frozen mutation.
- **TPH-012**: Pre-allocated slot retype (FrozenMap.set on existing key).
- **TPH-014**: RunQueue operations (schedule selection, yield, no-eligible).

## WS-S Phase S1 — Trust Boundaries (v0.19.0)

Phase S1 addressed all 5 High-severity findings and Rust type-safety defects
from two comprehensive v0.18.7 audits. Key trust boundary documentation:

- **ThreadId.toObjId identity mapping** (`Prelude.lean`): `toObjId` performs no
  validation — callers must verify the returned `ObjId` references a TCB by
  pattern-matching `.tcb tcb` after lookup. The checked variant `toObjIdChecked`
  rejects sentinel values. See `ThreadId.toObjId_injective` for injectivity proof.
- **Badge forging via Mint** (`Capability/Operations.lean`): Mint authority on
  an endpoint allows minting derived capabilities with arbitrary badge values.
  Badges are opaque identifiers, not cryptographic authenticators. Authentication
  relies on CDT tracking.
- **MemoryRegion.wellFormed** (`Machine.lean`): Converted from `Bool` runtime
  check to `Prop` proof obligation with `Decidable` instance, ensuring malformed
  regions cannot be constructed without explicit proof.
- **AccessRightSet.valid** (`Model/Object/Types.lean`): `bits < 2^5` predicate
  enforced via `ofNat` masking constructor. Proofs: `ofNat_valid`, `ofNat_idempotent`.
- **Rust Cap type safety** (`rust/sele4n-sys/src/cap.rs`): `Cap::restrict()` and
  `Cap::to_read_only()` return `Result<_, CapError>` (no panics). `Restricted::RIGHTS`
  fixed to store actual runtime rights. `#![deny(unsafe_code)]` enforced on `sele4n-abi`.

See [`docs/spec/SELE4N_SPEC.md` §10.1](../spec/SELE4N_SPEC.md) for the canonical
trust boundary specification.

## 23. Hardware preparation — memory scrubbing and TLB enforcement (WS-S Phase S6)

**Memory scrubbing** (`Machine.lean`, `Lifecycle/Operations.lean`):
- `zeroMemoryRange` — zeros a contiguous physical memory range.
- `memoryZeroed` — postcondition predicate asserting all bytes in range are zero.
- `scrubObjectMemory` — composes `zeroMemoryRange` for an object's backing memory.
- Preservation: `scrubObjectMemory_preserves_lifecycleInvariantBundle` (trivial —
  only modifies `machine.memory`, lifecycle invariants are over `objects`/`lifecycle`).
- NI: `scrubObjectMemory_preserves_lowEquivalent` — scrubbing non-observable
  targets preserves low-equivalence.

**TLB flush enforcement** (`Architecture/VSpace.lean`, `Kernel/API.lean`):
- Production API dispatch uses `vspaceMapPageCheckedWithFlush` and
  `vspaceUnmapPageWithFlush` exclusively (S6-A).
- Unflushed variants (`vspaceMapPage`, `vspaceUnmapPage`) documented as
  internal proof decomposition helpers with explicit warnings (S6-B).

**Device tree abstraction** (`Platform/DeviceTree.lean`):
- `DeviceTree` structure — platform-independent board configuration.
- `DeviceTree.fromBoardConstants` — static construction from hardcoded constants.
- `DeviceTree.fromDtb` — stub for future DTB parsing (WS-T).
- `rpi5DeviceTree` — RPi5 instance with validation proof (`rpi5DeviceTree_valid`).

## 24. SchedContext type foundation (WS-Z Phase Z1)

**Scheduling Context** (`Kernel/SchedContext/Types.lean`) — first-class kernel
object for Constant Bandwidth Server (CBS) scheduling. Threads bind to a
SchedContext to receive CPU bandwidth reservations independent of thread priority.

**Typed identifiers** (`Prelude.lean`):
- `SchedContextId` — typed wrapper with `Hashable`, `LawfulHashable`,
  `EquivBEq`, `LawfulBEq` instances.
- `toObjId`/`ofObjId` — round-trip conversions with `toObjId_injective` proof.
- `sentinel`/`isReserved`/`valid` — sentinel value 0, reservation predicate.

**CBS primitives** (`Kernel/SchedContext/Types.lean`):
- `Budget` — CPU time in ticks with saturating decrement (`consume`) and
  ceiling refill (`refill`).
- `Period` — replenishment period (must be > 0).
- `Bandwidth` — budget/period pair with `utilizationPerMille` accessor.
- `ReplenishmentEntry` — (amount, eligibleAt) for CBS replenishment queue.
- `maxReplenishments` = 8 — bounded replenishment list.

**SchedContext structure** — 11 fields: `scId`, `budget`, `period`, `priority`,
`deadline`, `domain`, `budgetRemaining`, `periodStart`, `replenishments`,
`boundThread`, `isActive`.
- `SchedContext.wellFormed` — period > 0 ∧ budget ≤ period ∧
  budgetRemaining ≤ budget ∧ replenishments.length ≤ maxReplenishments.
- `SchedContext.empty` — default constructor satisfying `wellFormed`.
- `SchedContext.mkChecked` — validated constructor returning `Option`.

**Thread binding** (`Model/Object/Types.lean`):
- `SchedContextBinding` — `unbound | bound scId | donated scId originalOwner`.
- `TCB.schedContextBinding` field (defaults to `.unbound`).
- `threadSchedulingParams` — migration bridge accessor resolving effective
  scheduling parameters from bound SchedContext or falling back to legacy
  TCB fields.

**Kernel object integration** (`Model/Object/Structures.lean`, `FrozenState.lean`):
- `KernelObject.schedContext` — 7th variant (tag 6).
- `KernelObjectType.schedContext` — type enum extension.
- `FrozenKernelObject.schedContext` — frozen representation (passthrough).
- `freezeObject_schedContext_passthrough` — freeze is identity for SchedContext.
- `objectTypeAllocSize` — 256 bytes for SchedContext.
- Pattern match exhaustiveness updated across ~24 files (~150 match arms).

## 25. CBS Budget Engine (WS-Z Phase Z2)

**CBS operations** (`Kernel/SchedContext/Budget.lean`) — pure-function budget
management for Constant Bandwidth Server scheduling. All operations are total,
deterministic, and produce `SchedContext` values suitable for machine-checked
invariant proofs.

**Budget consumption and exhaustion**:
- `consumeBudget` — saturating decrement of `budgetRemaining` by `ticks`.
  Proof: `consumeBudget_budgetRemaining_le` (result ≤ input).
- `isBudgetExhausted` — predicate for zero remaining budget.

**Replenishment scheduling**:
- `mkReplenishmentEntry` — creates entry eligible at `currentTime + period`.
  Proof: `mkReplenishmentEntry_amount_eq`.
- `truncateReplenishments` — bounds list to `maxReplenishments` via `List.drop`.
  Proof: `truncateReplenishments_length_le`.
- `scheduleReplenishment` — composes entry creation + truncation.

**Replenishment processing**:
- `partitionEligible` — partitions list by `eligibleAt ≤ currentTime`.
  Proof: `partitionEligible_eligible_sublist`.
- `sumReplenishments` — recursive sum of entry amounts.
  Proofs: `sumReplenishments_nil`, `sumReplenishments_cons`.
- `applyRefill` — adds refill amount capped at budget ceiling.
  Proof: `applyRefill_le_budget`.
- `processReplenishments` — composes partition → sum → refill.

**CBS deadline and combined operations**:
- `cbsUpdateDeadline` — sets `deadline := currentTime + period` on
  replenishment after exhaustion.
- `cbsBudgetCheck` — combined per-tick entry point returning
  `(updatedSc, wasPreempted)`.
- `admissionCheck` — total utilization ≤ 1000 per-mille.

**Invariant definitions** (`Kernel/SchedContext/Invariant/Defs.lean`):
- `budgetWithinBounds` — `budgetRemaining ≤ budget ≤ period`.
- `replenishmentListWellFormed` — bounded length, no zero-amount entries.
- `replenishmentAmountsBounded` — each entry's amount ≤ configured budget.
- `schedContextWellFormed` — 4-conjunct bundle: `wellFormed ∧ budgetWithinBounds ∧ replenishmentListWellFormed ∧ replenishmentAmountsBounded`.

**Preservation theorems** (16 per-sub-invariant + 1 bundled composite,
composing into `cbsBudgetCheck_preserves_schedContextWellFormed`):
- `consumeBudget_preserves_{budgetWithinBounds, wellFormed, replenishmentListWellFormed, replenishmentAmountsBounded}`
- `processReplenishments_preserves_{budgetWithinBounds, wellFormed, replenishmentListWellFormed, replenishmentAmountsBounded}`
- `scheduleReplenishment_preserves_{replenishmentListWellFormed, wellFormed, budgetWithinBounds, replenishmentAmountsBounded}`
- `cbsUpdateDeadline_preserves_{budgetWithinBounds, wellFormed, replenishmentListWellFormed, replenishmentAmountsBounded}`

**Bandwidth theorems**:
- `totalConsumed` — accumulator summing replenishment amounts in a time window.
- `totalConsumed_le_max_budget` — core bound: consumption ≤ `maxReplenishments × budget`.
- `cbs_single_period_bound` — single-period specialization of the core bound.
- `cbs_bandwidth_bounded` — multi-period isolation: consumption over any window
  bounded by `maxReplenishments × budget`.
- Design note: the tighter bound `budget × ⌈window/period⌉` requires temporal
  ordering across scheduler ticks (deferred to Z4 scheduler integration).
