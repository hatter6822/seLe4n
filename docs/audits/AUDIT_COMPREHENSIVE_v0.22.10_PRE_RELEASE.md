# Comprehensive Pre-Release Audit — seLe4n v0.22.10

**Date**: 2026-03-28
**Scope**: All 114 Lean modules (~81,403 lines), 27 Rust files (~4,479 lines)
**Methodology**: Line-by-line automated + manual cross-reference analysis
**Auditor**: Claude Opus 4.6 (comprehensive multi-agent audit)

---

## Executive Summary

This audit covers every production Lean module and the complete Rust ABI/sys/types
implementation ahead of the first major release and benchmarking phase. The codebase
demonstrates exceptional proof hygiene (**zero sorry, zero axiom** in production code)
and strong architectural discipline. However, significant findings require attention:

| Severity | Count | Category |
|----------|-------|----------|
| **CRITICAL** | 2 | Rust ABI bugs (wrong syscall IDs, missing error variant) |
| **HIGH** | 1 | Rust-Lean KernelError enum desync |
| **MEDIUM** | 3 | Dead code bloat, unused subsystems, test coverage gaps |
| **LOW** | 2 | Documentation drift, minor code quality |

**Estimated dead code**: ~450+ definitions across 40+ files with zero external references.

---

## CRITICAL Findings

### CRIT-1: `notification_signal` uses wrong SyscallId (Rust)

**File**: `rust/sele4n-sys/src/ipc.rs:133`
**Severity**: CRITICAL — wrong syscall executed on real hardware

```rust
// CURRENT (WRONG):
pub fn notification_signal(ntfn: CPtr) -> KernelResult<SyscallResponse> {
    ...
    invoke_syscall(SyscallRequest {
        ...
        syscall_id: SyscallId::Send,  // BUG: should be NotificationSignal
    })
}
```

The function uses `SyscallId::Send` (discriminant 0) instead of
`SyscallId::NotificationSignal` (discriminant 14). On real ARM64 hardware,
this would invoke the IPC endpoint send path instead of the notification
signal path, causing:
- Wrong kernel transition (endpoint send instead of badge accumulation)
- Potential capability type mismatch errors
- Silent data corruption if an endpoint exists at the same capability address

**Fix**: Replace `SyscallId::Send` with `SyscallId::NotificationSignal`.

### CRIT-2: `notification_wait` uses wrong SyscallId (Rust)

**File**: `rust/sele4n-sys/src/ipc.rs:147`
**Severity**: CRITICAL — wrong syscall executed on real hardware

```rust
// CURRENT (WRONG):
syscall_id: SyscallId::Receive,  // BUG: should be NotificationWait
```

Same pattern as CRIT-1. Uses `SyscallId::Receive` (discriminant 1) instead of
`SyscallId::NotificationWait` (discriminant 15). Would invoke endpoint receive
instead of notification wait.

**Fix**: Replace `SyscallId::Receive` with `SyscallId::NotificationWait`.

---

## HIGH Findings

### HIGH-1: Rust `KernelError` missing `mmioUnaligned` variant

**File**: `rust/sele4n-types/src/error.rs`
**Severity**: HIGH — ABI desynchronization

The Lean `KernelError` inductive (State.lean:60) has **41 variants** ending with
`mmioUnaligned` (discriminant 40). The Rust enum has only **40 variants**, ending
at `InvalidArgument = 39`. The `mmioUnaligned` variant is missing.

**Impact**: When the kernel returns error code 40 (`mmioUnaligned`), the Rust
`from_u32(40)` returns `None`, causing `decode_response` to map it to
`InvalidSyscallNumber` — a completely unrelated error. This misreports MMIO
alignment failures as syscall number errors, making hardware debugging extremely
difficult.

**Fix**: Add `MmioUnaligned = 40` to the Rust `KernelError` enum and update
the `from_u32` match, `Display` impl, and all conformance tests (bump range
from 0–39 to 0–40).

---

## MEDIUM Findings

### MED-1: Massive dead code accumulation (~450+ unused definitions)

**Severity**: MEDIUM — code bloat, maintenance burden, slower builds

The project has accumulated significant dead code across nearly every module.
Below is the complete inventory organized by subsystem:

#### Foundation Layer (164 dead definitions)

**SeLe4n/Prelude.lean** (27 dead):
- `toObjIdChecked_eq_some_of_not_reserved` — orphan theorem, never used in any proof chain
- `toObjIdVerified_eq_checked_when_isTcb` — orphan theorem
- `default_eq_sentinel` — trivial lemma, no consumers
- `sentinel_isReserved` — trivial lemma, no consumers
- `bor_comm` — Badge commutativity, never referenced in proofs
- `bor_idempotent` — Badge idempotence, never referenced in proofs
- `ofNatMasked_lt_eq` — arithmetic helper, no consumers
- `get_returns_state`, `set_replaces_state`, `modify_applies_function` — KernelM monad laws, never used
- `liftExcept_ok`, `liftExcept_error`, `throw_errors` — monad combinator proofs, never used
- `pure_bind_law`, `bind_pure_law`, `bind_assoc_law` — monad associativity proofs, never used
- `RHTable_contains_iff_get_some`, `RHTable_not_contains_iff_get_none` — RHTable bridge lemmas, no consumers
- `RHTable_contains_insert_self`, `RHTable_contains_erase_self` — RHTable bridge lemmas, no consumers
- `RHTable_erase_preserves_invExtK`, `RHTable_insert_preserves_invExtK` — invExtK bridge lemmas, no consumers
- `RHTable_filter_preserves_invExtK`, `RHTable_filter_preserves_key` — filter bridge lemmas, no consumers
- `RHTable_filter_filter_getElem?` — filter composition lemma, no consumers
- `RHTable_size_insert_bound`, `RHTable_size_erase_bound` — size bound lemmas, no consumers

**SeLe4n/Machine.lean** (40 dead):
- `arm64GPRCount` — constant, never referenced outside definition
- `isValidDec_iff` — decidability lemma, no consumers
- `RegName.toNat_ofNat`, `RegName.ofNat_toNat`, `RegName.ofNat_injective` — roundtrip/injectivity proofs, unused
- `RegValue.toNat_ofNat`, `RegValue.ofNat_toNat`, `RegValue.ofNat_injective` — roundtrip/injectivity proofs, unused
- `RegisterFile.ext` — extensionality, never used in proofs
- `machineWordBounded`, `machineWordBounded_default` — machine word bound proofs, unused
- `readReg_writeReg_eq`, `readReg_writeReg_ne` — register frame lemmas, never used in kernel proofs
- `readMem_writeMem_eq`, `readMem_writeMem_ne` — memory frame lemmas, never used
- `writeReg_preserves_pc`, `writeReg_preserves_sp` — register preservation, unused
- `writeMem_preserves_regs`, `writeMem_preserves_timer` — memory preservation, unused
- `setPC_preserves_memory`, `setPC_preserves_timer` — PC preservation, unused
- `tick_preserves_regs`, `tick_preserves_memory`, `tick_timer_succ` — timer proofs, unused
- `default_registerFile_pc_zero`, `default_registerFile_sp_zero`, `default_timer_zero` — default state proofs, unused
- `wordAligned`, `pageAligned` — alignment definitions, never used
- `pageAligned_implies_wordAligned`, `wordAligned_zero`, `pageAligned_zero` — alignment proofs, unused
- `zeroMemoryRange_frame`, `zeroMemoryRange_preserves_regs`, `zeroMemoryRange_preserves_timer` — zero memory frame, unused
- `zeroMemoryRange_zero_size_memory` — edge case proof, unused
- `registerFileGPRCount_eq_registerCount_default` — constant equality, unused
- `isPowerOfTwo_spec` — power-of-two specification, unused
- `totalRAM`, `addressInMap` — RAM model definitions, never used

**SeLe4n/Model/Object/Types.lean** (28 dead):
- `ofNat_valid`, `ofNat_idempotent`, `mk_checked_valid` — AccessRightSet construction proofs, unused
- `empty_valid`, `singleton_valid`, `union_valid`, `inter_valid` — AccessRightSet validity proofs, unused
- `isWord5_of_valid` — 5-bit bounds proof, unused
- `ofList_comm`, `ofList_valid` — AccessRightSet list construction proofs, unused
- `TCB.not_lawfulBEq` — negative lawfulness proof, unused
- `freeSpace`, `canAllocate` — UntypedObject helpers, unused externally
- `empty_watermarkValid`, `empty_childrenWithinWatermark`, `empty_childrenNonOverlap` — empty untyped proofs, unused
- `empty_childrenUniqueIds`, `empty_wellFormed` — empty untyped well-formedness, unused
- `canAllocate_implies_fits`, `allocate_some_iff` — allocation specification proofs, unused
- `allocate_watermark_advance`, `allocate_offset_eq_watermark` — watermark proofs, unused
- `allocate_watermark_monotone`, `allocate_preserves_region` — monotonicity proofs, unused
- `reset_watermarkValid`, `reset_wellFormed` — reset proofs, unused
- `maxLength` — IpcMessage max length constant, unused (duplicate of `maxMessageRegisters`)
- `maxExtraCaps'` — duplicate of `maxExtraCaps`, unused

**SeLe4n/Model/Object/Structures.lean** (52 dead):
- `PagePermissions.readOnly_wxCompliant` — W^X compliance proof, unused
- `PagePermissions.ofNat?_valid/invalid/wxViolation/wxSafe` — 4 permission validation proofs, unused
- `noVirtualOverlap_trivial`, `noVirtualOverlap_empty` — VSpace overlap proofs, unused
- `lookup_eq_none_iff` — CNode lookup lemma, unused
- `VSpaceRoot.beq_sound` — BEq soundness, unused
- `resolveSlot_mask_idempotent` — slot resolution idempotence, unused
- `findFirstEmptySlot_spec/zero/none_iff` — empty slot specification proofs, unused
- `lookup_mem_of_some` — CNode lookup membership, unused
- `resolveSlot_depthMismatch`, `resolveSlot_guardMismatch_of_not_guardBounded` — error path proofs, unused
- `empty_guardBounded`, `empty_slotsUnique`, `empty_slotCountBounded` — empty CNode proofs, unused
- `mem_lookup_of_slotsUnique`, `lookup_remove_ne` — CNode manipulation lemmas, unused
- `CNode.beq_sound`, `CNode.empty_not_wellFormed` — CNode proofs, unused
- `SlotAddr` — type alias, never used
- `isChildOf`, `isParentOf`, `parentOf` — CDT navigation helpers, unused
- `removeAsChild`, `removeAsParent` — CDT removal helpers, unused
- `empty_acyclic` — CDT acyclicity for empty tree, unused
- `addEdge_preserves_edgeWellFounded_fresh` — CDT edge preservation, unused
- `addEdgeWouldBeSafe` — CDT safety check, unused
- `empty_childMapConsistent`, `addEdge_childMapConsistent` — CDT consistency proofs, unused
- `empty_parentMapConsistent`, `addEdge_parentMapConsistent` — CDT consistency proofs, unused
- `addEdge_preserves_cdtMapsConsistent` — CDT map consistency, unused
- `removeNode_parentMapConsistent`, `removeNode_childMapConsistent` — CDT removal proofs, unused
- `isAncestor` — CDT ancestor predicate, unused
- `addEdge_preserves_edgeWellFounded_noParent` — CDT edge preservation, unused
- `empty_cdtMapsConsistent`, `mk_checked_cdtMapsConsistent` — CDT consistency proofs, unused
- `descendantsOf_go_acc_subset`, `descendantsOf_go_children_found` — descendant traversal proofs, unused
- `descendantsOf_children_subset`, `descendantsOf_go_fuel_mono` — descendant proofs, unused
- `descendantsOf_go_head_children_found`, `descendantsOf_fuel_bound` — descendant proofs, unused
- `descendantsOf_fuel_sufficiency`, `descendantsOf_go_mem_children_found` — descendant proofs, unused
- `makeObjectCap` — capability constructor, unused

**SeLe4n/Model/State.lean** (17 dead):
- `CSpaceOwner` — type alias, never used
- `allTablesInvExtK_witness` — witness construction, unused
- `objectIndexBounded`, `objectCount_le_maxObjects`, `default_objectCount_le_maxObjects` — object count proofs, unused
- `storeObject_preserves_objectIndexBounded` — preservation proof, unused
- `revokeAndClearRefsState_preserves_objectIndexSet` — preservation proof, unused
- `hasServiceDependency` — dependency predicate, unused externally
- `storeCapabilityRef_lookup_eq` — frame lemma, unused
- `storeObject_asidTable_non_vspaceRoot` — frame lemma, unused
- `objectIndexSetSync`, `objectIndexSetSync_contains_of_mem` — sync definitions, unused
- `storeObject_updates_objectTypeMeta` — metadata update proof, unused
- `ownerOfSlot`, `ownedSlots` — CSpace ownership, unused
- `observedCdtEdges`, `observedCdtEdges_eq_projection` — CDT observation, unused

#### Kernel Subsystems (~140 dead definitions)

**SeLe4n/Kernel/Scheduler/RunQueue.lean** (12 dead):
- `atPriority` — priority-level accessor, unused
- `contains_false_of_not_mem` — containment lemma, unused
- `toList_filter_insert_congr` — filter congruence, unused
- `toList_nodup_of_flat_nodup` — NoDup lift lemma, unused
- `mem_toList_rotateToBack_self`, `mem_toList_rotateToBack_ne` — rotation membership proofs, unused
- `rotateToBack_membership`, `rotateToBack_maxPriority`, `rotateToBack_contains` — rotation proofs, unused
- `rotateToBack_flat_subset`, `rotateToBack_flat_superset` — rotation subset proofs, unused
- `insert_maxPriority_consistency` — priority consistency, unused

**SeLe4n/Kernel/Scheduler/Invariant.lean** (16 dead):
- `schedulerWellFormed_iff_queueCurrentConsistent` — biconditional, unused
- `queueCurrentConsistent_when_no_current` — vacuous truth case, unused
- `runQueueThreadPriorityConsistent_default` — default state proof, unused
- `default_runnableThreadsAreTCBs` — default state proof, unused
- `runnableThreadsAreTCBs_of_scheduler_objects_eq` — frame lemma, unused
- `schedulerInvariantBundleFull_to_base` — projection theorem, unused
- `schedulerInvariantBundleFull_to_contextMatchesCurrent` — projection theorem, unused
- `schedulerInvariantBundleFull_to_priorityMatch` — projection theorem, unused
- `schedulerInvariantBundleFull_to_domainTimeRemainingPositive` — projection theorem, unused
- `threadPriority_membership_consistent` — priority consistency predicate, unused
- `threadPriority_membership_consistent_empty` — empty case, unused
- `runQueueThreadPriorityConsistent_of_tpmc` — bridge theorem, unused
- `threadPriority_membership_consistent_insert` — insert preservation, unused
- `threadPriority_membership_consistent_remove` — remove preservation, unused
- `domainTimeRemainingPositive_default` — default proof, unused
- `domainTimeRemainingPositive_of_scheduler_eq` — frame lemma, unused

**SeLe4n/Kernel/Scheduler/Operations/Core.lean** (2 dead):
- `saveOutgoingContext_preserves_objects_invExt` — preservation proof, unused
- `restoreIncomingContext_establishes_context` — context restoration proof, unused

**SeLe4n/Kernel/Scheduler/Operations/Selection.lean** (2 dead):
- `isBetterCandidate_asymm` — asymmetry proof, unused
- `bucketFirst_fullScan_equivalence` — equivalence theorem, unused

**SeLe4n/Kernel/Capability/Operations.lean** (11 dead):
- `resolveCapAddressK` — alternative resolution function, unused
- `resolveCapAddress_zero_bits` — zero-bits case proof, unused
- `resolveCapAddress_result_valid_cnode` — result validity, unused
- `resolveCapAddress_guard_reject`, `resolveCapAddress_guard_match` — guard proofs, unused
- `cspaceInsertSlot_preserves_objects_invExt` — invExt preservation, unused
- `cspaceInsertSlot_rejects_occupied_slot` — rejection proof, unused
- `hasCdtChildren` — CDT children predicate, unused
- `cspaceMove_error_no_state`, `cspaceMove_ok_implies_source_exists` — move proofs, unused
- `severDerivationEdge` — CDT edge removal, unused

**SeLe4n/Kernel/Lifecycle/Operations.lean** (24 dead):
- `lifecycleRetypeAuthority` — authority check, unused
- `cleanupTcbReferences` and 4 associated proofs — TCB reference cleanup, unused
- `detachCNodeSlots` and 2 associated proofs — CNode slot detach, unused
- `lifecyclePreRetypeCleanup` and 2 associated proofs — pre-retype cleanup, unused
- `requiresPageAlignment`, `allocationBasePageAligned` — alignment checks, unused
- `scrubObjectMemory_scheduler_eq/tlb_eq/establishes_memoryZeroed/objectIndex_eq/objectIndexSet_eq` — scrub frame lemmas, unused
- `lookupUntyped` — untyped lookup, unused
- `retypeFromUntyped_error_typeMismatch/allocSizeTooSmall/regionExhausted` — error proofs, unused
- `lifecycle_storeObject_objects_ne` — frame lemma, unused
- `lifecycleRetypeObject_ok_runnable_membership/not_runnable_membership` — membership proofs, unused
- `lifecycleRetypeObject_error_illegalState/illegalAuthority` — error proofs, unused
- `lifecycleRetypeObject_success_updates_object` — success proof, unused
- `lifecycleRevokeDeleteRetype_ok_implies_authority_ne_cleanup` — authority proof, unused
- `lifecycleRetypeWithCleanup_ok_runnable_no_dangling` — dangling proof, unused
- `objectOfTypeTag_error_iff`, `objectOfTypeTag_type` — type tag proofs, unused
- `objectOfKernelType_type`, `objectOfKernelType_eq_objectOfTypeTag` — equivalence, unused
- `lifecycleRetypeDirect_eq_lifecycleRetypeObject` — equivalence, unused
- `lifecycleRetypeDirect_error_objectNotFound/illegalState/illegalAuthority` — error proofs, unused

**SeLe4n/Kernel/Service/Operations.lean** (6 dead):
- `maxServiceFuel` — fuel constant, unused
- `serviceRegisterDependency_error_self_loop` — self-loop rejection, unused
- `serviceHasPathTo_fuel_zero_is_true` — base case, unused
- `serviceHasPathTo_false_implies_not_fuel_exhaustion` — implication, unused
- `serviceBfsFuel_adequate` — fuel adequacy, unused
- `serviceRegisterDependency_rejects_if_path_or_fuel_exhausted` — rejection proof, unused

**SeLe4n/Kernel/Service/Registry.lean** (10 dead):
- `removeDependenciesOf_interfaceRegistry_eq` — frame lemma, unused
- `registerInterface_error_duplicate/success_stores/preserves_objects/preserves_services` — 4 interface proofs, unused
- `registerService_error_duplicate/error_unknown_interface/error_no_write_right` — 3 error proofs, unused
- `registerService_preserves_scheduler` — frame lemma, unused
- `revokeService_error_not_found/preserves_scheduler` — 2 proofs, unused

#### Architecture Layer (~55 dead definitions)

**SeLe4n/Kernel/Architecture/VSpace.lean** (12 dead):
- `asidBoundToRoot`, `asidBound`, `asidBoundForConfig` — ASID bound helpers, unused
- `resolveAsidRootChecked`, `resolveAsidRootChecked_eq_of_valid` — checked ASID resolution, unused
- `physicalAddressBoundForConfig`, `physicalAddressBoundForConfig_le_default` — address bounds, unused
- `vspaceMapPageCheckedWithFlushPlatform` — platform-specific map, unused
- `vspaceMapPageCheckedWithFlush_default_is_readOnly` — default proof, unused
- `tlbFlushByASID/ByPage/ByASIDPage` — TLB flush variants, unused

**SeLe4n/Kernel/Architecture/TlbModel.lean** (14 dead):
- `adapterFlushTlb_restores_tlbConsistent` — TLB consistency proof, unused
- `adapterFlushTlbByAsid_preserves_tlbConsistent` — preservation proof, unused
- `vspaceMapPage_then_flush_preserves_tlbConsistent` — composition proof, unused
- `vspaceUnmapPage_then_flush_preserves_tlbConsistent` — composition proof, unused
- `adapterFlushTlbByAsid_removes_matching/preserves_other` — filter proofs, unused
- `sequential_modifications_then_flush_preserves_tlbConsistent` — sequential proof, unused
- `adapterFlushTlbByVAddr_preserves_tlbConsistent/removes_matching/preserves_other` — 3 proofs, unused
- `vaddrFlush_after_asidFlush_no_asid_entries` — composition proof, unused
- `cross_asid_tlb_isolation` — isolation proof, unused
- `vspaceMapPageWithFlush/UnmapPageWithFlush_preserves_tlbConsistent` — 2 proofs, unused
- `tlbConsistent_of_objects_eq` — frame lemma, unused

**SeLe4n/Kernel/Architecture/VSpace.lean** (additional):
- `tlbFlushAll`, `tlbFlushAll_empty` — full TLB flush, unused
- `tlbFlushByASID_state_frame`, `tlbFlushByPage_state_frame` — state frame lemmas, unused
- `storeObject_objectIndex_eq_of_mem` — object index preservation, unused

#### Information Flow Layer (~55 dead definitions)

**SeLe4n/Kernel/InformationFlow/Policy.lean** (35 dead):
- `integrityFlowsTo_is_not_biba` — documentation theorem, unused
- `integrityFlowsTo_denies_write_up_biba_allows` — BIBA comparison, unused
- `defaultLabelingContext_all_threads_observable` — default context proof, unused
- `confidentialityFlowsTo_refl/trans/antisymm` — lattice proofs, unused
- `integrityFlowsTo_refl/trans/antisymm` — lattice proofs, unused
- `securityFlowsTo_refl/trans/antisymm` — lattice proofs, unused
- `securityFlowsTo_lattice_verified` — lattice verification theorem, unused
- `isReflexive`, `isTransitive` — DomainFlowPolicy predicates, unused
- `DomainFlowPolicy.allowAll_reflexive/transitive` — allowAll proofs, unused
- `DomainFlowPolicy.linearOrder_reflexive/transitive/wellFormed` — linearOrder proofs, unused
- `domainFlowsTo_refl/trans` — domain flow proofs, unused
- `endpointFlowCheck_fallback/override` — flow check proofs, unused
- `embedLegacyLabel_public/kernelTrusted/preserves_flow` — legacy label proofs, unused
- `liftLegacyContext` — legacy context lift, unused
- `securityLattice_reflexive/transitive` — lattice proofs, unused
- `recordDeclassification_preserves_existing/contains_new/length` — declassification proofs, unused
- `isDeclassificationAuthorized_not_reflexive` — auth proof, unused
- `endpointFlowPolicyWellFormed/no_overrides` — well-formedness, unused
- `endpointFlowCheck_reflexive/transitive` — flow check proofs, unused
- `endpointPolicyRestricted/no_overrides` — restriction proofs, unused
- `endpointFlowCheck_restricted_subset` — subset proof, unused

**SeLe4n/Kernel/InformationFlow/Projection.lean** (14 dead):
- `projectServiceRegistry_consistent_with_presence` — projection consistency, unused
- `capTargetObservable` — cap target observability, unused
- `projectKernelObject_idempotent/objectType` — projection proofs, unused
- `projectMemory_no_ownership` — memory projection, unused
- `acceptedCovertChannel_scheduling` — covert channel documentation, unused
- `computeObservableSet_mem/not_mem` — observable set membership, unused
- `projectObjectsFast/IrqHandlersFast/ObjectIndexFast` — fast projection variants, unused
- `projectStateFast`, `projectStateFast_eq` — fast state projection, unused
- `lowEquivalent_refl/symm/trans` — low-equivalence proofs, unused

**SeLe4n/Kernel/InformationFlow/Enforcement/Wrappers.lean** (6 dead):
- `endpointSendDualChecked_flowDenied` — flow denial proof, unused
- `enforcement_sufficiency_endpointSendDual/cspaceMint` — sufficiency proofs, unused
- `capabilityOnlyOperations` — capability operations list, unused
- `enforcementBoundaryComplete_counts` — boundary count, unused
- `enforcementBoundary_names_nonempty` — non-emptiness proof, unused

#### Data Structures Layer (~45 dead definitions)

**SeLe4n/Kernel/FrozenOps/Core.lean** (8 dead):
- `frozenLookupEndpoint/Notification/CNode` — typed lookup helpers, unused
- `frozenStoreEndpoint/Notification` — typed store helpers, unused
- `frozenQueuePushTailObjects` — queue push objects, unused
- `frozenStoreObject_preserves_scheduler/machine` — frame lemmas, unused

**SeLe4n/Kernel/FrozenOps/Operations.lean** (5 dead):
- `frozenChooseThread` — frozen scheduler selection, unused
- `frozenCspaceLookupSlot` — frozen CSpace lookup, unused
- `frozenOpCoverage/count/exhaustive` — coverage documentation theorems, unused

**SeLe4n/Kernel/FrozenOps/Commutativity.lean** (16 dead):
- `frozenMap_set_get?_same` — set/get roundtrip, unused
- `FrozenMap.set_indexMap_eq` — index map equality, unused
- `frozenStoreObject_preserves_irqHandlers/asidTable/serviceRegistry` — 3 frame lemmas, unused
- `FrozenMap.set_data_size/set_contains_eq` — frozen map proofs, unused
- `frozenStoreObject_preserves_objectTypes/capabilityRefs/interfaceRegistry/objectIndexSet` — 4 frame lemmas, unused
- `frozenQueuePushTail_preserves_scheduler/machine/asidTable/serviceRegistry/cdtEdges/irqHandlers` — 6 frame lemmas, unused

**SeLe4n/Kernel/RobinHood/Core.lean** (2 dead):
- `nextIndex_lt` — index bound proof, unused externally
- `RHTable.resize_preserves_len` — resize length preservation, unused

**SeLe4n/Kernel/RobinHood/Bridge.lean** (12 dead):
- `RHTable.beq_symmetric` — BEq symmetry, unused
- `RHTable.getElem?_eq_some_getElem` — getElem bridge, unused
- `RHTable.fold_eq_slots_foldl` — fold equivalence, unused
- `RHTable.size_filter_le_capacity/insert_size_lt_capacity/erase_size_lt_capacity/filter_size_lt_capacity` — 4 size proofs, unused
- `RHTable.ofList_invExt/ofList_size_lt_capacity` — ofList proofs, unused
- `RHTable.invExtK_invExt/invExtK_size_lt_capacity/invExtK_capacity_ge4` — invExtK bridge, unused
- `RHTable.mk_invExtK/ofList_invExtK` — construction proofs, unused

**SeLe4n/Kernel/RobinHood/Set.lean** (7 dead):
- `RHSet.toList/fold/size/capacity` — set accessors, unused
- `RHSet.insert_idempotent/erase_absent_noop/mem_iff_contains` — set proofs, unused

**SeLe4n/Kernel/RadixTree/Core.lean** (1 dead):
- `extractBits_zero_width` — zero-width extraction proof, unused

**SeLe4n/Kernel/CrossSubsystem.lean** (14 dead):
- `crossSubsystemInvariantFolded/iff_folded` — folded invariant, unused
- `crossSubsystemPredicates_count` — predicate count, unused
- `registryEndpointValid_fields` — field decomposition, unused
- `regDepConsistent_disjoint_staleEndpoint/staleNotification` — disjointness, unused
- `serviceGraph_disjoint_staleEndpoint/staleNotification` — disjointness, unused
- `regDepConsistent_disjoint_regEndpointValid` — disjointness, unused
- `serviceGraph_disjoint_regEndpointValid` — disjointness, unused
- `staleEndpoint_shares_staleNotification` — overlap witness, unused
- `regEndpointValid_shares_staleEndpoint/staleNotification` — overlap witnesses, unused
- `regDepConsistent_shares_serviceGraph` — overlap witness, unused
- `crossSubsystemFieldSets_count` — field set count, unused
- `registryDependencyConsistent_frame/serviceGraphInvariant_frame/monotone` — 3 frame lemmas, unused

#### Platform Layer (~95 dead definitions)

**SeLe4n/Platform/Boot.lean** (33 dead):
- `irqsUnique/objectIdsUnique` — uniqueness predicates, unused
- `foldIrqs/foldObjects` — fold helpers, unused
- `bootFromPlatform_empty/allTablesInvExtK/perObjectSlots/perObjectMappings/lifecycleConsistent` — 5 boot proofs, unused
- `irqsUnique_empty/objectIdsUnique_empty` — empty case proofs, unused
- `PlatformConfig.wellFormed/wellFormed_empty` — well-formedness, unused
- `bootFromPlatformChecked_eq_bootFromPlatform/rejects_invalid` — checked boot proofs, unused
- `bootFromPlatform_empty_state` — empty boot state, unused
- `emptyBoot_proofLayerInvariantBundle/freeze_preserves` — empty boot invariant proofs, unused
- `bootToRuntime_invariantBridge_empty` — empty invariant bridge, unused
- `bootFromPlatform_scheduler_eq/cdt_eq/services_eq/serviceRegistry_eq` — 4 frame lemmas, unused
- `bootFromPlatform_interfaceRegistry_eq/asidTable_eq/tlb_eq/machine_eq` — 4 frame lemmas, unused
- `bootFromPlatform_capabilityRefs_eq/cdtNodeSlot_eq` — 2 frame lemmas, unused
- `bootSafeObject`, `PlatformConfig.bootSafe` — boot safety predicates, unused
- `bootFromPlatform_proofLayerInvariantBundle_general` — general invariant proof, unused
- `bootToRuntime_invariantBridge_general` — general invariant bridge, unused

**SeLe4n/Platform/DeviceTree.lean** (26 dead — **entire module is dead code**):
- `DeviceTree.fromDtb/fromDtbWithRegions/fromDtbFull/fromDtbParsed` — DTB parsing, unused
- `fdtMagic/fdtBeginNode/fdtEndNode/fdtProp/fdtNop/fdtEnd` — FDT constants, unused
- `readBE32/readBE64/readCells/readCString` — binary readers, unused
- `parseFdtHeader/FdtHeader.isValid/parseAndValidateFdtHeader/parseFdtHeader_empty` — header parsing, unused
- `extractMemoryRegions/extractMemoryRegions_truncated/empty` — region extraction, unused
- `classifyMemoryRegion/fdtRegionsToMemoryRegions` — region classification, unused
- `extractMemoryRegionsGeneral/entrySize_eq` — general extraction, unused
- `lookupFdtString/findMemoryRegProperty` — string/property lookup, unused
- `parseFdtHeader_fromDtbFull_some` — composition proof, unused

**SeLe4n/Platform/RPi5/Board.lean** (8 dead):
- `peripheralBaseLow/High` — BCM2712 address constants, unused
- `bcm2712DefaultConfig` — default config, unused
- `rpi5MemoryMapForConfig` — memory map, unused
- `virtualTimerPpiId` — timer interrupt ID, unused
- `mmioRegions` — MMIO region list, unused
- `rpi5MachineConfig_wellFormed` — well-formedness proof, unused
- `rpi5DeviceTree/rpi5DeviceTree_valid` — device tree + validation, unused

**SeLe4n/Platform/RPi5/MmioAdapter.lean** (21 dead — **entire module is dead code**):
- All 29 definitions in MmioAdapter.lean have zero external references
- `inMmioRegion/findMmioRegion/rpi5MmioRegionDescs/isDeviceAddress` — MMIO address helpers
- `mmioRead/mmioWrite/mmioWrite32/mmioWrite64/mmioReadBytes32` — MMIO operations
- `mmioWrite32W1C` — write-1-to-clear operation
- `isAligned` — alignment check
- All 12 associated proofs (rejection, frame, idempotence proofs)

#### Testing Layer (3 dead definitions)

**SeLe4n/Testing/StateBuilder.lean** (3 dead):
- `listLookup` — list lookup helper, unused
- `withMachine` — machine state builder, unused
- `buildValidated` — validated state builder, unused

#### Dead Code Summary

| Layer | Files Affected | Dead Definitions |
|-------|---------------|-----------------|
| Foundation (Prelude, Machine, Model) | 5 | ~164 |
| Kernel Subsystems | 10 | ~140 |
| Architecture | 3 | ~55 |
| Information Flow | 3 | ~55 |
| Data Structures | 8 | ~45 |
| Platform | 4 | ~88 |
| Testing | 1 | 3 |
| **Total** | **34 files** | **~450+** |

**Note**: Two entire modules (`DeviceTree.lean`, `MmioAdapter.lean`) have zero
external consumers. These contain ~50 definitions totaling ~500+ lines that
could be removed entirely if they are not planned for near-term integration.

### MED-2: Entire FrozenOps subsystem has no runtime consumers

**Files**: `SeLe4n/Kernel/FrozenOps/*.lean` (4 files, ~29 definitions)
**Severity**: MEDIUM — architectural dead weight

The FrozenOps subsystem (`Core.lean`, `Operations.lean`, `Commutativity.lean`,
`Invariant.lean`) defines frozen-state kernel operations with extensive proofs,
but nearly all definitions have zero external references. The `frozenChooseThread`,
`frozenCspaceLookupSlot`, `frozenLookupEndpoint`, etc. are never invoked by the
API layer, test suites, or any other subsystem. The commutativity proofs
(`frozenMap_set_get?_same`, frame lemmas) serve no downstream proof chain.

**Recommendation**: Either integrate FrozenOps into the main kernel transition
pipeline before release, or move to a `Future/` directory to reduce build time
and maintenance scope.

### MED-3: Monad law proofs in Prelude are orphaned

**File**: `SeLe4n/Prelude.lean`
**Severity**: MEDIUM — false confidence in proof completeness

The KernelM monad laws (`pure_bind_law`, `bind_pure_law`, `bind_assoc_law`,
`get_returns_state`, `set_replaces_state`, `modify_applies_function`,
`liftExcept_ok`, `liftExcept_error`, `throw_errors`) are proved but never
used in any downstream proof. While they are mathematically correct, their
presence suggests they form part of the proof infrastructure when in reality
no kernel invariant proof depends on them. This creates a false sense of
completeness — if the monad implementation changed, these proofs would break
but no actual invariant would be affected.

**Recommendation**: Either wire these into a `LawfulMonad` instance that
downstream proofs consume, or remove them to avoid maintenance burden.

---

## LOW Findings

### LOW-1: `MessageInfo.decode` bit-field semantics — Lean vs Rust label mask

**Files**: `SeLe4n/Model/Object/Types.lean:742`, `rust/sele4n-abi/src/message_info.rs:131`
**Severity**: LOW — no current impact, potential future divergence

The Lean `MessageInfo.decode` extracts the label with `raw >>> 9` and then
bounds-checks `label ≤ maxLabel`. The Rust `MessageInfo::decode` does the same
with `raw >> 9`. Both produce identical results. However, if `maxLabel` were
ever changed independently on either side, the decode would silently diverge.

The Rust side correctly rejects labels > `MAX_LABEL` (2^20 - 1), and the Lean
side does the same via `decide (mi.label ≤ maxLabel)`. The round-trip proofs
are solid on both sides.

**Recommendation**: Add a compile-time `const_assert!` in Rust verifying that
`MAX_LABEL` matches the Lean `maxLabel` value (currently both 2^20 - 1 = 1048575).

### LOW-2: `IpcBuffer` overflow semantics — `set_mr` silent no-op for inline indices

**File**: `rust/sele4n-abi/src/ipc_buffer.rs:86`
**Severity**: LOW — documented but potentially confusing API

`set_mr(index, value)` returns `Ok(false)` for indices 0–3 without storing
the value anywhere. The caller must separately place these in
`SyscallRequest.msg_regs`. While documented, this split interface is error-prone.
`get_mr(index)` for indices 0–3 returns `Err(InvalidArgument)`, creating an
asymmetry where set succeeds silently but get fails.

**Recommendation**: Consider returning `Err(InvalidArgument)` from `set_mr`
for indices 0–3 as well, matching the `get_mr` behavior, to make the API
consistent. Alternatively, document more prominently that `set_mr(0..3)`
is a no-op.

---

## Positive Assessment

### Proof Hygiene — Exemplary

| Metric | Result |
|--------|--------|
| `sorry` in production code | **0** |
| `axiom` declarations | **0** |
| `native_decide` uses | **6** (all justified: RPi5/Board.lean ×3, Boot.lean ×3) |
| `trivial` usage | Appropriate (case-elimination in match arms only) |
| `todo!/unimplemented!/unreachable!` in Rust | **0** |
| `unsafe` blocks in Rust | **1** (correctly isolated in `trap.rs:31`) |

The zero-sorry, zero-axiom surface across 81,403 lines of Lean is exceptional.
Every theorem is machine-checked by the Lean kernel.

### Rust Implementation — Strong

| Metric | Result |
|--------|--------|
| `#[repr(transparent)]` on all identifier newtypes | ✅ Correct |
| `#[repr(u64)]` on SyscallId | ✅ Matches Lean |
| `#[repr(u32)]` on KernelError | ✅ Matches Lean (except missing variant) |
| `#[repr(C)]` on IpcBuffer | ✅ With compile-time layout assertions |
| `#[non_exhaustive]` on KernelError | ✅ Future-proof |
| `TryFrom<u8>` for AccessRights | ✅ Validates bit range |
| Private fields on MessageInfo | ✅ Construction only via validated paths |
| `clobber_abi("C")` on ARM64 `svc` | ✅ Correct ABI clobber specification |
| Test coverage | Excellent (roundtrip, bounds, error paths, conformance) |

### Architecture — Well-Structured

- **Invariant/Operations split** consistently maintained across all subsystems
- **Deterministic semantics** — all transitions return explicit `Except KernelError`
- **Typed identifiers** — `ThreadId`, `ObjId`, `CPtr`, etc. prevent type confusion
- **Re-export hub pattern** — backward-compatible module organization
- **Cross-subsystem invariants** properly formalized in `CrossSubsystem.lean`
- **Information flow** enforcement with machine-checked non-interference proofs
- **Dual-queue IPC** with comprehensive structural invariants (acyclicity, link integrity)

### Security Model — Robust

- Capability-based access control with formal authority reduction proofs
- Information flow policy with confidentiality + integrity lattice proofs
- Non-interference formalized with projection-based low-equivalence
- Badge well-formedness enforced system-wide (word-bounded)
- Queue invariants prevent infinite loops (acyclicity) and corruption (NoDup)
- Dequeue-on-dispatch coherence prevents current-thread conflicts
- Register decode is total with explicit error returns (no undefined behavior)

---

## Rust Conformance Cross-Check

### SyscallId mapping (Lean → Rust): ✅ PASS

| Lean variant | Lean discriminant | Rust variant | Rust discriminant | Match |
|---|---|---|---|---|
| send | 0 | Send | 0 | ✅ |
| receive | 1 | Receive | 1 | ✅ |
| call | 2 | Call | 2 | ✅ |
| reply | 3 | Reply | 3 | ✅ |
| cspaceMint | 4 | CSpaceMint | 4 | ✅ |
| cspaceCopy | 5 | CSpaceCopy | 5 | ✅ |
| cspaceMove | 6 | CSpaceMove | 6 | ✅ |
| cspaceDelete | 7 | CSpaceDelete | 7 | ✅ |
| lifecycleRetype | 8 | LifecycleRetype | 8 | ✅ |
| vspaceMap | 9 | VSpaceMap | 9 | ✅ |
| vspaceUnmap | 10 | VSpaceUnmap | 10 | ✅ |
| serviceRegister | 11 | ServiceRegister | 11 | ✅ |
| serviceRevoke | 12 | ServiceRevoke | 12 | ✅ |
| serviceQuery | 13 | ServiceQuery | 13 | ✅ |
| notificationSignal | 14 | NotificationSignal | 14 | ✅ |
| notificationWait | 15 | NotificationWait | 15 | ✅ |
| replyRecv | 16 | ReplyRecv | 16 | ✅ |

### KernelError mapping (Lean → Rust): ❌ FAIL

- Variants 0–39: ✅ All match
- Variant 40 (`mmioUnaligned`): ❌ **Missing from Rust** (see HIGH-1)

### AccessRight mapping: ✅ PASS

| Lean | Bit | Rust | Bit | Match |
|---|---|---|---|---|
| read | 0 | Read | 0 | ✅ |
| write | 1 | Write | 1 | ✅ |
| grant | 2 | Grant | 2 | ✅ |
| grantReply | 3 | GrantReply | 3 | ✅ |
| retype | 4 | Retype | 4 | ✅ |

### Identifier types: ✅ PASS

All 14 Lean identifier types (`ObjId`, `ThreadId`, `CPtr`, `Slot`, `DomainId`,
`Priority`, `Deadline`, `Irq`, `ServiceId`, `InterfaceId`, `Badge`, `ASID`,
`VAddr`, `PAddr`) have corresponding `#[repr(transparent)]` Rust newtypes
wrapping `u64`.

---

## Recommendations

### Immediate (Pre-Release Blockers)

1. **Fix CRIT-1 + CRIT-2**: Change `SyscallId::Send` → `SyscallId::NotificationSignal`
   and `SyscallId::Receive` → `SyscallId::NotificationWait` in
   `rust/sele4n-sys/src/ipc.rs`.

2. **Fix HIGH-1**: Add `MmioUnaligned = 40` to `rust/sele4n-types/src/error.rs`,
   update `from_u32`, `Display`, and conformance tests.

### Short-Term (Pre-Benchmark)

3. **Dead code cleanup phase**: Remove the ~450 unused definitions identified
   in this audit. Prioritize:
   - Entire dead modules first (`DeviceTree.lean`, `MmioAdapter.lean` → move to `Future/`)
   - FrozenOps subsystem (if not needed for benchmarking)
   - Foundation layer orphan proofs (Prelude monad laws, Machine frame lemmas)
   - This will reduce build time and simplify the proof surface

4. **Add Rust compile-time ABI assertions**: Add `const_assert!` checks that
   key constants (`MAX_MSG_LENGTH`, `MAX_EXTRA_CAPS`, `MAX_LABEL`,
   `KernelError` variant count) match expected Lean values.

### Medium-Term

5. **Integrate or defer Platform modules**: `DeviceTree.lean`, `MmioAdapter.lean`,
   and many `RPi5/Board.lean` definitions are scaffolding for hardware binding
   that has no current consumer. Either connect them to the boot/runtime path
   or move them to a staging area.

6. **Wire monad laws into LawfulMonad**: The 9 monad law proofs in Prelude
   should either be consumed by a typeclass instance or removed.

---

## Files Audited

### Lean (114 files, 81,403 lines)

All files listed in `CLAUDE.md` source layout were audited via:
- Automated `sorry`/`axiom`/`native_decide`/`trivial` scanning (full codebase)
- Cross-reference dead code analysis (every `def`/`theorem`/`lemma`/`abbrev`
  checked for external usage via codebase-wide grep)
- Manual deep read of security-critical modules (IPC/Invariant/Defs.lean,
  API.lean, RegisterDecode.lean, Capability/Operations.lean)

### Rust (27 files, 4,479 lines)

All files in `rust/sele4n-types/`, `rust/sele4n-abi/`, `rust/sele4n-sys/`
were read line-by-line and audited for:
- ABI conformance (repr, discriminants, field layout)
- Unsafe code isolation
- Integer overflow/truncation
- Error handling completeness
- Cross-crate consistency

---

*End of audit report.*
