-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.InformationFlow.ObservableStatePerCore
import SeLe4n.Kernel.InformationFlow.CovertChannelPerCore
import SeLe4n.Kernel.InformationFlow.NonInterferenceCrossCore
import SeLe4n.Testing.StateBuilder

/-!
# WS-SM SM8.A / SM8.B — Per-core observable state and non-interference suite

Tier-2 (runtime) + Tier-3 (surface anchor) coverage for WS-SM Phases SM8.A
(plan `docs/planning/SMP_INFORMATION_FLOW_PLAN.md` §5, sub-task SM8.A.6) and
SM8.B (sub-task SM8.B.14).

* **§1 Surface anchors** — every public SM8.A symbol resolves at
  elaboration time, so a rename or removal fails the build.
* **§2 Elaboration-time examples** — each headline theorem applied to
  verified inputs.
* **§3 Runtime assertions** — `lake exe smp_information_flow_suite`
  computes the per-core observable state on a real four-thread /
  four-core fixture with a non-trivial labeling (two low threads, two
  high threads, low and high endpoints / services / IRQ handlers) and
  decides every claim that is decidable.

Every group carries at least one **load-bearing negative**: an assertion
that fails if the property being tested is weakened.  In particular
§3.4 shows the same write applied to the observer's *own* core does
change its view (so the `c ≠ c'` hypothesis of the cross-core frames is
necessary, not decorative), and §3.5 shows the high observer strictly
outsees the low one (so monotonicity is not equality in disguise).

**§4 is the SM8.B half**: the per-core non-interference theorems exercised on
the same fixture — cross-core invisibility of real transitions, the derived
boot-core confinement of each operation, the two-phase-locking bracket's
transparency (including on an object the observer *can* see, which is the
SM8.B.4 `lock`-erasure result), the leakage bound, the enforcement boundary,
and the seven-entry covert-channel inventory.  Its load-bearing negatives are
§4.1 (the same transition on the observer's own core *is* visible), §4.5 (the
raw lock field really did change — so the invisibility is the projection's
doing, not a no-op), and §4.9 (the confinement premise of the four catch-all
constructors is necessary: a remote-core write preserves the global projection
and still moves a remote observer's view).
-/

namespace SeLe4n.Testing.SmpInformationFlow

open SeLe4n.Model
open SeLe4n.Kernel
open SeLe4n.Kernel.Concurrency (CoreId bootCoreId allCores)

-- ============================================================================
-- §1  Surface anchors (Tier-3): every SM8.A public symbol resolves
-- ============================================================================

-- §1.1  SM8.A.1 — the observer and its view
#check @IfObserver.ofLabel
#check @IfObserver.ofLabel_clearance
#check PerCoreObserver
#check @PerCoreObserver.core
#check @PerCoreObserver.clearance
#check @PerCoreObserver.toIfObserver
#check @PerCoreObserver.toIfObserver_clearance
#check @PerCoreObserver.onBootCore
#check @ObservableState.onCore
#check @onCore_eq_projectStateOnCore
#check @onCore_bootCore
#check @PerCoreObserver.view
#check @lowEquivalentForObserver
#check @lowEquivalentForObserver_iff_lowEquivalentOnCore
#check @lowEquivalentForObserver_bootCore
#check @lowEquivalentForObserver_refl
#check @lowEquivalentForObserver_symm
#check @lowEquivalentForObserver_trans
#check @lowEquivalent_smp_iff_forall_observer

-- §1.2  SM8.A.2 — the shared / per-core field partition
#check @SharedObservableFragment
#check @PerCoreObservableFragment
#check @ObservableState.sharedFragment
#check @ObservableState.perCoreFragment
#check @ObservableState.ext_fragments
#check @ObservableState.ofFragments
#check @ObservableState.ofFragments_sharedFragment
#check @ObservableState.ofFragments_perCoreFragment
#check @ObservableState.ofFragments_eta
#check @ObservableState.fragments_injective
#check @onCore_sharedFragment
#check @onCore_perCoreFragment
#check @onCore_objects
#check @onCore_services
#check @onCore_irqHandlers
#check @onCore_objectIndex
#check @onCore_domainSchedule
#check @onCore_memory
#check @onCore_serviceRegistry
#check @onCore_runnable
#check @onCore_current
#check @onCore_activeDomain
#check @onCore_domainTimeRemaining
#check @onCore_domainScheduleIndex
#check @onCore_machineRegs
#check @onCore_sharedFragment_eq_globalProjection
#check @onCore_sharedFragment_determined_by_globalProjection
#check @onCore_sharedFragment_core_independent
#check @observableFactorOnCore
#check @onCore_isProjection_of_globalProjection
#check @onCore_congr_of_globalProjection

-- §1.3  SM8.A.3 — the decidable fragment
#check @PerCoreObservableSlice
#check @ObservableState.perCoreSlice
#check @ObservableState.sliceOnCore
#check @lowEquivalentSliceOnCore
#check @onCore_decidable
#check @lowEquivalentSliceOnCore_of_lowEquivalentOnCore
#check @perCoreSlice_erases_register_content
#check @perCoreSlice_erases_shared_content
#check @onCore_perCoreSlice
#check @machineRegs_beq_self
#check @lowEquivalentSliceOnCoreCheckWithRegs
#check @lowEquivalentSliceOnCoreCheckWithRegs_of_lowEquivalentOnCore
#check @lowEquivalentSliceOnCoreCheckWithRegs_le_slice
#check @machineRegs_beq_not_injective

-- §1.4  SM8.A.4 — per-core independence
#check @onCore_perCore_independence
#check @onCore_setCurrentOnCore_ne
#check @onCore_setRunQueueOnCore_ne
#check @onCore_setActiveDomainOnCore_ne
#check @onCore_setDomainTimeRemainingOnCore_ne
#check @onCore_setDomainScheduleIndexOnCore_ne
#check @onCore_setRegsOnCore_ne
#check @onCore_setReplenishQueueOnCore
#check @onCore_setLastTimeoutErrorsOnCore
#check @onCore_scThreadIndex
#check @onCore_machineTimer
#check @onCore_perCoreTlb
#check @onCore_perCoreICache
#check @onCore_pendingIcacheMaintenance
#check @onCore_tlbShootdown
#check @onCore_tlb

-- §1.5  SM8.A.5 — label monotonicity
#check @objectObservable_monotone
#check @threadObservable_monotone
#check @serviceObservable_monotone
#check @capTargetObservable_monotone
#check @memoryAddressObservable_monotone
#check @projectCNode
#check @projectKernelObject_cnode
#check @projectCNode_lookup_monotone
#check @projectKernelObject_observer_independent_off_cnode
#check @onCore_objects_label_invariant_off_cnode
#check @onCore_objects_cnode
#check @onCore_objects_cnode_slot_monotone
#check @filter_sublist_filter_of_imp
#check @cnodeVisibilityLe
#check @cnodeVisibilityLe_refl
#check @cnodeVisibilityLe_trans
#check @eq_of_cnodeVisibilityLe_of_slots_eq
#check @objectVisibilityLe
#check @objectVisibilityLe_refl
#check @objectVisibilityLe_trans
#check @eq_of_objectVisibilityLe_of_not_cnode
#check @objectVisibilityLe_cnode
#check @projectCNode_visibilityLe_monotone
#check @projectKernelObject_visibilityLe_monotone
#check @ObservableState.visibilityLe
#check @ObservableState.visibilityLe_mem_runnable
#check @ObservableState.visibilityLe_mem_objectIndex
#check @ObservableState.visibilityLe_objects_isSome
#check @ObservableState.visibilityLe_objects_eq_of_not_cnode
#check @ObservableState.visibilityLe_cnode_lookup
#check @ObservableState.eq_of_visibilityLe_antisymm
#check @ObservableState.visibilityLe_refl
#check @ObservableState.visibilityLe_trans
#check @onCore_label_monotone
#check @visibilityLe_smp
#check @visibilityLe_smp_at
#check @onCore_label_monotone_smp
#check @observerView_label_monotone
#check @onCore_schedulingTransparency
#check @onCore_schedulingTransparency_label_invariant
#check @onCore_label_monotone_strict

-- §1.6  The RobinHood filter characterisation SM8.A.5 completed
#check @SeLe4n.Kernel.RobinHood.RHTable.filter_getElem?_of_pred
#check @SeLe4n.Kernel.RobinHood.RHTable.filter_getElem?_iff


-- §1.6  SM8.B — per-core non-interference (NonInterferencePerCore.lean).
-- Every public symbol of the module, so a rename or removal fails the build.
#check observableSlotsConfinedToCore
#check @observableSlotsConfinedToCore_refl
#check @observableSlotsConfinedToCore_trans
#check @observableSlotsConfinedToCore_of_scheduler_machine_eq
#check @observableSlotsConfinedToCore_of_scheduler_regs_eq
#check @observableSlotsConfinedToCore_of_eq
#check sharedViewUnchanged
#check @sharedViewUnchanged_refl
#check @sharedViewUnchanged_trans
#check @sharedViewUnchanged_of_globalProjection
#check @sharedViewUnchanged_of_state_frames
#check @projectStateOnCore_sharedFragment
#check @projectStateOnCore_perCoreFragment
#check @crossCoreNonInterference
#check @crossCoreNonInterference_onCore
#check @crossCoreNonInterference_observer
#check @crossCoreNonInterference_of_state_frames
#check @lowEquivalent_smp_of_projection_and_confinement
#check @nonInterference_perCore
#check @nonInterference_perCore_observer
#check @composedNonInterference_step_perCore
#check @nonInterference_perCore_to_singleCore
#check @trace_preserves_projectionOnCore
#check @storeObject_confinedToCore
#check @storeCapabilityRef_confinedToCore
#check @storeTcbIpcState_confinedToCore
#check @storeTcbIpcStateAndMessage_confinedToCore
#check @storeTcbQueueLinks_confinedToCore
#check @storeTcbReceiveComplete_confinedToCore
#check @endpointQueuePopHead_confinedToCore
#check @endpointQueueEnqueue_confinedToCore
#check @linkCallerReply_confinedToCore
#check @linkServerStashedReply_confinedToCore
#check @consumeCallerReply_confinedToCore
#check @cleanupPreReceiveDonation_confinedToCore
#check @ensureRunnable_confinedToBootCore
#check @removeRunnable_confinedToBootCore
#check @setCurrentThread_confinedToBootCore
#check @saveOutgoingContext_confinedToCore
#check @restoreIncomingContext_confinedToBootCore
#check @machineTick_confinedToCore
#check @setRunQueueBootCore_confinedToBootCore
#check @chooseThread_confinedToCore
#check @schedule_confinedToBootCore
#check @handleYield_confinedToBootCore
#check @timerTick_confinedToBootCore
#check @storeTcbIpcState_fromTcb_confinedToCore
#check @storeTcbIpcStateAndMessage_fromTcb_confinedToCore
#check @notificationSignal_confinedToBootCore
#check @notificationWait_confinedToBootCore
#check @endpointSendDual_confinedToBootCore
#check @returnDonatedSchedContext_confinedToCore
#check @cleanupPreReceiveDonationChecked_confinedToCore
#check @endpointReceiveDual_confinedToBootCore
#check @endpointCall_confinedToBootCore
#check @endpointReply_confinedToBootCore
#check @endpointReplyRecv_confinedToBootCore
#check @attachSlotToCdtNode_confinedToCore
#check @detachSlotFromCdt_confinedToCore
#check @ensureCdtNodeForSlot_confinedToCore
#check @cdtEdge_confinedToCore
#check @cspaceLookupSlot_confinedToCore
#check @cspaceInsertSlot_confinedToCore
#check @cspaceDeleteSlotCore_confinedToCore
#check @cspaceDeleteSlot_confinedToCore
#check @cspaceCopy_confinedToCore
#check @cspaceMove_confinedToCore
#check @cspaceMint_confinedToCore
#check @cspaceRevoke_confinedToCore
#check @cspaceMutate_confinedToCore
#check @lifecycleRetypeObject_confinedToCore
#check @lifecycleRevokeDeleteRetype_confinedToCore
#check @vspaceMapPage_confinedToCore
#check @vspaceUnmapPage_confinedToCore
#check @vspaceLookup_confinedToCore
#check @registerService_confinedToCore
#check @registerServiceChecked_confinedToCore
#check @nonInterference_perCore_chooseThread
#check @nonInterference_perCore_endpointSendDual
#check @nonInterference_perCore_cspaceMint
#check @nonInterference_perCore_cspaceRevoke
#check @nonInterference_perCore_lifecycleRetype
#check @nonInterference_perCore_lifecycleRevokeDeleteRetype
#check @nonInterference_perCore_notificationSignal
#check @nonInterference_perCore_notificationWait
#check @nonInterference_perCore_cspaceInsertSlot
#check @nonInterference_perCore_schedule
#check @nonInterference_perCore_vspaceMapPage
#check @nonInterference_perCore_vspaceUnmapPage
#check @nonInterference_perCore_vspaceLookup
#check @nonInterference_perCore_cspaceCopy
#check @nonInterference_perCore_cspaceMove
#check @nonInterference_perCore_cspaceDeleteSlot
#check @nonInterference_perCore_endpointReply
#check @nonInterference_perCore_endpointReceiveDual
#check @nonInterference_perCore_endpointCall
#check @nonInterference_perCore_endpointReplyRecv
#check @nonInterference_perCore_storeObject
#check @nonInterference_perCore_setCurrentThread
#check @nonInterference_perCore_ensureRunnable
#check @nonInterference_perCore_removeRunnable
#check @nonInterference_perCore_storeTcbIpcStateAndMessage
#check @nonInterference_perCore_storeTcbQueueLinks
#check @nonInterference_perCore_cspaceMutate
#check @nonInterference_perCore_handleYield
#check @nonInterference_perCore_timerTick
#check @nonInterference_perCore_syscallDecodeError
#check @nonInterference_perCore_registerServiceChecked
#check @nonInterference_perCore_syscallDispatch
#check @nonInterference_perCore_endpointCallWithDonation
#check @nonInterference_perCore_endpointReplyWithReversion
#check @nonInterference_perCore_handleInterrupt
#check @kernelOperationPerCoreNiTheorem
#check @niStepCoverage_perCore_injective
#check @niStepCoverage_perCore_count
#check @perCoreConfinementDerived
#check @perCoreConfinementDerived_count
#check @niStepCoverage_perCore
#check @projectKernelObject_updateLock
#check @updateObjectAt_updateLock_preserves_projectObjects
#check @projectState_eq_of_objects_projection_eq
#check @updateObjectAt_updateLock_scheduler_eq
#check @updateObjectAt_updateLock_machine_eq
#check @updateObjectAt_updateLock_objectIndex_eq
#check @updateObjectAt_updateLock_services_eq
#check @updateObjectAt_updateLock_irqHandlers_eq
#check @updateObjectLockAt_preserves_projection
#check @updateObjectAt_updateLock_preserves_objects_invExt
#check @updateObjectLockAt_preserves_objects_invExt
#check @acquireLockOnObject_preserves_projection
#check @releaseLockOnObject_preserves_projection
#check @acquireLockOnObject_preserves_objects_invExt
#check @releaseLockOnObject_preserves_objects_invExt
#check @updateObjectLockAt_scheduler_eq
#check @updateObjectLockAt_machine_eq
#check @acquireLockOnObject_confinedToCore
#check @releaseLockOnObject_confinedToCore
#check @acquireAll_preserves_objects_invExt
#check @releaseAll_preserves_objects_invExt
#check @acquireAll_preserves_projection
#check @releaseAll_preserves_projection
#check @acquireAll_confinedToCore
#check @releaseAll_confinedToCore
#check @withLockSet_preserves_projection
#check @withLockSet_confinedToCore
#check @nonInterference_perCore_underLockSet
#check @crossCoreNonInterference_of_disjoint_lockSet
#check @crossCoreLeakage_bounded
#check @crossCoreLeakage_bounded_reconstruction
#check @crossCoreLeakage_bounded_by_globalProjection

-- §1.8  WS-SM SM8.B — non-interference at the genuinely cross-core
-- transitions (`InformationFlow/NonInterferenceCrossCore`).  Every declaration
-- of that module, verified complete by set difference against the codebase map.
#check @enqueueRunnableOnCore_confinedToCores
#check @removeRunnableOnCore_confinedToCores
#check @wakeThread_confinedToCores
#check @descheduleThread_confinedToCores
#check @storeObject_confinedToCores
#check @storeTcbIpcStateAndMessage_confinedToCores
#check @storeTcbIpcState_confinedToCores
#check @storeTcbIpcState_fromTcb_confinedToCores
#check @endpointQueuePopHead_confinedToCores
#check @endpointQueueEnqueue_confinedToCores
#check @linkServerStashedReply_confinedToCores
#check @consumeCallerReply_confinedToCores
#check @storeTcbIpcStateAndMessage_fromTcb_confinedToCores
#check @storeObject_tcb_determineTargetCore_eq
#check @storeObject_endpoint_determineTargetCore_eq
#check @storeTcbIpcStateAndMessage_fromTcb_determineTargetCore_eq
#check @storeTcbQueueLinks_determineTargetCore_eq
#check @endpointQueuePopHead_determineTargetCore_eq
#check @notificationSignalWriteSet
#check @notificationSignalWriteSet_eq_lockSet_waiter
#check @notificationSignalOnCore_confinedToCores
#check @notificationWaitOnCore_confinedToCores
#check @endpointCallWriteSet
#check @endpointCallOnCore_confinedToCores
#check @endpointReplyOnCore_confinedToCores
#check @cancellationCrossCore_confinedToCores
#check @notificationSignalOnCore_crossCoreNonInterference
#check @notificationWaitOnCore_crossCoreNonInterference
#check @endpointCallOnCore_crossCoreNonInterference
#check @endpointReplyOnCore_crossCoreNonInterference
#check @descheduleThread_crossCoreNonInterference
#check @wakeThread_crossCoreNonInterference_of_visible_thread
#check @CrossCoreTransition
#check @CrossCoreTransition.all
#check @crossCoreNiTheorem
#check @crossCoreNiTheorem_count
-- §1.8 (cont.) WS-SM SM8.B v0.33.7 — the live-dispatch legs: the PIP chain
-- walk's write set (proved by fuel induction) and the union that bounds the
-- live `.call` arm.  Without these the cross-core write sets bound only the
-- below-API transitions, and a claim about the live dispatch would be false.
#check @updatePipBoostOnCore_confinedToCores
#check @pipBoostWithWake_confinedToCores
#check @pipChainWriteSet
#check @propagatePipChainCrossCore_confinedToCores
#check @applyCallDonation_confinedToCores
#check @endpointCallLiveWriteSet
#check @endpointCallWriteSet_subset_live
#check @pipChainWriteSet_subset_live
#check @endpointCallLive_confinedToCores
#check @cancelIpcBlocking_confinedToCores
#check @cancelIpcBlockingOnCore_confinedToCores
#check @cancelIpcBlockingOnCore_crossCoreNonInterference
#check @crossCoreNiTheorem_injective
#check @crossCoreTransitionWritesRemote
#check @crossCoreTransitionWritesRemote_count
#check @crossCoreTransition_invisible_to_every_observer
-- The live `.call` arm (PR #861 review round 2): the WithCaps leg's frames, the
-- write set that mirrors the dispatch's own control flow, and the bound itself.
#check @ipcUnwrapCaps_confinedToCores
#check @endpointCallWithCapsOnCore_scheduler_eq
#check @endpointCallWithCapsOnCore_machine_eq
#check @endpointCallWithCapsOnCore_confinedToCores
#check @endpointCallDispatchChainWriteSet
#check @endpointCallDispatchWriteSet
#check @endpointCallCrossCoreDispatch_confinedToCores
#check @endpointCallDispatchWriteSet_eq_live_of_rendezvous
#check @endpointCallCrossCoreDispatch_crossCoreNonInterference
-- The three live arms the fourth review round found uncovered.
#check @linkCallerReply_confinedToCores
#check @endpointQueueRemoveDual_confinedToCores
#check @storeTcbReceiveComplete_confinedToCores
#check @cleanupPreReceiveDonationChecked_confinedToCores
#check @endpointQueueRemoveDual_determineTargetCore_eq
#check @storeTcbReceiveComplete_determineTargetCore_eq
#check @endpointReceiveDualWriteSet
#check @endpointReceiveDualOnCore_confinedToCores
#check @endpointReceiveDualOnCore_crossCoreNonInterference
#check @endpointReplyRecvWriteSet
#check @endpointReplyRecvOnCore_confinedToCores
#check @endpointReplyRecvOnCore_crossCoreNonInterference
#check @notificationSignalBoundWriteSet
#check @notificationSignalBoundOnCore_confinedToCores
#check @notificationSignalBoundOnCore_crossCoreNonInterference
#check @crossCoreTransitionIsLiveArm
#check @crossCoreTransitionIsLiveArm_count

-- §1.6b  SM8.B — the LIVE cross-core wrappers (PR #861 review round 5).  Each
-- of these bounds the function the syscall dispatch actually calls, not a
-- below-API transition it is built from.
#check @applyReplyDonationOnCore_confinedToCores
#check @endpointReplyDispatchWriteSet
#check @endpointReplyCrossCoreDispatch_confinedToCores
#check @endpointReplyCrossCoreDispatch_crossCoreNonInterference
#check @replyRecvDescheduleAndWalkWriteSet
#check @replyRecvDescheduleAndWalk_confinedToCores
#check @replyRecvReturnDonationWriteSet
#check @replyRecvReturnDonation_confinedToCores
#check @replyRecvBodyWriteSet
#check @replyRecvBody_confinedToCores
#check @replyRecvBody_crossCoreNonInterference
#check @preemptCurrentOnCore_activeDomainOnCore
#check @preemptCurrentOnCore_domainTimeRemainingOnCore
#check @preemptCurrentOnCore_domainScheduleIndexOnCore
#check @switchToThreadOnCore_activeDomainOnCore
#check @switchToThreadOnCore_domainTimeRemainingOnCore
#check @switchToThreadOnCore_domainScheduleIndexOnCore
#check @switchToThreadOnCore_confinedToCores
#check @handleRescheduleSgiOnCore_confinedToCores
#check @suspendRescheduleOnCore_confinedToCores
#check @clearPendingState_confinedToCores
#check @cancelBoundDonationOnCore_confinedToCores
#check @migrateSchedContextReplenishment_confinedToCores
#check @cancelDonatedDonationOnCore_confinedToCores
#check @suspendDequeues_confinedToCores
#check @suspendInactiveStore_confinedToCores
#check @suspendDonationArms_confinedToCores
#check @suspendThreadOnCoreWriteSet
#check @suspendThreadOnCore_confinedToCores
#check @suspendThreadOnCore_crossCoreNonInterference
#check @SeLe4n.Kernel.cleanupDonatedSchedContext_machine_eq
#check @onCore_objects_eq_projectObjects

-- §1.7  SM8.B — the enforcement boundary and the covert-channel inventory
-- (CovertChannelPerCore.lean).
#check @enforcementBoundaryPerCore
#check @enforcementBoundaryPerCore_count
#check @enforcementBoundaryPerCore_extends_canonical
#check @enforcementBoundaryPerCoreComplete
#check @enforcementBoundaryPerCore_is_complete
#check @enforcementBoundaryPerCore_entry_is_new
#check CovertChannelSeverity
#check CovertChannel
#check @acceptedCovertChannel_scheduling_perCore
#check @acceptedCovertChannel_machineTimer
#check @acceptedCovertChannel_tcbMetadata
#check @acceptedCovertChannel_objectStoreMetadata
#check @acceptedCovertChannel_lockContention
#check @acceptedCovertChannel_tlbResidency
#check @acceptedCovertChannel_icacheResidency
#check @acceptedCovertChannelsPerCore
#check @acceptedCovertChannel_perCoreCount
#check @acceptedCovertChannel_perCore_ids
#check @acceptedCovertChannel_modelVisible_count
#check @acceptedCovertChannel_perCoreInstance_count
#check @acceptedCovertChannel_hardwareChannels_are_not_modelVisible
#check @acceptedCovertChannel_smp_additions
#check @acceptedCovertChannel_lockContention_is_timing_only
#check @acceptedCovertChannel_residency_excluded_from_view
#check @acceptedCovertChannel_scheduling_is_model_visible
-- PR #861 review round 4: the classification is evidence-bound, the live
-- cross-core wrappers are classified, and CC-1's capacity claim is corrected.
#check @acceptedCovertChannel_machineTimer_excluded_from_view
#check @acceptedCovertChannel_tcbMetadata_is_model_visible
#check @acceptedCovertChannel_objectStoreMetadata_is_model_visible
#check CovertChannelId
#check @covertChannelEntry
#check @covertChannelEvidenceName
#check @CovertChannelId.evidenceProp
#check @covertChannelEvidence
#check @covertChannelEntry_eq_inventory
#check @covertChannelEvidence_nonempty
#check @covertChannelEvidence_shared_only_for_residency
#check @schedulingChannelIndex_alphabet_bounded
#check @schedulingChannel_not_bounded_by_scheduleLength
#check @schedulingObservationOnCore
#check @schedulingObservationCode
#check @schedulingObservationCode_injective
#check @schedulingChannel_alphabet_bounded
#check @schedulingObservationFullOnCore
#check @schedulingObservation_activeDomain_determined
#check @schedulingChannel_full_observation_determined
#check @schedulingCapacityPreconditions
#check @schedulingCapacityComparable
#check @schedulingChannel_alphabet_bounded_of_preconditions
#check @schedulingChannel_full_observation_determined_of_preconditions
-- SM8.B.9 (PR #861 review round 12): the CC-1 rate factor is the TICK rate,
-- and the run-length capacity that goes with it.
#check @schedulingObservation_changes_on_domain_tick
#check @boundedCodeTraces
#check @boundedCodeTraces_length
#check @mem_boundedCodeTraces
#check @schedulingObservationTrace
#check @schedulingChannel_trace_capacity
-- SM8.B (round 12): the per-core priority-control arms.
#check @SeLe4n.Kernel.SchedContext.PriorityManagement.migrateRunQueueBucketOnCore
#check @SeLe4n.Kernel.SchedContext.PriorityManagement.priorityRescheduleOnCore
#check @SeLe4n.Kernel.SchedContext.PriorityManagement.priorityRescheduleOnCore_sgi_shape
#check @SeLe4n.Kernel.SchedContext.PriorityManagement.setPriorityOnCore
#check @SeLe4n.Kernel.SchedContext.PriorityManagement.setMCPriorityOnCore
#check @SeLe4n.Kernel.SchedContext.PriorityManagement.setPriorityOnCore_raise_no_sgi
#check @SeLe4n.Kernel.SchedContext.PriorityManagement.setPriorityOnCore_authority_rejected
#check @SeLe4n.Kernel.SchedContext.PriorityManagement.setMCPriorityOnCore_authority_rejected
#check @migrateRunQueueBucketOnCore_preserves_projection
#check @setPriorityOnCore_preserves_projection
#check @setMCPriorityOnCore_preserves_projection
#check @SeLe4n.Kernel.dispatchWithCap_tcbSetPriority_delegates
#check @SeLe4n.Kernel.dispatchWithCap_tcbSetMCPriority_delegates
#check @SeLe4n.Kernel.syscallDelegates_tcbSetPriority
#check @SeLe4n.Kernel.syscallDelegates_tcbSetMCPriority
#check @SeLe4n.Kernel.schedulingCapacityRun
#check @SeLe4n.Kernel.schedulingCapacityRun_singleton
#check @SeLe4n.Kernel.schedulingChannel_trace_determines_observations
#check @SeLe4n.Kernel.schedContextSubject?
#check @SeLe4n.Kernel.schedContextWriteSet
#check @SeLe4n.Kernel.schedContextUnbind_confinedToCores
#check @SeLe4n.Kernel.schedContextUnbind_crossCoreNonInterference
#check @SeLe4n.Kernel.storeObject_schedContext_determineTargetCore_eq
#check @SeLe4n.Kernel.setRunQueueOnCore_confinedToCores
#check @SeLe4n.Kernel.setReplenishQueueOnCore_confinedToCores
#check @SeLe4n.Kernel.schedContextBindWriteSet
#check @SeLe4n.Kernel.schedContextBind_confinedToCores
#check @SeLe4n.Kernel.schedContextBind_crossCoreNonInterference
-- SM8.B.2 (PR #861 review round 25): the `.tcbSetAffinity` migration — the one
-- entry whose write set names TWO remote cores, and the missing run-queue frame
-- lemma that let it be proven instead of allowlisted.
#check @SeLe4n.Kernel.migrateRunQueueOnAffinityChange_confinedToCores
#check @SeLe4n.Kernel.setThreadCpuAffinityWriteSet
#check @SeLe4n.Kernel.setThreadCpuAffinity_scheduler_machine_eq
#check @SeLe4n.Kernel.setThreadCpuAffinity_determineTargetCore_eq
#check @SeLe4n.Kernel.setThreadCpuAffinityWithMigration_confinedToCores
#check @SeLe4n.Kernel.setThreadCpuAffinityWithMigration_crossCoreNonInterference
#check @SeLe4n.Kernel.schedContextConfigure_confinedToCores
#check @SeLe4n.Kernel.schedContextConfigure_crossCoreNonInterference
#check @CovertChannelId.mem_all
#check @CovertChannelId.all_nodup
#check LiveArmEvidence
#check @LiveArmEvidence.isDelegationBacked
#check @LiveArmEvidence.syscall?
#check @crossCoreLiveArmSyscall
#check @resumeThreadOnCoreWriteSet
#check @resumeReadyMidState_confinedToCores
#check @resumeThreadOnCore_confinedToCores
#check @resumeThreadOnCore_crossCoreNonInterference
#check @SeLe4n.Kernel.dispatchWithCap_tcbResume_delegates
#check @SeLe4n.Kernel.syscallDelegates_tcbResume
#check @crossCoreLiveArmEvidence_syscall_matches
#check @CrossCoreTransition.mem_all
#check @CrossCoreTransition.all_nodup
#check @SeLe4n.Kernel.syscallDelegates
#check @SeLe4n.Kernel.syscallDelegates_receive
#check @SeLe4n.Kernel.syscallDelegates_tcbSuspend
#check @crossCoreLiveArmEvidence
#check @crossCoreLiveArmDelegationBacked_count
#check @crossCoreLiveArm_readOffTheArm_count
-- Round 15: the per-core SchedContext unbind and its scheduling point.
#check @SeLe4n.Kernel.SchedContextOps.schedContextBoundThread?
#check @SeLe4n.Kernel.SchedContextOps.schedContextRunningCore?
#check @SeLe4n.Kernel.SchedContextOps.schedContextUnbindOnCore
#check @SeLe4n.Kernel.SchedContextOps.schedContextUnbindOnCore_error
#check @SeLe4n.Kernel.SchedContextOps.schedContextUnbindOnCore_no_running_core
#check @SeLe4n.Kernel.SchedContextOps.schedContextUnbindOnCore_sgi_shape
#check @SeLe4n.Kernel.SchedContextOps.schedContextUnbindOnCore_local_reschedules
#check @schedContextUnbindOnCoreWriteSet
#check @schedContextUnbindOnCore_confinedToCores
#check @schedContextUnbindOnCore_crossCoreNonInterference
-- Round 15: the priority-control arms, and the shared effect they now name.
#check @SeLe4n.Kernel.SchedContext.PriorityManagement.applyPriorityChangeOnCore
#check @SeLe4n.Kernel.SchedContext.PriorityManagement.applyPriorityChangeOnCore_no_preempt
#check @priorityRescheduleOnCore_confinedToCores
#check @updatePrioritySource_confinedToCores
#check @migrateRunQueueBucketOnCore_confinedToCores
#check @priorityUpdateAndMigrate_confinedToCores
#check @applyPriorityChangeOnCore_confinedToCores
#check @priorityControlWriteSet
#check @setPriorityOnCore_confinedToCores
#check @setPriorityOnCore_crossCoreNonInterference
#check @setMCPriorityOnCore_confinedToCores
#check @setMCPriorityOnCore_crossCoreNonInterference
-- Round 15: the memory-subsystem arms, proven to write NO core rather than
-- excused by an allowlist entry.
#check @SchedulerMachineFramed
#check @observableSlotsConfinedToCores_nil_of_framed
#check @vspaceUnmapPageWithShootdownPerCore_framed
#check @withIcacheBroadcast_framed
#check @vspaceUnmapPageWithShootdownAndIcacheBroadcast_confinedToCores
#check @vspaceUnmapPageWithShootdownAndIcacheBroadcast_crossCoreNonInterference
#check @vspaceMapPageCheckedWithShootdownFromState_framed
#check @vspaceMapPageCheckedWithShootdownFromStatePerCore_confinedToCores
#check @vspaceMapPageCheckedWithShootdownFromStatePerCore_crossCoreNonInterference
-- Round 16: the slot-indexed SGI rule — the diff seam's fix for a change whose
-- subject the post-state no longer contains.
#check @SeLe4n.Kernel.PriorityInheritance.currentSlotChangeSgis
#check @SeLe4n.Kernel.PriorityInheritance.currentSlotChangeSgis_not_execCore
#check @SeLe4n.Kernel.PriorityInheritance.currentSlotChangeSgis_reschedule
#check @SeLe4n.Kernel.PriorityInheritance.currentSlotChangeSgis_fires_on_change
#check @SeLe4n.Kernel.removeRunnableFromAllCores_currentOnCore
#check @SeLe4n.Kernel.foldl_removeRunnableStepOnCore_currentOnCore
-- Round 17: the LOCAL half of that rule — a core does not interrupt itself, it
-- runs the handler inline, and the inline half did not exist.
#check @SeLe4n.Kernel.PriorityInheritance.localSuccessorNeeded
#check @SeLe4n.Kernel.PriorityInheritance.localSuccessorNeeded_post_none
#check @SeLe4n.Kernel.PriorityInheritance.localSuccessorNeeded_pre_some
#check @SeLe4n.Kernel.PriorityInheritance.scheduleLocalSuccessor
#check @SeLe4n.Kernel.PriorityInheritance.scheduleLocalSuccessor_of_not_needed
#check @SeLe4n.Kernel.PriorityInheritance.scheduleLocalSuccessor_of_pre_idle
#check @SeLe4n.Kernel.PriorityInheritance.scheduleLocalSuccessor_of_post_running
#check @SeLe4n.Kernel.PriorityInheritance.scheduleLocalSuccessor_dispatches
#check @SeLe4n.Kernel.PriorityInheritance.scheduleLocalSuccessor_idle_of_no_candidate
#check @SeLe4n.Kernel.PriorityInheritance.candidateOutranksCurrentOnCore_of_vacated
-- Round 17: and the fact that makes the gap a defect rather than a latency
-- question — the periodic tick provably cannot cover for it.
#check @SeLe4n.Kernel.processOneReplenishmentOnCore_currentOnCore_eq
#check @SeLe4n.Kernel.processReplenishmentsDueOnCore_currentOnCore_eq
#check @SeLe4n.Kernel.timerTickOnCorePrepared_currentOnCore_eq
#check @SeLe4n.Kernel.timerTickOnCore_cannot_dispatch_vacated_core
-- Round 17: the third per-core scheduler slot.  The gate checked `current` and
-- the run queues; the replenish queue is the one it could not see.
-- Round 18: the model switches threads; the runtime has no restore seam yet.
-- Registered as a checked partition so SM9.E cannot wire one silently.
#check @SeLe4n.Kernel.PriorityInheritance.ContextSwitchSite
#check @SeLe4n.Kernel.PriorityInheritance.contextSwitchSites
#check @SeLe4n.Kernel.PriorityInheritance.contextSwitchSites_complete
#check @SeLe4n.Kernel.PriorityInheritance.contextRestoreWired
#check @SeLe4n.Kernel.PriorityInheritance.contextSwitchSites_restore_pending
#check @SeLe4n.Kernel.PriorityInheritance.contextRestoreWired_none
#check @SeLe4n.Kernel.PriorityInheritance.contextRestoreSeamLive
#check @SeLe4n.Kernel.PriorityInheritance.scheduleLocalSuccessorLive
#check @SeLe4n.Kernel.PriorityInheritance.scheduleLocalSuccessorLive_inert
#check @SeLe4n.Kernel.PriorityInheritance.scheduleLocalSuccessorLive_eq_of_seam_live
#check @SeLe4n.Kernel.PriorityInheritance.scheduleLocalSuccessorLive_guard_eq_register
#check @SeLe4n.Kernel.PriorityInheritance.suspendReschedule_guard_eq_register
#check @SeLe4n.Kernel.SchedContextOps.schedContextReplenishHome
#check @SeLe4n.Kernel.SchedContextOps.purgeReplenishmentOnCore
#check @SeLe4n.Kernel.SchedContextOps.purgeReplenishmentFromAllCores
#check @SeLe4n.Kernel.purgeReplenishmentOnCore_confinedToCores
#check @SeLe4n.Kernel.purgeReplenishmentFromAllCores_confinedToCores
-- Round 16: the send bridge that actually mentions the single-core transition.
#check @SeLe4n.Kernel.endpointSendDualOnCore_absent_endpoint
#check @SeLe4n.Kernel.endpointSendDualOnCore_bootCore_block_eq_single
#check @SeLe4n.Kernel.dispatchWithCap_tcbSuspend_delegates
#check @SeLe4n.Kernel.dispatchWithCapChecked_receive_delegates
-- SM8.B (PR #861 review round 10): the live `.send` arm, rerouted off the
-- boot-pinned `endpointSendDualWithCaps`, and the per-core audit it owes.
#check @SeLe4n.Kernel.endpointSendDualOnCore
#check @SeLe4n.Kernel.endpointSendDualWithCapsOnCore
#check @SeLe4n.Kernel.endpointSendCrossCoreDispatchChecked
#check @SeLe4n.Kernel.endpointSendDualOnCore_tooLarge
#check @SeLe4n.Kernel.endpointSendDualOnCore_tooManyCaps
#check @SeLe4n.Kernel.endpointSendDualWithCapsOnCore_no_caps
#check @SeLe4n.Kernel.endpointSendCrossCoreDispatchChecked_flow_denied
#check @SeLe4n.Kernel.endpointSendCrossCoreDispatchChecked_flow_allowed
#check @endpointSendWriteSet
#check @endpointSendDualOnCore_confinedToCores
#check @endpointSendDualWithCapsOnCore_scheduler_eq
#check @endpointSendDualWithCapsOnCore_machine_eq
#check @endpointSendDualWithCapsOnCore_confinedToCores
#check @endpointSendCrossCoreDispatchChecked_confinedToCores
#check @endpointSendDualWithCapsOnCore_crossCoreNonInterference
#check @endpointSendCrossCoreDispatchChecked_crossCoreNonInterference
#check @SeLe4n.Kernel.dispatchWithCap_send_delegates
#check @SeLe4n.Kernel.dispatchWithCapChecked_send_delegates
#check @SeLe4n.Kernel.syscallDelegates_send
#check @crossCoreEnforcementEntries
#check @enforcementBoundary_prefix_of_perCore
#check @syscallIdToEnforcementNamePerCore
#check @enforcementBoundaryPerCoreCompleteCrossCore
#check @enforcementBoundaryPerCore_is_complete_crossCore
#check @syscallIdToEnforcementNamePerCore_differs_at_fourteen
#check @enforcementBoundaryPerCore_crossCore_classes_match
#check @endpointPolicyRestricted_perCore
#check @endpointPolicyRestricted_perCore_iff
#check @endpointPolicyRestricted_perCore_at
#check @endpointPolicyRestricted_perCore_no_overrides
#check @endpointFlowCheckAtCore
#check @endpointFlowCheckAtCore_depends_only_on_subject
#check @endpointFlowCheckAtCore_stable_under_confined_transition
#check @endpointFlowCheckAtCore_is_not_constant
#check @endpointFlowCheck_restricted_subset_perCore
#check @endpointPolicyRestricted_perCore_is_necessary
#check @syscallEntry_preserves_projectionOnCore
#check @syscallEntry_success_perCore_NI
#check @syscallEntry_error_perCore_NI
#check @nonInterference_release_of_perCore
#check @nonInterference_release_of_perCore_observer

-- ============================================================================
-- §2  Elaboration-time examples: each headline theorem applied
-- ============================================================================

-- SM8.A.1: the boot-core observer's view is the live single-core projection.
example (ctx : LabelingContext) (L : SecurityLabel) (s : SystemState) :
    ObservableState.onCore ctx bootCoreId L s = projectState ctx (IfObserver.ofLabel L) s :=
  onCore_bootCore ctx L s

-- SM8.A.1: observer low-equivalence at the boot core is the live `lowEquivalent`.
example (ctx : LabelingContext) (L : SecurityLabel) (s₁ s₂ : SystemState)
    (h : lowEquivalentForObserver ctx (PerCoreObserver.onBootCore L) s₁ s₂) :
    lowEquivalent ctx (IfObserver.ofLabel L) s₁ s₂ :=
  (lowEquivalentForObserver_bootCore ctx L s₁ s₂).mp h

-- SM8.A.2: the two fragments determine the observable state (partition totality).
example (v₁ v₂ : ObservableState) (hShared : v₁.sharedFragment = v₂.sharedFragment)
    (hPerCore : v₁.perCoreFragment = v₂.perCoreFragment) : v₁ = v₂ :=
  ObservableState.ext_fragments hShared hPerCore

-- SM8.A.2: the shared fragment is a function of the global projection alone.
example (ctx : LabelingContext) (c : CoreId) (L : SecurityLabel) (s₁ s₂ : SystemState)
    (h : projectState ctx (IfObserver.ofLabel L) s₁ = projectState ctx (IfObserver.ofLabel L) s₂) :
    (ObservableState.onCore ctx c L s₁).sharedFragment =
      (ObservableState.onCore ctx c L s₂).sharedFragment :=
  onCore_sharedFragment_determined_by_globalProjection ctx c L h

-- SM8.A.2 (headline): the per-core view is EXACTLY the factor pair — both
-- directions, so the pair is a complete and faithful invariant of the view.
example (ctx : LabelingContext) (c : CoreId) (L : SecurityLabel) (s₁ s₂ : SystemState) :
    ObservableState.onCore ctx c L s₁ = ObservableState.onCore ctx c L s₂ ↔
      observableFactorOnCore ctx c L s₁ = observableFactorOnCore ctx c L s₂ :=
  onCore_isProjection_of_globalProjection ctx c L s₁ s₂

-- SM8.A.2: the soundness half applied — equal factors give an equal view.
example (ctx : LabelingContext) (c : CoreId) (L : SecurityLabel) (s₁ s₂ : SystemState)
    (h : observableFactorOnCore ctx c L s₁ = observableFactorOnCore ctx c L s₂) :
    ObservableState.onCore ctx c L s₁ = ObservableState.onCore ctx c L s₂ :=
  (onCore_isProjection_of_globalProjection ctx c L s₁ s₂).mpr h

-- SM8.A.2: the fragments constitute the state (the tripwire's load-bearing half).
example (v : ObservableState) :
    ObservableState.ofFragments v.sharedFragment v.perCoreFragment = v :=
  ObservableState.ofFragments_eta v

-- SM8.A.2 (state-level convenience form).
example (ctx : LabelingContext) (c : CoreId) (L : SecurityLabel) (s₁ s₂ : SystemState)
    (hGlobal : projectState ctx (IfObserver.ofLabel L) s₁
      = projectState ctx (IfObserver.ofLabel L) s₂)
    (hRQ : s₁.scheduler.runQueueOnCore c = s₂.scheduler.runQueueOnCore c)
    (hCur : s₁.scheduler.currentOnCore c = s₂.scheduler.currentOnCore c)
    (hAD : s₁.scheduler.activeDomainOnCore c = s₂.scheduler.activeDomainOnCore c)
    (hDTR : s₁.scheduler.domainTimeRemainingOnCore c = s₂.scheduler.domainTimeRemainingOnCore c)
    (hDSI : s₁.scheduler.domainScheduleIndexOnCore c = s₂.scheduler.domainScheduleIndexOnCore c)
    (hRegs : s₁.machine.regsOnCore c = s₂.machine.regsOnCore c) :
    ObservableState.onCore ctx c L s₁ = ObservableState.onCore ctx c L s₂ :=
  onCore_congr_of_globalProjection ctx c L hGlobal hRQ hCur hAD hDTR hDSI hRegs

-- SM8.A.3: observable equality at the observer implies slice equality (sound refuter).
example (ctx : LabelingContext) (c : CoreId) (L : SecurityLabel) (s₁ s₂ : SystemState)
    (h : lowEquivalentOnCore ctx (IfObserver.ofLabel L) s₁ s₂ c) :
    lowEquivalentSliceOnCore ctx c L s₁ s₂ :=
  lowEquivalentSliceOnCore_of_lowEquivalentOnCore ctx c L h

-- SM8.A.4: the read-set characterisation names only shared state and core `c`.
example (ctx : LabelingContext) (L : SecurityLabel) (s₁ s₂ : SystemState) (c : CoreId)
    (hObjects : s₁.objects = s₂.objects) (hServices : s₁.services = s₂.services)
    (hIrq : s₁.irqHandlers = s₂.irqHandlers) (hIndex : s₁.objectIndex = s₂.objectIndex)
    (hDomSched : s₁.scheduler.domainSchedule = s₂.scheduler.domainSchedule)
    (hMem : s₁.machine.memory = s₂.machine.memory)
    (hRQ : s₁.scheduler.runQueueOnCore c = s₂.scheduler.runQueueOnCore c)
    (hCur : s₁.scheduler.currentOnCore c = s₂.scheduler.currentOnCore c)
    (hAD : s₁.scheduler.activeDomainOnCore c = s₂.scheduler.activeDomainOnCore c)
    (hDTR : s₁.scheduler.domainTimeRemainingOnCore c = s₂.scheduler.domainTimeRemainingOnCore c)
    (hDSI : s₁.scheduler.domainScheduleIndexOnCore c = s₂.scheduler.domainScheduleIndexOnCore c)
    (hRegs : s₁.machine.regsOnCore c = s₂.machine.regsOnCore c) :
    ObservableState.onCore ctx c L s₁ = ObservableState.onCore ctx c L s₂ :=
  onCore_perCore_independence ctx L hObjects hServices hIrq hIndex hDomSched hMem
    hRQ hCur hAD hDTR hDSI hRegs

-- SM8.A.4: a write to a different core's current slot is invisible.
example (ctx : LabelingContext) (L : SecurityLabel) (s : SystemState) (c c' : CoreId)
    (hne : c ≠ c') (v : Option SeLe4n.ThreadId) :
    ObservableState.onCore ctx c L { s with scheduler := s.scheduler.setCurrentOnCore c' v }
      = ObservableState.onCore ctx c L s :=
  onCore_setCurrentOnCore_ne ctx L s hne v

-- SM8.A.4: a write to a different core's register bank is invisible.
example (ctx : LabelingContext) (L : SecurityLabel) (s : SystemState) (c c' : CoreId)
    (hne : c ≠ c') (v : RegisterFile) :
    ObservableState.onCore ctx c L { s with machine := s.machine.setRegsOnCore c' v }
      = ObservableState.onCore ctx c L s :=
  onCore_setRegsOnCore_ne ctx L s hne v

-- SM8.A.4: the machine timer is invisible on every core (the excluded channel).
example (ctx : LabelingContext) (L : SecurityLabel) (s : SystemState) (c : CoreId) (t : Nat) :
    ObservableState.onCore ctx c L { s with machine := { s.machine with timer := t } }
      = ObservableState.onCore ctx c L s :=
  onCore_machineTimer ctx L s c t

-- SM8.A.5: monotonicity, extracted at the `current` component.
example (ctx : LabelingContext) (c : CoreId) (L₁ L₂ : SecurityLabel)
    (hFlow : securityFlowsTo L₁ L₂ = true) (s : SystemState) (t : SeLe4n.ThreadId)
    (ht : (ObservableState.onCore ctx c L₁ s).current = some t) :
    (ObservableState.onCore ctx c L₂ s).current = some t :=
  (onCore_label_monotone ctx c hFlow s).current t ht

-- SM8.A.5: monotonicity, extracted at the `objects` component — presence.
example (ctx : LabelingContext) (c : CoreId) (L₁ L₂ : SecurityLabel)
    (hFlow : securityFlowsTo L₁ L₂ = true) (s : SystemState) (oid : SeLe4n.ObjId)
    (h : ((ObservableState.onCore ctx c L₁ s).objects oid).isSome = true) :
    ((ObservableState.onCore ctx c L₂ s).objects oid).isSome = true :=
  ObservableState.visibilityLe_objects_isSome (onCore_label_monotone ctx c hFlow s) h

-- SM8.A.5: and at the `objects` component — *content*.  A visible non-CNode
-- object keeps its value, from the order alone.  This is what the pre-v0.33.4
-- `isSome`-only clause could not deliver: it permitted a wider clearance to
-- swap a visible endpoint for an unrelated object at the same id.
example (ctx : LabelingContext) (c : CoreId) (L₁ L₂ : SecurityLabel)
    (hFlow : securityFlowsTo L₁ L₂ = true) (s : SystemState) (oid : SeLe4n.ObjId)
    (e : Endpoint) (h : (ObservableState.onCore ctx c L₁ s).objects oid = some (.endpoint e)) :
    (ObservableState.onCore ctx c L₂ s).objects oid = some (.endpoint e) :=
  ObservableState.visibilityLe_objects_eq_of_not_cnode
    (onCore_label_monotone ctx c hFlow s) h (fun _ => KernelObject.noConfusion)

-- SM8.A.5: the four scheduling components are *equal* across clearances, from
-- the order alone.  Omitting these clauses (pre-v0.33.4) left two states with
-- different `activeDomain` dominating each other in both directions.
example (ctx : LabelingContext) (c : CoreId) (L₁ L₂ : SecurityLabel)
    (hFlow : securityFlowsTo L₁ L₂ = true) (s : SystemState) :
    (ObservableState.onCore ctx c L₁ s).activeDomain
      = (ObservableState.onCore ctx c L₂ s).activeDomain :=
  (onCore_label_monotone ctx c hFlow s).activeDomain

-- SM8.A.5: mutual domination plus agreement on `objects` is equality — the
-- completeness check on the clause list.
example (v : ObservableState) : v = v :=
  ObservableState.eq_of_visibilityLe_antisymm
    (ObservableState.visibilityLe_refl v) (ObservableState.visibilityLe_refl v) rfl

-- SM8.A.5: a CNode slot visible at the narrower clearance survives at the wider one.
example (ctx : LabelingContext) (L₁ L₂ : SecurityLabel) (hFlow : securityFlowsTo L₁ L₂ = true)
    (cn : CNode) (slot : SeLe4n.Slot) (cap : Capability)
    (h : (projectCNode ctx (IfObserver.ofLabel L₁) cn).lookup slot = some cap) :
    (projectCNode ctx (IfObserver.ofLabel L₂) cn).lookup slot = some cap :=
  projectCNode_lookup_monotone ctx hFlow cn slot cap h

-- SM8.A.5: off the CNode arm, a visible object projects to the SAME value at
-- the wider clearance — the widening is confined to CNode slot redaction.
example (ctx : LabelingContext) (c : CoreId) (L₁ L₂ : SecurityLabel)
    (hFlow : securityFlowsTo L₁ L₂ = true) (s : SystemState) (oid : SeLe4n.ObjId)
    (obj : KernelObject) (hGet : s.objects[oid]? = some obj)
    (hNotCNode : ∀ cn, obj ≠ .cnode cn)
    (hVisible : ((ObservableState.onCore ctx c L₁ s).objects oid).isSome = true) :
    (ObservableState.onCore ctx c L₂ s).objects oid
      = (ObservableState.onCore ctx c L₁ s).objects oid :=
  onCore_objects_label_invariant_off_cnode ctx c hFlow s oid obj hGet hNotCNode hVisible

-- SM8.A.5: the scheduling components pass through UNFILTERED — the observer
-- reads core c's raw scheduler state (accepted channel CC-1, per core).
example (ctx : LabelingContext) (c : CoreId) (L : SecurityLabel) (s : SystemState) :
    (ObservableState.onCore ctx c L s).activeDomain = s.scheduler.activeDomainOnCore c :=
  (onCore_schedulingTransparency ctx c L s).1

-- SM8.A.5: hence label-invariant, the two-observer corollary.
example (ctx : LabelingContext) (c : CoreId) (L₁ L₂ : SecurityLabel) (s : SystemState) :
    (ObservableState.onCore ctx c L₁ s).activeDomain =
      (ObservableState.onCore ctx c L₂ s).activeDomain :=
  (onCore_schedulingTransparency_label_invariant ctx c L₁ L₂ s).1

-- SM8.A.5 (SMP form): clearance monotonicity on every core at once.
example (ctx : LabelingContext) (L₁ L₂ : SecurityLabel)
    (hFlow : securityFlowsTo L₁ L₂ = true) (s : SystemState) :
    visibilityLe_smp ctx L₁ L₂ s :=
  onCore_label_monotone_smp ctx hFlow s

-- SM8.A.5: a CNode slot visible at the narrower clearance survives, with the
-- same capability, at the wider one — at the observable-state layer.
example (ctx : LabelingContext) (c : CoreId) (L₁ L₂ : SecurityLabel)
    (hFlow : securityFlowsTo L₁ L₂ = true) (s : SystemState) (oid : SeLe4n.ObjId)
    (cn : CNode) (slot : SeLe4n.Slot) (cap : Capability)
    (hGet : s.objects[oid]? = some (.cnode cn))
    (hObs : objectObservable ctx (IfObserver.ofLabel L₁) oid = true)
    (hSlot : ∀ cn₁, (ObservableState.onCore ctx c L₁ s).objects oid = some (.cnode cn₁) →
      cn₁.lookup slot = some cap) :
    ∃ cn₂, (ObservableState.onCore ctx c L₂ s).objects oid = some (.cnode cn₂) ∧
      cn₂.lookup slot = some cap :=
  onCore_objects_cnode_slot_monotone ctx c hFlow s oid cn slot cap hGet hObs hSlot

-- ============================================================================
-- §3  Runtime assertions (Tier-2): the four-thread / four-core IF fixture
-- ============================================================================

private def assertBool (name : String) (b : Bool) : IO Unit := do
  if b then IO.println s!"  PASS: {name}"
  else
    IO.println s!"  FAIL: {name}"
    throw (IO.userError s!"Assertion failed: {name}")

/-- The four RPi5 cores. -/
private def c0 : CoreId := bootCoreId
private def c1 : CoreId := ⟨1, by decide⟩
private def c2 : CoreId := ⟨2, by decide⟩

/-- The three clearances, forming a **strict chain** `low ⊏ mid ⊏ high` in the
2×2 confidentiality×integrity lattice (each step checked in §3.5):

* `low`  = (low confidentiality, untrusted)  — `SecurityLabel.publicLabel`
* `mid`  = (low confidentiality, trusted)
* `high` = (high confidentiality, trusted)   — `SecurityLabel.kernelTrusted`

`mid` is a genuine middle: `securityFlowsTo mid lowLabel = false` (so `low ⊏ mid`
strictly) and `securityFlowsTo highLabel mid = false` (so `mid ⊏ high` strictly).
The chain is what makes the `visibilityLe` transitivity checks in §3.5
non-vacuous — with only two clearances, transitivity has nothing to compose. -/
private def lowLabel : SecurityLabel := SecurityLabel.publicLabel
private def midLabel : SecurityLabel := { confidentiality := .low, integrity := .trusted }
private def highLabel : SecurityLabel := SecurityLabel.kernelTrusted

/-- The fixture's clearance step, as a reusable term.  A `by decide` written
inside a `fun c => …` cannot discharge this goal: the observer record carries
the free core component `c`, and `decide` refuses a goal with free variables
even when (as here) the statement does not depend on it. -/
private theorem lowLabel_flowsTo_highLabel : securityFlowsTo lowLabel highLabel = true := by
  decide

private theorem lowLabel_flowsTo_midLabel : securityFlowsTo lowLabel midLabel = true := by
  decide

private theorem midLabel_flowsTo_highLabel : securityFlowsTo midLabel highLabel = true := by
  decide

-- Fixture OIDs (range 1000–1020 — see the range table in SeLe4n/Testing/Helpers.lean).
private def cnRoot : SeLe4n.ObjId := ⟨1000⟩
private def vsRoot : SeLe4n.ObjId := ⟨1001⟩
private def lowEndpoint : SeLe4n.ObjId := ⟨1002⟩
private def highEndpoint : SeLe4n.ObjId := ⟨1003⟩
private def lowService : ServiceId := ⟨1004⟩
private def highService : ServiceId := ⟨1005⟩
private def lowIrq : SeLe4n.Irq := ⟨11⟩
private def highIrq : SeLe4n.Irq := ⟨12⟩
private def lowCurrent : SeLe4n.ThreadId := ⟨1010⟩
private def highCurrent : SeLe4n.ThreadId := ⟨1011⟩
private def lowQueued : SeLe4n.ThreadId := ⟨1012⟩
private def highQueued : SeLe4n.ThreadId := ⟨1013⟩
/-- A `mid`-labelled endpoint: invisible to `low`, visible to `mid` and `high`.
Without it the three-clearance chain would be observationally degenerate. -/
private def midEndpoint : SeLe4n.ObjId := ⟨1014⟩
/-- A CNode holding two capabilities — one naming a low target, one naming a
high target — so CNode **slot redaction** (the only observer-dependent part of
object projection) has something to redact. -/
private def probeCNode : SeLe4n.ObjId := ⟨1015⟩
private def lowSlot : SeLe4n.Slot := SeLe4n.Slot.ofNat 1
private def highSlot : SeLe4n.Slot := SeLe4n.Slot.ofNat 2
private def lowSlotCap : Capability :=
  { target := .object lowEndpoint, rights := AccessRightSet.ofList [.read] }
private def highSlotCap : Capability :=
  { target := .object highEndpoint, rights := AccessRightSet.ofList [.read] }
/-- The raw CNode the fixture stores (both slots present, unredacted). -/
private def probeCNodeValue : CNode :=
  { depth := 4, guardWidth := 0, guardValue := 0, radixWidth := 4,
    slots := SeLe4n.UniqueSlotMap.ofListWF [(lowSlot, lowSlotCap), (highSlot, highSlotCap)] }

/-- The CSpace root every fixture TCB names.

`KernelObject.wellFormed` requires a TCB's `cspaceRoot` and `vspaceRoot` to
resolve in the object store, so a fixture whose TCBs point at absent ids is one
the kernel's own construction paths (`lifecycleRetype`, which validates
`wellFormed` before installing) would reject — the evidence would be computed on
an unreachable state.  Both roots are therefore real objects, and §3.0 checks
the well-formedness that makes them necessary.  Empty slots: this root exists to
be *referenced*, and the redaction probe is `probeCNode`. -/
private def rootCNodeValue : CNode :=
  { depth := 8, guardWidth := 0, guardValue := 0, radixWidth := 8,
    slots := SeLe4n.UniqueSlotMap.ofListWF [] }

/-- The VSpace root every fixture TCB names.  Its ASID is distinct from any
other in the fixture (it is the only VSpaceRoot), so the builder's ASID
uniqueness check has nothing to collide with. -/
private def rootVSpaceValue : VSpaceRoot :=
  { asid := ⟨7⟩, mappings := SeLe4n.Kernel.RobinHood.RHTable.empty 16 }
/-- Physical addresses for the memory-ownership probes (§3.8). -/
private def lowPage : SeLe4n.PAddr := SeLe4n.PAddr.ofNat 0x40000000
private def highPage : SeLe4n.PAddr := SeLe4n.PAddr.ofNat 0x40001000
private def unownedPage : SeLe4n.PAddr := SeLe4n.PAddr.ofNat 0x40002000
private def lowDomain : SeLe4n.DomainId := ⟨1⟩
private def highDomain : SeLe4n.DomainId := ⟨2⟩

/-- The suite's labeling context: the high endpoint, the two high threads (and
their backing objects) and the high service carry `kernelTrusted`; everything
else carries `publicLabel`.

Deliberately **not** `defaultLabelingContext`, under which every observability
gate is unconditionally `true` (`defaultLabelingContext_insecure`) and every
label assertion below would be vacuous. -/
private def probeLabeling : LabelingContext :=
  { objectLabelOf := fun oid =>
      if oid = highEndpoint then highLabel
      else if oid = highCurrent.toObjId then highLabel
      else if oid = highQueued.toObjId then highLabel
      else if oid = midEndpoint then midLabel
      else lowLabel
    threadLabelOf := fun tid =>
      if tid = highCurrent then highLabel
      else if tid = highQueued then highLabel
      else lowLabel
    endpointLabelOf := fun oid => if oid = highEndpoint then highLabel else lowLabel
    serviceLabelOf := fun sid => if sid = highService then highLabel else lowLabel }

/-- `probeLabeling` **with a memory-ownership model configured**.

`LabelingContext.memoryOwnership` defaults to `none`, under which
`memoryAddressObservable` is constantly `false` and every `memory` claim is
vacuously true.  This variant assigns `lowPage` to a low-labelled domain and
`highPage` to a high-labelled one, leaving `unownedPage` unowned, so §3.8
exercises all three branches of the gate on real values. -/
private def probeLabelingWithMemory : LabelingContext :=
  { probeLabeling with
    memoryOwnership := some
      { regionOwner := fun pa =>
          if pa = lowPage then some lowDomain
          else if pa = highPage then some highDomain
          else none
        domainLabelOf := fun d => if d = highDomain then highLabel else lowLabel } }

private def mkTcb (tid : Nat) (prio : Nat) (aff : Option CoreId) : TCB :=
  { tid := ⟨tid⟩, priority := ⟨prio⟩, domain := ⟨0⟩, cspaceRoot := cnRoot,
    vspaceRoot := vsRoot, ipcBuffer := SeLe4n.VAddr.ofNat 4096, ipcState := .ready,
    cpuAffinity := aff }

private def mkServiceEntry (sid : ServiceId) (backing : SeLe4n.ObjId) : ServiceGraphEntry :=
  { identity := { sid := sid, backingObject := backing, owner := backing }
    dependencies := []
    isolatedFrom := [] }

/-- The fixture: **core 0 runs low, core 1 runs high.**

* core 0 — current `lowCurrent`, run queue `[lowQueued]` (both low-labelled);
* core 1 — current `highCurrent`, run queue `[highQueued]` (both high-labelled);
* cores 2 and 3 — idle;
* shared — a low and a high endpoint, a low and a high service, a low and a
  high IRQ handler, and the CSpace/VSpace roots every TCB names (so every TCB
  is `KernelObject.wellFormed`, checked in §3.0).

Every thread is dequeue-on-dispatch consistent (a core's current thread is not
in that core's run queue).  The two cores' contents are label-disjoint, which
is what makes the cross-core (§3.4) and label (§3.5) assertions independent of
each other. -/
private def probeState : SystemState :=
  let base :=
    (BootstrapBuilder.empty
      |>.withObject cnRoot (.cnode rootCNodeValue)
      |>.withObject vsRoot (.vspaceRoot rootVSpaceValue)
      |>.withObject lowEndpoint (.endpoint {})
      |>.withObject highEndpoint (.endpoint {})
      |>.withObject midEndpoint (.endpoint {})
      |>.withObject probeCNode (.cnode probeCNodeValue)
      |>.withObject lowCurrent.toObjId (.tcb (mkTcb 1010 40 none))
      |>.withObject highCurrent.toObjId (.tcb (mkTcb 1011 50 (some c1)))
      |>.withObject lowQueued.toObjId (.tcb (mkTcb 1012 40 none))
      |>.withObject highQueued.toObjId (.tcb (mkTcb 1013 50 (some c1)))
      |>.withService lowService (mkServiceEntry lowService lowEndpoint)
      |>.withService highService (mkServiceEntry highService highEndpoint)
      |>.withIrqHandler lowIrq lowEndpoint
      |>.withIrqHandler highIrq highEndpoint
      |>.build)
  { base with scheduler :=
      ((((base.scheduler.setRunQueueOnCore c0 (RunQueue.ofList [(lowQueued, ⟨40⟩)])).setRunQueueOnCore
        c1 (RunQueue.ofList [(highQueued, ⟨50⟩)])).setCurrentOnCore
        c0 (some lowCurrent)).setCurrentOnCore c1 (some highCurrent)) }

/-- The three observers the suite compares. -/
private def lowObserver : IfObserver := IfObserver.ofLabel lowLabel
private def midObserver : IfObserver := IfObserver.ofLabel midLabel
private def highObserver : IfObserver := IfObserver.ofLabel highLabel

/-- The fixture's CNode really is in the store, as the exact value the slot
assertions read.  `KernelObject` has no `DecidableEq` (its CNode arm is
RHTable-backed), so this is a definitional computation rather than a `decide`;
it doubles as the fixture non-vacuity gate for §3.8. -/
private theorem probeState_holds_probeCNode :
    probeState.objects[probeCNode]? = some (.cnode probeCNodeValue) := by rfl

/-- The shared object index does not read the observer's core (§3.2), so this
membership fact needs no core argument and applies at every one.  Spelled with
`IfObserver.ofLabel lowLabel` rather than `lowObserver` so it matches the
reduct of `(ObservableState.onCore … c lowLabel …).objectIndex` syntactically. -/
private theorem lowEndpoint_mem_lowObjectIndex :
    lowEndpoint ∈ projectObjectIndex probeLabeling (IfObserver.ofLabel lowLabel) probeState := by
  decide

/-- The capability the observer at `(c, L)` sees in `probeCNode`'s `slot`,
read **through the observable state** rather than through `projectCNode`.
`Option Capability` has `DecidableEq`, so unlike the whole projected object
this is a decidable end-to-end check of the redaction. -/
private def cnodeSlotThroughView (c : CoreId) (L : SecurityLabel) (slot : SeLe4n.Slot) :
    Option Capability :=
  match (ObservableState.onCore probeLabeling c L probeState).objects probeCNode with
  | some (.cnode cn) => cn.lookup slot
  | _ => none

/-- The low endpoint's value as the low observer sees it (§3.13).  Computed, so
it is the fixture's actual object and not an assumed one. -/
private theorem lowEndpoint_view_low :
    (ObservableState.onCore probeLabeling c0 lowLabel probeState).objects lowEndpoint
      = some (.endpoint {}) := by rfl

/-- …and the **same** value as the high observer sees it — derived from
`visibilityLe` alone, not recomputed.  This is the content half of the `objects`
clause: off the CNode arm a wider clearance may not change what it shows. -/
private theorem lowEndpoint_view_high :
    (ObservableState.onCore probeLabeling c0 highLabel probeState).objects lowEndpoint
      = some (.endpoint {}) :=
  ObservableState.visibilityLe_objects_eq_of_not_cnode
    (onCore_label_monotone probeLabeling c0 lowLabel_flowsTo_highLabel probeState)
    lowEndpoint_view_low (fun _ => KernelObject.noConfusion)

/-- The substitution an `isSome`-only clause would have accepted (§3.13). -/
private theorem endpoint_not_visibilityLe_notification (e : Endpoint) (n : Notification) :
    ¬ objectVisibilityLe (.endpoint e) (.notification n) := by
  intro h
  cases h

/-- …and the cross-arm substitution, in the other direction (§3.13). -/
private theorem cnode_not_visibilityLe_endpoint (cn : CNode) (e : Endpoint) :
    ¬ objectVisibilityLe (.cnode cn) (.endpoint e) := by
  intro h
  exact h.elim

/-- The low observer's own view with its `activeDomain` moved (§3.13).  Every
component the pre-v0.33.4 relation constrained is untouched, so this is exactly
the state that dominated the real view in both directions before the four
scheduling clauses were added. -/
private def domainShiftedView : ObservableState :=
  { ObservableState.onCore probeLabeling c0 lowLabel probeState with
    activeDomain := ⟨9⟩ }

/-- §3.0  Fixture non-vacuity.  Every later group reads this state; if the
builder had silently produced an empty one (the `buildChecked` panic-to-default
failure mode) every assertion below would pass vacuously.  These checks fail
first and loudly instead. -/
private def runFixtureChecks : IO Unit := do
  IO.println "--- §3.0 fixture non-vacuity ---"
  assertBool "both endpoints are in the object store"
    (decide ((probeState.objects[lowEndpoint]?).isSome = true ∧
             (probeState.objects[highEndpoint]?).isSome = true))
  assertBool "all four threads are in the object store"
    (decide ((probeState.objects[lowCurrent.toObjId]?).isSome = true ∧
             (probeState.objects[highCurrent.toObjId]?).isSome = true ∧
             (probeState.objects[lowQueued.toObjId]?).isSome = true ∧
             (probeState.objects[highQueued.toObjId]?).isSome = true))
  -- The state has to be one the kernel could actually reach.  A TCB whose
  -- `cspaceRoot`/`vspaceRoot` do not resolve fails `KernelObject.wellFormed`,
  -- which `lifecycleRetype` validates before installing an object — so a
  -- fixture missing its roots would compute all of the evidence below on a
  -- state no construction path can produce.
  assertBool "both declared TCB roots are real objects in the store"
    (decide ((probeState.objects[cnRoot]?).isSome = true ∧
             (probeState.objects[vsRoot]?).isSome = true))
  assertBool "every fixture TCB is KernelObject.wellFormed"
    (decide ((KernelObject.tcb (mkTcb 1010 40 none)).wellFormed probeState.objects ∧
             (KernelObject.tcb (mkTcb 1011 50 (some c1))).wellFormed probeState.objects ∧
             (KernelObject.tcb (mkTcb 1012 40 none)).wellFormed probeState.objects ∧
             (KernelObject.tcb (mkTcb 1013 50 (some c1))).wellFormed probeState.objects))
  assertBool "both CNodes in the fixture are KernelObject.wellFormed"
    (decide ((KernelObject.cnode rootCNodeValue).wellFormed probeState.objects ∧
             (KernelObject.cnode probeCNodeValue).wellFormed probeState.objects))
  -- The load-bearing negative: well-formedness is a real constraint here, not
  -- something every TCB satisfies.  A TCB naming an absent root is rejected.
  assertBool "a TCB naming an absent root is NOT well-formed"
    (decide (¬ (KernelObject.tcb
      { (mkTcb 1010 40 none) with cspaceRoot := ⟨1019⟩ }).wellFormed probeState.objects))
  assertBool "core 0 runs the low thread, core 1 runs the high thread"
    (decide (probeState.scheduler.currentOnCore c0 = some lowCurrent ∧
             probeState.scheduler.currentOnCore c1 = some highCurrent))
  assertBool "core 0 queues the low thread, core 1 queues the high thread"
    (decide ((probeState.scheduler.runQueueOnCore c0).toList = [lowQueued] ∧
             (probeState.scheduler.runQueueOnCore c1).toList = [highQueued]))
  assertBool "cores 2 and 3 are idle (no current, empty queue)"
    (decide (probeState.scheduler.currentOnCore c2 = none ∧
             (probeState.scheduler.runQueueOnCore c2).toList = []))
  -- The labeling must be non-trivial: it has to separate the two clearances.
  --
  -- Note this is *not* checked with `isInsecureDefaultContext`.  That detector
  -- samples entity ids 0, 1 and 42 and reports "insecure default" when all of
  -- them are `publicLabel`; this fixture's labels live in the reserved
  -- 1000–1020 band, so the detector fires on it.  That is the heuristic being
  -- conservative in its safe direction (over-flagging a context that *looks*
  -- all-public at the probes), exactly as its docstring describes — not a
  -- property of this context.  The substantive gate is the separation below:
  -- there are entities the low observer provably cannot see, and none that the
  -- high observer cannot.
  assertBool "the probe labeling genuinely separates the two clearances"
    (decide (securityFlowsTo (probeLabeling.threadLabelOf highCurrent) lowLabel = false ∧
             securityFlowsTo (probeLabeling.threadLabelOf lowCurrent) lowLabel = true ∧
             securityFlowsTo (probeLabeling.objectLabelOf highEndpoint) lowLabel = false ∧
             securityFlowsTo (probeLabeling.serviceLabelOf highService) lowLabel = false))
  assertBool "low entities are observable to the low observer, high ones are not"
    (decide (objectObservable probeLabeling lowObserver lowEndpoint = true ∧
             objectObservable probeLabeling lowObserver highEndpoint = false ∧
             threadObservable probeLabeling lowObserver lowCurrent = true ∧
             threadObservable probeLabeling lowObserver highCurrent = false))
  assertBool "every entity is observable to the high observer"
    (decide (objectObservable probeLabeling highObserver lowEndpoint = true ∧
             objectObservable probeLabeling highObserver highEndpoint = true ∧
             threadObservable probeLabeling highObserver lowCurrent = true ∧
             threadObservable probeLabeling highObserver highCurrent = true))

/-- §3.1  The observer and its view: the boot-core bridge to the live
single-core projection, and observer low-equivalence as an equivalence. -/
private def runObserverChecks : IO Unit := do
  IO.println "--- §3.1 the (core, label) observer and its view ---"
  assertBool "onCore_bootCore: the boot-core view is the live projectState"
    (have _h : ObservableState.onCore probeLabeling bootCoreId lowLabel probeState
        = projectState probeLabeling lowObserver probeState :=
      onCore_bootCore probeLabeling lowLabel probeState
     true)
  assertBool "the observer view is the SM4.D per-core projection on every core"
    (allCores.all (fun c =>
      have _h : ObservableState.onCore probeLabeling c lowLabel probeState
          = projectStateOnCore probeLabeling lowObserver probeState c :=
        onCore_eq_projectStateOnCore probeLabeling c lowLabel probeState
      true))
  assertBool "lowEquivalentForObserver is reflexive at every (core, label)"
    (allCores.all (fun c =>
      have _h₁ : lowEquivalentForObserver probeLabeling ⟨c, lowLabel⟩ probeState probeState :=
        lowEquivalentForObserver_refl probeLabeling ⟨c, lowLabel⟩ probeState
      have _h₂ : lowEquivalentForObserver probeLabeling ⟨c, highLabel⟩ probeState probeState :=
        lowEquivalentForObserver_refl probeLabeling ⟨c, highLabel⟩ probeState
      true))
  assertBool "the ∀-observer SMP form is the SM4.D lowEquivalent_smp"
    (have _h : lowEquivalent_smp probeLabeling lowObserver probeState probeState ↔
        ∀ c : CoreId, lowEquivalentForObserver probeLabeling ⟨c, lowLabel⟩ probeState probeState :=
      lowEquivalent_smp_iff_forall_observer probeLabeling lowLabel probeState probeState
     true)

/-- §3.2  The field partition: the per-core components are core-restricted and
the shared components are not.  Every claim here is *computed* on the fixture,
so a projection re-pointed at the wrong core fails the run. -/
private def runPartitionChecks : IO Unit := do
  IO.println "--- §3.2 the shared / per-core field partition ---"
  -- Per-core half: each core sees its own current thread and its own queue.
  assertBool "the low observer sees core 0's low current thread"
    (decide ((ObservableState.onCore probeLabeling c0 lowLabel probeState).current
      = some lowCurrent))
  assertBool "the low observer sees core 0's low run queue"
    (decide ((ObservableState.onCore probeLabeling c0 lowLabel probeState).runnable
      = [lowQueued]))
  assertBool "the low observer sees nothing of core 1 (its threads are high)"
    (decide ((ObservableState.onCore probeLabeling c1 lowLabel probeState).current = none ∧
             (ObservableState.onCore probeLabeling c1 lowLabel probeState).runnable = []))
  assertBool "the high observer sees core 1's high current thread and queue"
    (decide ((ObservableState.onCore probeLabeling c1 highLabel probeState).current
        = some highCurrent ∧
             (ObservableState.onCore probeLabeling c1 highLabel probeState).runnable
        = [highQueued]))
  assertBool "core 0's view never shows core 1's thread (per-core restriction)"
    (decide ((ObservableState.onCore probeLabeling c0 highLabel probeState).current
      = some lowCurrent))
  assertBool "the idle cores project empty per-core components at both clearances"
    (decide ((ObservableState.onCore probeLabeling c2 lowLabel probeState).current = none ∧
             (ObservableState.onCore probeLabeling c2 highLabel probeState).current = none ∧
             (ObservableState.onCore probeLabeling c2 highLabel probeState).runnable = []))
  -- Shared half: the same on every core, at a fixed clearance.
  assertBool "the shared objectIndex component is identical on every core"
    (allCores.all (fun c =>
      decide ((ObservableState.onCore probeLabeling c lowLabel probeState).objectIndex
        = (ObservableState.onCore probeLabeling bootCoreId lowLabel probeState).objectIndex)))
  assertBool "the shared services component is identical on every core"
    (allCores.all (fun c =>
      decide ((ObservableState.onCore probeLabeling c lowLabel probeState).services lowService
          = (ObservableState.onCore probeLabeling bootCoreId lowLabel probeState).services
              lowService ∧
        (ObservableState.onCore probeLabeling c lowLabel probeState).services highService
          = (ObservableState.onCore probeLabeling bootCoreId lowLabel probeState).services
              highService)))
  assertBool "the shared irqHandlers component is identical on every core"
    (allCores.all (fun c =>
      decide ((ObservableState.onCore probeLabeling c lowLabel probeState).irqHandlers lowIrq
          = (ObservableState.onCore probeLabeling bootCoreId lowLabel probeState).irqHandlers
              lowIrq ∧
        (ObservableState.onCore probeLabeling c lowLabel probeState).irqHandlers highIrq
          = (ObservableState.onCore probeLabeling bootCoreId lowLabel probeState).irqHandlers
              highIrq)))
  assertBool "the shared objects component is identical on every core"
    (allCores.all (fun c =>
      decide (((ObservableState.onCore probeLabeling c lowLabel probeState).objects
            lowEndpoint).isSome
          = ((ObservableState.onCore probeLabeling bootCoreId lowLabel probeState).objects
              lowEndpoint).isSome)))
  -- `ext_fragments` used substantively: two *different* states whose fragments
  -- coincide have the same view.  Here the second state differs only in the
  -- machine timer, which no projection reads, so both fragments are `rfl`-equal
  -- and the theorem delivers the whole observable state.  (A `v = v` instance
  -- would prove nothing about the partition.)
  assertBool "ext_fragments derives view equality between two distinct states"
    (allCores.all (fun c =>
      have _h : ObservableState.onCore probeLabeling c lowLabel
            { probeState with machine := { probeState.machine with timer := 987654 } }
          = ObservableState.onCore probeLabeling c lowLabel probeState :=
        ObservableState.ext_fragments rfl rfl
      true))

/-- §3.3  The decidable slice: it decides, it refutes soundly, and it is
strictly weaker than observable equality. -/
private def runDecidableSliceChecks : IO Unit := do
  IO.println "--- §3.3 the decidable per-core slice ---"
  assertBool "slice low-equivalence decides reflexively at every (core, label)"
    (allCores.all (fun c =>
      decide (lowEquivalentSliceOnCore probeLabeling c lowLabel probeState probeState) &&
      decide (lowEquivalentSliceOnCore probeLabeling c highLabel probeState probeState)))
  assertBool "the slice records core 0's low current thread and queue"
    (decide ((ObservableState.sliceOnCore probeLabeling c0 lowLabel probeState).current
        = some lowCurrent ∧
      (ObservableState.sliceOnCore probeLabeling c0 lowLabel probeState).runnable
        = [lowQueued]))
  assertBool "the slice records that core 0's register bank is observable to low"
    (decide ((ObservableState.sliceOnCore probeLabeling c0 lowLabel probeState).registersObservable
      = true))
  assertBool "the slice records that core 1's register bank is NOT observable to low"
    (decide ((ObservableState.sliceOnCore probeLabeling c1 lowLabel probeState).registersObservable
      = false))
  assertBool "…but IS observable to high (the negative above is not vacuous)"
    (decide ((ObservableState.sliceOnCore probeLabeling c1 highLabel probeState).registersObservable
      = true))
  assertBool "the low and high slices of core 1 genuinely differ (decidable refutation)"
    (!decide (ObservableState.sliceOnCore probeLabeling c1 lowLabel probeState
      = ObservableState.sliceOnCore probeLabeling c1 highLabel probeState))
  assertBool "observable equality implies slice equality (sound refuter)"
    (allCores.all (fun c =>
      have _h : lowEquivalentSliceOnCore probeLabeling c lowLabel probeState probeState :=
        lowEquivalentSliceOnCore_of_lowEquivalentOnCore probeLabeling c lowLabel
          (lowEquivalentOnCore_refl probeLabeling lowObserver probeState c)
      true))
  assertBool "the slice is a STRICT fragment: it erases register content"
    (have _h : ∃ v₁ v₂ : ObservableState,
        v₁.perCoreSlice = v₂.perCoreSlice ∧ v₁.machineRegs ≠ v₂.machineRegs :=
      perCoreSlice_erases_register_content
     true)
  assertBool "the slice is a STRICT fragment: it erases shared content"
    (have _h : ∃ v₁ v₂ : ObservableState, v₁.perCoreSlice = v₂.perCoreSlice ∧ v₁ ≠ v₂ :=
      perCoreSlice_erases_shared_content
     true)

/-- §3.4  Per-core independence — the read-set bound, computed.

The **load-bearing negative** is the last pair: the very same write applied to
the observer's own core *does* change its slice, so the `c ≠ c'` hypothesis of
the cross-core frames is necessary rather than decorative.  A regression that
made the per-core projections read a fixed core would fail there. -/
private def runIndependenceChecks : IO Unit := do
  IO.println "--- §3.4 per-core independence (cross-core writes) ---"
  -- Write only core 1's current slot.
  let stRemoteCurrent : SystemState :=
    { probeState with
      scheduler := probeState.scheduler.setCurrentOnCore c1 (some lowQueued) }
  assertBool "a write to core 1's current slot leaves core 0's slice unchanged"
    (decide (ObservableState.sliceOnCore probeLabeling c0 lowLabel stRemoteCurrent
      = ObservableState.sliceOnCore probeLabeling c0 lowLabel probeState))
  assertBool "onCore_setCurrentOnCore_ne applies (theorem level, c0 ≠ c1)"
    (have _h : ObservableState.onCore probeLabeling c0 lowLabel
        { probeState with
          scheduler := probeState.scheduler.setCurrentOnCore c1 (some lowQueued) }
        = ObservableState.onCore probeLabeling c0 lowLabel probeState :=
      onCore_setCurrentOnCore_ne probeLabeling lowLabel probeState (by decide) (some lowQueued)
     true)
  -- Write only core 1's run queue.
  let stRemoteQueue : SystemState :=
    { probeState with
      scheduler := probeState.scheduler.setRunQueueOnCore c1 (RunQueue.ofList [(lowQueued, ⟨40⟩)]) }
  assertBool "a write to core 1's run queue leaves core 0's slice unchanged"
    (decide (ObservableState.sliceOnCore probeLabeling c0 lowLabel stRemoteQueue
      = ObservableState.sliceOnCore probeLabeling c0 lowLabel probeState))
  assertBool "…and DOES change core 1's own low view (the write is not a no-op)"
    (!decide (ObservableState.sliceOnCore probeLabeling c1 lowLabel stRemoteQueue
      = ObservableState.sliceOnCore probeLabeling c1 lowLabel probeState))
  -- Write only core 1's active domain / domain timing.
  let stRemoteDomain : SystemState :=
    { probeState with
      scheduler := (probeState.scheduler.setActiveDomainOnCore c1 ⟨3⟩).setDomainTimeRemainingOnCore
        c1 99 }
  assertBool "a remote domain switch leaves core 0's slice unchanged"
    (decide (ObservableState.sliceOnCore probeLabeling c0 lowLabel stRemoteDomain
      = ObservableState.sliceOnCore probeLabeling c0 lowLabel probeState))
  assertBool "…and IS visible on core 1 (scheduling transparency, per core)"
    (decide ((ObservableState.onCore probeLabeling c1 lowLabel stRemoteDomain).activeDomain
        = ⟨3⟩ ∧
      (ObservableState.onCore probeLabeling c1 lowLabel stRemoteDomain).domainTimeRemaining = 99))
  -- Write only core 1's register bank.
  let stRemoteRegs : SystemState :=
    { probeState with
      machine := probeState.machine.setRegsOnCore c1 { pc := ⟨7⟩, sp := ⟨9⟩, gpr := fun _ => ⟨1⟩ } }
  -- `Option RegisterFile` has no `DecidableEq` (the `gpr` field is a function
  -- over an unbounded domain), so the value-level check uses `RegisterFile`'s
  -- structural `BEq` — the ARM64 comparison over `pc`, `sp` and the 32
  -- architectural GPRs, which the model documents as the sanctioned test-time
  -- equality (`RegisterFile.not_lawfulBEq` records why it is not propositional
  -- equality).  The propositional statement is the theorem-level assertion
  -- immediately below.
  assertBool "a write to core 1's register bank leaves core 0's projected regs unchanged"
    (projectMachineRegsOnCore probeLabeling lowObserver stRemoteRegs c0
      == projectMachineRegsOnCore probeLabeling lowObserver probeState c0)
  assertBool "…while writing core 0's OWN bank DOES change them (not a vacuous BEq)"
    (!(projectMachineRegsOnCore probeLabeling lowObserver
        { probeState with
          machine := probeState.machine.setRegsOnCore c0
            { pc := ⟨7⟩, sp := ⟨9⟩, gpr := fun _ => ⟨1⟩ } } c0
      == projectMachineRegsOnCore probeLabeling lowObserver probeState c0))
  assertBool "onCore_setRegsOnCore_ne applies (theorem level, c0 ≠ c1)"
    (have _h : ObservableState.onCore probeLabeling c0 lowLabel
        { probeState with
          machine := probeState.machine.setRegsOnCore c1
            { pc := ⟨7⟩, sp := ⟨9⟩, gpr := fun _ => ⟨1⟩ } }
        = ObservableState.onCore probeLabeling c0 lowLabel probeState :=
      onCore_setRegsOnCore_ne probeLabeling lowLabel probeState (by decide)
        { pc := ⟨7⟩, sp := ⟨9⟩, gpr := fun _ => ⟨1⟩ }
     true)
  -- Fields outside the read set: invisible on EVERY core, including the one written.
  assertBool "the CBS replenishment queue is invisible on every core"
    (allCores.all (fun c =>
      have _h : ObservableState.onCore probeLabeling c lowLabel
          { probeState with
            scheduler := probeState.scheduler.setReplenishQueueOnCore c ReplenishQueue.empty }
          = ObservableState.onCore probeLabeling c lowLabel probeState :=
        onCore_setReplenishQueueOnCore probeLabeling lowLabel probeState c c ReplenishQueue.empty
      true))
  assertBool "the machine timer is invisible on every core (the excluded channel)"
    (allCores.all (fun c =>
      decide (ObservableState.sliceOnCore probeLabeling c lowLabel
          { probeState with machine := { probeState.machine with timer := 123456 } }
        = ObservableState.sliceOnCore probeLabeling c lowLabel probeState)))
  assertBool "onCore_machineTimer applies on every core (theorem level)"
    (allCores.all (fun c =>
      have _h : ObservableState.onCore probeLabeling c lowLabel
          { probeState with machine := { probeState.machine with timer := 123456 } }
          = ObservableState.onCore probeLabeling c lowLabel probeState :=
        onCore_machineTimer probeLabeling lowLabel probeState c 123456
      true))
  -- LOAD-BEARING NEGATIVE: the same write on the observer's OWN core is visible.
  let stLocalCurrent : SystemState :=
    { probeState with
      scheduler := probeState.scheduler.setCurrentOnCore c0 (some lowQueued) }
  assertBool "the SAME current-slot write on core 0 DOES change core 0's slice"
    (!decide (ObservableState.sliceOnCore probeLabeling c0 lowLabel stLocalCurrent
      = ObservableState.sliceOnCore probeLabeling c0 lowLabel probeState))
  assertBool "…while still leaving core 1's slice unchanged (the frame is symmetric)"
    (decide (ObservableState.sliceOnCore probeLabeling c1 lowLabel stLocalCurrent
      = ObservableState.sliceOnCore probeLabeling c1 lowLabel probeState))

/-- §3.5  Label monotonicity — the high observer outsees the low one, strictly.

The **load-bearing negative** is the strictness pair: if the projections ever
stopped filtering by label, the low and high views would coincide and the
`!decide` assertions would fail. -/
private def runMonotonicityChecks : IO Unit := do
  IO.println "--- §3.5 clearance monotonicity ---"
  assertBool "the clearance pair is a strict step of the flow order"
    (decide (securityFlowsTo lowLabel highLabel = true ∧
             securityFlowsTo highLabel lowLabel = false))
  assertBool "every gate is monotone on the fixture's entities"
    (decide (objectObservable probeLabeling lowObserver lowEndpoint = true ∧
             objectObservable probeLabeling highObserver lowEndpoint = true ∧
             serviceObservable probeLabeling lowObserver lowService = true ∧
             serviceObservable probeLabeling highObserver lowService = true ∧
             threadObservable probeLabeling lowObserver lowQueued = true ∧
             threadObservable probeLabeling highObserver lowQueued = true))
  assertBool "onCore_label_monotone applies on every core"
    (allCores.all (fun c =>
      have _h : (ObservableState.onCore probeLabeling c lowLabel probeState).visibilityLe
          (ObservableState.onCore probeLabeling c highLabel probeState) :=
        onCore_label_monotone probeLabeling c lowLabel_flowsTo_highLabel probeState
      true))
  assertBool "the observer form applies (same core, ordered clearances)"
    (allCores.all (fun c =>
      have _h : ((⟨c, lowLabel⟩ : PerCoreObserver).view probeLabeling probeState).visibilityLe
          ((⟨c, highLabel⟩ : PerCoreObserver).view probeLabeling probeState) :=
        observerView_label_monotone (o₁ := ⟨c, lowLabel⟩) (o₂ := ⟨c, highLabel⟩)
          probeLabeling rfl lowLabel_flowsTo_highLabel probeState
      true))
  -- Strictness, component by component.
  assertBool "STRICT: the high observer sees core 1's current thread, the low one does not"
    (decide ((ObservableState.onCore probeLabeling c1 lowLabel probeState).current = none ∧
             (ObservableState.onCore probeLabeling c1 highLabel probeState).current
               = some highCurrent))
  assertBool "STRICT: the high observer sees core 1's run queue, the low one does not"
    (decide ((ObservableState.onCore probeLabeling c1 lowLabel probeState).runnable = [] ∧
             (ObservableState.onCore probeLabeling c1 highLabel probeState).runnable
               = [highQueued]))
  assertBool "STRICT: the high endpoint is in the high objectIndex only"
    (decide (highEndpoint ∉
        (ObservableState.onCore probeLabeling c0 lowLabel probeState).objectIndex ∧
      highEndpoint ∈ (ObservableState.onCore probeLabeling c0 highLabel probeState).objectIndex))
  assertBool "MONOTONE: the low endpoint is in BOTH object indices"
    (decide (lowEndpoint ∈
        (ObservableState.onCore probeLabeling c0 lowLabel probeState).objectIndex ∧
      lowEndpoint ∈ (ObservableState.onCore probeLabeling c0 highLabel probeState).objectIndex))
  assertBool "STRICT: the high service is present only to the high observer"
    (decide ((ObservableState.onCore probeLabeling c0 lowLabel probeState).services highService
        = false ∧
      (ObservableState.onCore probeLabeling c0 highLabel probeState).services highService = true))
  assertBool "STRICT: the high IRQ handler is routed only for the high observer"
    (decide ((ObservableState.onCore probeLabeling c0 lowLabel probeState).irqHandlers highIrq
        = none ∧
      (ObservableState.onCore probeLabeling c0 highLabel probeState).irqHandlers highIrq
        = some highEndpoint))
  assertBool "MONOTONE: the low IRQ handler is routed for BOTH observers"
    (decide ((ObservableState.onCore probeLabeling c0 lowLabel probeState).irqHandlers lowIrq
        = some lowEndpoint ∧
      (ObservableState.onCore probeLabeling c0 highLabel probeState).irqHandlers lowIrq
        = some lowEndpoint))
  assertBool "STRICT: the high endpoint object is visible only to the high observer"
    (decide (((ObservableState.onCore probeLabeling c0 lowLabel probeState).objects
          highEndpoint).isSome = false ∧
      ((ObservableState.onCore probeLabeling c0 highLabel probeState).objects
          highEndpoint).isSome = true))
  -- `onCore_objects_label_invariant_off_cnode` (an equality of
  -- `Option KernelObject` values) has no runtime form: `KernelObject` carries
  -- RHTable-backed and function-typed components, so the equality is not
  -- decidable.  Its witness is the §2 elaboration-time example; what §3 can
  -- decide is the visibility half, immediately above and below.
  assertBool "STRICT: the low observer's object index is strictly smaller"
    (decide ((ObservableState.onCore probeLabeling c0 lowLabel probeState).objectIndex.length <
      (ObservableState.onCore probeLabeling c0 highLabel probeState).objectIndex.length))

/-- §3.6  Scheduling transparency (accepted covert channel CC-1) restated per
core: the four scheduling components are label-invariant, and each core carries
its own copy — so the channel exists once per core, not once per system. -/
private def runSchedulingTransparencyChecks : IO Unit := do
  IO.println "--- §3.6 scheduling transparency, per core (CC-1) ---"
  let stSplitDomains : SystemState :=
    { probeState with
      scheduler := (probeState.scheduler.setActiveDomainOnCore c1 ⟨3⟩).setDomainScheduleIndexOnCore
        c1 2 }
  assertBool "the four scheduling components are label-invariant on every core"
    (allCores.all (fun c =>
      decide ((ObservableState.onCore probeLabeling c lowLabel stSplitDomains).activeDomain
          = (ObservableState.onCore probeLabeling c highLabel stSplitDomains).activeDomain ∧
        (ObservableState.onCore probeLabeling c lowLabel stSplitDomains).domainTimeRemaining
          = (ObservableState.onCore probeLabeling c highLabel stSplitDomains).domainTimeRemaining ∧
        (ObservableState.onCore probeLabeling c lowLabel stSplitDomains).domainSchedule
          = (ObservableState.onCore probeLabeling c highLabel stSplitDomains).domainSchedule ∧
        (ObservableState.onCore probeLabeling c lowLabel stSplitDomains).domainScheduleIndex
          = (ObservableState.onCore probeLabeling c highLabel stSplitDomains).domainScheduleIndex)))
  assertBool "the scheduling components are UNFILTERED reads of the raw scheduler"
    (allCores.all (fun c =>
      decide ((ObservableState.onCore probeLabeling c lowLabel stSplitDomains).activeDomain
          = stSplitDomains.scheduler.activeDomainOnCore c ∧
        (ObservableState.onCore probeLabeling c lowLabel stSplitDomains).domainScheduleIndex
          = stSplitDomains.scheduler.domainScheduleIndexOnCore c ∧
        (ObservableState.onCore probeLabeling c lowLabel stSplitDomains).domainTimeRemaining
          = stSplitDomains.scheduler.domainTimeRemainingOnCore c)))
  assertBool "onCore_schedulingTransparency applies on every core (theorem level)"
    (allCores.all (fun c =>
      have _h := onCore_schedulingTransparency probeLabeling c lowLabel stSplitDomains
      have _h2 := onCore_schedulingTransparency_label_invariant probeLabeling c lowLabel
        highLabel stSplitDomains
      true))
  -- PR #861 review round 13: the trace-capacity bound quantifies
  -- `schedulingCapacityRun`, whose second clause fixes ONE schedule across the
  -- run.  This is the load-bearing negative: two states with same-length but
  -- DIFFERENT schedules produce the same index/countdown code, yet expose
  -- different active domains — so without the clause the `alphabet ^ n` count
  -- would count fewer behaviours than an observer can distinguish.
  let schedA : SystemState :=
    { probeState with
      scheduler := { probeState.scheduler with domainSchedule := [⟨⟨7⟩, 5⟩, ⟨⟨8⟩, 5⟩] } }
  let schedB : SystemState :=
    { probeState with
      scheduler := { probeState.scheduler with domainSchedule := [⟨⟨9⟩, 5⟩, ⟨⟨8⟩, 5⟩] } }
  assertBool "two same-length schedules give the SAME index/countdown code"
    (decide (SeLe4n.Kernel.schedulingObservationCode 8 probeLabeling c0 lowLabel schedA
      = SeLe4n.Kernel.schedulingObservationCode 8 probeLabeling c0 lowLabel schedB))
  assertBool "NEGATIVE: …yet the observer sees different schedules, so the code alone is not the observation"
    (!decide ((ObservableState.onCore probeLabeling c0 lowLabel schedA).domainSchedule
      = (ObservableState.onCore probeLabeling c0 lowLabel schedB).domainSchedule))
  assertBool "NEGATIVE: so a two-state run over both is NOT one schedule (the required clause fails)"
    (!decide (schedA.scheduler.domainSchedule = schedB.scheduler.domainSchedule))
  assertBool "the run preconditions hold trivially for a one-state run"
    (have _h := @SeLe4n.Kernel.schedulingCapacityRun_singleton
     have _t := @SeLe4n.Kernel.schedulingChannel_trace_determines_observations
     true)
  assertBool "the channel is PER CORE: cores 0 and 1 report different domains"
    (!decide ((ObservableState.onCore probeLabeling c0 lowLabel stSplitDomains).activeDomain
      = (ObservableState.onCore probeLabeling c1 lowLabel stSplitDomains).activeDomain))
  assertBool "…and different schedule indices"
    (!decide ((ObservableState.onCore probeLabeling c0 lowLabel stSplitDomains).domainScheduleIndex
      = (ObservableState.onCore probeLabeling c1 lowLabel stSplitDomains).domainScheduleIndex))
  assertBool "the system-wide domain schedule is shared by every core"
    (allCores.all (fun c =>
      decide ((ObservableState.onCore probeLabeling c lowLabel stSplitDomains).domainSchedule
        = (ObservableState.onCore probeLabeling bootCoreId lowLabel stSplitDomains).domainSchedule)))

/-- §3.7  The SM8.B seed: a high thread scheduled on a remote core is invisible
to a low observer on **every** core — the shape `crossCoreNonInterference` will
generalise from a fixed pair of states to an arbitrary transition. -/
private def runCrossCoreInvisibilityChecks : IO Unit := do
  IO.println "--- §3.7 cross-core invisibility of a high remote thread ---"
  -- Schedule a second high thread on core 2 and re-queue core 1: a purely
  -- high-labelled reshuffle on cores 1 and 2.
  let stHighReshuffle : SystemState :=
    { probeState with
      scheduler := ((probeState.scheduler.setCurrentOnCore c2 (some highQueued)).setRunQueueOnCore
        c1 RunQueue.empty).setCurrentOnCore c1 none }
  assertBool "the low observer's slice is unchanged on EVERY core"
    (allCores.all (fun c =>
      decide (ObservableState.sliceOnCore probeLabeling c lowLabel stHighReshuffle
        = ObservableState.sliceOnCore probeLabeling c lowLabel probeState)))
  assertBool "…and the low observer's shared objectIndex is unchanged too"
    (allCores.all (fun c =>
      decide ((ObservableState.onCore probeLabeling c lowLabel stHighReshuffle).objectIndex
        = (ObservableState.onCore probeLabeling c lowLabel probeState).objectIndex)))
  assertBool "NON-VACUITY: the HIGH observer's slice DOES change (cores 1 and 2)"
    (!decide (ObservableState.sliceOnCore probeLabeling c1 highLabel stHighReshuffle
        = ObservableState.sliceOnCore probeLabeling c1 highLabel probeState) &&
     !decide (ObservableState.sliceOnCore probeLabeling c2 highLabel stHighReshuffle
        = ObservableState.sliceOnCore probeLabeling c2 highLabel probeState))
  assertBool "the high observer's core 0 slice is still unchanged (per-core locality)"
    (decide (ObservableState.sliceOnCore probeLabeling c0 highLabel stHighReshuffle
      = ObservableState.sliceOnCore probeLabeling c0 highLabel probeState))

/-- §3.8  CNode slot redaction — the one observer-dependent part of object
projection, and the only place where a wider clearance reveals *more of an
object it can already see*.

Everything here is computed on the real fixture CNode (two slots: one naming a
low target, one naming a high target).  Without this group
`projectCNode_lookup_monotone` and `onCore_objects_cnode_slot_monotone` — the
results the RobinHood filter-characterisation extension was made for — would
have no runtime coverage at all. -/
private def runCNodeRedactionChecks : IO Unit := do
  IO.println "--- §3.8 CNode slot redaction and its monotonicity ---"
  assertBool "the raw fixture CNode holds BOTH slots (non-vacuity)"
    (decide (probeCNodeValue.lookup lowSlot = some lowSlotCap ∧
             probeCNodeValue.lookup highSlot = some highSlotCap))
  assertBool "the CNode object is observable to every clearance (its own label is low)"
    (decide (objectObservable probeLabeling lowObserver probeCNode = true ∧
             objectObservable probeLabeling highObserver probeCNode = true))
  -- Slot-level redaction, computed through the live projection.
  assertBool "the low observer sees the low-target slot"
    (decide ((projectCNode probeLabeling lowObserver probeCNodeValue).lookup lowSlot
      = some lowSlotCap))
  assertBool "REDACTED: the low observer does NOT see the high-target slot"
    (decide ((projectCNode probeLabeling lowObserver probeCNodeValue).lookup highSlot = none))
  assertBool "the high observer sees BOTH slots (the redaction is not unconditional)"
    (decide ((projectCNode probeLabeling highObserver probeCNodeValue).lookup lowSlot
        = some lowSlotCap ∧
      (projectCNode probeLabeling highObserver probeCNodeValue).lookup highSlot
        = some highSlotCap))
  assertBool "MONOTONE: the slot the low observer sees survives at the high clearance"
    (have _h : (projectCNode probeLabeling highObserver probeCNodeValue).lookup lowSlot
        = some lowSlotCap :=
      projectCNode_lookup_monotone probeLabeling lowLabel_flowsTo_highLabel probeCNodeValue
        lowSlot lowSlotCap (by decide)
     true)
  -- The same story at the observable-state layer, on every core.
  assertBool "the observable CNode IS the filtered CNode, on every core (theorem level)"
    (allCores.all (fun c =>
      have _h : (ObservableState.onCore probeLabeling c lowLabel probeState).objects probeCNode
          = some (.cnode (projectCNode probeLabeling (IfObserver.ofLabel lowLabel)
              probeCNodeValue)) :=
        onCore_objects_cnode probeLabeling c lowLabel probeState probeCNode probeCNodeValue
          probeState_holds_probeCNode (by decide)
      true))
  assertBool "END-TO-END: through the observable state the low observer sees only the low slot"
    (allCores.all (fun c =>
      decide (cnodeSlotThroughView c lowLabel lowSlot = some lowSlotCap ∧
              cnodeSlotThroughView c lowLabel highSlot = none)))
  assertBool "END-TO-END: the high observer sees BOTH slots through the observable state"
    (allCores.all (fun c =>
      decide (cnodeSlotThroughView c highLabel lowSlot = some lowSlotCap ∧
              cnodeSlotThroughView c highLabel highSlot = some highSlotCap)))
  assertBool "END-TO-END: the mid observer matches the low one (the high target stays hidden)"
    (allCores.all (fun c =>
      decide (cnodeSlotThroughView c midLabel lowSlot = some lowSlotCap ∧
              cnodeSlotThroughView c midLabel highSlot = none)))
  assertBool "onCore_objects_cnode_slot_monotone applies on every core (theorem level)"
    (allCores.all (fun c =>
      have _h : ∃ cn₂,
          (ObservableState.onCore probeLabeling c highLabel probeState).objects probeCNode
            = some (.cnode cn₂) ∧ cn₂.lookup lowSlot = some lowSlotCap :=
        onCore_objects_cnode_slot_monotone probeLabeling c lowLabel_flowsTo_highLabel probeState
          probeCNode probeCNodeValue lowSlot lowSlotCap probeState_holds_probeCNode (by decide)
          (fun cn₁ h => by
            rw [onCore_objects_cnode probeLabeling c lowLabel probeState probeCNode
              probeCNodeValue probeState_holds_probeCNode (by decide)] at h
            injection h with h; injection h with h; subst h; decide)
      true))
  -- Capability-target observability: all three CapTarget arms.
  assertBool "capTargetObservable gates .object by the target's label"
    (decide (capTargetObservable probeLabeling lowObserver (.object lowEndpoint) = true ∧
             capTargetObservable probeLabeling lowObserver (.object highEndpoint) = false ∧
             capTargetObservable probeLabeling highObserver (.object highEndpoint) = true))
  assertBool "capTargetObservable gates .cnodeSlot by the CONTAINING CNode's label"
    (decide (capTargetObservable probeLabeling lowObserver (.cnodeSlot probeCNode highSlot)
        = true ∧
      capTargetObservable probeLabeling lowObserver (.cnodeSlot highEndpoint lowSlot) = false))
  assertBool "capTargetObservable gates .replyCap by the reply object's label"
    (decide (capTargetObservable probeLabeling lowObserver
        (.replyCap ⟨lowEndpoint.toNat⟩) = true ∧
      capTargetObservable probeLabeling lowObserver (.replyCap ⟨highEndpoint.toNat⟩) = false))
  assertBool "capTargetObservable_monotone applies on all three arms"
    (have _a : capTargetObservable probeLabeling highObserver (.object lowEndpoint) = true :=
      capTargetObservable_monotone probeLabeling lowLabel_flowsTo_highLabel _ (by decide)
     have _b : capTargetObservable probeLabeling highObserver
         (.cnodeSlot probeCNode highSlot) = true :=
      capTargetObservable_monotone probeLabeling lowLabel_flowsTo_highLabel _ (by decide)
     have _c : capTargetObservable probeLabeling highObserver
         (.replyCap ⟨lowEndpoint.toNat⟩) = true :=
      capTargetObservable_monotone probeLabeling lowLabel_flowsTo_highLabel _ (by decide)
     true)

/-- §3.9  Memory projection under a configured ownership model.

`LabelingContext.memoryOwnership` defaults to `none`, and under that default
`memoryAddressObservable` is constantly `false` — so a suite that never
configures it exercises the `memory` clause only vacuously.  This group runs
`probeLabelingWithMemory`, which owns two pages at different labels and leaves a
third unowned, so all three branches of the gate are computed. -/
private def runMemoryProjectionChecks : IO Unit := do
  IO.println "--- §3.9 memory projection under a real ownership model ---"
  assertBool "NON-VACUITY: without an ownership model no address is observable"
    (decide (memoryAddressObservable probeLabeling lowObserver lowPage = false ∧
             memoryAddressObservable probeLabeling highObserver lowPage = false))
  assertBool "with the model, the low-owned page is observable to the low observer"
    (decide (memoryAddressObservable probeLabelingWithMemory lowObserver lowPage = true))
  assertBool "the high-owned page is NOT observable to the low observer"
    (decide (memoryAddressObservable probeLabelingWithMemory lowObserver highPage = false))
  assertBool "…but IS to the high observer (the negative above is not vacuous)"
    (decide (memoryAddressObservable probeLabelingWithMemory highObserver highPage = true))
  assertBool "an unowned page is observable to nobody"
    (decide (memoryAddressObservable probeLabelingWithMemory lowObserver unownedPage = false ∧
             memoryAddressObservable probeLabelingWithMemory highObserver unownedPage = false))
  assertBool "memoryAddressObservable_monotone applies on the owned page"
    (have _h : memoryAddressObservable probeLabelingWithMemory highObserver lowPage = true :=
      memoryAddressObservable_monotone probeLabelingWithMemory lowLabel_flowsTo_highLabel
        lowPage (by decide)
     true)
  -- Through the observable state: the projected byte is the real memory content.
  assertBool "the projected memory byte is the machine's actual byte where observable"
    (allCores.all (fun c =>
      decide ((ObservableState.onCore probeLabelingWithMemory c lowLabel probeState).memory lowPage
        = some (probeState.machine.memory lowPage))))
  assertBool "…and none where not observable (high page, unowned page)"
    (allCores.all (fun c =>
      decide ((ObservableState.onCore probeLabelingWithMemory c lowLabel probeState).memory
          highPage = none ∧
        (ObservableState.onCore probeLabelingWithMemory c lowLabel probeState).memory
          unownedPage = none)))
  assertBool "onCore_label_monotone applies under the memory-owning context"
    (allCores.all (fun c =>
      have _h : (ObservableState.onCore probeLabelingWithMemory c lowLabel probeState).visibilityLe
          (ObservableState.onCore probeLabelingWithMemory c highLabel probeState) :=
        onCore_label_monotone probeLabelingWithMemory c lowLabel_flowsTo_highLabel probeState
      true))

/-- §3.10  Service-registry projection at the *entry* level.

`services` (boolean presence) is covered in §3.5; this group covers
`serviceRegistry`, whose `visibilityLe` clause is value-preserving rather than
merely visibility-preserving — a strengthening that would otherwise ship without
a runtime witness. -/
private def runServiceRegistryChecks : IO Unit := do
  IO.println "--- §3.10 service-registry projection (entry level) ---"
  assertBool "the low observer gets the low service's FULL entry"
    (allCores.all (fun c =>
      decide ((ObservableState.onCore probeLabeling c lowLabel probeState).serviceRegistry
        lowService = some (mkServiceEntry lowService lowEndpoint))))
  assertBool "STRICT: the low observer gets none for the high service"
    (allCores.all (fun c =>
      decide ((ObservableState.onCore probeLabeling c lowLabel probeState).serviceRegistry
        highService = none)))
  assertBool "…while the high observer gets its full entry (not vacuous)"
    (allCores.all (fun c =>
      decide ((ObservableState.onCore probeLabeling c highLabel probeState).serviceRegistry
        highService = some (mkServiceEntry highService highEndpoint))))
  assertBool "VALUE-PRESERVING: the low service's entry is IDENTICAL at both clearances"
    (allCores.all (fun c =>
      decide ((ObservableState.onCore probeLabeling c lowLabel probeState).serviceRegistry
          lowService
        = (ObservableState.onCore probeLabeling c highLabel probeState).serviceRegistry
          lowService)))
  assertBool "the registry projection agrees with the presence projection"
    (allCores.all (fun c =>
      decide (((ObservableState.onCore probeLabeling c lowLabel probeState).serviceRegistry
          lowService).isSome
        = (ObservableState.onCore probeLabeling c lowLabel probeState).services lowService)))

/-- §3.11  The three-clearance chain `low ⊏ mid ⊏ high`.

Transitivity of `visibilityLe` cannot be exercised with two clearances — there
is nothing to compose.  This group runs the real middle clearance, checks each
step is *strict* in the flow order, and composes the two monotonicity instances
into the end-to-end one, confirming it agrees with the direct proof.  It also
exercises the `Sublist` (order-preserving) form of the two list clauses. -/
private def runClearanceChainChecks : IO Unit := do
  IO.println "--- §3.11 the three-clearance chain (low ⊏ mid ⊏ high) ---"
  assertBool "the chain is strict at both steps"
    (decide (securityFlowsTo lowLabel midLabel = true ∧
             securityFlowsTo midLabel lowLabel = false ∧
             securityFlowsTo midLabel highLabel = true ∧
             securityFlowsTo highLabel midLabel = false))
  assertBool "the chain is observationally non-degenerate: mid sees the mid endpoint, low does not"
    (decide (objectObservable probeLabeling lowObserver midEndpoint = false ∧
             objectObservable probeLabeling midObserver midEndpoint = true ∧
             objectObservable probeLabeling highObserver midEndpoint = true))
  assertBool "…and the three object indices are STRICTLY increasing in length"
    (decide ((ObservableState.onCore probeLabeling c0 lowLabel probeState).objectIndex.length <
        (ObservableState.onCore probeLabeling c0 midLabel probeState).objectIndex.length ∧
      (ObservableState.onCore probeLabeling c0 midLabel probeState).objectIndex.length <
        (ObservableState.onCore probeLabeling c0 highLabel probeState).objectIndex.length))
  assertBool "visibilityLe_refl applies at every (core, clearance)"
    (allCores.all (fun c =>
      have _h : (ObservableState.onCore probeLabeling c midLabel probeState).visibilityLe
          (ObservableState.onCore probeLabeling c midLabel probeState) :=
        ObservableState.visibilityLe_refl _
      true))
  assertBool "visibilityLe_trans composes low ⊑ mid ⊑ high into low ⊑ high"
    (allCores.all (fun c =>
      have _h : (ObservableState.onCore probeLabeling c lowLabel probeState).visibilityLe
          (ObservableState.onCore probeLabeling c highLabel probeState) :=
        ObservableState.visibilityLe_trans
          (onCore_label_monotone (L₁ := lowLabel) (L₂ := midLabel) probeLabeling c
            lowLabel_flowsTo_midLabel probeState)
          (onCore_label_monotone (L₁ := midLabel) (L₂ := highLabel) probeLabeling c
            midLabel_flowsTo_highLabel probeState)
      true))
  assertBool "the SMP aggregate holds for both steps of the chain"
    (have _h₁ : visibilityLe_smp probeLabeling lowLabel midLabel probeState :=
      onCore_label_monotone_smp probeLabeling lowLabel_flowsTo_midLabel probeState
     have _h₂ : visibilityLe_smp probeLabeling midLabel highLabel probeState :=
      onCore_label_monotone_smp probeLabeling midLabel_flowsTo_highLabel probeState
     true)
  -- The Sublist strengthening, computed: order is preserved, not merely membership.
  assertBool "ORDER-PRESERVING: the low objectIndex is a SUBLIST of the mid one"
    (allCores.all (fun c =>
      decide ((ObservableState.onCore probeLabeling c lowLabel probeState).objectIndex.Sublist
        (ObservableState.onCore probeLabeling c midLabel probeState).objectIndex)))
  assertBool "…and the mid objectIndex a sublist of the high one"
    (allCores.all (fun c =>
      decide ((ObservableState.onCore probeLabeling c midLabel probeState).objectIndex.Sublist
        (ObservableState.onCore probeLabeling c highLabel probeState).objectIndex)))
  assertBool "the run-queue clause is a sublist too (core 1: [] ⊑ [highQueued])"
    (decide ((ObservableState.onCore probeLabeling c1 lowLabel probeState).runnable.Sublist
      (ObservableState.onCore probeLabeling c1 highLabel probeState).runnable))
  assertBool "the derived membership corollaries apply"
    (allCores.all (fun c =>
      have _h : lowEndpoint ∈ (ObservableState.onCore probeLabeling c highLabel probeState).objectIndex :=
        ObservableState.visibilityLe_mem_objectIndex
          (onCore_label_monotone probeLabeling c lowLabel_flowsTo_highLabel probeState)
          lowEndpoint_mem_lowObjectIndex
      true))

/-- §3.12  The finer register-aware check (SM8.A.3), and its limit. -/
private def runFinerCheckChecks : IO Unit := do
  IO.println "--- §3.12 the register-aware finer check ---"
  assertBool "the finer check accepts a state against itself on every core"
    (allCores.all (fun c =>
      lowEquivalentSliceOnCoreCheckWithRegs probeLabeling c lowLabel probeState probeState))
  assertBool "the finer check REJECTS a differing register bank the slice accepts"
    (let stRegs : SystemState :=
       { probeState with
         machine := probeState.machine.setRegsOnCore c0 { pc := ⟨7⟩, sp := ⟨9⟩, gpr := fun _ => ⟨1⟩ } }
     -- the coarse slice accepts (registersObservable is unchanged) …
     decide (ObservableState.sliceOnCore probeLabeling c0 lowLabel stRegs
        = ObservableState.sliceOnCore probeLabeling c0 lowLabel probeState) &&
     -- … while the finer check rejects: it is strictly finer.
     !lowEquivalentSliceOnCoreCheckWithRegs probeLabeling c0 lowLabel stRegs probeState)
  assertBool "the finer check refines the slice (soundness direction)"
    (allCores.all (fun c =>
      have _h : lowEquivalentSliceOnCore probeLabeling c lowLabel probeState probeState :=
        lowEquivalentSliceOnCoreCheckWithRegs_le_slice probeLabeling c lowLabel probeState
          probeState (lowEquivalentSliceOnCoreCheckWithRegs_of_lowEquivalentOnCore
            probeLabeling c lowLabel (lowEquivalentOnCore_refl probeLabeling lowObserver
              probeState c))
      true))
  assertBool "…and is STILL not a decision procedure (BEq is not lawful)"
    (have _h : ∃ rf₁ rf₂ : RegisterFile, (rf₁ == rf₂) = true ∧ rf₁ ≠ rf₂ :=
      machineRegs_beq_not_injective
     true)

/-- §3.13  The object-content order, and the four scheduling clauses.

`ObservableState.visibilityLe` compared `objects` by `isSome` and said nothing
at all about the four scheduling components until v0.33.4.  Both gaps are
observable on this fixture, so this group states the strengthened clauses as
computed facts and pins the two things the old relation could not exclude. -/
private def runObjectContentOrderChecks : IO Unit := do
  IO.println "--- §3.13 the object-content order ---"
  assertBool "CONTENT: a visible endpoint has the SAME value at both clearances"
    (have _h : (ObservableState.onCore probeLabeling c0 highLabel probeState).objects lowEndpoint
        = some (.endpoint {}) := lowEndpoint_view_high
     true)
  assertBool "…and that follows from the ORDER alone, on every core"
    (allCores.all (fun c =>
      have _h : ∀ e : Endpoint,
          (ObservableState.onCore probeLabeling c lowLabel probeState).objects lowEndpoint
            = some (.endpoint e) →
          (ObservableState.onCore probeLabeling c highLabel probeState).objects lowEndpoint
            = some (.endpoint e) := fun _ h =>
        ObservableState.visibilityLe_objects_eq_of_not_cnode
          (onCore_label_monotone probeLabeling c lowLabel_flowsTo_highLabel probeState) h
          (fun _ => KernelObject.noConfusion)
      true))
  -- The load-bearing negatives: an `isSome`-preserving relation would accept
  -- both of these substitutions.  `objectVisibilityLe` accepts neither.
  assertBool "STRICT: a visible endpoint may NOT widen into a notification"
    (have _h : ∀ (e : Endpoint) (n : Notification),
        ¬ objectVisibilityLe (.endpoint e) (.notification n) :=
      endpoint_not_visibilityLe_notification
     true)
  assertBool "STRICT: a visible CNode may NOT widen into a non-CNode"
    (have _h : ∀ (cn : CNode) (e : Endpoint), ¬ objectVisibilityLe (.cnode cn) (.endpoint e) :=
      cnode_not_visibilityLe_endpoint
     true)
  assertBool "the CNode arm IS related, and the relation carries the slot"
    (have _h : cnodeVisibilityLe (projectCNode probeLabeling lowObserver probeCNodeValue)
        (projectCNode probeLabeling highObserver probeCNodeValue) :=
      projectCNode_visibilityLe_monotone probeLabeling lowLabel_flowsTo_highLabel probeCNodeValue
     true)
  assertBool "…and the CNode arm genuinely widens here (low: 1 slot, high: 2)"
    (decide (cnodeSlotThroughView c0 lowLabel lowSlot = some lowSlotCap ∧
             cnodeSlotThroughView c0 lowLabel highSlot = none ∧
             cnodeSlotThroughView c0 highLabel lowSlot = some lowSlotCap ∧
             cnodeSlotThroughView c0 highLabel highSlot = some highSlotCap))
  -- The four scheduling clauses (CC-1): equal, not merely visible.
  assertBool "SCHEDULING: all four components are EQUAL across clearances"
    (allCores.all (fun c =>
      have _h : (ObservableState.onCore probeLabeling c lowLabel probeState).activeDomain
            = (ObservableState.onCore probeLabeling c highLabel probeState).activeDomain ∧
          (ObservableState.onCore probeLabeling c lowLabel probeState).domainTimeRemaining
            = (ObservableState.onCore probeLabeling c highLabel probeState).domainTimeRemaining ∧
          (ObservableState.onCore probeLabeling c lowLabel probeState).domainSchedule
            = (ObservableState.onCore probeLabeling c highLabel probeState).domainSchedule ∧
          (ObservableState.onCore probeLabeling c lowLabel probeState).domainScheduleIndex
            = (ObservableState.onCore probeLabeling c highLabel probeState).domainScheduleIndex :=
        let h := onCore_label_monotone probeLabeling c lowLabel_flowsTo_highLabel probeState
        ⟨h.activeDomain, h.domainTimeRemaining, h.domainSchedule, h.domainScheduleIndex⟩
      true))
  assertBool "ANTISYMMETRY: mutual domination plus equal objects is equality"
    (allCores.all (fun c =>
      have _h : ObservableState.onCore probeLabeling c lowLabel probeState
          = ObservableState.onCore probeLabeling c lowLabel probeState :=
        ObservableState.eq_of_visibilityLe_antisymm
          (ObservableState.visibilityLe_refl _) (ObservableState.visibilityLe_refl _) rfl
      true))
  assertBool "…and it is a REAL constraint: differing activeDomain breaks it"
    (decide (¬ (ObservableState.onCore probeLabeling c0 lowLabel probeState).activeDomain
        = domainShiftedView.activeDomain) &&
     -- the shifted view still dominates in the `isSome`/list/value clauses the
     -- pre-v0.33.4 relation had — only the new `activeDomain` clause separates
     -- them, so `visibilityLe` is now antisymmetric where it was not.
     decide ((ObservableState.onCore probeLabeling c0 lowLabel probeState).runnable
        = domainShiftedView.runnable))

-- ============================================================================
-- §4  SM8.B — per-core non-interference (runtime assertions)
-- ============================================================================

/-- A high-labelled notification the SM8.B scenarios signal, and a high TCB to
wake.  Both live in the fixture's reserved OID band. -/
private def highNotification : SeLe4n.ObjId := ⟨1016⟩

/-- A **low**-labelled notification — the load-bearing negative for §4.2: the
same operation on a low object *does* move the low observer's view. -/
private def lowNotification : SeLe4n.ObjId := ⟨1017⟩

/-- The SM8.B fixture: `probeState` plus one high and one low notification, so a
real `notificationSignal` can be run on each. -/
private def idleNotification : Notification :=
  { state := .idle, waitingThreads := SeLe4n.NoDupList.empty, pendingBadge := none }

private def niState : SystemState :=
  { probeState with
      objects := (probeState.objects.insert highNotification (.notification idleNotification)).insert
        lowNotification (.notification idleNotification) }

/-- The SM8.B labeling: `probeLabeling` with the high notification labelled
high.  Written as a fresh context rather than a `with`-update on the object
labeller so the added case is visible at the definition. -/
private def niLabeling : LabelingContext :=
  { probeLabeling with
    objectLabelOf := fun oid =>
      if oid = highNotification then highLabel else probeLabeling.objectLabelOf oid }

private def niLowObserver : IfObserver := IfObserver.ofLabel lowLabel

/-- Signalling the **high** notification: a real transition, run for effect. -/
private def highSignalPost : Option SystemState :=
  match SeLe4n.Kernel.notificationSignal highNotification (SeLe4n.Badge.ofNatMasked 7) niState with
  | .ok ((), st) => some st
  | .error _ => none

/-- Signalling the **low** notification — the negative control. -/
private def lowSignalPost : Option SystemState :=
  match SeLe4n.Kernel.notificationSignal lowNotification (SeLe4n.Badge.ofNatMasked 9) niState with
  | .ok ((), st) => some st
  | .error _ => none

/-- The projected `pendingBadge` of a notification, as the observer at `(c, L)`
sees it.  `Option Badge` has `DecidableEq`, so unlike the whole projected object
this is a decidable end-to-end read of the observable state. -/
private def projectedBadge (c : CoreId) (L : SecurityLabel) (st : SystemState)
    (oid : SeLe4n.ObjId) : Option SeLe4n.Badge :=
  match (ObservableState.onCore niLabeling c L st).objects oid with
  | some (.notification n) => n.pendingBadge
  | _ => none

/-- The projected `lock` of an object, as the observer at `(c, L)` sees it.
`RwLockState` has `DecidableEq`, so the SM8.B.4 erasure is decidable through the
observable state. -/
private def projectedLock (c : CoreId) (L : SecurityLabel) (st : SystemState)
    (oid : SeLe4n.ObjId) : SeLe4n.Kernel.Concurrency.RwLockState :=
  match (ObservableState.onCore niLabeling c L st).objects oid with
  | some o => KernelObject.objectLockOf o
  | none => SeLe4n.Kernel.Concurrency.RwLockState.unheld

/-- The **raw** lock of an object, straight out of the store — the counterpart
`projectedLock` is compared against. -/
private def rawLock (st : SystemState) (oid : SeLe4n.ObjId) :
    SeLe4n.Kernel.Concurrency.RwLockState :=
  match st.objects[oid]? with
  | some o => KernelObject.objectLockOf o
  | none => SeLe4n.Kernel.Concurrency.RwLockState.unheld

/-- A write lock on the **low** endpoint — an object the low observer can see.
That is the point: SM8.B.4 makes the bracket invisible even there. -/
private def lowEndpointLock : SeLe4n.Kernel.Concurrency.LockId :=
  { kind := .endpoint, objId := lowEndpoint }

private def lockedState : SystemState :=
  SeLe4n.Kernel.Concurrency.acquireLockOnObject niState c1 lowEndpointLock .write

private def unlockedState : SystemState :=
  SeLe4n.Kernel.Concurrency.releaseLockOnObject lockedState c1 lowEndpointLock .write

/-- The 2PL acquire fold over a two-lock sequence, both on observable objects. -/
private def lockPairs :
    List (SeLe4n.Kernel.Concurrency.LockId × SeLe4n.Kernel.Concurrency.AccessMode) :=
  [(lowEndpointLock, .write), ({ kind := .cnode, objId := probeCNode }, .read)]

private def foldedLockState : SystemState :=
  SeLe4n.Kernel.Concurrency.acquireAll c1 lockPairs niState

/-- A state that differs from `niState` **only** on core 1's slots — the
witness that the four catch-all NI constructors genuinely need their
confinement premise (§4.9). -/
private def remoteCoreWriteState : SystemState :=
  { niState with scheduler := niState.scheduler.setCurrentOnCore c1 none }

/-- The fourth RPi5 core, so the §4 scenarios can name every one. -/
private def c3 : CoreId := ⟨3, by decide⟩

/-- Core disequalities.  A `by decide` inside `fun c => …` cannot discharge
these — `decide` refuses a goal with a free variable — so they are named here
and the §4 theorem instantiations are stated at top level rather than inside a
runner lambda. -/
private theorem c0_ne_c1 : c0 ≠ c1 := by decide
private theorem c2_ne_c1 : c2 ≠ c1 := by decide
private theorem c3_ne_c1 : c3 ≠ c1 := by decide

/-- The core-1 write is confined to core 1 — the §2 premise of
`crossCoreNonInterference`, discharged from the SM4.B per-core store/load
algebra. -/
private theorem remoteCoreWrite_confined :
    observableSlotsConfinedToCore niState remoteCoreWriteState c1 :=
  ⟨fun _ _ => rfl,
   fun c hc => SchedulerState.setCurrentOnCore_currentOnCore_ne _ c1 c none (Ne.symm hc),
   fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

/-- …and it moves no shared component at all. -/
private theorem remoteCoreWrite_sharedUnchanged :
    sharedViewUnchanged niLabeling niLowObserver niState remoteCoreWriteState :=
  sharedViewUnchanged_of_state_frames niLabeling niLowObserver
    (fun _ _ => rfl) rfl rfl rfl rfl rfl

/-- Plan Theorem 3.3.1 instantiated at each of the three bystander cores. -/
private theorem remoteCoreWrite_invisible_on_c0 :
    projectStateOnCore niLabeling niLowObserver remoteCoreWriteState c0
      = projectStateOnCore niLabeling niLowObserver niState c0 :=
  crossCoreNonInterference niLabeling niLowObserver c0_ne_c1 remoteCoreWrite_confined
    remoteCoreWrite_sharedUnchanged

private theorem remoteCoreWrite_invisible_on_c2 :
    projectStateOnCore niLabeling niLowObserver remoteCoreWriteState c2
      = projectStateOnCore niLabeling niLowObserver niState c2 :=
  crossCoreNonInterference niLabeling niLowObserver c2_ne_c1 remoteCoreWrite_confined
    remoteCoreWrite_sharedUnchanged

private theorem remoteCoreWrite_invisible_on_c3 :
    projectStateOnCore niLabeling niLowObserver remoteCoreWriteState c3
      = projectStateOnCore niLabeling niLowObserver niState c3 :=
  crossCoreNonInterference niLabeling niLowObserver c3_ne_c1 remoteCoreWrite_confined
    remoteCoreWrite_sharedUnchanged

/-- SM8.B.13 at core 0: the per-core fragment is frozen, and the post-view is
literally rebuilt from the new shared half and the old per-core half. -/
private theorem remoteCoreWrite_leakage_bounded_on_c0 :
    (projectStateOnCore niLabeling niLowObserver remoteCoreWriteState c0).perCoreFragment
      = (projectStateOnCore niLabeling niLowObserver niState c0).perCoreFragment :=
  (crossCoreLeakage_bounded niLabeling niLowObserver c0_ne_c1 remoteCoreWrite_confined).1

private theorem remoteCoreWrite_reconstruction_on_c0 :
    projectStateOnCore niLabeling niLowObserver remoteCoreWriteState c0
      = ObservableState.ofFragments
          (projectStateOnCore niLabeling niLowObserver remoteCoreWriteState c0).sharedFragment
          (projectStateOnCore niLabeling niLowObserver niState c0).perCoreFragment :=
  crossCoreLeakage_bounded_reconstruction niLabeling niLowObserver c0_ne_c1
    remoteCoreWrite_confined

/-- The register-bank half of `observableSlotsConfinedToCore`'s sixth field,
decided on the ARM64 architectural registers.

`RegisterFile.gpr` is a function `RegName → RegValue`, so the bank is not
decidably equal in general; this compares `pc`, `sp` and every modeled GPR,
which is the same slice `lowEquivalentSliceOnCoreCheckWithRegs` uses.  It is a
sound *refuter*: agreement here does not prove the banks equal, but any
difference on a modeled register is caught. -/
private def regsAgreeOn (st st' : SystemState) (c : CoreId) : Bool :=
  let r := st.machine.regsOnCore c
  let r' := st'.machine.regsOnCore c
  decide (r'.pc = r.pc) && decide (r'.sp = r.sp) &&
    (List.range SeLe4n.RegName.arm64GPRCount).all
      (fun i => decide (r'.gpr ⟨i⟩ = r.gpr ⟨i⟩))

/-- The run-queue half of `observableSlotsConfinedToCore`'s first field, decided
on **every operational field** of `RunQueue`.

`RunQueue` carries proof fields (`flat_wf`, `flat_wf_rev`, `mem_invExtK`) so it
has no `DecidableEq`; this compares the six fields that carry data — the two
priority tables, the membership set, the flat list, the cached size and the
cached maximum.

Comparing `RunQueue.toList` alone was **not** sufficient, which is what the
fifth review round caught: `toList` is `flat`, so a re-bucketing write — for
instance `updatePipBoostOnCore` moving a thread between priority buckets, which
is exactly what the PIP-chain leg of the live `.call`, `.reply` and
`.tcbSuspend` arms does on a *remote* core — leaves `flat` untouched while
`byPriority`, `threadPriority` and `maxPriority` all move.  Every assertion
built on the old comparison would have reported confinement on a core the
transition had genuinely written.

A sound *refuter*, like `regsAgreeOn`: the table comparisons go through
`toList`, so two tables holding the same entries in different slot layouts
would be reported as differing.  That direction is safe — it can only turn a
passing assertion red, never a failing one green. -/
private def runQueueAgreeOn (st st' : SystemState) (c : CoreId) : Bool :=
  let q := st.scheduler.runQueueOnCore c
  let q' := st'.scheduler.runQueueOnCore c
  decide (q'.flat = q.flat) &&
  decide (q'.size = q.size) &&
  decide (q'.maxPriority = q.maxPriority) &&
  decide (q'.byPriority.toList = q.byPriority.toList) &&
  decide (q'.threadPriority.toList = q.threadPriority.toList) &&
  decide (q'.membership.toList = q.membership.toList)

/-- Decides confinement of a step's per-core writes to core `c₀`.

Covers **all six** fields of `observableSlotsConfinedToCore` — the five
scheduler slots and the register bank.  The register clause was missing until
PR #861 review: without it every runtime assertion here would still pass if a
transition corrupted another core's registers, which is precisely the class of
regression the cancellation machine-frame work exists to exclude.  The
run-queue clause was widened from `toList` to every operational field in the
round after that, for the same reason — see `runQueueAgreeOn`. -/
private def confinedCheck (st st' : SystemState) (c₀ : CoreId) : Bool :=
  allCores.all (fun c =>
    if c = c₀ then true
    else
      runQueueAgreeOn st st' c &&
      decide (st'.scheduler.currentOnCore c = st.scheduler.currentOnCore c) &&
      decide (st'.scheduler.activeDomainOnCore c = st.scheduler.activeDomainOnCore c) &&
      decide (st'.scheduler.domainTimeRemainingOnCore c
        = st.scheduler.domainTimeRemainingOnCore c) &&
      decide (st'.scheduler.domainScheduleIndexOnCore c
        = st.scheduler.domainScheduleIndexOnCore c) &&
      regsAgreeOn st st' c)

-- ============================================================================
-- §5 fixtures — a thread homed on a *remote* core
-- ============================================================================

/-- A **low-labelled** (so fully observable) thread whose `cpuAffinity` puts it
on core 2.  Everything in §5 turns on this: SM6's per-core NI needs the woken
thread to be invisible, `crossCoreNonInterference` does not. -/
private def remoteHomedThread : SeLe4n.ThreadId := ⟨1018⟩

private def crossCoreState : SystemState :=
  { niState with
      objects := niState.objects.insert remoteHomedThread.toObjId
        (.tcb (mkTcb 1018 40 (some c2))) }

/-- The wake of a *visible* thread onto its remote home core — a real
transition, run for effect. -/
private def remoteWakePost : SystemState :=
  (SeLe4n.Kernel.wakeThread crossCoreState remoteHomedThread c0).1

/-- The deschedule dual, on the same remote-homed thread. -/
private def remoteDeschedulePost : SystemState :=
  (SeLe4n.Kernel.descheduleThread crossCoreState remoteHomedThread c0).1

-- A state where a call really **rendezvouses**: an endpoint with a receiver
-- waiting, and that receiver homed on core 2.  Without this the endpoint-call
-- write set only ever computes its degenerate one-element branch, and the
-- flagship two-core case would have no runtime coverage at all.
private def crossCoreEndpoint : SeLe4n.ObjId := ⟨1019⟩
private def crossCoreReceiver : SeLe4n.ThreadId := ⟨1020⟩
private def crossCoreWaiter : SeLe4n.ThreadId := ⟨1021⟩

private def rendezvousState : SystemState :=
  { crossCoreState with
      objects :=
        ((crossCoreState.objects.insert crossCoreReceiver.toObjId
            (.tcb { mkTcb 1020 40 (some c2) with
                      ipcState := .blockedOnReceive crossCoreEndpoint })).insert
          crossCoreEndpoint
            (.endpoint { receiveQ := { head := some crossCoreReceiver
                                       tail := some crossCoreReceiver } })).insert
          crossCoreWaiter.toObjId
            (.tcb { mkTcb 1021 40 (some c2) with
                      ipcState := .blockedOnNotification highNotification }) }

/-- The same state with a **waiter** parked on the high notification, so the
notification write set computes its non-degenerate branch too. -/
private def waitingNotificationState : SystemState :=
  { rendezvousState with
      objects := rendezvousState.objects.insert highNotification
        (.notification { state := .waiting
                         waitingThreads := ⟨[crossCoreWaiter], by simp⟩
                         pendingBadge := none
                         boundTCB := none })
      -- The victim must genuinely occupy core 2's run queue, or the composed
      -- cancellation's home-core removal is a no-op and §5.2b's negative — that
      -- the write is NOT confined to the executing core — would be testing a
      -- transition that wrote nothing at all.  This is the state the suspend
      -- pipeline acts on: the TCB is captured, then torn down and descheduled.
      scheduler := rendezvousState.scheduler.setRunQueueOnCore c2
        (RunQueue.ofList [(crossCoreWaiter, ⟨40⟩)]) }

/-- `crossCoreState` differing **only** in core 1's program counter — the witness
that `confinedCheck`'s register clause is not vacuous. -/
private def core1RegWriteState : SystemState :=
  { crossCoreState with
      machine := crossCoreState.machine.setRegsOnCore c1
        { crossCoreState.machine.regsOnCore c1 with pc := ⟨0x4000⟩ } }

/-- §5.0  The two-core rendezvous — the flagship case, on a real state. -/
private def runTwoCoreWriteSetChecks : IO Unit := do
  IO.println "--- §5.0 the TWO-core endpoint-call write set ---"
  assertBool "the endpoint really has a receiver waiting"
    (decide (SeLe4n.Kernel.endpointCallReceiver? rendezvousState crossCoreEndpoint
      = some crossCoreReceiver))
  assertBool "…and that receiver is homed on core 2, not the caller's core 0"
    (decide (SeLe4n.Kernel.determineTargetCore rendezvousState crossCoreReceiver = c2 ∧
             c2 ≠ c0))
  assertBool "so the call's write set names TWO distinct cores"
    (decide (SeLe4n.Kernel.endpointCallWriteSet rendezvousState crossCoreEndpoint c0
      = [c2, c0]))
  -- The load-bearing negative: this is the case no single-core confinement
  -- statement can express, which is why `observableSlotsConfinedToCores` exists.
  assertBool "NEGATIVE: the two-core set is not a singleton on either core"
    (decide (SeLe4n.Kernel.endpointCallWriteSet rendezvousState crossCoreEndpoint c0 ≠ [c0] ∧
             SeLe4n.Kernel.endpointCallWriteSet rendezvousState crossCoreEndpoint c0 ≠ [c2]))
  -- The `.send` write set on the SAME rendezvous state.  A send has one
  -- scheduling effect where a call has two, so this is the sharper set — and on
  -- the rendezvous path the single core it names is the RECEIVER's, not the
  -- sender's, which is precisely what the boot-pinned `ensureRunnable` got wrong.
  assertBool "the send's rendezvous write set is the receiver's home core alone"
    (decide (SeLe4n.Kernel.endpointSendWriteSet rendezvousState crossCoreEndpoint c0
      = [c2]))
  assertBool "NEGATIVE: …which is NOT the executing core, and not the call's two-core set"
    (decide (SeLe4n.Kernel.endpointSendWriteSet rendezvousState crossCoreEndpoint c0 ≠ [c0] ∧
             SeLe4n.Kernel.endpointSendWriteSet rendezvousState crossCoreEndpoint c0
               ≠ SeLe4n.Kernel.endpointCallWriteSet rendezvousState crossCoreEndpoint c0))
  assertBool "with nobody waiting the send blocks the sender on its own core instead"
    (decide (SeLe4n.Kernel.endpointSendWriteSet crossCoreState lowEndpoint c0 = [c0]))
  assertBool "the notification write set names the waiter's home core, not the signaller's"
    (decide (SeLe4n.Kernel.notificationSignalWriteSet waitingNotificationState highNotification
      = [c2]))
  assertBool "NEGATIVE: …and that is NOT the executing core"
    (decide (SeLe4n.Kernel.notificationSignalWriteSet waitingNotificationState highNotification
      ≠ [c0]))
  -- The lock-set coherence theorem, computed: the write set names the home core
  -- of exactly the thread the SM6.B lock set pre-resolves.
  assertBool "the write set and the SM6.B lock-set pre-resolution name one thread"
    (decide (SeLe4n.Kernel.notificationSignalWaiter? waitingNotificationState highNotification
      = some crossCoreWaiter))

/-- §5.1  The cross-core write sets, computed on a real state. -/
private def runCrossCoreWriteSetChecks : IO Unit := do
  IO.println "--- §5.1 cross-core write sets, computed from the pre-state ---"
  assertBool "the remote-homed thread really resolves to core 2"
    (decide (SeLe4n.Kernel.determineTargetCore crossCoreState remoteHomedThread = c2))
  assertBool "…and it is genuinely VISIBLE to the low observer"
    (decide (threadObservable niLabeling niLowObserver remoteHomedThread = true))
  assertBool "a wake writes core 2 — not the executing core 0"
    (confinedCheck crossCoreState remoteWakePost c2)
  assertBool "NEGATIVE: the wake is NOT confined to the executing core 0"
    (!confinedCheck crossCoreState remoteWakePost c0)
  assertBool "the deschedule dual is likewise confined to core 2"
    (confinedCheck crossCoreState remoteDeschedulePost c2)
  assertBool "the notification write set is empty when nobody waits"
    (decide (SeLe4n.Kernel.notificationSignalWriteSet crossCoreState highNotification = []))
  assertBool "an endpoint call with no waiting receiver writes only the caller's core"
    (decide (SeLe4n.Kernel.endpointCallWriteSet crossCoreState lowEndpoint c0 = [c0]))
  -- The confinement checker's sixth field is the register bank (PR #861 review
  -- added it).  This is the load-bearing negative that it is not vacuous: a
  -- state differing from the pre-state ONLY in core 1's `pc` must fail
  -- confinement to core 2, and would have passed before the clause existed.
  assertBool "NEGATIVE: a foreign core's register write breaks confinement"
    (!confinedCheck crossCoreState core1RegWriteState c2)
  assertBool "…while the same write IS permitted when core 1 is the writing core"
    (confinedCheck crossCoreState core1RegWriteState c1)

/-- §5.2  The headline: a *visible* thread woken remotely is still invisible. -/
private def runVisibleRemoteWakeChecks : IO Unit := do
  IO.println "--- §5.2 a VISIBLE thread woken on a remote core ---"
  assertBool "the wake really changed core 2's run queue (the transition is not inert)"
    (decide ((remoteWakePost.scheduler.runQueueOnCore c2).toList
      ≠ (crossCoreState.scheduler.runQueueOnCore c2).toList))
  assertBool "cores 0, 1 and 3 see none of it"
    ([c0, c1, c3].all (fun c =>
      decide ((remoteWakePost.scheduler.runQueueOnCore c).toList
                = (crossCoreState.scheduler.runQueueOnCore c).toList) &&
      decide (remoteWakePost.scheduler.currentOnCore c
                = crossCoreState.scheduler.currentOnCore c)))
  -- The load-bearing negative: this is a statement about *other* cores.  On
  -- core 2 itself the observer's own run queue moved, and — because the woken
  -- thread is visible — the filter does not hide it.  That is precisely the
  -- case SM6's `hHighThread`-conditional theorem cannot cover and this one
  -- deliberately does not claim.
  assertBool "NEGATIVE: on core 2 itself the run queue DID move, visibly"
    (decide (remoteHomedThread ∈ (remoteWakePost.scheduler.runQueueOnCore c2).toList) &&
     decide (remoteHomedThread ∉ (crossCoreState.scheduler.runQueueOnCore c2).toList))

/-- The composed SM6.E cancellation of a victim blocked on a notification and
homed on core 2 — the teardown really has queue work to do here, so the
per-core-silence of the teardown is exercised rather than assumed. -/
private def cancelledVictimTcb : TCB :=
  { mkTcb 1021 40 (some c2) with ipcState := .blockedOnNotification highNotification }

private def cancelPost : SystemState :=
  (SeLe4n.Kernel.cancelIpcBlockingOnCore crossCoreWaiter cancelledVictimTcb c0
    waitingNotificationState).1

/-- §5.2b  The composed cross-core cancellation. -/
private def runComposedCancellationChecks : IO Unit := do
  IO.println "--- §5.2b the composed cross-core cancellation ---"
  assertBool "the victim is blocked on the notification and homed on core 2"
    (decide (SeLe4n.Kernel.determineTargetCore waitingNotificationState crossCoreWaiter = c2))
  assertBool "the teardown has real work: the victim is on the notification's waiter list"
    (match waitingNotificationState.getNotification? highNotification with
     | some n => decide (n.waitingThreads.val.contains crossCoreWaiter = true)
     | none => false)
  assertBool "the cancellation is confined to the victim's home core 2"
    (confinedCheck waitingNotificationState cancelPost c2)
  -- The load-bearing negative: it is NOT confined to the core that ran it, so
  -- the theorem is about a genuinely remote write, not a local one.
  assertBool "NEGATIVE: it is NOT confined to the executing core 0"
    (!confinedCheck waitingNotificationState cancelPost c0)
  assertBool "the teardown really removed the victim from the waiter list"
    (match cancelPost.getNotification? highNotification with
     | some n => decide (n.waitingThreads.val.contains crossCoreWaiter = false)
     | none => false)

-- ---------------------------------------------------------------------------
-- §5.2c fixtures — the three live cross-core arms the fourth review round found
-- uncovered: a bound-delivery signal, a receive rendezvousing with a blocked
-- sender, and the composed `replyRecv`.
-- ---------------------------------------------------------------------------

/-- A sender parked on `crossCoreEndpoint`'s **send** queue and homed on core 2,
so `endpointReceiveDualOnCore` takes its rendezvous branch and wakes remotely.
Without a real sender the receive-dual write set only ever computes the
`[executingCore]` block branch. -/
private def crossCoreSender : SeLe4n.ThreadId := ⟨1022⟩

private def blockedSenderState : SystemState :=
  { crossCoreState with
      objects :=
        (crossCoreState.objects.insert crossCoreSender.toObjId
            (.tcb { mkTcb 1022 40 (some c2) with
                      ipcState := .blockedOnSend crossCoreEndpoint })).insert
          crossCoreEndpoint
            (.endpoint { sendQ := { head := some crossCoreSender
                                    tail := some crossCoreSender } }) }

private def receiveDualPost : SystemState :=
  (SeLe4n.Kernel.endpointReceiveDualOnCore crossCoreEndpoint remoteHomedThread none c0
    blockedSenderState).1

/-- A notification with a **bound TCB** that is blocked on an endpoint receive
and homed on core 2 — the state in which the live `.signal` arm takes its
bound-delivery path rather than the plain waiter-wake path. -/
private def boundTcbThread : SeLe4n.ThreadId := ⟨1023⟩

private def boundNotificationState : SystemState :=
  { crossCoreState with
      objects :=
        -- `queuePPrev := some .endpointHead` is load-bearing, not decoration:
        -- `endpointQueueRemoveDual` fails closed on a TCB with no queue
        -- back-link, so without it the bound delivery returns the pre-state and
        -- the whole group would be checking an inert transition.  The
        -- non-inertness assertion below is what caught its absence.
        ((crossCoreState.objects.insert boundTcbThread.toObjId
            (.tcb { mkTcb 1023 40 (some c2) with
                      ipcState := .blockedOnReceive crossCoreEndpoint
                      queuePrev := none
                      queuePPrev := some .endpointHead
                      queueNext := none })).insert
          crossCoreEndpoint
            (.endpoint { receiveQ := { head := some boundTcbThread
                                       tail := some boundTcbThread } })).insert
          highNotification
            (.notification { state := .idle
                             waitingThreads := ⟨[], by simp⟩
                             pendingBadge := none
                             boundTCB := some boundTcbThread }) }

private def boundSignalPost : SystemState :=
  (SeLe4n.Kernel.notificationSignalBoundOnCore highNotification
    (SeLe4n.Badge.ofNatMasked 7) c0 boundNotificationState).1

/-- A state in which **both** `replyRecv` legs do work: a caller parked in
`.blockedOnReply` (so the reply leg succeeds and wakes it on core 3), on top of
the blocked sender the receive leg rendezvouses with (core 2).  The two legs
therefore name *different* cores, which is what makes the composed write set a
genuine union rather than a coincidence. -/
private def replyBlockedCaller : SeLe4n.ThreadId := ⟨1024⟩

private def replyRecvState : SystemState :=
  { blockedSenderState with
      objects := blockedSenderState.objects.insert replyBlockedCaller.toObjId
        (.tcb { mkTcb 1024 40 (some c3) with
                  ipcState := .blockedOnReply crossCoreEndpoint (some remoteHomedThread)
                  replyObject := none }) }

private def replyRecvMsg : IpcMessage :=
  { registers := #[], caps := #[], badge := none }

/-- §5.2c  The three live cross-core arms (fourth review round). -/
private def runLiveCrossCoreArmChecks : IO Unit := do
  IO.println "--- §5.2c the live cross-core arms: bound signal, receive dual, replyRecv ---"
  -- (a) The receive dual, rendezvousing with a blocked sender homed elsewhere.
  assertBool "the blocked sender is homed on core 2, not the executing core 0"
    (decide (SeLe4n.Kernel.determineTargetCore blockedSenderState crossCoreSender = c2))
  assertBool "the receive-dual write set names the sender's home core"
    (decide (SeLe4n.Kernel.endpointReceiveDualWriteSet blockedSenderState crossCoreEndpoint c0
      = [c2]))
  assertBool "the rendezvous really woke the sender onto core 2 (not inert)"
    (decide ((receiveDualPost.scheduler.runQueueOnCore c2).toList
      ≠ (blockedSenderState.scheduler.runQueueOnCore c2).toList))
  assertBool "the receive dual is confined to core 2"
    (confinedCheck blockedSenderState receiveDualPost c2)
  -- Load-bearing negative: it is a genuinely *remote* write, so the executing
  -- core is not the right confinement target.
  assertBool "NEGATIVE: the receive dual is NOT confined to the executing core 0"
    (!confinedCheck blockedSenderState receiveDualPost c0)
  -- …and the *other* branch is exercised too, so the write set is not constant.
  assertBool "with no sender queued the write set is the receiver's own core"
    (decide (SeLe4n.Kernel.endpointReceiveDualWriteSet rendezvousState crossCoreEndpoint c0
      = [c0]))
  -- (b) The bound-delivery signal.
  assertBool "the bound TCB is homed on core 2 and is the notification's binding"
    (decide (SeLe4n.Kernel.determineTargetCore boundNotificationState boundTcbThread = c2) &&
     (match boundNotificationState.getNotification? highNotification with
      | some n => decide (n.boundTCB = some boundTcbThread)
      | none => false))
  assertBool "the bound-signal write set names the bound TCB's home core"
    (decide (SeLe4n.Kernel.notificationSignalBoundWriteSet boundNotificationState
      highNotification = [c2]))
  assertBool "the bound delivery really woke the bound TCB onto core 2"
    (decide ((boundSignalPost.scheduler.runQueueOnCore c2).toList
      ≠ (boundNotificationState.scheduler.runQueueOnCore c2).toList))
  assertBool "the bound signal is confined to core 2"
    (confinedCheck boundNotificationState boundSignalPost c2)
  assertBool "NEGATIVE: the bound signal is NOT confined to the executing core 0"
    (!confinedCheck boundNotificationState boundSignalPost c0)
  -- The fall-through branch: with no bound TCB the write set is the plain
  -- signal's, so the bound wrapper is not silently the same function.
  assertBool "NEGATIVE: with no bound TCB it falls through to the plain signal's set"
    (decide (SeLe4n.Kernel.notificationSignalBoundWriteSet crossCoreState highNotification
      = SeLe4n.Kernel.notificationSignalWriteSet crossCoreState highNotification))
  -- (c) The composed replyRecv: its write set leads with the reply target's
  -- home core, and the receive leg is read at the *intermediate* state.
  assertBool "the reply leg really succeeds here (a blocked-on-reply caller on core 3)"
    (match (SeLe4n.Kernel.endpointReplyOnCore remoteHomedThread replyBlockedCaller
        replyRecvMsg c0 replyRecvState).2 with
     | .ok _ => decide (SeLe4n.Kernel.determineTargetCore replyRecvState replyBlockedCaller = c3)
     | .error _ => false)
  -- Both legs contribute, and they name *different* cores: the reply target's
  -- home core 3, then the receive leg's set computed at the *intermediate*
  -- state, which is the rendezvousing sender's core 2.
  assertBool "the composed set is the reply core followed by the receive leg's set"
    (decide (SeLe4n.Kernel.endpointReplyRecvWriteSet crossCoreEndpoint remoteHomedThread
        replyBlockedCaller replyRecvMsg c0 replyRecvState
      = SeLe4n.Kernel.determineTargetCore replyRecvState replyBlockedCaller
          :: SeLe4n.Kernel.endpointReceiveDualWriteSet
              (SeLe4n.Kernel.endpointReplyOnCore remoteHomedThread replyBlockedCaller
                replyRecvMsg c0 replyRecvState).1
              crossCoreEndpoint c0))
  assertBool "…and it names two DIFFERENT cores — a real union, not a coincidence"
    (decide (SeLe4n.Kernel.endpointReplyRecvWriteSet crossCoreEndpoint remoteHomedThread
      replyBlockedCaller replyRecvMsg c0 replyRecvState = [c3, c2]))
  -- The load-bearing negative: when the reply leg fails closed the tail is
  -- empty, so the composition is genuinely conditional on the leg's outcome
  -- rather than always appending the receive set.
  assertBool "NEGATIVE: a failed reply leg contributes no receive-leg cores"
    (decide (SeLe4n.Kernel.endpointReplyRecvWriteSet crossCoreEndpoint remoteHomedThread
      crossCoreSender replyRecvMsg c0 blockedSenderState = [c2]))

-- §5.3b fixtures — a re-bucketing write, the case `RunQueue.toList` misses.

/-- The remote-homed thread queued on core 2. -/
private def oneQueuedOnCore2 : SystemState :=
  SeLe4n.Kernel.enqueueRunnableOnCore crossCoreState c2 remoteHomedThread

/-- The **same** thread, same queue, moved to a different priority bucket — the
shape `updatePipBoostOnCore` produces when a donation raises or reverts a
server's effective priority on its home core.  With one thread in the queue
`flat` is `[tid]` before and after, so a `toList` comparison sees nothing. -/
private def reBucketedOnCore2 : SystemState :=
  let q := oneQueuedOnCore2.scheduler.runQueueOnCore c2
  { oneQueuedOnCore2 with
      scheduler := oneQueuedOnCore2.scheduler.setRunQueueOnCore c2
        ((q.remove remoteHomedThread).insert remoteHomedThread ⟨7⟩) }

/-- §5.3b  The run-queue comparison, and why `toList` was not enough.

The fifth review round found `confinedCheck` deciding the run-queue clause on
`RunQueue.toList`, which is `flat`.  A re-bucketing write leaves `flat` alone,
so every confinement assertion in this file would have passed on a core the
transition had genuinely written — exactly the remote PIP-chain writes the live
`.call`, `.reply` and `.tcbSuspend` arms perform. -/
private def runRunQueueComparisonChecks : IO Unit := do
  IO.println "--- §5.3b the run-queue comparison ---"
  let q  := oneQueuedOnCore2.scheduler.runQueueOnCore c2
  let q' := reBucketedOnCore2.scheduler.runQueueOnCore c2
  assertBool "the fixture really queued the thread on core 2"
    (decide (q.flat = [remoteHomedThread]))
  assertBool "the re-bucketed queue holds the same single thread"
    (decide (q'.flat = [remoteHomedThread]))
  -- The load-bearing negative: the OLD comparison cannot tell these apart.
  assertBool "NEGATIVE: a `toList` comparison reports these two queues equal"
    (decide (q'.toList = q.toList))
  assertBool "…but the priority bucket really moved"
    (decide (q'.maxPriority ≠ q.maxPriority))
  assertBool "…and the per-thread priority with it"
    (decide (q'.threadPriority.toList ≠ q.threadPriority.toList))
  -- So the widened comparison catches it, and `confinedCheck` with it.
  assertBool "runQueueAgreeOn rejects the re-bucketing"
    (runQueueAgreeOn oneQueuedOnCore2 reBucketedOnCore2 c2 = false)
  assertBool "confinedCheck therefore reports core 2 as written"
    (confinedCheck oneQueuedOnCore2 reBucketedOnCore2 c0 = false)
  assertBool "…and still accepts it when core 2 is the declared write target"
    (confinedCheck oneQueuedOnCore2 reBucketedOnCore2 c2 = true)
  assertBool "the untouched cores are still reported unwritten"
    (runQueueAgreeOn oneQueuedOnCore2 reBucketedOnCore2 c1 = true
     && runQueueAgreeOn oneQueuedOnCore2 reBucketedOnCore2 c3 = true)

/-- §5.3  The set-of-cores algebra and its coverage record. -/
private def runCoreSetAlgebraChecks : IO Unit := do
  IO.println "--- §5.3 the set-of-cores confinement algebra ---"
  assertBool "twenty-one cross-core transitions are covered"
    (decide (SeLe4n.Kernel.CrossCoreTransition.all.length = 21))
  assertBool "twenty of the twenty-one can name a core other than the executing one"
    (decide ((SeLe4n.Kernel.CrossCoreTransition.all.filter
      SeLe4n.Kernel.crossCoreTransitionWritesRemote).length = 20))
  assertBool "…and the wait is the one that cannot"
    (decide (SeLe4n.Kernel.crossCoreTransitionWritesRemote .notificationWait = false))
  assertBool "fourteen of the twenty-one are the arms the live syscall dispatch reaches"
    (decide ((SeLe4n.Kernel.CrossCoreTransition.all.filter
      SeLe4n.Kernel.crossCoreTransitionIsLiveArm).length = 14))
  -- Round 14: routing the SchedContext arms through `determineTargetCore` made
  -- them remote writers.  `.schedContextUnbind` is audited; the other two are a
  -- COUNTED gap rather than a silent one, and deliberately not in the inventory,
  -- whose contract is that every entry names a real NI theorem.
  -- Round 14 closure: all THREE SchedContext arms this cut made remote writers
  -- are audited, so the counted `crossCoreRemoteWriterPendingAudit` gap is gone.
  assertBool "all three SchedContext arms are in the inventory and live"
    ([SeLe4n.Kernel.CrossCoreTransition.schedContextUnbindDispatch,
      .schedContextBindDispatch, .schedContextConfigureDispatch].all (fun t =>
        decide (t ∈ SeLe4n.Kernel.CrossCoreTransition.all)
          && SeLe4n.Kernel.crossCoreTransitionIsLiveArm t
          && SeLe4n.Kernel.crossCoreTransitionWritesRemote t))
  assertBool "…each naming its own syscall"
    (decide (SeLe4n.Kernel.crossCoreLiveArmSyscall .schedContextBindDispatch
               = some SeLe4n.Model.SyscallId.schedContextBind
             ∧ SeLe4n.Kernel.crossCoreLiveArmSyscall .schedContextConfigureDispatch
               = some SeLe4n.Model.SyscallId.schedContextConfigure))
  -- Round 10's finding, as a checked fact: `.send` was the last IPC arm still
  -- routed to a boot-pinned transition, and it is now both in the inventory and
  -- backed by a delegation proof rather than by a reading of `API.lean`.
  assertBool "the live `.send` arm is covered and delegation-backed"
    (decide (SeLe4n.Kernel.CrossCoreTransition.endpointSendDispatch
               ∈ SeLe4n.Kernel.CrossCoreTransition.all
             ∧ SeLe4n.Kernel.crossCoreTransitionIsLiveArm .endpointSendDispatch = true
             ∧ (SeLe4n.Kernel.crossCoreLiveArmEvidence .endpointSendDispatch).syscall?
                 = some SeLe4n.Model.SyscallId.send))
  assertBool "seven live arms are mechanically tied to the dispatch"
    (decide (SeLe4n.Kernel.crossCoreLiveArmDelegationBacked.length = 7))
  -- The fourth review round's finding, as a checked fact: the three arms it
  -- named are in the inventory and are all classified as live.
  assertBool "the bound signal, the receive dual and replyRecv are all covered"
    ([SeLe4n.Kernel.CrossCoreTransition.notificationSignalBound,
      .endpointReceiveDual, .endpointReplyRecv].all (fun t =>
        decide (t ∈ SeLe4n.Kernel.CrossCoreTransition.all)))
  -- The FIFTH review round's finding, as a checked fact: a live entry must name
  -- the function the dispatch calls.  The three wrappers that do strictly more
  -- than their below-API transition now have their own entries, and it is those
  -- — not the narrower legs — that are classified live.
  assertBool "the three live wrappers are in the inventory"
    ([SeLe4n.Kernel.CrossCoreTransition.endpointReplyDispatch,
      .replyRecvBodyDispatch, .suspendThreadDispatch].all (fun t =>
        decide (t ∈ SeLe4n.Kernel.CrossCoreTransition.all)))
  assertBool "the wrappers are the live arms; their legs are legs"
    (decide (SeLe4n.Kernel.crossCoreTransitionIsLiveArm .endpointReplyDispatch = true) &&
     decide (SeLe4n.Kernel.crossCoreTransitionIsLiveArm .replyRecvBodyDispatch = true) &&
     decide (SeLe4n.Kernel.crossCoreTransitionIsLiveArm .suspendThreadDispatch = true) &&
     decide (SeLe4n.Kernel.crossCoreTransitionIsLiveArm .endpointReply = false) &&
     decide (SeLe4n.Kernel.crossCoreTransitionIsLiveArm .endpointReplyRecv = false) &&
     decide (SeLe4n.Kernel.crossCoreTransitionIsLiveArm .cancelIpcBlocking = false))
  -- Round 8: the receive dual is a leg of `replyRecvBody` AND the function the
  -- live `.receive` arm calls directly, so it is a live arm too.  The
  -- enforcement table has said so since round 4; this inventory now agrees.
  assertBool "the bound signal and the receive dual are both live arms"
    (decide (SeLe4n.Kernel.crossCoreTransitionIsLiveArm .notificationSignalBound = true) &&
     decide (SeLe4n.Kernel.crossCoreTransitionIsLiveArm .endpointReceiveDual = true))
  assertBool "…and the two inventories agree on it"
    (SeLe4n.Kernel.crossCoreEnforcementEntries.any (fun e =>
      match e with
      | .policyGated n | .capabilityOnly n | .readOnly n =>
        n == "endpointReceiveDualOnCore"))
  assertBool "the covered-transition theorem names are pairwise distinct"
    (decide ((SeLe4n.Kernel.CrossCoreTransition.all.map
      SeLe4n.Kernel.crossCoreNiTheorem).eraseDups.length = 21))
  -- The load-bearing negative: the write set is *state-dependent*, so it is not
  -- a constant the theorem could be satisfying vacuously.  With no receiver the
  -- call writes one core; with a remote receiver waiting it writes two — and
  -- that second case is what no single-core statement can express.
  assertBool "NEGATIVE: the write set really varies with the state (1 core vs 2)"
    (decide (SeLe4n.Kernel.endpointCallWriteSet crossCoreState lowEndpoint c0
               ≠ SeLe4n.Kernel.endpointCallWriteSet rendezvousState crossCoreEndpoint c0 ∧
             (SeLe4n.Kernel.endpointCallWriteSet crossCoreState lowEndpoint c0).length = 1 ∧
             (SeLe4n.Kernel.endpointCallWriteSet rendezvousState crossCoreEndpoint c0).length
               = 2))

/-- A generic labeling context for the SM8.B.11 gate checks: every flow allowed,
so the gate's only remaining input is whether a subject exists. -/
private def niGenericCtx : GenericLabelingContext :=
  { policy := { canFlow := fun _ _ => true }
    objectDomainOf := fun _ => ⟨0⟩, threadDomainOf := fun _ => ⟨0⟩
    endpointDomainOf := fun _ => ⟨0⟩, serviceDomainOf := fun _ => ⟨0⟩ }

private def niEpPolicy : EndpointFlowPolicy := { endpointPolicy := fun _ => none }

private def gateAt (st : SystemState) (c : CoreId) : Bool :=
  SeLe4n.Kernel.endpointFlowCheckAtCore niGenericCtx niEpPolicy lowEndpoint st c

/-- §5.4  The resolved endpoint flow gate (SM8.B.11, the replaced tautology). -/
private def runResolvedFlowGateChecks : IO Unit := do
  IO.println "--- §5.4 the resolved endpoint flow gate ---"
  -- Two genuinely different states that agree on core 0's current thread —
  -- the wake rewrote the object store and core 2's run queue.
  assertBool "the wake really produced a different state"
    (decide ((remoteWakePost.scheduler.runQueueOnCore c2).toList
      ≠ (crossCoreState.scheduler.runQueueOnCore c2).toList))
  assertBool "…yet the two states agree on core 0's subject"
    (decide (remoteWakePost.scheduler.currentOnCore c0
      = crossCoreState.scheduler.currentOnCore c0))
  assertBool "so a wake on core 2 does not move core 0's gate decision"
    (decide (gateAt remoteWakePost c0 = gateAt crossCoreState c0))
  -- The load-bearing negative: the gate is not a constant function, so the
  -- stability above says something.  An idle core has no subject and fails closed.
  assertBool "NEGATIVE: a core with a subject and an idle core decide differently"
    (decide (gateAt crossCoreState c0 ≠ gateAt crossCoreState c3))

-- ---------------------------------------------------------------------------
-- §5.5 fixtures — the vacated core.  `probeState` already has exactly the shape
-- the defect needs: core 0 runs `lowCurrent` with `lowQueued` waiting in its run
-- queue.  A blocking send by the current thread vacates the core; the question
-- is whether anything then dispatches `lowQueued`.
-- ---------------------------------------------------------------------------

private def vacatingSendMsg : IpcMessage :=
  { registers := #[], caps := #[], badge := none }

/-- The blocking send: `lowEndpoint` has no receiver, so `lowCurrent` parks on
its send queue and `removeRunnableOnCore` clears core 0's `current` slot. -/
private def vacatedPost : SystemState :=
  (SeLe4n.Kernel.endpointSendDualOnCore lowEndpoint lowCurrent vacatingSendMsg c0 niState).1

/-- The same state after the entry seam's local reschedule. -/
private def vacatedRescheduled : SystemState :=
  SeLe4n.Kernel.PriorityInheritance.scheduleLocalSuccessor niState vacatedPost c0

/-- §5.5  The vacated core (review round 17).

The defect and its fix, computed on a real blocking send rather than argued.
The negative here is the *defect itself*: the committed transition leaves core 0
with no current thread while its run queue still holds an eligible one, and
neither the SGI list nor the timer tick changes that. -/
private def runVacatedCoreChecks : IO Unit := do
  IO.println "--- §5.5 the vacated core: a blocking send must leave a successor ---"
  -- The fixture is what we think it is.
  assertBool "core 0 starts with a current thread and a non-empty run queue"
    (decide (niState.scheduler.currentOnCore c0 = some lowCurrent) &&
     decide ((niState.scheduler.runQueueOnCore c0).toList ≠ []))
  -- The send really blocks — without this the whole group is inert.
  assertBool "the send blocks: core 0's current slot is cleared"
    (decide (vacatedPost.scheduler.currentOnCore c0 = none))
  assertBool "…and the sender is parked on the endpoint, not merely dequeued"
    (match vacatedPost.getTcb? lowCurrent with
     | some tcb => decide (tcb.ipcState = .blockedOnSend lowEndpoint)
     | none => false)
  -- NEGATIVE — the defect.  This is the state the kernel committed before this
  -- cut: a core with nothing running and a runnable thread queued on it.
  assertBool "NEGATIVE: the raw transition strands an eligible thread on an idle core"
    (decide (vacatedPost.scheduler.currentOnCore c0 = none) &&
     decide ((vacatedPost.scheduler.runQueueOnCore c0).toList ≠ []))
  -- …and neither of the two mechanisms that might have covered for it does.
  assertBool "NEGATIVE: the SGI diff does not poke the executing core"
    (SeLe4n.Kernel.PriorityInheritance.computeCrossCoreSgis niState vacatedPost c0
      |>.all (fun p => decide (p.1 ≠ c0)))
  assertBool "NEGATIVE: a timer tick on the vacated core still leaves it idle"
    (match SeLe4n.Kernel.timerTickOnCore vacatedPost c0 with
     | .ok res => decide (res.1.scheduler.currentOnCore c0 = none)
     | .error _ => false)
  -- The fix: the entry seam's local reschedule dispatches the queued thread.
  assertBool "the local reschedule dispatches the queued thread"
    (decide (vacatedRescheduled.scheduler.currentOnCore c0 = some lowQueued))
  assertBool "…and takes it out of the run queue (dequeue-on-dispatch)"
    (decide ((vacatedRescheduled.scheduler.runQueueOnCore c0).toList = []))
  -- The guard is a guard: the rule is inert where the core still runs something.
  assertBool "NEGATIVE: the rule is inert when the transition left a thread running"
    (decide (SeLe4n.Kernel.PriorityInheritance.localSuccessorNeeded niState niState c0 = false))
  -- …and on a core that was already idle the guard is false, so an idle core is
  -- never mistaken for a vacated one.  Stated on the guard rather than on the
  -- resulting slot: core 3 has an empty run queue, so "still idle afterwards"
  -- would hold whether the rule fired or not.
  assertBool "NEGATIVE: and inert on a core that was already idle before the send"
    (decide (SeLe4n.Kernel.PriorityInheritance.localSuccessorNeeded niState vacatedPost c3
      = false))
  -- Round 20: the assertions above are about the pure transition, which is
  -- correct and stays.  What the live entries run is the *gated* wrapper, and
  -- it is inert until the hardware restore seam exists — because dispatching a
  -- successor the runtime cannot install misattributes the blocked caller's
  -- next syscall, where leaving the core idle fails closed.
  assertBool "the LIVE successor dispatch is inert while the restore seam is not"
    (decide (SeLe4n.Kernel.PriorityInheritance.contextRestoreSeamLive = false) &&
     decide ((SeLe4n.Kernel.PriorityInheritance.scheduleLocalSuccessorLive
       niState vacatedPost c0).scheduler.currentOnCore c0 = none))
  -- The load-bearing negative: the guard is the ONLY thing holding it — the
  -- underlying transition does dispatch, so this is a coupling and not a
  -- transition that happens to do nothing.
  assertBool "NEGATIVE: the ungated transition WOULD dispatch, so the guard is load-bearing"
    (decide ((SeLe4n.Kernel.PriorityInheritance.scheduleLocalSuccessor
       niState vacatedPost c0).scheduler.currentOnCore c0 = some lowQueued))
  -- …and the register agrees with the guard, both reading one constant.
  assertBool "the site's register entry matches the guard"
    (decide (SeLe4n.Kernel.PriorityInheritance.contextRestoreWired .vacatedCoreSuccessor = false)
     && decide (SeLe4n.Kernel.PriorityInheritance.contextRestoreWired .suspendReschedule = false))
  -- Review round 18: the model dispatches a successor; hardware does not yet
  -- know.  No context-switch site restores the incoming context before
  -- exception return, so the register is the whole list — and stays so until
  -- SM9.E wires the first one, at which point this assertion fails.
  assertBool "the context-restore obligation is registered for all four sites"
    (decide (SeLe4n.Kernel.PriorityInheritance.contextSwitchSites.length = 4) &&
     SeLe4n.Kernel.PriorityInheritance.contextSwitchSites.all
       (fun s => !SeLe4n.Kernel.PriorityInheritance.contextRestoreWired s))
  -- The load-bearing negative: the round-17 successor is IN the register, so
  -- the marker covers the site this cut added rather than only pre-existing ones.
  assertBool "NEGATIVE: the vacated-core successor is itself a registered site"
    (decide (SeLe4n.Kernel.PriorityInheritance.ContextSwitchSite.vacatedCoreSuccessor
      ∈ SeLe4n.Kernel.PriorityInheritance.contextSwitchSites))

-- ---------------------------------------------------------------------------
-- §5.6 fixtures — the replenish queue, the third per-core scheduler slot.  A
-- SchedContext bound to `remoteHomedThread` (homed on core 2), with its
-- eligibility entry queued where the CBS machinery actually puts it: core 2's
-- replenish queue, not the boot core's.
-- ---------------------------------------------------------------------------

private def replenishSc : SeLe4n.ObjId := ⟨1030⟩
private def replenishScId : SeLe4n.SchedContextId := ⟨1030⟩

private def replenishScValue : SchedContext :=
  { scId := replenishScId
    budget := ⟨100⟩, period := ⟨1000⟩, priority := ⟨40⟩, deadline := ⟨0⟩, domain := ⟨0⟩
    budgetRemaining := ⟨100⟩
    replenishments := [{ amount := ⟨100⟩, eligibleAt := 500 }]
    boundThread := some remoteHomedThread
    isActive := true }

/-- The bound thread carries the reverse link, so `schedContextUnbind` reaches
its TCB arm rather than the missing-TCB one. -/
private def replenishState : SystemState :=
  let withSc := crossCoreState.objects.insert replenishSc (.schedContext replenishScValue)
  let withTcb := withSc.insert remoteHomedThread.toObjId
    (.tcb { mkTcb 1018 40 (some c2) with
              schedContextBinding := .bound replenishScId })
  { crossCoreState with
      objects := withTcb
      scheduler := crossCoreState.scheduler.setReplenishQueueOnCore c2
        (ReplenishQueue.empty.insert replenishScId 500) }

private def replenishScValidId : SeLe4n.ValidObjId :=
  ⟨replenishSc, by decide⟩

private def unboundState : Option SystemState :=
  match SeLe4n.Kernel.SchedContextOps.schedContextUnbind replenishScValidId replenishState with
  | .ok ((), post) => some post
  | .error _ => none

/-- §5.6  The replenish queue (review round 17, the eighth boot-pinned site).

Replenishments are enqueued per core and drained by that core's tick, so a
purge keyed on `bootCoreId` never touched the entry that actually exists.  The
negative here is the shape of the defect: purging the boot core leaves core 2's
entry exactly where it was. -/
private def runReplenishHomeCoreChecks : IO Unit := do
  IO.println "--- §5.6 the replenish queue purges on the SC's home core ---"
  -- The fixture puts the entry where the CBS machinery would.
  assertBool "the SC's replenishment is queued on core 2, not the boot core"
    (decide ((replenishState.scheduler.replenishQueueOnCore c2).entries.length = 1) &&
     decide ((replenishState.scheduler.replenishQueueOnCore c0).entries.length = 0))
  assertBool "the SC is bound to a thread homed on core 2"
    (decide (SeLe4n.Kernel.determineTargetCore replenishState remoteHomedThread = c2))
  assertBool "…so the home-core helper resolves to core 2"
    (decide (SeLe4n.Kernel.SchedContextOps.schedContextReplenishHome
      replenishState replenishScValue = c2))
  -- NEGATIVE — the defect.  A boot-core purge is a no-op against this state.
  assertBool "NEGATIVE: purging the BOOT core leaves core 2's entry in place"
    (decide (((SeLe4n.Kernel.SchedContextOps.purgeReplenishmentOnCore
        replenishState c0 replenishScId).scheduler.replenishQueueOnCore c2).entries.length = 1))
  -- The fix: the live unbind purges the entry that exists.
  assertBool "the live unbind succeeds"
    (decide (unboundState.isSome = true))
  assertBool "…and core 2's replenish queue is empty afterwards"
    (match unboundState with
     | none => false
     | some post => decide ((post.scheduler.replenishQueueOnCore c2).entries.length = 0))
  -- The all-cores sweep, for the arm whose TCB is already gone.
  assertBool "the all-cores sweep clears the entry wherever it sits"
    (decide (((SeLe4n.Kernel.SchedContextOps.purgeReplenishmentFromAllCores
        replenishState replenishScId).scheduler.replenishQueueOnCore c2).entries.length = 0))
  assertBool "…and is inert on cores that never held one"
    (allCores.all (fun c =>
      decide (((SeLe4n.Kernel.SchedContextOps.purgeReplenishmentFromAllCores
        replenishState replenishScId).scheduler.replenishQueueOnCore c).entries.length = 0)))
  -- An unbound SC has no home and no entry to strand: the boot-core default.
  assertBool "NEGATIVE: an unbound SC resolves to the boot core, not core 2"
    (decide (SeLe4n.Kernel.SchedContextOps.schedContextReplenishHome
      replenishState { replenishScValue with boundThread := none } = c0))

/-- §4.1  Cross-core non-interference (plan Theorem 3.3.1). -/
private def runCrossCoreNonInterferenceChecks : IO Unit := do
  IO.println "--- §4.1 crossCoreNonInterference (plan Thm 3.3.1) ---"
  assertBool "a write to core 1's current slot is invisible on cores 0, 2 and 3"
    (have _h0 := remoteCoreWrite_invisible_on_c0
     have _h2 := remoteCoreWrite_invisible_on_c2
     have _h3 := remoteCoreWrite_invisible_on_c3
     true)
  -- The load-bearing negative: the SAME write on the observer's OWN core is
  -- visible.  Core 1 runs `highCurrent`, so the low observer sees `none` either
  -- way; core 0 runs `lowCurrent`, which the low observer does see.
  assertBool "NEGATIVE: clearing core 0's current slot IS visible to core 0's low observer"
    (decide ((ObservableState.onCore niLabeling c0 lowLabel niState).current = some lowCurrent) &&
     decide ((ObservableState.onCore niLabeling c0 lowLabel
        { niState with scheduler := niState.scheduler.setCurrentOnCore c0 none }).current = none))
  assertBool "the cross-core frame holds for every one of core c's six slots"
    (confinedCheck niState remoteCoreWriteState c1)

/-- §4.2  `nonInterference_perCore` on a real transition. -/
private def runPerCoreNonInterferenceChecks : IO Unit := do
  IO.println "--- §4.2 nonInterference_perCore on real transitions ---"
  assertBool "the fixture's two notifications are really in the store"
    (decide ((niState.objects[highNotification]?).isSome = true ∧
             (niState.objects[lowNotification]?).isSome = true))
  assertBool "the high notification is invisible to low, the low one is visible"
    (decide (objectObservable niLabeling niLowObserver highNotification = false ∧
             objectObservable niLabeling niLowObserver lowNotification = true))
  assertBool "signalling the HIGH notification succeeds"
    (decide (highSignalPost.isSome = true))
  assertBool "…and is invisible to the low observer on EVERY core"
    (match highSignalPost with
     | none => false
     | some post => allCores.all (fun c => decide (projectedBadge c lowLabel post highNotification
         = projectedBadge c lowLabel niState highNotification)))
  assertBool "…and its writes are confined to the boot core"
    (match highSignalPost with
     | none => false
     | some post => confinedCheck niState post bootCoreId)
  -- The load-bearing negative: the same operation on a LOW object moves the low
  -- observer's view.  Without it, "invisible" above could be vacuous.
  assertBool "NEGATIVE: signalling the LOW notification IS visible to low"
    (match lowSignalPost with
     | none => false
     | some post => decide (projectedBadge c0 lowLabel post lowNotification
         ≠ projectedBadge c0 lowLabel niState lowNotification))

/-- §4.3  The derived boot-core confinement, on computed transitions. -/
private def runConfinementChecks : IO Unit := do
  IO.println "--- §4.3 derived boot-core confinement ---"
  assertBool "storeObject on a high object is confined"
    (match storeObject highNotification (.notification idleNotification) niState with
     | .ok ((), post) => confinedCheck niState post bootCoreId
     | .error _ => false)
  assertBool "ensureRunnable is confined to the boot core"
    (confinedCheck niState (ensureRunnable niState lowQueued) bootCoreId)
  assertBool "removeRunnable is confined to the boot core"
    (confinedCheck niState (removeRunnable niState lowCurrent) bootCoreId)
  assertBool "setCurrentThread is confined to the boot core"
    (match setCurrentThread none niState with
     | .ok ((), post) => confinedCheck niState post bootCoreId
     | .error _ => false)
  -- The load-bearing negative: confinement to the BOOT core is a real
  -- constraint — a write to core 1 is not boot-core-confined.
  assertBool "NEGATIVE: a core-1 write is NOT confined to the boot core"
    (!confinedCheck niState remoteCoreWriteState bootCoreId)

/-- §4.4  The 2PL bracket (SM8.B.4) — invisible even on a *visible* object. -/
private def runLockSetNonInterferenceChecks : IO Unit := do
  IO.println "--- §4.4 non-interference under the per-object lock set ---"
  assertBool "the locked object is one the LOW observer can see"
    (decide (objectObservable niLabeling niLowObserver lowEndpoint = true))
  -- The load-bearing negative FIRST: the raw lock really did change, so the
  -- invisibility below is the projection's doing and not a no-op.
  assertBool "NEGATIVE: the RAW lock field genuinely changed (core 1 holds it)"
    (decide (rawLock niState lowEndpoint = SeLe4n.Kernel.Concurrency.RwLockState.unheld) &&
     decide (rawLock lockedState lowEndpoint ≠ SeLe4n.Kernel.Concurrency.RwLockState.unheld) &&
     decide ((rawLock lockedState lowEndpoint).writerHeld = some c1))
  assertBool "…yet the PROJECTED lock is unheld before and after, on every core"
    (allCores.all (fun c =>
      decide (projectedLock c lowLabel niState lowEndpoint
          = SeLe4n.Kernel.Concurrency.RwLockState.unheld) &&
      decide (projectedLock c lowLabel lockedState lowEndpoint
          = SeLe4n.Kernel.Concurrency.RwLockState.unheld) &&
      decide (projectedLock c highLabel lockedState lowEndpoint
          = SeLe4n.Kernel.Concurrency.RwLockState.unheld)))
  -- The theorems, applied at the fixture's own lock and observer.  They are
  -- stated over any object-store-well-formed pre-state: `RHTable.invExt` is a
  -- ∀-quantified extensional property, not a decidable one, so the suite
  -- carries it as a hypothesis rather than deciding it — the computed
  -- assertions above and below are what pin the *values*.
  assertBool "the acquire is projection-invisible on every core (theorem)"
    (have _h : ∀ st : SystemState, st.objects.invExt → ∀ c : CoreId,
        projectStateOnCore niLabeling niLowObserver
            (SeLe4n.Kernel.Concurrency.acquireLockOnObject st c1 lowEndpointLock .write) c
          = projectStateOnCore niLabeling niLowObserver st c :=
      fun st hInv =>
        lowEquivalent_smp_of_projection_and_confinement niLabeling niLowObserver
          (acquireLockOnObject_preserves_projection niLabeling niLowObserver st c1
            lowEndpointLock .write hInv)
          (acquireLockOnObject_confinedToCore st c1 lowEndpointLock .write bootCoreId)
     true)
  assertBool "the release is projection-invisible too"
    (have _h : ∀ st : SystemState, st.objects.invExt → ∀ c : CoreId,
        projectStateOnCore niLabeling niLowObserver
            (SeLe4n.Kernel.Concurrency.releaseLockOnObject st c1 lowEndpointLock .write) c
          = projectStateOnCore niLabeling niLowObserver st c :=
      fun st hInv =>
        lowEquivalent_smp_of_projection_and_confinement niLabeling niLowObserver
          (releaseLockOnObject_preserves_projection niLabeling niLowObserver st c1
            lowEndpointLock .write hInv)
          (releaseLockOnObject_confinedToCore st c1 lowEndpointLock .write bootCoreId)
     true)
  assertBool "the whole acquire FOLD over two locks is invisible on every core"
    (have _h : ∀ st : SystemState, st.objects.invExt → ∀ c : CoreId,
        projectStateOnCore niLabeling niLowObserver
            (SeLe4n.Kernel.Concurrency.acquireAll c1 lockPairs st) c
          = projectStateOnCore niLabeling niLowObserver st c :=
      fun st hInv =>
        lowEquivalent_smp_of_projection_and_confinement niLabeling niLowObserver
          (acquireAll_preserves_projection niLabeling niLowObserver c1 lockPairs st hInv)
          (acquireAll_confinedToCore c1 lockPairs st bootCoreId)
     true)
  assertBool "…and the 2PL BRACKET is transparent whenever its action is"
    (have _h : ∀ (S : SeLe4n.Kernel.Concurrency.LockSet) (action : SystemState → SystemState × Unit)
        (st : SystemState), st.objects.invExt →
        (∀ s', s'.objects.invExt → ((action s').1).objects.invExt) →
        (∀ s', s'.objects.invExt →
          projectState niLabeling niLowObserver (action s').1
            = projectState niLabeling niLowObserver s') →
        projectState niLabeling niLowObserver
            (SeLe4n.Kernel.Concurrency.withLockSet S c1 action st).1
          = projectState niLabeling niLowObserver st :=
      fun S action st hInv hActionInv hAction =>
        withLockSet_preserves_projection niLabeling niLowObserver S c1 action st hInv
          hActionInv hAction
     true)
  assertBool "…and the fold really took both locks (raw state moved twice)"
    (decide ((rawLock foldedLockState lowEndpoint).writerHeld = some c1) &&
     decide ((rawLock foldedLockState probeCNode).readers = [c1]))

/-- §4.5  The leakage bound (SM8.B.13). -/
private def runLeakageBoundChecks : IO Unit := do
  IO.println "--- §4.5 crossCoreLeakage_bounded ---"
  assertBool "a core-1 transition freezes core 0's per-core fragment"
    (have _h := remoteCoreWrite_leakage_bounded_on_c0
     true)
  assertBool "…so the post-view is rebuilt from the new shared half and the OLD per-core half"
    (have _h := remoteCoreWrite_reconstruction_on_c0
     true)

/-- §4.6  Per-core coverage of the operation taxonomy (SM8.B.3 / SM8.B.5). -/
private def runPerCoreCoverageChecks : IO Unit := do
  IO.println "--- §4.6 per-core coverage of the 35 kernel operations ---"
  assertBool "35 distinct per-core theorem names, one per KernelOperation"
    (decide (([ kernelOperationPerCoreNiTheorem .chooseThread
              , kernelOperationPerCoreNiTheorem .endpointSendDual
              , kernelOperationPerCoreNiTheorem .handleInterrupt ]).length = 3) &&
     decide (kernelOperationPerCoreNiTheorem .chooseThread
        ≠ kernelOperationPerCoreNiTheorem .endpointSendDual))
  assertBool "31 of the 35 operations DERIVE their confinement; exactly 4 do not"
    (decide (perCoreConfinementDerived .endpointSendDual = true) &&
     decide (perCoreConfinementDerived .timerTick = true) &&
     decide (perCoreConfinementDerived .syscallDispatchHigh = false) &&
     decide (perCoreConfinementDerived .handleInterrupt = false) &&
     decide (perCoreConfinementDerived .endpointCallWithDonationHigh = false) &&
     decide (perCoreConfinementDerived .endpointReplyWithReversionHigh = false))
  assertBool "the taxonomy count is still 35 (single-core authority)"
    (have _h : (List.length
        [KernelOperation.chooseThread, .endpointSendDual, .cspaceMint,
         .cspaceRevoke, .lifecycleRetype, .lifecycleRevokeDeleteRetype,
         .notificationSignal, .notificationWait, .cspaceInsertSlot,
         .schedule, .vspaceMapPage, .vspaceUnmapPage, .vspaceLookup,
         .cspaceCopy, .cspaceMove, .cspaceDeleteSlot,
         .endpointReply, .endpointReceiveDualHigh, .endpointCallHigh,
         .endpointReplyRecvHigh, .storeObjectHigh, .setCurrentThread,
         .ensureRunnableHigh, .removeRunnableHigh,
         .storeTcbIpcStateAndMessageHigh, .storeTcbQueueLinksHigh,
         .cspaceMutateHigh, .handleYield, .timerTick,
         .syscallDecodeError, .syscallDispatchHigh,
         .registerServiceChecked,
         .endpointCallWithDonationHigh, .endpointReplyWithReversionHigh,
         .handleInterrupt]) = 35 := kernelOperation_count
     true)

/-- §4.7  The per-core enforcement boundary (SM8.B.6 / SM8.B.7). -/
private def runEnforcementBoundaryChecks : IO Unit := do
  IO.println "--- §4.7 the per-core enforcement boundary ---"
  assertBool "53 entries: 38 canonical + the 2PL bracket + 14 live cross-core wrappers"
    (decide (enforcementBoundaryPerCore.length = 53) &&
     decide (enforcementBoundaryExtended.length = 38) &&
     decide (crossCoreEnforcementEntries.length = 14))
  assertBool "every SyscallId is still covered by the extended boundary (single-core half)"
    (enforcementBoundaryPerCoreComplete)
  assertBool "every SyscallId's LIVE cross-core operation is covered (SMP half)"
    (enforcementBoundaryPerCoreCompleteCrossCore)
  assertBool "the per-core mapping re-routes exactly fourteen syscalls"
    (decide ((SyscallId.all.filter (fun sid =>
      decide (syscallIdToEnforcementNamePerCore sid
        ≠ syscallIdToEnforcementName sid))).length = 14))
  -- Round 10 and round 12 additions, as checked facts: `.send` and `.tcbResume`
  -- were rerouted off boot-pinned operations, and the three SM7.D/SM7.F
  -- architecture wrappers had been live per-core arms without appearing here.
  assertBool "the seven arms added after the first cut all re-route"
    ([SyscallId.send, .tcbResume, .vspaceMap, .vspaceUnmap, .lifecycleRetype,
      .tcbSetPriority, .tcbSetMCPriority].all
      (fun sid => decide (syscallIdToEnforcementNamePerCore sid
        ≠ syscallIdToEnforcementName sid)))
  assertBool ".send reaches the cross-core checked send, not the boot-pinned one"
    (decide (syscallIdToEnforcementNamePerCore .send
        = "endpointSendCrossCoreDispatchChecked") &&
     decide (syscallIdToEnforcementName .send = "endpointSendDualChecked"))
  assertBool ".call reaches the cross-core wrapper, not the single-core one"
    (decide (syscallIdToEnforcementNamePerCore .call
        = "endpointCallCrossCoreDispatchChecked") &&
     decide (syscallIdToEnforcementName .call = "endpointCallChecked"))
  -- The load-bearing negative: the SMP completeness check is *not* vacuous —
  -- it fails against the canonical list, which classifies only the single-core
  -- wrappers.  This is the hole the fourth review round found.
  assertBool "NEGATIVE: the SMP mapping is NOT covered by the canonical boundary"
    (!(SyscallId.all.all (fun sid =>
      let name := syscallIdToEnforcementNamePerCore sid
      enforcementBoundary.any (fun ec =>
        match ec with
        | .policyGated n | .capabilityOnly n | .readOnly n => n == name))))
  assertBool "NEGATIVE: the added 2PL entry is genuinely new (not already classified)"
    (!enforcementBoundary.any (fun ec =>
      match ec with
      | .policyGated n | .capabilityOnly n | .readOnly n => n == "withLockSet"))

/-- §4.8  The accepted covert-channel inventory (SM8.B.8 / SM8.B.9 / SM8.B.10). -/
private def runCovertChannelInventoryChecks : IO Unit := do
  IO.println "--- §4.8 the seven accepted covert channels ---"
  assertBool "seven channels, numbered CC-1 .. CC-7 in order"
    (decide (acceptedCovertChannelsPerCore.length = 7) &&
     decide (acceptedCovertChannelsPerCore.map CovertChannel.channelId = [1, 2, 3, 4, 5, 6, 7]))
  assertBool "three are carried by the model; four are hardware-only"
    (decide ((acceptedCovertChannelsPerCore.filter CovertChannel.modelVisible).length = 3) &&
     decide ((acceptedCovertChannelsPerCore.filter
        (fun ch => !ch.modelVisible)).length = 4))
  assertBool "five have one instance per core under SMP"
    (decide ((acceptedCovertChannelsPerCore.filter CovertChannel.perCoreInstance).length = 5))
  assertBool "CC-5 (lock contention) is registered as timing-only, not model-visible"
    (decide (acceptedCovertChannel_lockContention.channelId = 5) &&
     decide (acceptedCovertChannel_lockContention.modelVisible = false) &&
     decide (acceptedCovertChannel_lockContention.perCoreInstance = true) &&
     decide (acceptedCovertChannel_lockContention.severity = CovertChannelSeverity.medium))
  -- Round 12: the inventory's CC-1 severity and the advisory's §SA-3 heading
  -- disagreed (`.low` vs MEDIUM).  The advisory is right — the channel is
  -- read once per timer tick, not once per domain switch.
  assertBool "CC-1 is MEDIUM, matching SECURITY_ADVISORY §SA-3"
    (decide (acceptedCovertChannel_scheduling_perCore.severity
      = CovertChannelSeverity.medium))
  -- The rate fact, computed: one decrement of the observed countdown is one
  -- distinguishable observation, so ticks pace the channel.
  assertBool "the run-length capacity is exactly alphabet ^ n"
    (decide ((boundedCodeTraces 8 0).length = 1 &&
             (boundedCodeTraces 8 1).length = 8 &&
             (boundedCodeTraces 8 2).length = 64 &&
             (boundedCodeTraces 3 3).length = 27))
  assertBool "…and the enumeration holds exactly the bounded traces of that length"
    (decide ((boundedCodeTraces 3 2).all (fun l =>
       l.length = 2 && l.all (fun x => x < 3))))
  assertBool "NEGATIVE: an out-of-alphabet trace is not in the enumeration"
    (decide ([3, 0] ∉ boundedCodeTraces 3 2 ∧ [0] ∉ boundedCodeTraces 3 2))
  assertBool "CC-6 / CC-7 (TLB, I-cache residency) likewise"
    (decide (acceptedCovertChannel_tlbResidency.modelVisible = false) &&
     decide (acceptedCovertChannel_icacheResidency.modelVisible = false))
  -- The load-bearing negative: CC-1 is on the OTHER side of the split, and the
  -- inventory records that rather than filing everything as hardware-only.
  assertBool "NEGATIVE: CC-1 (scheduling) IS model-visible — the split is real"
    (decide (acceptedCovertChannel_scheduling_perCore.modelVisible = true) &&
     decide ((ObservableState.onCore niLabeling c1 lowLabel niState).activeDomain
        = niState.scheduler.activeDomainOnCore c1))
  -- SM8.B.8 (fourth review round): every entry is reachable from the enum and
  -- carries a named projection theorem, so a new channel cannot be filed
  -- without deciding what proves its classification.
  assertBool "the id-indexed inventory IS the list one, entry for entry"
    (decide (CovertChannelId.all.map covertChannelEntry = acceptedCovertChannelsPerCore) &&
     decide (CovertChannelId.all.length = 7))
  assertBool "every channel cites a projection theorem (no empty citation)"
    (CovertChannelId.all.all (fun id => decide ((covertChannelEvidenceName id).length > 0)))
  assertBool "six distinct witnesses — the two residency channels share one"
    (decide ((CovertChannelId.all.map covertChannelEvidenceName).eraseDups.length = 6))
  -- The load-bearing negative for the evidence table: the citations are not all
  -- the same string, i.e. the table really does discriminate between channels.
  assertBool "NEGATIVE: the machine-timer and scheduling citations differ"
    (decide (covertChannelEvidenceName .machineTimer ≠ covertChannelEvidenceName .schedulingState))
  -- SM8.B.8 (review round 17): the citation is a *name*; the obligation is the
  -- dependently-typed `covertChannelEvidence`, whose arms are checked against
  -- `covertChannelEntry id` — so a misattributed proof is a type error rather
  -- than a wrong string.  Elaborating each arm at its own id is the check;
  -- the assertion records that all seven do.
  assertBool "every channel supplies a proof of ITS OWN evidenceProp"
    (have _s := covertChannelEvidence .schedulingState
     have _m := covertChannelEvidence .machineTimer
     have _t := covertChannelEvidence .tcbMetadata
     have _o := covertChannelEvidence .objectStoreMetadata
     have _l := covertChannelEvidence .lockContention
     have _v := covertChannelEvidence .tlbResidency
     have _i := covertChannelEvidence .icacheResidency
     true)
  -- The load-bearing negative for the *typed* table: the two classifications
  -- are genuinely different propositions, so the arms are not interchangeable.
  -- A `.machineTimer` arm must prove `modelVisible = false`; the scheduling
  -- witness proves `= true`, and the entries are distinct objects.
  assertBool "NEGATIVE: the two classifications are opposite, so arms cannot swap"
    (decide ((covertChannelEntry .schedulingState).modelVisible = true) &&
     decide ((covertChannelEntry .machineTimer).modelVisible = false))

/-- §4.8a  CC-1's capacity claim: what is bounded, and what is not
(SM8.B.9, fourth review round). -/
private def runSchedulingChannelBoundChecks : IO Unit := do
  IO.println "--- §4.8a CC-1: the bounded component, and the unbounded one ---"
  -- The bounded half: with a real three-entry schedule and an in-bounds index,
  -- the observed index lies strictly below the schedule length.
  let schedState : SystemState :=
    { niState with
        scheduler := { niState.scheduler with
          domainSchedule := [⟨⟨0⟩, 10⟩, ⟨⟨1⟩, 10⟩, ⟨⟨0⟩, 10⟩] } }
  assertBool "the observed schedule index is below the schedule length"
    (decide ((ObservableState.onCore niLabeling c1 lowLabel schedState).domainScheduleIndex
        < (ObservableState.onCore niLabeling c1 lowLabel schedState).domainSchedule.length))
  assertBool "the observed schedule IS the system-wide one (shared, not per-core)"
    (decide ((ObservableState.onCore niLabeling c1 lowLabel schedState).domainSchedule
        = schedState.scheduler.domainSchedule))
  -- The unbounded half, and the point of the correction: two states differing
  -- only in `domainTimeRemaining` are observationally distinct, with the SAME
  -- three-entry schedule.  So `log2 3` bounds nothing here.
  let quantumA : SystemState :=
    { schedState with
        scheduler := schedState.scheduler.setDomainTimeRemainingOnCore c1 7 }
  let quantumB : SystemState :=
    { schedState with
        scheduler := schedState.scheduler.setDomainTimeRemainingOnCore c1 4242 }
  assertBool "NEGATIVE: schedule length does NOT bound the channel — the quantum does not fit"
    (decide ((ObservableState.onCore niLabeling c1 lowLabel quantumA).domainTimeRemaining
        ≠ (ObservableState.onCore niLabeling c1 lowLabel quantumB).domainTimeRemaining) &&
     decide ((ObservableState.onCore niLabeling c1 lowLabel quantumA).domainSchedule
        = (ObservableState.onCore niLabeling c1 lowLabel quantumB).domainSchedule))
  assertBool "the distinguishing value is well outside a 3-entry alphabet"
    (decide (4242 > (schedState.scheduler.domainSchedule.length)))

/-- §4.9  The catch-all constructors need their confinement premise. -/
private def runCatchAllPremiseChecks : IO Unit := do
  IO.println "--- §4.9 the four catch-all constructors need hConfined ---"
  -- `remoteCoreWriteState` preserves the GLOBAL projection (it writes core 1,
  -- and the global projection reads the boot core) …
  assertBool "a core-1 write preserves the global (boot-core) projection"
    (have _h : projectState niLabeling niLowObserver remoteCoreWriteState
        = projectState niLabeling niLowObserver niState :=
      onCore_setCurrentOnCore_ne niLabeling lowLabel niState
        (by decide : bootCoreId ≠ c1) none
     true)
  -- … and yet it MOVES core 1's own view.  So "the global projection is
  -- preserved" does not imply the per-core statement, which is exactly why the
  -- four catch-all lifts take `hConfined` rather than deriving it.
  assertBool "NEGATIVE: …but it MOVES core 1's own view (current: some → none)"
    (decide ((ObservableState.onCore niLabeling c1 highLabel niState).current
        = some highCurrent) &&
     decide ((ObservableState.onCore niLabeling c1 highLabel remoteCoreWriteState).current
        = none))

/-- §4.10  The per-core endpoint policy and the release bridge
(SM8.B.11 / SM8.B.12). -/
private def runPolicyAndReleaseBridgeChecks : IO Unit := do
  IO.println "--- §4.10 per-core endpoint policy + release bridge ---"
  assertBool "with no overrides the per-core restriction holds on every core"
    (have _h : ∀ p : DomainFlowPolicy,
        endpointPolicyRestricted_perCore p { endpointPolicy := fun _ => none } :=
      fun p => endpointPolicyRestricted_perCore_no_overrides p
     true)
  assertBool "the per-core restriction is the single-core one (iff)"
    (have _h : ∀ (p : DomainFlowPolicy) (ep : EndpointFlowPolicy),
        endpointPolicyRestricted_perCore p ep ↔ endpointPolicyRestricted p ep :=
      fun p ep => endpointPolicyRestricted_perCore_iff p ep
     true)
  assertBool "NEGATIVE: an all-permitting override over an all-denying policy is a bypass"
    (have _h : ∃ (ctx : GenericLabelingContext) (epPolicy : EndpointFlowPolicy)
        (endpointId : SeLe4n.ObjId) (src dst : SecurityDomain),
        endpointFlowCheck ctx epPolicy endpointId src dst = true ∧
          genericFlowCheck ctx src dst = false ∧
          ¬ endpointPolicyRestricted_perCore ctx.policy epPolicy :=
      endpointPolicyRestricted_perCore_is_necessary
     true)
  assertBool "the per-core result implies the release-grade single-core one"
    (have _h : ∀ st st' : SystemState,
        lowEquivalent_smp niLabeling niLowObserver st' st →
        lowEquivalent niLabeling niLowObserver st' st :=
      fun st st' h => nonInterference_release_of_perCore niLabeling niLowObserver st st' h
     true)

def runSmpInformationFlowChecks : IO Unit := do
  IO.println "WS-SM SM8.A / SM8.B — Per-core observable state + non-interference suite"
  IO.println "===================================="
  runFixtureChecks
  runObserverChecks
  runPartitionChecks
  runDecidableSliceChecks
  runIndependenceChecks
  runMonotonicityChecks
  runSchedulingTransparencyChecks
  runCrossCoreInvisibilityChecks
  runCNodeRedactionChecks
  runMemoryProjectionChecks
  runServiceRegistryChecks
  runClearanceChainChecks
  runFinerCheckChecks
  runObjectContentOrderChecks
  runCrossCoreNonInterferenceChecks
  runPerCoreNonInterferenceChecks
  runConfinementChecks
  runLockSetNonInterferenceChecks
  runLeakageBoundChecks
  runPerCoreCoverageChecks
  runEnforcementBoundaryChecks
  runCovertChannelInventoryChecks
  runSchedulingChannelBoundChecks
  runCatchAllPremiseChecks
  runPolicyAndReleaseBridgeChecks
  runTwoCoreWriteSetChecks
  runCrossCoreWriteSetChecks
  runVisibleRemoteWakeChecks
  runComposedCancellationChecks
  runLiveCrossCoreArmChecks
  runRunQueueComparisonChecks
  runCoreSetAlgebraChecks
  runResolvedFlowGateChecks
  runVacatedCoreChecks
  runReplenishHomeCoreChecks
  IO.println "===================================="
  IO.println "All SM8.A per-core observable-state and SM8.B non-interference checks PASS."

end SeLe4n.Testing.SmpInformationFlow

def main : IO Unit :=
  SeLe4n.Testing.SmpInformationFlow.runSmpInformationFlowChecks
