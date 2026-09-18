-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.CrossCore.Cancellation
import SeLe4n.Kernel.Lifecycle.Invariant.CancellationQueueShape
import SeLe4n.Kernel.Lifecycle.Invariant.CancellationNotificationShape
import SeLe4n.Kernel.Lifecycle.Invariant.CancellationReplyShape
import SeLe4n.Kernel.Concurrency.Locks.ResolvedFootprintBounds
import SeLe4n.Kernel.Architecture.SyscallReturn
import SeLe4n.Kernel.Scheduler.PriorityInheritance.PerCore
import SeLe4n.Testing.StateBuilder

/-!
# WS-SM SM6.E — Cross-core cancellation test suite

Tier-2 (runtime) + Tier-3 (surface anchor) coverage for the WS-SM Phase SM6.E
"Cancellation across cores" deliverable
(`docs/planning/SMP_CROSS_CORE_IPC_PLAN.md` §3.1, §5).

* **§1 Surface anchors** — every public SM6.E symbol resolves at elaboration
  time (rename/removal fails the build).
* **§2 Elaboration-time examples** — apply the headline theorems (the
  `cancellation_cross_core_correct` flagship, SGI emission, 2PL atomicity)
  to verified inputs.
* **§3 Runtime assertions** — `lake exe smp_cancellation_suite` exercises the
  actual `cancelIpcBlockingOnCore` / `cancelDonationOnCore` /
  `lockSet_cancelIpcBlocking` computations on the SM6.E cancellation
  scenarios: cancelling endpoint-blocked / notification-blocked /
  reply-blocked victims homed on a remote core, descheduling an actively
  running remote victim (SGI) vs a local one (no SGI), the per-core
  donation-cancellation arms (bound unbind with home-core replenish-queue
  purge; donated return-to-owner), the dispatcher identity on `.unbound`,
  the state-resolved lock-set footprints, and the `withLockSet` bracket's
  operational atomicity.
-/

namespace SeLe4n.Testing.SmpCancellation

open SeLe4n.Model
open SeLe4n.Kernel
open SeLe4n.Kernel.Concurrency
open SeLe4n.Kernel.Lifecycle.Suspend
open SeLe4n.Testing

-- ============================================================================
-- §1  Surface anchors (Tier-3): every SM6.E public symbol resolves
-- ============================================================================

-- SM6.E.5 the per-core deschedule primitive (wakeThread dual) + its surface,
-- keyed on placement since WS-RR RR8.6:
#check @descheduleAt
#check @descheduleSgi?
#check @descheduleThread
#check @descheduleThread_state_eq
#check @descheduleThread_sgi_eq
#check @descheduleThread_objects_eq
#check @descheduleThread_emits_sgi_if_remote_current
#check @descheduleThread_no_sgi_if_local
#check @descheduleThread_no_sgi_if_not_current
#check @descheduleThread_unplaced
#check @descheduleThread_descheduled_at_placement
#check @descheduleThread_independent_of_other_core

-- SM6.E.1/.5 cross-core cancellation transitions + reductions:
#check @cancelIpcBlockingOnCore
#check @cancelIpcBlockingOnCore_state_eq
#check @cancelIpcBlockingOnCore_objects_eq
#check @cancelIpcBlockingOnCore_eq_descheduleThread
#check @cancelIpcBlockingOnCore_ready_eq_descheduleThread

-- SM6.E.3 per-core donation cancellation + the bootCore bridge:
#check @cancelBoundDonationOnCore
#check @cancelBoundDonationOnCore_bootCoreId
#check @cancelDonationOnCore

-- SM6.E.5 SGI emission of the composite:
#check @cancelIpcBlockingOnCore_emits_sgi_if_remote_current
#check @cancelIpcBlockingOnCore_no_sgi_if_local
#check @cancelIpcBlockingOnCore_no_sgi_if_not_current

-- SM6.E.1/.3 lock-set footprints + pre-resolution + state-resolved forms:
#check @cancelBlockedEndpoint?
#check @cancelBlockedNotification?
#check @cancelConsumedReply?
#check @cancelBindingSc?
#check @cancelDonatedOwner?
#check @lockSet_cancelIpcBlocking
#check @lockSet_cancelDonation
#check @lockSet_cancelIpcBlockingOnCore
#check @lockSet_cancelDonationOnCore

-- SM6.E.1/.3 lock-set hierarchical correctness:
#check @lockSet_consistent_cancelIpcBlocking
#check @lockSet_consistent_cancelDonation
#check @cancelIpcBlockingOnCore_lockSet_correct
#check @cancelDonationOnCore_lockSet_correct
#check @lockSet_cancelIpcBlockingOnCore_correct
#check @lockSet_cancelDonationOnCore_correct

-- SM6.E write coverage (cancellation footprints + the enclosing suspend
-- footprint, member-by-member):
#check @LockSet.mem_insertOrMerge_write_of_mem_write
#check @mem_write_lockSetExtendOpt
#check @lockSet_cancelIpcBlocking_victim_tcb_write_mem
#check @lockSet_cancelIpcBlocking_blocked_endpoint_write_mem
#check @lockSet_cancelIpcBlocking_blocked_notification_write_mem
#check @lockSet_cancelIpcBlocking_consumed_reply_write_mem
#check @lockSet_cancelDonation_victim_tcb_write_mem
#check @lockSet_cancelDonation_binding_sc_write_mem
#check @lockSet_cancelDonation_donated_owner_tcb_write_mem
-- **WS-OD (`v0.35.4`)**: the parametric `lockSet_tcbSuspend_*_write_mem` family
-- is retired with the footprint it was about.  The syscall's footprint is
-- `lockSet_tcbSuspendOnCore`, *defined over* the state-resolved cancellation
-- footprint, so the teardown's coverage crosses one lift and the pipeline's own
-- members have their own family.
#check @lockSet_tcbSuspendOnCore
#check @lockSet_tcbSuspendOnCore_correct
#check @lockSet_tcbSuspendOnCore_covers_cancelIpcBlockingOnCore
#check @lockSet_tcbSuspendOnCore_covers_victim
#check @lockSet_tcbSuspendOnCore_covers_tail
#check @lockSet_tcbSuspendOnCore_covers_boundCancel
#check @lockSet_tcbSuspendOnCore_covers_donatedCancel
#check @lockSet_tcbSuspendOnCore_covers_reclaimSecondPop
#check @suspendDonationCancelTail?
#check @suspendDonationCancelTailOf?
#check @cancelledCallerAlreadyBound
-- WS-OD (`v0.35.4`): the teardown footprint's own new members.
#check @cancelReclaimHead?
#check @cancelSplicedFrameAbove?
#check @cancelDonationPopMembers?
#check @lockSet_cancelIpcBlocking_reclaim_head_write_mem
#check @lockSet_cancelIpcBlocking_spliced_frame_above_write_mem
#check @lockSet_cancelIpcBlocking_below_head_write_mem
#check @lockSet_cancelIpcBlocking_outer_caller_containsKey
#check @lockSet_cancelDonation_head_write_mem
#check @lockSet_cancelDonation_below_head_write_mem
#check @lockSet_cancelDonation_outer_caller_containsKey
#check @lockSet_cancelIpcBlockingOnCore_covers_reclaim
#check @lockSet_cancelIpcBlockingOnCore_covers_splicedFrameAbove

-- SM6.E.2/.4 2PL atomicity (single-core + cross-core forms):
#check @cancelIpcBlocking_atomic_under_lockSet
#check @cancelIpcBlockingOnCore_atomic_under_lockSet
#check @cancelDonation_atomic_under_lockSet
#check @cancelDonationOnCore_atomic_under_lockSet

-- SM6.E invariant preservation + per-core donation frames:
#check @cancelIpcBlocking_preserves_objects_invExt
#check @cancelIpcBlockingOnCore_preserves_objects_invExt
#check @cancelBoundDonation_preserves_objects_invExt
#check @cancelBoundDonationOnCore_preserves_objects_invExt
#check @cancelDonatedDonation_preserves_objects_invExt
#check @cancelDonation_preserves_objects_invExt
#check @cancelDonationOnCore_preserves_objects_invExt
#check @cancelDonatedDonation_scheduler_eq
#check @cancelBoundDonationOnCore_runQueue_current_eq
#check @cancelBoundDonationOnCore_replenishQueue_purged
#check @cancelBoundDonationOnCore_replenishQueue_ne
#check @cancelDonationOnCore_runQueue_current_eq

-- SM6.E cleanup-primitive invExt lemmas (CleanupPreservation):
#check @spliceOutMidQueueNode_preserves_objects_invExt
#check @removeFromAllEndpointQueues_preserves_objects_invExt
#check @removeFromAllNotificationWaitLists_preserves_objects_invExt
#check @cleanupDonatedSchedContext_preserves_objects_invExt

-- SM6.E flagship:
#check @cancellation_cross_core_correct

-- SM6.E completion cut: the closed-form composition, resolution frames,
-- per-key lookup keystones, ipcInvariant preservation, observational
-- atomicity, live per-core suspend, and the SGI deschedule rule.
#check @SeLe4n.Kernel.RobinHood.RHTable.fold_preserves_of_lookup
#check @spliceOutMidQueueNode_tcb_lookup
#check @removeFromAllEndpointQueues_tcb_lookup
#check @removeFromAllNotificationWaitLists_tcb_lookup
#check @cancelIpcBlocking_tcb_lookup
#check @cancelIpcBlocking_getTcb?_none
#check @cancelIpcBlocking_determineTargetCore_eq
-- WS-RR RR8.6: the placement the composite deschedules at, read off the
-- pre-state — the relation between a footprint declared before the transition
-- runs and a removal resolved after the reclaim's wake.
#check @placedCoreOf?_congr_of_contains_current_eq
#check @placedCoreOf?_eq_some_of_unique
#check @descheduleAtPlacementCores_eq_toList
#check @cancelIpcBlockingMigrated_placedCoreOf?
#check @cancelIpcBlockingOnCore_placedCoreOf?_cases
#check @cancelIpcBlockingOnCore_placedCoreOf?_of_some
#check @cancelIpcBlockingOnCore_runningOnSomeCore
#check @cancelIpcBlockingOnCoreSchedLockSet_covers_deschedule
#check @notificationQueueWellFormed_filter_correct
#check @cancelIpcBlocking_preserves_ipcInvariant
#check @cancelIpcBlockingOnCore_preserves_ipcInvariant
#check @cancelDonationOnCore_preserves_ipcInvariant
#check @descheduleThread_preserves_ipcInvariant
#check @updateObjectLockAt_getTcb?_ipcState
#check @acquireLockOnObject_preserves_invExt
#check @releaseLockOnObject_preserves_invExt
#check @cancelLockOnObject_preserves_invExt
#check @cancellationObserver_acquireInsensitiveOn
#check @cancellationObserver_unwindInsensitiveOn
#check @cancelIpcBlockingOnCore_observer_atomic
#check @cancelIpcBlockingOnCore_bootPlaced_state_eq
#check @descheduleThread_fully_descheduled
#check @cancelBoundDonationOnCore_replenishments_purged
#check @cancelDonationOnCore_bootHome_ok
#check @cancelDonationOnCore_bootHome_error
#check @Lifecycle.Suspend.suspendThreadOnCore
#check @Lifecycle.Suspend.suspendThreadOnCore_rejects_absent
#check @Lifecycle.Suspend.suspendThreadOnCore_rejects_inactive
#check @Lifecycle.Suspend.suspendThreadOnCore_sgi_remote_reschedule
#check @Lifecycle.Suspend.suspendThreadOnCore_local_no_sgi

-- PR #831 review 2: disinheritance scheduling points (local preemption gate +
-- the diff seam's deboosted-current rule) + the factored G7 dispatch.
#check @Lifecycle.Suspend.currentEffectivePrio?
#check @Lifecycle.Suspend.currentDeboostedFrom
#check @Lifecycle.Suspend.suspendRescheduleOnCore
#check @Lifecycle.Suspend.suspendRescheduleOnCore_sgi_shape
#check @Lifecycle.Suspend.suspendRescheduleOnCore_local_no_sgi
#check @SeLe4n.Kernel.PriorityInheritance.crossCoreSgiBody_remote_deboost_current

-- PR #831 review 4: running-core resolution + write-set-honest sweeps.
#check @Lifecycle.Suspend.runningCoreOf?
#check @SeLe4n.Kernel.PriorityInheritance.currentScan_boot_of_single_core
#check @queueSpliceNeighbors?

-- Audit closure: sorted run-queue triple, current-uniqueness slice,
-- donation-side observer capstone.
#check @sortedSchedCoreTriple
#check @sortedSchedCoreTriple_pairwise_le
#check @currentThreadUniqueAcrossCores
#check @default_currentThreadUniqueAcrossCores
#check @removeRunnableOnCore_preserves_currentThreadUniqueAcrossCores
#check @descheduleThread_preserves_currentThreadUniqueAcrossCores
#check @cancelDonationOnCore_observer_atomic
#check @PriorityInheritance.crossCoreSgiBody_remote_deschedule
-- WS-RR RR7.22 (residual): the object-store sweep, characterised per key.  The
-- fact the cancellation bundle needs — "afterwards no endpoint still names the
-- swept thread at a boundary" — is false of the accumulator mid-fold, so it is
-- not a fold invariant; `RHTable.fold_pointwise` is the lemma that establishes
-- a pointwise one, and the sweep body is named so a proof can quantify over it.
#check @SeLe4n.Kernel.RobinHood.RHTable.fold_pointwise
#check @endpointSweepBody
#check @removeFromAllEndpointQueues_eq_fold
#check @threadOffQueueBoundaries
#check @removeThreadFromQueue_off_boundary
#check @removeFromAllEndpointQueues_off_boundary
#check @removeFromAllEndpointQueues_endpoint_value
#check @removeFromAllEndpointQueues_tcb_frame
#check @removeFromAllEndpointQueues_tcb_source
#check @removeFromAllEndpointQueues_endpoint_source
-- The mid-queue splice's own per-key readings: what it installs at the two
-- neighbours, and what it leaves everywhere else.
#check @tcbQueueLinkRewrite
#check @queueNeighbourPatch
#check @spliceOutMidQueueNode_eq_patches
#check @spliceOutMidQueueNode_tcb_backward
#check @spliceOutMidQueueNode_nonTcb
#check @spliceOutMidQueueNode_victim_tcb
#check @spliceOutMidQueueNode_next_queuePrev
#check @spliceOutMidQueueNode_prev_queueNext
#check @spliceOutMidQueueNode_queuePrev_frame
#check @spliceOutMidQueueNode_queueNext_frame
-- WS-RR RR7.22 (residual): the queue shape across sweep-then-restore, and the
-- three facts `ipcInvariantFull` does not entail, stated rather than assumed.
#check @queueBoundaryCoherentAt
#check @sweptThreadBoundaryCoherent
#check @sweptPredecessorBlocked
#check @sweptSuccessorAnchored
#check @sweptThreadQueueCoherent
#check @queueBoundaryCoherentAt_of_off_boundary
#check @sweptQueue_wellFormed
#check @restoredTcb
#check @restoredTcb_eq
#check @sweptAndRestored
#check @sweptAndRestored_tcb_iff
#check @sweptAndRestored_victim_tcb
#check @sweptAndRestored_tcbQueueLinkIntegrity
#check @sweptAndRestored_edge_source
#check @sweptAndRestored_path_transport
#check @sweptAndRestored_tcbQueueChainAcyclic
#check @sweptAndRestored_dualQueueSystemInvariant
-- WS-RR RR7.22 (residual): the sharp pointwise reading and the transports.
#check @sweptAndRestored_tcb_pullback
#check @sweptAndRestored_tcb_value
#check @sweptAndRestored_tcb_forward
#check @sweptAndRestored_no_next_to_victim
#check @sweptAndRestored_endpoint_queues
#check @sweptAndRestored_endpoint_forward
#check @sweptAndRestored_membership_witness
#check @sweptAndRestored_nonTcbNonEndpoint
#check @sweptAndRestored_sameSchedContextBindings
#check @sweptAndRestored_timeoutBudgetFrame
#check @sweptAndRestored_passiveServerIdleFrame
#check @sweptAndRestored_donationOwnerFrame
#check @sweptAndRestored_replyLinkageFrame
-- WS-RR RR7.22 (residual): every conjunct of `ipcInvariantFull`, then the bundle
-- and the live cancellation arm it covers.
#check @sweptAndRestored_ipcInvariant
#check @sweptAndRestored_badgeWellFormed
#check @sweptAndRestored_allPendingMessagesBounded
#check @sweptAndRestored_blockedThreadsPendingMessageConsistent
#check @sweptAndRestored_blockedOnReplyHasTarget
#check @sweptAndRestored_donationChainAcyclic
#check @sweptAndRestored_queueNextTargetBlocked
#check @sweptAndRestored_queueNextBlockingConsistent
#check @sweptAndRestored_endpointQueueNoDup
#check @sweptAndRestored_ipcStateQueueMembershipConsistent
#check @sweptAndRestored_queueHeadBlockedConsistent
#check @sweptAndRestored_endpointQueueTailBlockedConsistent
#check @sweptAndRestored_replyCallerLinkage
#check @sweptAndRestored_pendingReceiveReplyWellFormed
#check @sweptAndRestored_preserves_ipcInvariantFull
#check @cancelIpcBlocking_endpoint_arm_eq
#check @cancelIpcBlocking_endpointArm_preserves_ipcInvariantFull
#check @replyObject_none_of_not_blockedOnReply
-- WS-RR RR7.22 (residual): the notification arm — its purge description, its one
-- coherence hypothesis, every conjunct, the keystone and the live arm.
#check @notificationPurgeBody
#check @removeFromAllNotificationWaitLists_eq_fold
#check @removeFromAllNotificationWaitLists_nonNotification
#check @removeFromAllNotificationWaitLists_notification_badge
#check @purgedAndRestored
#check @sweptThreadOffQueueChains
#check @purgedAndRestored_tcb_iff
#check @purgedAndRestored_victim_tcb
#check @purgedAndRestored_tcb_pullback
#check @purgedAndRestored_tcb_links
#check @purgedAndRestored_tcb_links_forward
#check @purgedAndRestored_path_transport
#check @purgedAndRestored_dualQueueSystemInvariant
#check @purgedAndRestored_sameSchedContextBindings
#check @purgedAndRestored_timeoutBudgetFrame
#check @purgedAndRestored_passiveServerIdleFrame
#check @purgedAndRestored_donationOwnerFrame
#check @purgedAndRestored_replyLinkageFrame
#check @purgedAndRestored_ipcInvariant
#check @purgedAndRestored_badgeWellFormed
#check @purgedAndRestored_allPendingMessagesBounded
#check @purgedAndRestored_blockedThreadsPendingMessageConsistent
#check @purgedAndRestored_blockedOnReplyHasTarget
#check @purgedAndRestored_donationChainAcyclic
#check @purgedAndRestored_pendingReceiveReplyWellFormed
#check @purgedAndRestored_replyCallerLinkage
#check @purgedAndRestored_victim_off_endpoint_boundaries
#check @purgedAndRestored_queueHeadBlockedConsistent
#check @purgedAndRestored_endpointQueueTailBlockedConsistent
#check @purgedAndRestored_edge_avoids_victim
#check @purgedAndRestored_queueNextTargetBlocked
#check @purgedAndRestored_queueNextBlockingConsistent
#check @purgedAndRestored_endpointQueueNoDup
#check @purgedAndRestored_ipcStateQueueMembershipConsistent
#check @purgedAndRestored_preserves_ipcInvariantFull
#check @cancelIpcBlocking_notification_arm_eq
#check @cancelIpcBlocking_notificationArm_preserves_ipcInvariantFull
-- WS-RR RR7.22 (residual, remediation): the cancelled caller's donation goes
-- back — seL4-MCS's `reply_remove` semantics at the cancellation point, where
-- upstream defers them to Reply-object finalisation (`v0.35.40`: `cancelIPC` itself
-- runs `reply_remove_tcb` and donates nothing) — and the fact that makes the
-- return well defined, stated rather than assumed.
#check @Lifecycle.Suspend.cancelledCallerDonation?
#check @Lifecycle.Suspend.returnDonationToCancelledCaller
#check @cancelledCallerDonation?_some
-- WS-RR RR8.7: the reply arm's own keystone and the four steps it composes.
#check @abortHolderQueueCoherent
#check @abortHolderPendingIpc_preserves_ipcInvariantFull
#check @abortHolderPendingIpc_preserves_allTimeoutBudgetsNone
#check @cancelledCallerDonation?_holder_holds_victim_donation
#check @cancelledCallerDonation?_holder_ne_victim
#check @abortHolderPendingIpc_offQueue_tcb_eq
#check @returnDonationToCancelledCaller_preserves_ipcInvariantFull
#check @returnDonationToCancelledCaller_preserves_allTimeoutBudgetsNone
#check @returnDonationToCancelledCaller_victim_tcb_rewrite
#check @spliceThreadReplyFrameOut_preserves_ipcInvariantFull
#check @restoredAndConsumed_congr
#check @cancelIpcBlocking_reply_arm_eq
#check @cancelIpcBlocking_replyArm_preserves_ipcInvariantFull
-- WS-HP HP5.2: the coherence fact re-keyed onto the head-driven trigger, with
-- both vacuous discharges and the builder that measures what it costs.
#check @donatedContextIsOwnerFrameHead
#check @donatedContextIsOwnerFrameHead_of_no_owner
#check @donatedContextIsOwnerFrameHead_of_no_donation
#check @donatedContextIsOwnerFrameHead_of_donationOwnerValid
#check @returnDonationToCancelledCaller_no_donation_to_victim
#check @cancelIpcBlocking_reply_no_donation_to_victim
#check @Lifecycle.Suspend.returnDonationToCancelledCaller_scheduler_eq
#check @Lifecycle.Suspend.returnDonationToCancelledCaller_machine_eq
#check @Lifecycle.Suspend.returnDonationToCancelledCaller_serviceRegistry_eq
#check @Lifecycle.Suspend.returnDonationToCancelledCaller_preserves_objects_invExt
#check @Lifecycle.Suspend.returnDonationToCancelledCaller_preserves_ipcInvariant
#check @Lifecycle.Suspend.returnDonationToCancelledCaller_tcb_lookup
#check @Lifecycle.Suspend.returnDonationToCancelledCaller_eq_self_of_getTcb?_none
-- WS-OD OD1.4: the reclaim's holder abort — the `passiveServerIdle` half.  The
-- operation, its frames, the two facts the hand-back reads across it
-- (`donationOwnerValid`, the holder's own binding), the identity-registry
-- carriage its information-flow argument needs, and the exact bound on its
-- reach: it is the identity unless the holder is blocked sending or calling.
#check @Lifecycle.Suspend.abortHolderPendingIpc
#check @abortPendingIpcOnEndpoint_shape
#check @abortPendingIpcOnEndpoint_preserves_ipcInvariantFull
#check @abortPendingIpcOnEndpoint_preserves_donationOwnerValid
#check @abortPendingIpcOnEndpoint_schedContext_forward
#check @abortPendingIpcOnEndpoint_unwritten_kind_forward
#check @abortPendingIpcOnEndpoint_preserves_objectIndexSetComplete
#check @abortPendingIpcOnEndpoint_preserves_objectIndexSet_invExt
#check @endpointQueueRemove_objects_present_backward
#check @endpointQueueRemove_objectIndexSet_eq
#check @endpointQueueRemove_preserves_objectIndexSetComplete
#check @Lifecycle.Suspend.abortHolderPendingIpc_scheduler_eq
#check @Lifecycle.Suspend.abortHolderPendingIpc_machine_eq
#check @Lifecycle.Suspend.abortHolderPendingIpc_serviceRegistry_eq
#check @Lifecycle.Suspend.abortHolderPendingIpc_preserves_objects_invExt
#check @Lifecycle.Suspend.abortHolderPendingIpc_preserves_objectIndexSetComplete
#check @Lifecycle.Suspend.abortHolderPendingIpc_preserves_objectIndexSet_invExt
#check @Lifecycle.Suspend.abortHolderPendingIpc_preserves_donationOwnerValid
#check @Lifecycle.Suspend.abortHolderPendingIpc_binding_forward
#check @Lifecycle.Suspend.abortHolderPendingIpc_binding_backward
#check @Lifecycle.Suspend.abortHolderPendingIpc_eq_self_of_allowed
-- WS-OD OD1.4: the information-flow obligation the abort adds
-- (`abortHolderProjectionStable`) and the states on which it is free live in
-- the **staged** `IPC/CrossCore/CancellationNI.lean`, which no executable suite
-- imports; they are pinned by Tier 3 anchors instead.
#check @returnDonatedSchedContext_ok_storeChain
#check @returnDonatedSchedContext_tcb_rewrite
#check @tcbBindingRewrite
#check @cancelIpcBlockingMigrated
#check @cancelIpcBlockingMigrated_of_no_donation
#check @cancelIpcBlockingMigrated_objects
#check @lockSet_cancelIpcBlocking_returned_donation_sc_write_mem
#check @lockSet_cancelIpcBlocking_donation_holder_tcb_write_mem
#check @lockSet_cancelIpcBlockingOnCore_size_le
-- WS-OD OD1.5: the reclaim's abort prefix is three more declared writes — the
-- holder's endpoint and its two queue neighbours — resolved from `st` rather
-- than from the victim's TCB, since the holder is resolved rather than supplied.
#check @cancelHolderBlockedEndpoint?
#check @cancelHolderSpliceNeighbors?
#check @lockSet_cancelIpcBlocking_holder_endpoint_write_mem
#check @lockSet_cancelIpcBlocking_holder_splice_prev_write_mem
#check @lockSet_cancelIpcBlocking_holder_splice_next_write_mem
#check @lockSet_cancelIpcBlocking_reply_size_le
#check @lockSet_cancelIpcBlocking_noDonation_size_le
-- WS-OD OD3.5: the footprint is **arm-selected** rather than summed — the
-- victim's own splice neighbours are declared on the arm that splices and on no
-- other, which is what takes the reply arm from ten members to eight and is
-- checked in both directions.
#check @cancelArmSpliceNeighbors?
#check @cancelArmSpliceNeighbors?_of_blockedEndpoint
#check @cancelArmSpliceNeighbors?_of_not_blockedEndpoint
#check @lockSet_cancelIpcBlockingOnCore_replyArm_eq
#check @lockSet_cancelIpcBlockingOnCore_endpointArm_covers_prev
#check @lockSet_cancelIpcBlockingOnCore_endpointArm_covers_next
#check @lockSet_cancelIpcBlockingOnCore_size_le_thirteen
#check @lockSet_cancelIpcBlockingOnCore_size_le_of_no_donation
#check @lockSet_cancelIpcBlockingOnCore_size_le_of_donation
#check @lockSet_tcbSuspendOnCore_size_le_seventeen
#check @lockSet_tcbSuspendOnCore_size_le
-- ...and the frames that license it: the arms that declare no neighbour write
-- none.
#check @cancelIpcBlocking_notificationArm_tcb_frame
#check @cancelIpcBlocking_replyArm_noDonation_tcb_frame
#check @consumeReplyLink_other_tcb_eq
-- ...and the general reply-arm frame, with the reclaim live: the four steps
-- stated OUTSIDE their write sets, and the composite over them.
#check @endpointQueueRemove_ok_getEndpoint?
#check @endpointQueueRemove_eq_patches
#check @endpointQueueRemove_objects_ne
#check @abortPendingIpcOnEndpoint_other_tcb_eq
#check @abortHolderPendingIpc_other_tcb_eq
#check @returnDonatedSchedContext_other_tcb_eq
#check @cancelIpcBlocking_replyArm_tcb_frame
-- WS-OD OD1.5: and the payoff — `passiveServerIdle` is preserved by
-- `cancelIpcBlocking` on every arm, which is what OD1 exists to prove.
#check @passiveServerIdleFrame_of_backward_of_not_allowed
#check @abortPendingIpcOnEndpoint_ok
#check @abortPendingIpcOnEndpoint_aborted_ipcState
#check @abortPendingIpcOnEndpoint_passiveServerIdleFrame
#check @Lifecycle.Suspend.abortHolderPendingIpc_passiveServerIdleFrame
#check @Lifecycle.Suspend.abortHolderPendingIpc_holder_ipcState_allowed
#check @consumeReplyLink_passiveServerIdleFrame
#check @restoreToReadyStaging_passiveServerIdleFrame
#check @returnDonatedSchedContext_passiveServerIdleFrame
#check @returnDonationToCancelledCaller_passiveServerIdleFrame
#check @cancelIpcBlocking_passiveServerIdleFrame
#check @cancelIpcBlocking_preserves_passiveServerIdle

-- ============================================================================
-- §2  Elaboration-time examples: headline theorems applied
-- ============================================================================

section ElaborationExamples

variable (victim : SeLe4n.ThreadId) (tcb : TCB) (ec : CoreId)
variable (st s : SystemState)
variable (blEp blN : Option SeLe4n.ObjId) (r? : Option SeLe4n.ReplyId)
variable (sc? : Option SeLe4n.SchedContextId) (ot? : Option SeLe4n.ThreadId)
variable (rdSc? : Option SeLe4n.SchedContextId) (dh? : Option SeLe4n.ThreadId)
-- WS-OD OD1.5: the reclaim's abort prefix declares three more members — the
-- holder's endpoint and its two queue neighbours.
variable (hEp? : Option SeLe4n.ObjId)
variable (hNb? : Option SeLe4n.ThreadId × Option SeLe4n.ThreadId)
-- WS-OD OD3.7: and two more — the Reply one frame below the reply-stack head and
-- that frame's caller's TCB, which the hand-back reaches at call depth ≥ 2.
variable (bhR? : Option SeLe4n.ReplyId) (oc? : Option SeLe4n.ThreadId)
-- WS-OD (`v0.35.4`): and two more again — the head the reclaim's pop clears, and
-- the frame above a cancelled *middle* caller's own, which the splice rewrites.
variable (rh? fa? : Option SeLe4n.ReplyId)
-- **WS-HP HP3.4**: the frame the removal's splice re-links below the cut.
variable (sb? : Option SeLe4n.ReplyId)
-- WS-OD (`v0.35.4`): the donation cancellation's pop members.
variable (dh1? dh2? : Option SeLe4n.ReplyId) (doc? : Option SeLe4n.ThreadId)

-- WS-RR RR8.6: the flagship is keyed on the core the pre-state PLACES the
-- victim on, not on its home; its three hypotheses are the placement, the
-- victim being current there, and that core being remote.
/-- SM6.E.5: the flagship's remote-poke conjunct applies. -/
example (c : CoreId) (h1 : placedCoreOf? st victim = some c)
    (h2 : st.scheduler.currentOnCore c = some victim)
    (h3 : c ≠ ec) :
    (cancelIpcBlockingOnCore victim tcb ec st).2 = some (c, SgiKind.reschedule) :=
  (cancellation_cross_core_correct victim tcb ec c st h1 h2 h3).1

/-- SM6.E.5: the flagship's placed-core deschedule conjunct applies. -/
example (c : CoreId) (h1 : placedCoreOf? st victim = some c)
    (h2 : st.scheduler.currentOnCore c = some victim)
    (h3 : c ≠ ec) :
    victim ∉ (cancelIpcBlockingOnCore victim tcb ec st).1.scheduler.runQueueOnCore c :=
  (cancellation_cross_core_correct victim tcb ec c st h1 h2 h3).2.1

/-- SM6.E.5: the flagship's object-level fidelity conjunct applies. -/
example (c : CoreId) (h1 : placedCoreOf? st victim = some c)
    (h2 : st.scheduler.currentOnCore c = some victim)
    (h3 : c ≠ ec) :
    (cancelIpcBlockingOnCore victim tcb ec st).1.objects
      = (cancelIpcBlocking st victim tcb).objects :=
  -- WS-OD OD1.7: one projection deeper — the per-core locality conjunct split
  -- into a run-queue half (conditioned on the holder wake's core) and an
  -- unconditional current-slot half.
  (cancellation_cross_core_correct victim tcb ec c st h1 h2 h3).2.2.2.2.2

/-- WS-OD OD1.7: the flagship's **current-slot** locality conjunct applies, and
is still unconditional — the reclaim's holder wake inserts into a run queue and
moves nothing onto a core. -/
example (c : CoreId) (h1 : placedCoreOf? st victim = some c)
    (h2 : st.scheduler.currentOnCore c = some victim)
    (h3 : c ≠ ec) (c' : CoreId) (hc' : c' ≠ c) :
    (cancelIpcBlockingOnCore victim tcb ec st).1.scheduler.currentOnCore c'
      = st.scheduler.currentOnCore c' :=
  (cancellation_cross_core_correct victim tcb ec c st h1 h2 h3).2.2.2.2.1 c' hc'

/-- WS-OD OD1.7: the flagship's **run-queue** locality conjunct applies, on a
core the holder wake does not target. -/
example (c : CoreId) (h1 : placedCoreOf? st victim = some c)
    (h2 : st.scheduler.currentOnCore c = some victim)
    (h3 : c ≠ ec) (c' : CoreId) (hc' : c' ≠ c)
    (hWake : cancelAbortedHolderWakeCore? st (cancelIpcBlockingMigrated victim tcb st)
        victim tcb ≠ some c') :
    (cancelIpcBlockingOnCore victim tcb ec st).1.scheduler.runQueueOnCore c'
      = st.scheduler.runQueueOnCore c' :=
  (cancellation_cross_core_correct victim tcb ec c st h1 h2 h3).2.2.2.1 c' hc' hWake

-- WS-OD OD1.7: the holder-wake surface — the resolver, its core, the
-- scheduler-only placement, its frames, and the payoff that says a holder the
-- reclaim's abort unblocked is on a run queue afterwards.
#check @cancelAbortedHolderWake?
#check @cancelAbortedHolderWakeCore?
#check @cancelAbortedHolderWakeCore?_of_no_donation
#check @enqueueAbortedHolderOnCore
#check @enqueueAbortedHolderOnCore_objects
#check @enqueueAbortedHolderOnCore_getTcb?
#check @enqueueAbortedHolderOnCore_currentOnCore
#check @enqueueAbortedHolderOnCore_runQueueOnCore_ne
#check @enqueueAbortedHolderOnCore_agrees_runQueueOnCore
#check @enqueueAbortedHolderOnCore_ipcState_ready
#check @wakeAbortedDonationHolder
#check @wakeAbortedDonationHolder_of_no_donation
#check @wakeAbortedDonationHolder_objects
#check @wakeAbortedDonationHolder_getTcb?
#check @wakeAbortedDonationHolder_currentOnCore
#check @wakeAbortedDonationHolder_runQueueOnCore_ne
#check @wakeAbortedDonationHolder_holder_runnable
#check @cancelIpcBlockingOnCoreSchedLockSet_none
#check @cancelIpcBlockingOnCoreSchedLockSet_dedup
#check @cancelIpcBlockingOnCoreSchedLockSet_write_only
#check @cancelIpcBlockingOnCoreSchedLockSet_contains_wake_runQueue_write
#check @cancelIpcBlockingOnCoreSchedLockSet_contains_placed_runQueue_write

/-- WS-OD OD1.7 payoff: a holder the reclaim's abort unblocked is queued or
executing afterwards — the complete statement of "not stranded", and the one the
defect made false.  The disjunction rather than plain `runnableOnSomeCore`
because the placement declines a thread that is already *running*: dequeue-on-
dispatch means a running thread is on no run queue, and enqueuing it would break
`queueCurrentConsistent`. -/
example (stPost : SystemState) (holder : SeLe4n.ThreadId) (t : TCB)
    (hW : cancelAbortedHolderWake? st stPost victim tcb = some holder)
    (hT : stPost.getTcb? holder = some t) :
    (runnableOnSomeCore (wakeAbortedDonationHolder st stPost victim tcb) holder
      || runningOnSomeCore (wakeAbortedDonationHolder st stPost victim tcb) holder) = true :=
  wakeAbortedDonationHolder_holder_runnable st stPost victim tcb holder t hW hT

/-- SM6.E.2: the single-core atomicity theorem applies (2PL bracket shape). -/
example :
    withLockSet (lockSet_cancelIpcBlocking victim blEp blN r? rdSc? dh? hEp? hNb? bhR? oc? rh? fa? sb?) ec
        (fun st => (cancelIpcBlocking st victim tcb, ())) s
      = (unwindAll ec
          (lockSet_cancelIpcBlocking victim blEp blN r? rdSc? dh? hEp? hNb? bhR? oc? rh? fa? sb?).lockAcquireSequence.reverse
          (cancelIpcBlocking
            (acquireAll ec
              (lockSet_cancelIpcBlocking victim blEp blN r? rdSc? dh? hEp? hNb? bhR? oc? rh? fa? sb?).lockAcquireSequence s)
            victim tcb),
         ()) :=
  cancelIpcBlocking_atomic_under_lockSet victim tcb ec blEp blN r? rdSc? dh? hEp? hNb?
    bhR? oc? rh? fa? sb? s

/-- SM6.E.4: the donation atomicity companion applies (dispatcher form). -/
example :
    withLockSet (lockSet_cancelDonation victim sc? ot? dh1? dh2? doc?) ec
        (cancelDonationOnCore victim tcb) s
      = (unwindAll ec
          (lockSet_cancelDonation victim sc? ot? dh1? dh2? doc?).lockAcquireSequence.reverse
          (cancelDonationOnCore victim tcb
            (acquireAll ec (lockSet_cancelDonation victim sc? ot? dh1? dh2? doc?).lockAcquireSequence s)).1,
         (cancelDonationOnCore victim tcb
            (acquireAll ec (lockSet_cancelDonation victim sc? ot? dh1? dh2? doc?).lockAcquireSequence s)).2) :=
  cancelDonationOnCore_atomic_under_lockSet victim tcb ec sc? ot? dh1? dh2? doc? s

/-- SM6.E.1: `objects.invExt` transports through the cross-core cancellation. -/
example (hInv : st.objects.invExt) :
    (cancelIpcBlockingOnCore victim tcb ec st).1.objects.invExt :=
  cancelIpcBlockingOnCore_preserves_objects_invExt victim tcb ec st hInv

/-- WS-RR RR7.22 (residual): the whole bundle across the cancellation's endpoint
arm, applied — the shape a caller sees. -/
example (ep : SeLe4n.ObjId)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st victim = some tcb)
    (hBlocked : tcb.ipcState = .blockedOnSend ep)
    (hBundle : ipcInvariantFull st) (hBudgets : allTimeoutBudgetsNone st)
    (hCoh : sweptThreadQueueCoherent st victim) :
    ipcInvariantFull (Lifecycle.Suspend.cancelIpcBlocking st victim tcb) :=
  cancelIpcBlocking_endpointArm_preserves_ipcInvariantFull st victim tcb ep hInv hLookup
    (Or.inl hBlocked) hBundle hBudgets hCoh

/-- WS-RR RR7.22 (residual): the boundary clause costs a caller nothing on an
endpoint the swept thread does not bound — which is every endpoint but the one it
is being cancelled out of. -/
example (q : IntrusiveQueue)
    (hH : q.head ≠ some victim) (hT : q.tail ≠ some victim) :
    queueBoundaryCoherentAt q victim tcb :=
  queueBoundaryCoherentAt_of_off_boundary q victim tcb hH hT

/-- WS-RR RR7.22 (residual): the whole bundle across the cancellation's
notification arm, applied. -/
example (n : SeLe4n.ObjId)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st victim = some tcb)
    (hBlocked : tcb.ipcState = .blockedOnNotification n)
    (hBundle : ipcInvariantFull st) (hBudgets : allTimeoutBudgetsNone st)
    (hOff : sweptThreadOffQueueChains st victim) :
    ipcInvariantFull (Lifecycle.Suspend.cancelIpcBlocking st victim tcb) :=
  cancelIpcBlocking_notificationArm_preserves_ipcInvariantFull st victim tcb n hInv hLookup
    hBlocked hBundle hBudgets hOff

/-- WS-RR RR7.22 (residual, remediation): after the corrected reply arm no thread
holds a SchedContext donated by the cancelled caller — the invariant premise the
old arm left dangling.

WS-OD OD3.1: the arm's reclaim is now a reply-stack *pop*, whose head validation
is fail-closed, so the statement gained `donationChainWellFormed` — the predicate
that says the head this context names resolves.  Without it the reclaim could
refuse, and a refused reclaim leaves exactly the donation this result denies. -/
example (ep : SeLe4n.ObjId) (rt : Option SeLe4n.ThreadId)
    (holder : SeLe4n.ThreadId) (holderTcb : TCB) (sc : SeLe4n.SchedContextId)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st victim = some tcb)
    (hBlocked : tcb.ipcState = .blockedOnReply ep rt)
    (hOwner : donationOwnerValid st)
    (hChain : donationChainWellFormed st)
    (hHolder : donatedContextIsOwnerFrameHead st victim)
    -- **WS-OD OD4.4**: the reclaim resolves its new owner off the holder's reply
    -- stack at the post-abort state, so the arm carries that obligation in the
    -- cancellation's own shape (`cancelDonationStackValid`, vacuous wherever the
    -- context heads no stack).
    (hStack : cancelDonationStackValid st victim tcb)
    (hTcb : (Lifecycle.Suspend.cancelIpcBlocking st victim tcb).objects[holder.toObjId]?
      = some (.tcb holderTcb)) :
    holderTcb.schedContextBinding ≠ .donated sc victim :=
  cancelIpcBlocking_reply_no_donation_to_victim st victim tcb ep rt hInv hLookup hBlocked
    hOwner hChain hHolder hStack holder holderTcb sc hTcb

/-- **WS-RR RR8.7: the whole bundle across the cancellation's reply arm, applied**
— the shape a caller sees, and the third of the three arms.

Longer than its endpoint and notification siblings because the arm is a four-step
composition rather than one sweep, and because it carries **two** stated coherence
facts: `hOwed` runs head -> binding (the pop's carriage is stated over the binding)
and `hHolder` runs binding -> head (the no-donation payoff quantifies over
bindings).  Neither entails the other and `ipcInvariantFull` entails neither, so a
caller discharges both. -/
example (ep : SeLe4n.ObjId) (rt : Option SeLe4n.ThreadId)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st victim = some tcb)
    (hBlocked : tcb.ipcState = .blockedOnReply ep rt)
    (hBundle : ipcInvariantFull st) (hChain : donationChainWellFormed st)
    (hBudgets : allTimeoutBudgetsNone st)
    (hOff : sweptThreadOffQueueChains st victim)
    (hOwed : ∀ rid, tcb.replyObject = some rid → replyFrameHeadHolderDonation st rid victim)
    (hHolder : donatedContextIsOwnerFrameHead st victim)
    (hStack : cancelDonationStackValid st victim tcb)
    (hCoh : ∀ (sc : SeLe4n.SchedContextId) (holder : SeLe4n.ThreadId),
      Lifecycle.Suspend.cancelledCallerDonation? st victim tcb = some (sc, holder) →
      abortHolderQueueCoherent st holder) :
    ipcInvariantFull (Lifecycle.Suspend.cancelIpcBlocking st victim tcb) :=
  cancelIpcBlocking_replyArm_preserves_ipcInvariantFull st victim tcb ep rt hInv hLookup
    hBlocked hBundle hChain hBudgets hOff hOwed hHolder hStack hCoh

/-- **WS-RR RR8.7**: and the arm *is* that composition — reclaim, splice, then the
teardown pair — by `rfl`, so a step inserted or reordered fails to elaborate rather
than quietly escaping the keystone above. -/
example (ep : SeLe4n.ObjId) (rt : Option SeLe4n.ThreadId)
    (hBlocked : tcb.ipcState = .blockedOnReply ep rt) :
    Lifecycle.Suspend.cancelIpcBlocking st victim tcb =
      restoredAndConsumed
        (spliceThreadReplyFrameOut
          (Lifecycle.Suspend.returnDonationToCancelledCaller st victim tcb) tcb)
        victim tcb (some Architecture.cancelledIpcFrame) :=
  cancelIpcBlocking_reply_arm_eq st victim tcb ep rt hBlocked

/-- WS-RR RR7.22 (residual): the swept thread holds no Reply object, derived from
the bundle's own reciprocity rather than assumed. -/
example (ep : SeLe4n.ObjId)
    (hLink : replyCallerLinkage st)
    (hTcb : st.objects[victim.toObjId]? = some (.tcb tcb))
    (hBlocked : tcb.ipcState = .blockedOnReceive ep) :
    tcb.replyObject = none :=
  replyObject_none_of_not_blockedOnReply st hLink victim tcb hTcb
    (fun _ _ hEq => by rw [hBlocked] at hEq; cases hEq)

end ElaborationExamples

-- ============================================================================
-- §3  Runtime assertions (Tier-2): the SM6.E cancellation scenarios
-- ============================================================================

private def assertBool (name : String) (b : Bool) : IO Unit := do
  if b then IO.println s!"  PASS: {name}"
  else
    IO.println s!"  FAIL: {name}"
    throw (IO.userError s!"Assertion failed: {name}")

private def core1 : CoreId := ⟨1, by decide⟩

private def epId : SeLe4n.ObjId := ⟨700⟩
private def nId : SeLe4n.ObjId := ⟨701⟩
private def rId : SeLe4n.ReplyId := ⟨702⟩
private def scId : SeLe4n.SchedContextId := SeLe4n.SchedContextId.ofNat 703
private def cnRoot : SeLe4n.ObjId := ⟨300⟩
private def victimTid : SeLe4n.ThreadId := ⟨710⟩
private def ownerTid : SeLe4n.ThreadId := ⟨711⟩
private def bystanderTid : SeLe4n.ThreadId := ⟨712⟩
private def prevTid : SeLe4n.ThreadId := ⟨713⟩
private def nextTid : SeLe4n.ThreadId := ⟨714⟩
private def runnerTid : SeLe4n.ThreadId := ⟨715⟩

private def mkTcb (tid : Nat) (prio : Nat) (aff : Option CoreId) : TCB :=
  { tid := ⟨tid⟩, priority := ⟨prio⟩, domain := ⟨0⟩, cspaceRoot := cnRoot,
    vspaceRoot := ⟨310⟩, ipcBuffer := SeLe4n.VAddr.ofNat 4096, ipcState := .ready,
    cpuAffinity := aff }

/-- The victim's TCB as stored in `st` (`default` when absent — assertions on
absent lookups fail loudly through the field checks). -/
private def victimTcb (st : SystemState) : TCB :=
  (st.getTcb? victimTid).getD (mkTcb 710 30 none)

-- ----------------------------------------------------------------------------
-- Scenario A: victim homed on core 1, blocked on an endpoint call
-- (driven through the real `endpointCallOnCore` block path).
-- ----------------------------------------------------------------------------

/-- Base: an endpoint (no receiver) + a core1-homed victim + a bystander,
victim runnable on the boot core (it will block itself via `.call`). -/
private def stCallBase : SystemState :=
  (BootstrapBuilder.empty
    |>.withObject epId (.endpoint {})
    |>.withObject victimTid.toObjId (.tcb (mkTcb 710 30 (some core1)))
    |>.withObject bystanderTid.toObjId (.tcb (mkTcb 712 20 none))
    |>.withRunnable [victimTid, bystanderTid]
    |>.build)

/-- Drive the victim into `.blockedOnCall epId` via the real cross-core call
(block path: no receiver waiting). -/
private def stCallBlocked? : Option SystemState :=
  match endpointCallOnCore epId victimTid IpcMessage.empty bootCoreId stCallBase with
  | (st, .ok none) => some st
  | _ => none

private def runEndpointCancelChecks : IO Unit := do
  IO.println "--- §3.1 SM6.E.5 cancel an endpoint-blocked victim (remote home, no SGI) ---"
  match stCallBlocked? with
  | some st =>
      let tcb := victimTcb st
      assertBool "setup: victim is .blockedOnCall on the endpoint"
        (decide (tcb.ipcState = .blockedOnCall epId))
      -- Pre-resolution names the endpoint (and nothing else).
      assertBool "cancelBlockedEndpoint? resolves the blocked-on endpoint"
        (decide (cancelBlockedEndpoint? tcb = some epId))
      assertBool "cancelBlockedNotification?/cancelConsumedReply? resolve none"
        (decide (cancelBlockedNotification? tcb = none ∧ cancelConsumedReply? tcb = none))
      let (st', sgi) := cancelIpcBlockingOnCore victimTid tcb bootCoreId st
      -- A blocked victim is not current anywhere: no SGI even though its home
      -- core (core 1) is remote.
      assertBool "cancelling a blocked (non-running) remote victim surfaces no SGI"
        (decide (sgi = none))
      -- The victim's IPC teardown: .ready + cleared queue links.
      assertBool "victim ipcState is .ready after cancellation"
        (match st'.getTcb? victimTid with
         | some t => decide (t.ipcState = .ready ∧ t.queuePrev = none ∧ t.queueNext = none)
         | none => false)
      -- The endpoint's send queue no longer references the victim.
      assertBool "endpoint send queue is emptied of the victim"
        (match st'.objects[epId]? with
         | some (.endpoint ep) =>
             decide (ep.sendQ.head ≠ some victimTid ∧ ep.sendQ.tail ≠ some victimTid)
         | _ => false)
      -- Object-level fidelity: same objects as the single-core teardown.
      assertBool "cross-core post-objects = single-core cancelIpcBlocking objects"
        (((cancelIpcBlocking st victimTid tcb).objects[victimTid.toObjId]?
            == st'.objects[victimTid.toObjId]?)
         && ((cancelIpcBlocking st victimTid tcb).objects[epId]?
            == st'.objects[epId]?))
      -- State-resolved lock-set: victim TCB write + endpoint write, permitted + Nodup.
      let ls := lockSet_cancelIpcBlockingOnCore st victimTid
      assertBool "state-resolved cancel lock-set kinds all permitted (.tcbSuspend)"
        (decide (∀ p ∈ ls.pairs, p.fst.kind ∈ permittedKinds .tcbSuspend))
      assertBool "state-resolved cancel lock-set keys are duplicate-free"
        (decide ((ls.pairs.map (·.fst)).Nodup))
      assertBool "victim TCB write lock is in the cancel footprint"
        (decide ((tcbLock victimTid, AccessMode.write) ∈ ls.pairs))
      assertBool "blocked endpoint write lock is in the cancel footprint"
        (decide ((endpointLock epId, AccessMode.write) ∈ ls.pairs))
      assertBool "no notification/reply lock in the endpoint-blocked footprint"
        (decide ((notificationLock nId, AccessMode.write) ∉ ls.pairs
          ∧ (replyLock rId, AccessMode.write) ∉ ls.pairs))
  | none => assertBool "setup: endpointCallOnCore block path succeeded" false

-- ----------------------------------------------------------------------------
-- Scenario B: victim blocked on a notification (driven through the real
-- `notificationWaitOnCore` block path), homed on core 1.
-- ----------------------------------------------------------------------------

private def stNtfnBase : SystemState :=
  (BootstrapBuilder.empty
    |>.withObject nId (.notification { state := .idle, waitingThreads := SeLe4n.NoDupList.empty })
    |>.withObject victimTid.toObjId (.tcb (mkTcb 710 30 (some core1)))
    |>.withRunnable [victimTid]
    |>.build)

private def stNtfnBlocked? : Option SystemState :=
  match notificationWaitOnCore nId victimTid bootCoreId stNtfnBase with
  | (st, .ok none) => some st
  | _ => none

private def runNotificationCancelChecks : IO Unit := do
  IO.println "--- §3.2 SM6.E.5 cancel a notification-blocked victim ---"
  match stNtfnBlocked? with
  | some st =>
      let tcb := victimTcb st
      assertBool "setup: victim is .blockedOnNotification"
        (decide (tcb.ipcState = .blockedOnNotification nId))
      assertBool "cancelBlockedNotification? resolves the notification"
        (decide (cancelBlockedNotification? tcb = some nId))
      let (st', sgi) := cancelIpcBlockingOnCore victimTid tcb bootCoreId st
      assertBool "cancelling a notification-blocked victim surfaces no SGI"
        (decide (sgi = none))
      assertBool "victim ipcState is .ready after cancellation"
        (match st'.getTcb? victimTid with
         | some t => decide (t.ipcState = .ready)
         | none => false)
      assertBool "the victim is dropped from the notification's waiter list"
        (match st'.objects[nId]? with
         | some (.notification ntfn) => decide (victimTid ∉ ntfn.waitingThreads.val)
         | _ => false)
      -- State-resolved lock-set picks the notification write lock.
      let ls := lockSet_cancelIpcBlockingOnCore st victimTid
      assertBool "blocked notification write lock is in the cancel footprint"
        (decide ((notificationLock nId, AccessMode.write) ∈ ls.pairs))
  | none => assertBool "setup: notificationWaitOnCore block path succeeded" false

-- ----------------------------------------------------------------------------
-- Scenario C: victim blocked awaiting a reply, holding a live reply link.
-- ----------------------------------------------------------------------------

private def stReplyBlocked : SystemState :=
  (BootstrapBuilder.empty
    |>.withObject epId (.endpoint {})
    |>.withObject rId.toObjId (.reply { replyId := rId, caller := some victimTid })
    |>.withObject victimTid.toObjId (.tcb { mkTcb 710 30 (some core1) with
        ipcState := .blockedOnReply epId (some ownerTid),
        replyObject := some rId })
    |>.build)

/-- WS-OD OD3.5: a reply-blocked victim that *also* carries queue links — the
shape the arm-selected split is about.  The links are stale (a `.blockedOnReply`
thread is on no endpoint queue) and nothing in `ipcInvariantFull` forbids them,
which is exactly why the footprint must decide by arm rather than by reading the
fields. -/
private def stReplyBlockedStaleLinks : SystemState :=
  (BootstrapBuilder.empty
    |>.withObject epId (.endpoint {})
    |>.withObject rId.toObjId (.reply { replyId := rId, caller := some victimTid })
    |>.withObject bystanderTid.toObjId (.tcb (mkTcb 712 20 none))
    |>.withObject ownerTid.toObjId (.tcb (mkTcb 713 20 none))
    |>.withObject victimTid.toObjId (.tcb { mkTcb 710 30 (some core1) with
        ipcState := .blockedOnReply epId (some ownerTid),
        replyObject := some rId,
        queuePrev := some bystanderTid,
        queueNext := some ownerTid })
    |>.build)

private def runReplyCancelChecks : IO Unit := do
  IO.println "--- §3.3 SM6.E.5 cancel a reply-blocked victim (reply link consumed) ---"
  let tcb := victimTcb stReplyBlocked
  assertBool "cancelConsumedReply? resolves the victim's reply object"
    (decide (cancelConsumedReply? tcb = some rId))
  let (st', sgi) := cancelIpcBlockingOnCore victimTid tcb bootCoreId stReplyBlocked
  assertBool "cancelling a reply-blocked victim surfaces no SGI"
    (decide (sgi = none))
  assertBool "victim ipcState is .ready and its reply forward link is cleared"
    (match st'.getTcb? victimTid with
     | some t => decide (t.ipcState = .ready ∧ t.replyObject = none)
     | none => false)
  assertBool "the Reply object's caller back-link is severed"
    (match st'.getReply? rId with
     | some r => decide (r.caller = none)
     | none => false)
  -- State-resolved lock-set picks the reply write lock (the SM6.E footprint
  -- extension closing the SM6.D reply-fold gap).
  let ls := lockSet_cancelIpcBlockingOnCore stReplyBlocked victimTid
  assertBool "consumed Reply write lock is in the cancel footprint"
    (decide ((replyLock rId, AccessMode.write) ∈ ls.pairs))
  assertBool "reply-extended footprint kinds all permitted (.tcbSuspend now covers .reply)"
    (decide (∀ p ∈ ls.pairs, p.fst.kind ∈ permittedKinds .tcbSuspend))
  -- **WS-OD (`v0.35.4`)**: the enclosing suspend footprint covers the reply write
  -- *by construction* — it is defined over the state-resolved cancellation
  -- footprint, so every write that one declares is a write it declares.
  assertBool "suspend footprint covers the consumed Reply write lock"
    (decide ((replyLock rId, AccessMode.write) ∈
      (lockSet_tcbSuspendOnCore stReplyBlocked bystanderTid cnRoot victimTid).pairs))
  -- WS-OD OD3.5: **the arm-selected split, exercised on the shape it is about.**
  -- The victim below is reply-blocked *and* carries queue links — a stale pair,
  -- since a `.blockedOnReply` thread is on no endpoint queue.  The summed
  -- resolver read them and put two TCB write locks in the footprint for a splice
  -- this arm does not perform; the arm-selected one answers `(none, none)`.
  --
  -- The fixture KEEPS the links and varies the arm, which is the mutation that
  -- finds this class: deleting them would leave every check passing against
  -- either resolver.
  let staleTcb := victimTcb stReplyBlockedStaleLinks
  assertBool "setup: the reply-blocked victim carries stale queue links"
    (decide (staleTcb.queuePrev = some bystanderTid
      ∧ staleTcb.queueNext = some ownerTid))
  assertBool "the summed resolver still reads them (it is not arm-aware)"
    (decide (queueSpliceNeighbors? staleTcb = (some bystanderTid, some ownerTid)))
  assertBool "the ARM-selected resolver answers (none, none) on the reply arm"
    (decide (cancelArmSpliceNeighbors? staleTcb = (none, none)))
  let lsStale := lockSet_cancelIpcBlockingOnCore stReplyBlockedStaleLinks victimTid
  assertBool "no neighbour TCB write lock in the reply arm's footprint"
    (decide ((tcbLock bystanderTid, AccessMode.write) ∉ lsStale.pairs
      ∧ (tcbLock ownerTid, AccessMode.write) ∉ lsStale.pairs))
  assertBool "...and the reply arm's footprint is within the sharp eight-member bound"
    (decide (lsStale.size ≤ 8))

-- ----------------------------------------------------------------------------
-- Scenario D: actively RUNNING victim on a remote core (cross-core suspend).
-- ----------------------------------------------------------------------------

private def stRunningRemote : SystemState :=
  let base :=
    (BootstrapBuilder.empty
      |>.withObject victimTid.toObjId (.tcb { mkTcb 710 30 (some core1) with
          threadState := .Running })
      |>.withObject bystanderTid.toObjId (.tcb (mkTcb 712 20 none))
      |>.withRunnable [bystanderTid]
      |>.build)
  { base with scheduler := base.scheduler.setCurrentOnCore core1 (some victimTid) }

private def runRemoteRunningCancelChecks : IO Unit := do
  IO.println "--- §3.4 SM6.E.5 cancel a victim RUNNING on a remote core (SGI) ---"
  let tcb := victimTcb stRunningRemote
  assertBool "setup: victim is current on core 1"
    (decide (stRunningRemote.scheduler.currentOnCore core1 = some victimTid))
  assertBool "setup: the state places the victim on core 1 (it is current there)"
    (decide (placedCoreOf? stRunningRemote victimTid = some core1))
  let (st', sgi) := cancelIpcBlockingOnCore victimTid tcb bootCoreId stRunningRemote
  -- (1) remote poke
  assertBool "cancelling a remotely-running victim fires a reschedule SGI to core 1"
    (decide (sgi = some (core1, SgiKind.reschedule)))
  -- (2) full deschedule at the placement
  assertBool "victim is cleared from core 1's current slot"
    (decide (st'.scheduler.currentOnCore core1 ≠ some victimTid))
  assertBool "victim is not in core 1's run queue"
    (decide (victimTid ∉ st'.scheduler.runQueueOnCore core1))
  -- (3) per-core locality: boot core untouched
  assertBool "boot core's run queue and current slot are untouched"
    (decide (bystanderTid ∈ st'.scheduler.runQueueOnCore bootCoreId)
      && decide (st'.scheduler.currentOnCore bootCoreId
        = stRunningRemote.scheduler.currentOnCore bootCoreId))
  -- The `.ready` arm: the composite reduces to the pure deschedule.
  assertBool "a .ready victim's cancellation equals the pure descheduleThread"
    (let d := descheduleThread stRunningRemote victimTid bootCoreId
     decide (sgi = d.2 ∧ st'.scheduler.currentOnCore core1 = d.1.scheduler.currentOnCore core1))

private def runLocalRunningCancelChecks : IO Unit := do
  IO.println "--- §3.5 SM6.E.5 cancel a victim running on the executing core (no SGI) ---"
  -- Same fixture, but the cancel runs ON core 1 (the victim's own core).
  let tcb := victimTcb stRunningRemote
  let (st', sgi) := cancelIpcBlockingOnCore victimTid tcb core1 stRunningRemote
  assertBool "cancelling on the victim's own core surfaces no SGI"
    (decide (sgi = none))
  assertBool "victim is still cleared from core 1's current slot (local deschedule)"
    (decide (st'.scheduler.currentOnCore core1 ≠ some victimTid))

-- ----------------------------------------------------------------------------
-- Scenario E: donation cancellation — bound arm, remote home core.
-- ----------------------------------------------------------------------------

private def mkSc (bound : Option SeLe4n.ThreadId) (active : Bool) : SchedContext :=
  { scId := scId, boundThread := bound,
    budget := ⟨1000⟩, period := ⟨1000⟩,
    priority := ⟨10⟩, deadline := ⟨0⟩, domain := ⟨0⟩,
    budgetRemaining := ⟨1000⟩, isActive := active, replenishments := [] }

private def stBoundDonation : SystemState :=
  let base :=
    (BootstrapBuilder.empty
      |>.withObject victimTid.toObjId (.tcb { mkTcb 710 30 (some core1) with
          schedContextBinding := .bound scId })
      |>.withObject scId.toObjId (.schedContext (mkSc (some victimTid) true))
      |>.build)
  -- Seed a pending replenishment for the SC on the victim's home core (core 1),
  -- per the SM5.H affinity discipline.
  let rq1 := (base.scheduler.replenishQueueOnCore core1).insert scId 42
  { base with scheduler := base.scheduler.setReplenishQueueOnCore core1 rq1 }

private def runBoundDonationCancelChecks : IO Unit := do
  IO.println "--- §3.6 SM6.E.3 bound-donation cancel (home-core replenish purge) ---"
  let tcb := victimTcb stBoundDonation
  assertBool "cancelBindingSc? resolves the bound SC"
    (decide (cancelBindingSc? tcb = some scId ∧ cancelDonatedOwner? tcb = none))
  assertBool "setup: core 1's replenish queue holds the SC's entry"
    ((stBoundDonation.scheduler.replenishQueueOnCore core1).entries.any
      (fun e => e.1 == scId))
  let (st', res) := cancelDonationOnCore victimTid tcb stBoundDonation
  assertBool "bound-donation cancel succeeds"
    (match res with | .ok () => true | .error _ => false)
  assertBool "victim's binding is cleared to .unbound"
    (match st'.getTcb? victimTid with
     | some t => decide (t.schedContextBinding = .unbound)
     | none => false)
  assertBool "the SC is deactivated and unbound"
    (match st'.getSchedContext? scId with
     | some sc => decide (sc.boundThread = none ∧ sc.isActive = false)
     | none => false)
  -- The per-core purge: the entry is removed from the HOME core's queue
  -- (the single-core arm would have purged bootCore's queue and left this).
  assertBool "the SC's replenishment is purged from core 1's queue (home core)"
    (!(st'.scheduler.replenishQueueOnCore core1).entries.any (fun e => e.1 == scId))
  assertBool "boot core's replenish queue is untouched"
    (decide ((st'.scheduler.replenishQueueOnCore bootCoreId).entries
      = (stBoundDonation.scheduler.replenishQueueOnCore bootCoreId).entries))
  -- No scheduler run-queue/current disturbance on any core.
  assertBool "run queues and current slots are untouched on both cores"
    (decide (st'.scheduler.currentOnCore bootCoreId
        = stBoundDonation.scheduler.currentOnCore bootCoreId)
      && decide (st'.scheduler.currentOnCore core1
        = stBoundDonation.scheduler.currentOnCore core1)
      && decide ((victimTid ∈ st'.scheduler.runQueueOnCore core1)
        ↔ (victimTid ∈ stBoundDonation.scheduler.runQueueOnCore core1)))
  -- Lock-set: victim TCB write + SC write, permitted + Nodup.
  let ls := lockSet_cancelDonationOnCore stBoundDonation victimTid
  assertBool "donation lock-set kinds all permitted (.tcbSuspend)"
    (decide (∀ p ∈ ls.pairs, p.fst.kind ∈ permittedKinds .tcbSuspend))
  assertBool "SC write lock is in the donation footprint"
    (decide ((schedContextLock scId, AccessMode.write) ∈ ls.pairs))

-- ----------------------------------------------------------------------------
-- Scenario F: donation cancellation — donated arm (return to original owner).
-- ----------------------------------------------------------------------------

private def stDonated : SystemState :=
  let base :=
    (BootstrapBuilder.empty
      |>.withObject victimTid.toObjId (.tcb { mkTcb 710 30 (some core1) with
          schedContextBinding := .donated scId ownerTid })
      |>.withObject ownerTid.toObjId (.tcb (mkTcb 711 25 none))
      |>.withObject scId.toObjId (.schedContext (mkSc (some victimTid) true))
      |>.build)
  -- Seed the SC's pending replenishment on the VICTIM's home core (core 1),
  -- per the SM5.H affinity discipline (per-core ticks enqueue there while the
  -- donated server runs).
  let rq1 := (base.scheduler.replenishQueueOnCore core1).insert scId 42
  { base with scheduler := base.scheduler.setReplenishQueueOnCore core1 rq1 }

private def runDonatedDonationCancelChecks : IO Unit := do
  IO.println "--- §3.7 SM6.E.3 donated-donation cancel (return to owner) ---"
  let tcb := victimTcb stDonated
  assertBool "cancelBindingSc?/cancelDonatedOwner? resolve the donated SC + owner"
    (decide (cancelBindingSc? tcb = some scId ∧ cancelDonatedOwner? tcb = some ownerTid))
  let (st', res) := cancelDonationOnCore victimTid tcb stDonated
  assertBool "donated-donation cancel succeeds"
    (match res with | .ok () => true | .error _ => false)
  assertBool "the SC is returned to the original owner"
    (match st'.getSchedContext? scId with
     | some sc => decide (sc.boundThread = some ownerTid)
     | none => false)
  assertBool "the owner's binding is re-established to .bound"
    (match st'.getTcb? ownerTid with
     | some t => decide (t.schedContextBinding = .bound scId)
     | none => false)
  assertBool "the victim's binding is cleared to .unbound"
    (match st'.getTcb? victimTid with
     | some t => decide (t.schedContextBinding = .unbound)
     | none => false)
  -- §2b replenishment migration: the SC's pending replenishment moves from
  -- the victim's home core (core 1) to the owner's home core (boot) at its
  -- original eligibility time.
  assertBool "SC replenishment is migrated off the victim's home core"
    (!(st'.scheduler.replenishQueueOnCore core1).entries.any (fun e => e.1 == scId))
  assertBool "SC replenishment lands on the owner's home core at its original time"
    ((st'.scheduler.replenishQueueOnCore bootCoreId).entries.any
      (fun e => e.1 == scId && e.2 == 42))
  -- Owner TCB write lock in the footprint (the plan row's "receiver TCB").
  let ls := lockSet_cancelDonationOnCore stDonated victimTid
  assertBool "original-owner TCB write lock is in the donation footprint"
    (decide ((tcbLock ownerTid, AccessMode.write) ∈ ls.pairs))

-- ----------------------------------------------------------------------------
-- Scenario G: dispatcher identity + ghost victim + bracket atomicity.
-- ----------------------------------------------------------------------------

private def runDispatcherEdgeChecks : IO Unit := do
  IO.println "--- §3.8 SM6.E dispatcher identity, ghost victim, bracket atomicity ---"
  -- `.unbound` dispatcher identity.
  let tcbU := mkTcb 710 30 none
  let stU :=
    (BootstrapBuilder.empty
      |>.withObject victimTid.toObjId (.tcb tcbU)
      |>.build)
  let (stU', resU) := cancelDonationOnCore victimTid tcbU stU
  assertBool "cancelDonationOnCore on .unbound is the identity (.ok, state preserved)"
    ((match resU with | .ok () => true | .error _ => false)
      && (match stU'.getTcb? victimTid with
          | some t => t == tcbU
          | none => false))
  -- Ghost victim: unresolvable tid → no SGI, objects untouched.
  let ghost : SeLe4n.ThreadId := ⟨999⟩
  let (stG, sgiG) := cancelIpcBlockingOnCore ghost (mkTcb 999 1 none) bootCoreId stU
  assertBool "ghost victim: no SGI and untouched victim object"
    (decide (sgiG = none)
      && (match stG.getTcb? victimTid with
          | some t => t == tcbU
          | none => false))
  -- `withLockSet` bracket: the business outcome equals the bare transition's
  -- (locks acquired and released around the same pure step — operational
  -- witness of `cancelIpcBlockingOnCore_atomic_under_lockSet`).
  match stCallBlocked? with
  | some st =>
      let tcb := victimTcb st
      let bare := cancelIpcBlockingOnCore victimTid tcb bootCoreId st
      let bracketed := withLockSet (lockSet_cancelIpcBlockingOnCore st victimTid)
        bootCoreId (cancelIpcBlockingOnCore victimTid tcb bootCoreId) st
      assertBool "withLockSet bracket returns the same SGI decision"
        (decide (bracketed.2 = bare.2))
      assertBool "withLockSet bracket commits the same victim teardown"
        (match bracketed.1.getTcb? victimTid, bare.1.getTcb? victimTid with
         | some a, some b => decide (a.ipcState = b.ipcState ∧ a.ipcState = .ready)
         | _, _ => false)
  | none => assertBool "setup: bracket fixture available" false

-- ----------------------------------------------------------------------------
-- Scenario H (SM6.E completion): notification waiter-list state correction.
-- ----------------------------------------------------------------------------

private def stNtfnTwoWaiters? : Option SystemState :=
  let base :=
    (BootstrapBuilder.empty
      |>.withObject nId (.notification { state := .idle, waitingThreads := SeLe4n.NoDupList.empty })
      |>.withObject victimTid.toObjId (.tcb (mkTcb 710 30 (some core1)))
      |>.withObject bystanderTid.toObjId (.tcb (mkTcb 712 20 none))
      |>.withRunnable [victimTid, bystanderTid]
      |>.build)
  match notificationWaitOnCore nId victimTid bootCoreId base with
  | (st1, .ok none) =>
      match notificationWaitOnCore nId bystanderTid bootCoreId st1 with
      | (st2, .ok none) => some st2
      | _ => none
  | _ => none

private def runNotificationStateCorrectionChecks : IO Unit := do
  IO.println "--- §3.9 SM6.E notification sole-waiter state correction ---"
  -- Sole waiter: cancelling the ONLY waiter must transition the notification
  -- back to `.idle` (the `removeFromAllNotificationWaitLists` invariant fix —
  -- pre-fix the sweep left an ipcInvariant-violating `.waiting` + `[]`).
  match stNtfnBlocked? with
  | some st =>
      let tcb := victimTcb st
      let (st', _) := cancelIpcBlockingOnCore victimTid tcb bootCoreId st
      assertBool "sole-waiter cancel: notification transitions to .idle"
        (match st'.objects[nId]? with
         | some (.notification n) =>
             decide (n.state = .idle ∧ n.waitingThreads.val = []
               ∧ n.pendingBadge = none)
         | _ => false)
  | none => assertBool "setup: sole-waiter fixture available" false
  -- Two waiters: cancelling one keeps the notification `.waiting` with the
  -- other still queued (the correction fires only on the last removal).
  match stNtfnTwoWaiters? with
  | some st =>
      let tcb := victimTcb st
      let (st', _) := cancelIpcBlockingOnCore victimTid tcb bootCoreId st
      assertBool "two-waiter cancel: notification stays .waiting with the other waiter"
        (match st'.objects[nId]? with
         | some (.notification n) =>
             decide (n.state = .waiting ∧ n.waitingThreads.val = [bystanderTid])
         | _ => false)
  | none => assertBool "setup: two-waiter fixture available" false

-- ----------------------------------------------------------------------------
-- Scenario I (SM6.E completion): mid-queue splice — a 3-deep endpoint queue.
-- ----------------------------------------------------------------------------

private def stThreeDeep? : Option SystemState :=
  let base :=
    (BootstrapBuilder.empty
      |>.withObject epId (.endpoint {})
      |>.withObject prevTid.toObjId (.tcb (mkTcb 713 30 none))
      |>.withObject victimTid.toObjId (.tcb (mkTcb 710 30 (some core1)))
      |>.withObject nextTid.toObjId (.tcb (mkTcb 714 30 none))
      |>.withRunnable [prevTid, victimTid, nextTid]
      |>.build)
  match endpointCallOnCore epId prevTid IpcMessage.empty bootCoreId base with
  | (st1, .ok none) =>
      match endpointCallOnCore epId victimTid IpcMessage.empty bootCoreId st1 with
      | (st2, .ok none) =>
          match endpointCallOnCore epId nextTid IpcMessage.empty bootCoreId st2 with
          | (st3, .ok none) => some st3
          | _ => none
      | _ => none
  | _ => none

private def runMidQueueSpliceChecks : IO Unit := do
  IO.println "--- §3.10 SM6.E mid-queue splice (3-deep endpoint queue) ---"
  match stThreeDeep? with
  | some st =>
      assertBool "setup: send queue spans prev..next with the victim mid-queue"
        (match st.objects[epId]?, st.getTcb? victimTid with
         | some (.endpoint ep), some vt =>
             decide (ep.sendQ.head = some prevTid ∧ ep.sendQ.tail = some nextTid
               ∧ vt.queuePrev = some prevTid ∧ vt.queueNext = some nextTid)
         | _, _ => false)
      let tcb := victimTcb st
      let (st', _) := cancelIpcBlockingOnCore victimTid tcb bootCoreId st
      -- The interior links are re-spliced around the removed victim.
      assertBool "predecessor's queueNext is patched to the successor"
        (match st'.getTcb? prevTid with
         | some t => decide (t.queueNext = some nextTid)
         | none => false)
      assertBool "successor's queuePrev is patched to the predecessor"
        (match st'.getTcb? nextTid with
         | some t => decide (t.queuePrev = some prevTid)
         | none => false)
      -- WS-OD OD3.9: and its `queuePPrev` with it.  The check above passed
      -- before the fix, because it asked about the field the splice wrote;
      -- `queuePPrev` is the field the splice *should* have written and the one
      -- `endpointQueueRemoveDual` validates.
      assertBool "successor's queuePPrev is patched to the predecessor"
        (match st'.getTcb? nextTid with
         | some t => decide (t.queuePPrev = some (.tcbNext prevTid))
         | none => false)
      -- WS-OD OD3.9 (the consequence, end to end): with a stale `queuePPrev`
      -- the successor failed `pprevConsistent` and could never leave the
      -- endpoint queue again -- so every later bound-notification delivery to
      -- it returned `.illegalState`.  Suspending the thread *ahead* of a
      -- passive server was therefore an authority-crossing denial of service
      -- on that server.  The dual removal is the operation that reads the
      -- field, so the regression is stated as that operation succeeding.
      assertBool "the successor can still be dequeued by the dual removal"
        (match endpointQueueRemoveDual epId false nextTid st' with
         | .ok _ => true
         | .error _ => false)
      -- ... and so can the promoted predecessor, which is the queue head.
      assertBool "the predecessor can still be dequeued by the dual removal"
        (match endpointQueueRemoveDual epId false prevTid st' with
         | .ok _ => true
         | .error _ => false)
      -- Head/tail survive; the queue-mates stay blocked and keep their homes
      -- (the `spliceOutMidQueueNode_tcb_lookup` frame, operationally).
      assertBool "send-queue head/tail still span prev..next"
        (match st'.objects[epId]? with
         | some (.endpoint ep) =>
             decide (ep.sendQ.head = some prevTid ∧ ep.sendQ.tail = some nextTid)
         | _ => false)
      assertBool "queue-mates keep their ipcState and cpuAffinity"
        (match st'.getTcb? prevTid, st'.getTcb? nextTid with
         | some p, some n =>
             decide (p.ipcState = .blockedOnCall epId ∧ n.ipcState = .blockedOnCall epId
               ∧ p.cpuAffinity = none ∧ n.cpuAffinity = none)
         | _, _ => false)
      -- PR #831 review 4: the splice's neighbour-TCB writes are declared
      -- footprint members (state-resolved from the victim's interior links).
      let lsSplice := lockSet_cancelIpcBlockingOnCore st victimTid
      assertBool "splice predecessor's TCB write lock is in the cancel footprint"
        (decide ((tcbLock prevTid, AccessMode.write) ∈ lsSplice.pairs))
      assertBool "splice successor's TCB write lock is in the cancel footprint"
        (decide ((tcbLock nextTid, AccessMode.write) ∈ lsSplice.pairs))
  | none => assertBool "setup: 3-deep call queue fixture available" false

-- ----------------------------------------------------------------------------
-- Scenario J (SM6.E completion): mirror SGI — boot-homed victim cancelled
-- from a remote executing core.
-- ----------------------------------------------------------------------------

private def stRunningBoot : SystemState :=
  let base :=
    (BootstrapBuilder.empty
      |>.withObject victimTid.toObjId (.tcb { mkTcb 710 30 none with
          threadState := .Running })
      |>.build)
  { base with scheduler := base.scheduler.setCurrentOnCore bootCoreId (some victimTid) }

private def runMirrorSgiChecks : IO Unit := do
  IO.println "--- §3.11 SM6.E mirror SGI (boot-homed victim, remote canceller) ---"
  let tcb := victimTcb stRunningBoot
  let (st', sgi) := cancelIpcBlockingOnCore victimTid tcb core1 stRunningBoot
  assertBool "cancelling a boot-running victim FROM core 1 pokes the boot core"
    (decide (sgi = some (bootCoreId, SgiKind.reschedule)))
  assertBool "victim is cleared from the boot core's current slot"
    (decide (st'.scheduler.currentOnCore bootCoreId ≠ some victimTid))

-- ----------------------------------------------------------------------------
-- Scenario K (SM6.E live wiring): the per-core suspend `suspendThreadOnCore`.
-- ----------------------------------------------------------------------------

private def stSuspendLocal : SystemState :=
  let base :=
    (BootstrapBuilder.empty
      |>.withObject victimTid.toObjId (.tcb { mkTcb 710 30 (some core1) with
          threadState := .Running })
      |>.withObject runnerTid.toObjId (.tcb { mkTcb 715 20 (some core1) with
          threadState := .Ready })
      |>.build)
  let st1 := enqueueRunnableOnCore base core1 runnerTid
  { st1 with scheduler := st1.scheduler.setCurrentOnCore core1 (some victimTid) }

private def runPerCoreSuspendChecks : IO Unit := do
  IO.println "--- §3.12 SM6.E live per-core suspend (suspendThreadOnCore) ---"
  match victimTid.toValid? with
  | none => assertBool "setup: victim ValidThreadId" false
  | some vtid =>
      -- (a) REMOTE: victim running on core 1, suspended from the boot core.
      match suspendThreadOnCore stRunningRemote vtid bootCoreId with
      | .ok (st', sgi) =>
          assertBool "remote suspend fires a reschedule SGI to the victim's home core"
            (decide (sgi = some (core1, SgiKind.reschedule)))
          assertBool "remote suspend sets the victim .Inactive"
            (match st'.getTcb? victimTid with
             | some t => decide (t.threadState = .Inactive)
             | none => false)
          assertBool "remote suspend fully descheduled the victim on core 1"
            (decide (st'.scheduler.currentOnCore core1 ≠ some victimTid)
              && decide (victimTid ∉ st'.scheduler.runQueueOnCore core1))
          -- (d) the diff seam re-derives the same poke (the SM6.E
          -- descheduled-current rule of `crossCoreSgiBody`).
          assertBool "computeCrossCoreSgis recovers the deschedule SGI from the diff"
            ((PriorityInheritance.computeCrossCoreSgis stRunningRemote st' bootCoreId).any
              (fun p => p.1 == core1 && p.2 == SgiKind.reschedule))
      | .error _ => assertBool "remote suspend succeeds" false
      -- (b) LOCAL: the executing core suspends its own current thread —
      -- no SGI, and the queued successor is dispatched inline.
      match suspendThreadOnCore stSuspendLocal vtid core1 with
      | .ok (st', sgi) =>
          assertBool "local suspend surfaces no SGI" (decide (sgi = none))
          assertBool "local suspend dispatches the queued successor inline"
            (decide (st'.scheduler.currentOnCore core1 = some runnerTid))
      | .error _ => assertBool "local suspend succeeds" false
      -- (c) rejection: an already-.Inactive victim.
      let stInactive :=
        (BootstrapBuilder.empty
          |>.withObject victimTid.toObjId (.tcb { mkTcb 710 30 (some core1) with
              threadState := .Inactive })
          |>.build)
      assertBool "suspending an .Inactive victim is rejected with illegalState"
        (match suspendThreadOnCore stInactive vtid bootCoreId with
         | .error .illegalState => true
         | _ => false)
      -- (e) single-core inertness: a boot-homed victim suspended on boot.
      match suspendThreadOnCore stRunningBoot vtid bootCoreId with
      | .ok (st', sgi) =>
          assertBool "boot-local suspend surfaces no SGI" (decide (sgi = none))
          assertBool "boot-local suspend fires nothing through the diff seam"
            (decide (PriorityInheritance.computeCrossCoreSgis stRunningBoot st'
              bootCoreId = []))
      | .error _ => assertBool "boot-local suspend succeeds" false

-- ----------------------------------------------------------------------------
-- Scenario L (SM6.E completion): send-/receive-blocked victims (direct
-- fixtures for the two teardown arms the call path does not reach).
-- ----------------------------------------------------------------------------

private def runSendReceiveCancelChecks : IO Unit := do
  IO.println "--- §3.13 SM6.E cancel send-/receive-blocked victims ---"
  let stSend :=
    (BootstrapBuilder.empty
      |>.withObject epId (.endpoint { sendQ := { head := some victimTid, tail := some victimTid } })
      |>.withObject victimTid.toObjId (.tcb { mkTcb 710 30 (some core1) with
          ipcState := .blockedOnSend epId })
      |>.build)
  let (stS, sgiS) := cancelIpcBlockingOnCore victimTid (victimTcb stSend) bootCoreId stSend
  assertBool "send-blocked cancel: victim .ready, no SGI, send queue emptied"
    (decide (sgiS = none)
      && (match stS.getTcb? victimTid with
          | some t => decide (t.ipcState = .ready)
          | none => false)
      && (match stS.objects[epId]? with
          | some (.endpoint ep) =>
              decide (ep.sendQ.head ≠ some victimTid ∧ ep.sendQ.tail ≠ some victimTid)
          | _ => false))
  let stRecv :=
    (BootstrapBuilder.empty
      |>.withObject epId (.endpoint { receiveQ := { head := some victimTid, tail := some victimTid } })
      |>.withObject victimTid.toObjId (.tcb { mkTcb 710 30 (some core1) with
          ipcState := .blockedOnReceive epId })
      |>.build)
  let (stR, sgiR) := cancelIpcBlockingOnCore victimTid (victimTcb stRecv) bootCoreId stRecv
  assertBool "receive-blocked cancel: victim .ready, no SGI, receive queue emptied"
    (decide (sgiR = none)
      && (match stR.getTcb? victimTid with
          | some t => decide (t.ipcState = .ready)
          | none => false)
      && (match stR.objects[epId]? with
          | some (.endpoint ep) =>
              decide (ep.receiveQ.head ≠ some victimTid ∧ ep.receiveQ.tail ≠ some victimTid)
          | _ => false))

-- ----------------------------------------------------------------------------
-- Scenario M (SM6.E PIP-revert ordering fix): suspending a reply-blocked
-- client drops the server's donated boost (D4-N capture → clear →
-- revert-from-server), migrates the server's bucket on ITS home core
-- (`updatePipBoostOnCore` via the SM5.F.4 chain walk), and the diff seam
-- derives the re-bucketing poke (the PR #831 review fix).
-- ----------------------------------------------------------------------------

private def serverTid : SeLe4n.ThreadId := ⟨716⟩
private def core2 : CoreId := ⟨2, by decide⟩

/-- A high-priority victim (prio 200, home core 1, running current there)
reply-blocked on a PIP-boosted server (base prio 50, `pipBoost` 200, home
core 2, runnable there).  Pre-fix, `suspendThread`'s revert-at-the-victim
ran before the victim left `waitersOf(server)`, so the recompute was a
fixed-point no-op and the server retained the suspended victim's donated
priority indefinitely. -/
private def stPipDonation : SystemState :=
  let base :=
    (BootstrapBuilder.empty
      |>.withObject epId (.endpoint {})
      |>.withObject rId.toObjId (.reply { replyId := rId, caller := some victimTid })
      |>.withObject victimTid.toObjId (.tcb { mkTcb 710 200 (some core1) with
          threadState := .Running,
          ipcState := .blockedOnReply epId (some serverTid),
          replyObject := some rId })
      |>.withObject serverTid.toObjId (.tcb { mkTcb 716 50 (some core2) with
          threadState := .Ready,
          pipBoost := some ⟨200⟩ })
      |>.build)
  let st1 := enqueueRunnableOnCore base core2 serverTid
  { st1 with scheduler := st1.scheduler.setCurrentOnCore core1 (some victimTid) }

private def runPipDonationDropChecks : IO Unit := do
  IO.println "--- §3.14 SM6.E PIP donation drop on suspend (ordering fix) ---"
  match victimTid.toValid? with
  | none => assertBool "setup: victim ValidThreadId" false
  | some vtid =>
      assertBool "setup: server runnable on core 2 carrying the donated boost"
        ((match stPipDonation.getTcb? serverTid with
          | some s => decide (s.pipBoost = some ⟨200⟩)
          | none => false)
          && decide (serverTid ∈ stPipDonation.scheduler.runQueueOnCore core2)
          && decide ((stPipDonation.scheduler.runQueueOnCore core2).threadPriority[serverTid]?
              = some ⟨200⟩))
      match suspendThreadOnCore stPipDonation vtid bootCoreId with
      | .ok (st', sgi) =>
          -- (i) the ordering fix: the revert runs AFTER the teardown, from the
          -- captured server, so the recompute sees `waitersOf(server)` without
          -- the victim and genuinely drops the donation.
          assertBool "suspend drops the server's donated pipBoost"
            (match st'.getTcb? serverTid with
             | some s => decide (s.pipBoost = none)
             | none => false)
          -- (ii) per-core migration: the server stays runnable on ITS home
          -- core and its recorded bucket drops 200 → 50 (the boot-pinned
          -- `updatePipBoost` would have left the core-2 bucket at the stale
          -- 200 — the SM5.F per-core-PIP-migration gap this closes).
          assertBool "server stays runnable on core 2 across the bucket migration"
            (decide (serverTid ∈ st'.scheduler.runQueueOnCore core2))
          assertBool "server's core-2 bucket is re-keyed to its base priority"
            (decide ((st'.scheduler.runQueueOnCore core2).threadPriority[serverTid]?
              = some ⟨50⟩))
          -- (iii) the review fix: the diff seam derives the core-2
          -- re-bucketing poke the FFI suspend entry now fires.
          assertBool "diff seam pokes core 2 for the server re-bucketing"
            ((PriorityInheritance.computeCrossCoreSgis stPipDonation st' bootCoreId).any
              (fun p => p.1 == core2 && p.2 == SgiKind.reschedule))
          assertBool "diff seam still pokes core 1 for the victim deschedule"
            ((PriorityInheritance.computeCrossCoreSgis stPipDonation st' bootCoreId).any
              (fun p => p.1 == core1 && p.2 == SgiKind.reschedule))
          assertBool "surfaced SGI remains the victim's home-core poke"
            (decide (sgi = some (core1, SgiKind.reschedule)))
      | .error _ => assertBool "PIP-donation suspend succeeds" false
      -- Single-core mirror: the boot pipeline (`suspendThread`) drops the
      -- boost through the same capture → clear → revert-from-server order.
      let stBootPip :=
        (BootstrapBuilder.empty
          |>.withObject epId (.endpoint {})
          |>.withObject rId.toObjId (.reply { replyId := rId, caller := some victimTid })
          |>.withObject victimTid.toObjId (.tcb { mkTcb 710 200 none with
              threadState := .Running,
              ipcState := .blockedOnReply epId (some serverTid),
              replyObject := some rId })
          |>.withObject serverTid.toObjId (.tcb { mkTcb 716 50 none with
              threadState := .Ready,
              pipBoost := some ⟨200⟩ })
          |>.withRunnable [serverTid]
          |>.build)
      match suspendThread stBootPip vtid with
      | .ok st' =>
          assertBool "single-core suspend also drops the server's donated boost"
            (match st'.getTcb? serverTid with
             | some s => decide (s.pipBoost = none)
             | none => false)
      | .error _ => assertBool "single-core PIP suspend succeeds" false

-- ----------------------------------------------------------------------------
-- Scenario N (PR #831 review 2): disinheritance scheduling points.  Suspending
-- a reply-blocked client deboosts its STILL-RUNNING server — (a) when the
-- executing core itself runs the server, a mid-priority ready thread must
-- preempt inline (no SGI can reach the executing core); (b) the single-core
-- pipeline mirrors it; (c) when the server runs on a remote core, the diff
-- seam's deboosted-current rule pokes that core.
-- ----------------------------------------------------------------------------

/-- The executing (boot) core runs the victim's server (base 50, boost 200);
a prio-100 bystander waits in the boot queue; the victim (prio 200, home
core 1, NOT current anywhere) is reply-blocked on the server. -/
private def stLocalDeboost : SystemState :=
  let base :=
    (BootstrapBuilder.empty
      |>.withObject epId (.endpoint {})
      |>.withObject rId.toObjId (.reply { replyId := rId, caller := some victimTid })
      |>.withObject victimTid.toObjId (.tcb { mkTcb 710 200 (some core1) with
          threadState := .Ready,
          ipcState := .blockedOnReply epId (some serverTid),
          replyObject := some rId })
      |>.withObject serverTid.toObjId (.tcb { mkTcb 716 50 none with
          threadState := .Running,
          pipBoost := some ⟨200⟩ })
      |>.withObject bystanderTid.toObjId (.tcb { mkTcb 712 100 none with
          threadState := .Ready })
      |>.withRunnable [bystanderTid]
      |>.build)
  { base with scheduler := base.scheduler.setCurrentOnCore bootCoreId (some serverTid) }

/-- The server (base 50, boost 200) is RUNNING on core 2 (current, not
queued); the victim (home core 1, not current) is reply-blocked on it. -/
private def stRemoteDeboost : SystemState :=
  let base :=
    (BootstrapBuilder.empty
      |>.withObject epId (.endpoint {})
      |>.withObject rId.toObjId (.reply { replyId := rId, caller := some victimTid })
      |>.withObject victimTid.toObjId (.tcb { mkTcb 710 200 (some core1) with
          threadState := .Ready,
          ipcState := .blockedOnReply epId (some serverTid),
          replyObject := some rId })
      |>.withObject serverTid.toObjId (.tcb { mkTcb 716 50 (some core2) with
          threadState := .Running,
          pipBoost := some ⟨200⟩ })
      |>.build)
  { base with scheduler := base.scheduler.setCurrentOnCore core2 (some serverTid) }

private def runDisinheritanceSchedulingChecks : IO Unit := do
  IO.println "--- §3.15 SM6.E disinheritance scheduling points (PR #831 review 2) ---"
  match victimTid.toValid? with
  | none => assertBool "setup: victim ValidThreadId" false
  | some vtid =>
      -- (a) LOCAL: the executing core runs the server; the deboosted (50)
      -- current must be preempted inline by the prio-100 bystander.
      match suspendThreadOnCore stLocalDeboost vtid bootCoreId with
      | .ok (st', sgi) =>
          assertBool "local disinheritance surfaces no SGI (victim was not current)"
            (decide (sgi = none))
          assertBool "deboosted server loses the boot current slot to the bystander"
            (decide (st'.scheduler.currentOnCore bootCoreId = some bystanderTid))
          assertBool "preempted server is re-enqueued on the boot queue at base priority"
            (decide (serverTid ∈ st'.scheduler.runQueueOnCore bootCoreId)
              && decide ((st'.scheduler.runQueueOnCore bootCoreId).threadPriority[serverTid]?
                  = some ⟨50⟩))
      | .error _ => assertBool "local-disinheritance suspend succeeds" false
      -- (b) single-core mirror (`suspendThread`, boot pipeline).
      match suspendThread stLocalDeboost vtid with
      | .ok st' =>
          assertBool "single-core suspend also preempts the deboosted boot current"
            (decide (st'.scheduler.currentOnCore bootCoreId = some bystanderTid))
      | .error _ => assertBool "single-core local-disinheritance suspend succeeds" false
      -- (c) REMOTE still-current: the state does not switch the remote core
      -- (only its own scheduler may), but the diff seam must poke it.
      match suspendThreadOnCore stRemoteDeboost vtid bootCoreId with
      | .ok (st', sgi) =>
          assertBool "remote still-current deboost surfaces no victim SGI"
            (decide (sgi = none))
          assertBool "server remains current on core 2 (only the poke crosses cores)"
            (decide (st'.scheduler.currentOnCore core2 = some serverTid))
          assertBool "diff seam pokes core 2 for the still-current deboosted server"
            ((PriorityInheritance.computeCrossCoreSgis stRemoteDeboost st' bootCoreId).any
              (fun p => p.1 == core2 && p.2 == SgiKind.reschedule))
      | .error _ => assertBool "remote-deboost suspend succeeds" false
      -- (d) footprint (PR #831 review 3): the executing core's run-queue
      -- write lock is a declared member of the suspend scheduler-domain
      -- footprint (the G7 local preemption gate writes under it), alongside
      -- the victim's home-core run-queue lock.
      assertBool "suspend sched footprint covers the executing core's run queue"
        (decide ((SchedLockId.runQueue ⟨bootCoreId⟩, Concurrency.AccessMode.write)
          ∈ suspendThreadOnCoreSchedLockSet core1 bootCoreId core1 core1 (some core1)))
      assertBool "suspend sched footprint still covers the victim's placed run queue"
        (decide ((SchedLockId.runQueue ⟨core1⟩, Concurrency.AccessMode.write)
          ∈ suspendThreadOnCoreSchedLockSet core1 bootCoreId core1 core1 (some core1)))

-- ----------------------------------------------------------------------------
-- Scenario O (PR #831 review 4, P1): an UNBOUND victim (home = boot) actually
-- RUNNING on a secondary core — reachable by unbinding a running
-- secondary-core thread (the migration reject gate only fires when the new
-- affinity forbids the running core; `none` admits every core).  The suspend
-- must deschedule and poke the RUNNING core, not the home.
-- ----------------------------------------------------------------------------

private def stUnboundRunningRemote : SystemState :=
  let base :=
    (BootstrapBuilder.empty
      |>.withObject victimTid.toObjId (.tcb { mkTcb 710 30 none with
          threadState := .Running })
      |>.build)
  { base with scheduler := base.scheduler.setCurrentOnCore core2 (some victimTid) }

private def runUnboundRunningSuspendChecks : IO Unit := do
  IO.println "--- §3.16 SM6.E unbound victim running on a secondary core (PR #831 review 4) ---"
  match victimTid.toValid? with
  | none => assertBool "setup: victim ValidThreadId" false
  | some vtid =>
      assertBool "setup: home = boot but the victim is current on core 2"
        (decide (determineTargetCore stUnboundRunningRemote victimTid = bootCoreId)
          && decide (stUnboundRunningRemote.scheduler.currentOnCore core2 = some victimTid)
          && decide (runningCoreOf? stUnboundRunningRemote victimTid = some core2))
      match suspendThreadOnCore stUnboundRunningRemote vtid bootCoreId with
      | .ok (st', sgi) =>
          assertBool "suspend pokes the RUNNING core (core 2), not the boot home"
            (decide (sgi = some (core2, SgiKind.reschedule)))
          assertBool "core 2's current slot no longer holds the victim"
            (decide (st'.scheduler.currentOnCore core2 ≠ some victimTid))
          assertBool "victim is .Inactive"
            (match st'.getTcb? victimTid with
             | some t => decide (t.threadState = .Inactive)
             | none => false)
          assertBool "diff seam derives the running-core poke (re-keyed descheduled rule)"
            ((PriorityInheritance.computeCrossCoreSgis stUnboundRunningRemote st'
              bootCoreId).any (fun p => p.1 == core2 && p.2 == SgiKind.reschedule))
          -- Audit closure, re-keyed at WS-RR RR8.6: the deschedule writes the core
          -- the state PLACES the victim on — core 2, where it is current — and
          -- that core's run-queue write lock is a DECLARED footprint member,
          -- resolved from the same pre-state expression the transition reads.
          assertBool "suspend sched footprint covers the PLACED core's run queue (core 2)"
            (decide ((SchedLockId.runQueue ⟨core2⟩, Concurrency.AccessMode.write)
              ∈ suspendThreadOnCoreSchedLockSet bootCoreId bootCoreId bootCoreId bootCoreId
                  (placedCoreOf? stUnboundRunningRemote victimTid)))
      | .error _ => assertBool "unbound-running suspend succeeds" false

-- ----------------------------------------------------------------------------
-- Scenario O' (WS-RR RR8.6): an UNPINNED victim (home = boot) QUEUED on a
-- secondary core and current nowhere — the placement the home-keyed removal
-- and the running-core removal both miss.  Reachable with ordinary syscalls:
-- pin to core 2, run there, unpin (`none` admits every core, so the
-- running-thread refusal does not fire), be preempted
-- (`preemptCurrentOnCore` re-enqueues on the core that ran it).
-- ----------------------------------------------------------------------------

private def stUnpinnedQueuedRemote : SystemState :=
  let base :=
    (BootstrapBuilder.empty
      |>.withObject victimTid.toObjId (.tcb { mkTcb 710 30 none with
          threadState := .Ready })
      |>.build)
  enqueueRunnableOnCore base core2 victimTid

/-- The RETIRED reading, computed here and nowhere else: the removal pair
`suspendThreadOnCore`'s G4 + G4b ran until WS-RR RR8.6 — at the victim's home
(`determineTargetCore`) and, when it differs, at the core running it
(`runningCoreOf?`).  `descheduleThread`'s own pre-RR8.6 state was the first
half alone.  Kept beside the live reading so the assertions below are known to
discriminate rather than merely to pass. -/
private def retiredHomeAndRunningDeschedule (st : SystemState)
    (tid : SeLe4n.ThreadId) : SystemState :=
  let home := determineTargetCore st tid
  let st := removeRunnableOnCore st tid home
  match runningCoreOf? st tid with
  | some c => if c == home then st else removeRunnableOnCore st tid c
  | none => st

private def runPlacementDescheduleChecks : IO Unit := do
  IO.println "--- §3.24 WS-RR RR8.6 the deschedule reads placement, not the home ---"
  assertBool "setup: the victim is unpinned, so its home is the boot core"
    (decide (determineTargetCore stUnpinnedQueuedRemote victimTid = bootCoreId))
  assertBool "setup: ...and it is QUEUED on core 2, current nowhere"
    (decide (victimTid ∈ stUnpinnedQueuedRemote.scheduler.runQueueOnCore core2)
      && decide (runningCoreOf? stUnpinnedQueuedRemote victimTid = none))
  assertBool "the placement resolver finds core 2"
    (decide (placedCoreOf? stUnpinnedQueuedRemote victimTid = some core2))
  -- The retired reading, side by side: a removal at the home (boot) is a no-op
  -- and there is no running core, so the victim stays queued on core 2.
  let retired := retiredHomeAndRunningDeschedule stUnpinnedQueuedRemote victimTid
  assertBool "the RETIRED home-and-running reading leaves the victim queued on core 2"
    (decide (victimTid ∈ retired.scheduler.runQueueOnCore core2))
  -- The live deschedule primitive.
  let (st', sgi) := descheduleThread stUnpinnedQueuedRemote victimTid bootCoreId
  assertBool "descheduleThread removes the victim from core 2's run queue"
    (decide (victimTid ∉ st'.scheduler.runQueueOnCore core2))
  assertBool "...and surfaces no SGI: a queued victim needs no poke"
    (decide (sgi = none))
  assertBool "...and the victim is placed nowhere afterwards"
    (decide (placedCoreOf? st' victimTid = none))
  -- The `.ready` cancellation composite agrees (its teardown is the identity).
  let tcb := victimTcb stUnpinnedQueuedRemote
  let (stC, sgiC) := cancelIpcBlockingOnCore victimTid tcb bootCoreId stUnpinnedQueuedRemote
  assertBool "cancelIpcBlockingOnCore removes the victim from core 2 too, with no SGI"
    (decide (victimTid ∉ stC.scheduler.runQueueOnCore core2) && decide (sgiC = none))
  -- The live `.tcbSuspend` operation: the victim ends `.Inactive` and on no core.
  match victimTid.toValid? with
  | none => assertBool "setup: victim ValidThreadId" false
  | some vtid =>
      match suspendThreadOnCore stUnpinnedQueuedRemote vtid bootCoreId with
      | .ok (stS, sgiS) =>
          assertBool "suspendThreadOnCore removes the victim from core 2's run queue"
            (decide (victimTid ∉ stS.scheduler.runQueueOnCore core2))
          assertBool "...the victim is placed on no core afterwards"
            (decide (placedCoreOf? stS victimTid = none))
          assertBool "...it is .Inactive"
            (match stS.getTcb? victimTid with
             | some t => decide (t.threadState = .Inactive)
             | none => false)
          assertBool "...and no SGI is surfaced (no core was executing it)"
            (decide (sgiS = none))
      | .error _ => assertBool "unpinned-queued-remote suspend succeeds" false
  -- The scheduler-domain footprints declare the placed core's run-queue lock,
  -- resolved from the same pre-state expression the transitions read.
  assertBool "suspend sched footprint covers core 2's run queue (the placement)"
    (decide ((SchedLockId.runQueue ⟨core2⟩, Concurrency.AccessMode.write)
      ∈ suspendThreadOnCoreSchedLockSet bootCoreId bootCoreId bootCoreId bootCoreId
          (placedCoreOf? stUnpinnedQueuedRemote victimTid)))
  assertBool "NEGATIVE: the members the retired keying declared here (home = boot, no running core) omit core 2"
    (decide ((SchedLockId.runQueue ⟨core2⟩, Concurrency.AccessMode.write)
      ∉ suspendThreadOnCoreSchedLockSet bootCoreId bootCoreId bootCoreId bootCoreId none))
  assertBool "cancellation sched footprint covers core 2's run queue (the placement)"
    (decide ((SchedLockId.runQueue ⟨core2⟩, Concurrency.AccessMode.write)
      ∈ cancelIpcBlockingOnCoreSchedLockSet (placedCoreOf? stUnpinnedQueuedRemote victimTid)
          none))

-- ----------------------------------------------------------------------------
-- Scenario P (audit closure): the diff seam's EDF deadline dimension and
-- queued-raise direction, plus full three-core suspend separation.
-- ----------------------------------------------------------------------------

/-- A core-2-homed thread queued on core 2 (prio 30, deadline 1000). -/
private def stEdfPre : SystemState :=
  let base :=
    (BootstrapBuilder.empty
      |>.withObject victimTid.toObjId (.tcb { mkTcb 710 30 (some core2) with
          threadState := .Ready, deadline := ⟨1000⟩ })
      |>.build)
  enqueueRunnableOnCore base core2 victimTid

/-- Rewrite one field of the victim's TCB in `stEdfPre`. -/
private def stEdfWith (f : TCB → TCB) : SystemState :=
  match stEdfPre.getTcb? victimTid with
  | some t => { stEdfPre with
      objects := stEdfPre.objects.insert victimTid.toObjId (.tcb (f t)) }
  | none => stEdfPre

/-- The victim RUNNING (current, not queued) on core 2, deadline 10. -/
private def stEdfCurPre : SystemState :=
  let base :=
    (BootstrapBuilder.empty
      |>.withObject victimTid.toObjId (.tcb { mkTcb 710 30 (some core2) with
          threadState := .Running, deadline := ⟨10⟩ })
      |>.build)
  { base with scheduler := base.scheduler.setCurrentOnCore core2 (some victimTid) }

private def stEdfCurWith (f : TCB → TCB) : SystemState :=
  match stEdfCurPre.getTcb? victimTid with
  | some t => { stEdfCurPre with
      objects := stEdfCurPre.objects.insert victimTid.toObjId (.tcb (f t)) }
  | none => stEdfCurPre

private def runDiffSeamEdfChecks : IO Unit := do
  IO.println "--- §3.17 audit closure: EDF deadline dimension + queued raise + 3-core suspend ---"
  -- (a) deadline-only change of a remote QUEUED thread fires the home poke
  -- (within-bucket selection is EDF; the bucket does not move).
  assertBool "queued remote deadline change fires the home-core poke"
    ((PriorityInheritance.computeCrossCoreSgis stEdfPre
      (stEdfWith (fun t => { t with deadline := ⟨10⟩ })) bootCoreId).any
      (fun p => p.1 == core2 && p.2 == SgiKind.reschedule))
  -- (b) priority RAISE of a remote queued thread fires (the wake/re-bucket
  -- rule is direction-agnostic by design).
  assertBool "queued remote priority raise fires the home-core poke"
    ((PriorityInheritance.computeCrossCoreSgis stEdfPre
      (stEdfWith (fun t => { t with priority := ⟨99⟩ })) bootCoreId).any
      (fun p => p.1 == core2 && p.2 == SgiKind.reschedule))
  -- (c) a STILL-CURRENT remote thread whose deadline moved LATER is weakened —
  -- the running core must re-run its preemption gate.
  assertBool "still-current remote deadline-later fires the running-core poke"
    ((PriorityInheritance.computeCrossCoreSgis stEdfCurPre
      (stEdfCurWith (fun t => { t with deadline := ⟨1000⟩ })) bootCoreId).any
      (fun p => p.1 == core2 && p.2 == SgiKind.reschedule))
  -- (d) ... and a STRENGTHENING (deadline pulled earlier) fires nothing.
  assertBool "still-current remote deadline-earlier fires nothing"
    (decide (PriorityInheritance.computeCrossCoreSgis stEdfCurPre
      (stEdfCurWith (fun t => { t with deadline := ⟨1⟩ })) bootCoreId = []))
  -- (e) three-core separation: victim (home boot, unbound) RUNNING on core 2,
  -- suspended from core 1 — the SGI and the slot clear both target core 2.
  match victimTid.toValid? with
  | none => assertBool "setup: victim ValidThreadId" false
  | some vtid =>
      match suspendThreadOnCore stUnboundRunningRemote vtid core1 with
      | .ok (st', sgi) =>
          assertBool "three-core suspend pokes the running core"
            (decide (sgi = some (core2, SgiKind.reschedule)))
          assertBool "three-core suspend clears the running core's slot"
            (decide (st'.scheduler.currentOnCore core2 ≠ some victimTid))
      | .error _ => assertBool "three-core suspend succeeds" false

-- ============================================================================
-- Aggregate runner
-- ============================================================================

-- ----------------------------------------------------------------------------
-- Scenario R: WS-RR RR7.14 — the return frame a forcibly unblocked thread reads
-- ----------------------------------------------------------------------------
--
-- A thread whose blocking IPC is destroyed under it has no value to receive.
-- Until RR7.14 the teardown staged nothing, so the SM10.1 context restore would
-- have delivered whatever the argument spill left in `x0`-`x5` — the thread's
-- own request registers, decoded as a return value.  The checks below are
-- written so they cannot pass vacuously: the victim carries a **recognisable**
-- pre-state register file (`x0 = 0xBAD0`, `x1 = 0xBAD1`, ...), so "the frame is
-- `.ipcCancelled`" and "the frame is not what was there before" are two
-- different assertions and both are made.

/-- A register file whose `x0`-`x5` are all recognisable non-frame values —
what a blocked caller's argument spill leaves behind. -/
private def staleRequestRegs : SeLe4n.RegisterFile :=
  { pc := ⟨0x4000⟩, sp := ⟨0x9000⟩,
    gpr := fun r => ⟨0xBAD0 + r.val⟩ }

private def mkTcbWithStaleRegs (tid : Nat) (prio : Nat) (aff : Option CoreId) : TCB :=
  { mkTcb tid prio aff with registerContext := staleRequestRegs }

/-- The endpoint-blocked scenario, with the victim carrying the stale window. -/
private def stCallBlockedStale? : Option SystemState :=
  let base :=
    (BootstrapBuilder.empty
      |>.withObject epId (.endpoint {})
      |>.withObject victimTid.toObjId (.tcb (mkTcbWithStaleRegs 710 30 (some core1)))
      |>.withObject bystanderTid.toObjId (.tcb (mkTcb 712 20 none))
      |>.withRunnable [victimTid, bystanderTid]
      |>.build)
  match endpointCallOnCore epId victimTid IpcMessage.empty bootCoreId base with
  | (st, .ok none) => some st
  | _ => none

/-- The notification-blocked scenario, likewise. -/
private def stNtfnBlockedStale? : Option SystemState :=
  let base :=
    (BootstrapBuilder.empty
      |>.withObject nId (.notification { state := .idle, waitingThreads := SeLe4n.NoDupList.empty })
      |>.withObject victimTid.toObjId (.tcb (mkTcbWithStaleRegs 710 30 (some core1)))
      |>.withRunnable [victimTid]
      |>.build)
  match notificationWaitOnCore nId victimTid bootCoreId base with
  | (st, .ok none) => some st
  | _ => none

private def runUnblockFrameStagingChecks : IO Unit := do
  IO.println "--- §3.19 WS-RR RR7.14 the cancellation return frame ---"
  -- The two frames are distinguishable, and neither is the success frame.
  assertBool "the timeout and cancellation frames differ"
    (decide (Architecture.timeoutFrame ≠ Architecture.cancelledIpcFrame))
  assertBool "neither unblock frame is the success frame (x1 = 0)"
    (decide (Architecture.timeoutFrame.x1 ≠ 0 ∧ Architecture.cancelledIpcFrame.x1 ≠ 0))
  assertBool "each unblock frame's label decodes back to its own error"
    (decide (Architecture.ofErrorLabel? (Architecture.errorLabel KernelError.ipcTimeout)
               = some KernelError.ipcTimeout
             ∧ Architecture.ofErrorLabel? (Architecture.errorLabel KernelError.ipcCancelled)
               = some KernelError.ipcCancelled))
  assertBool "the cancellation error is its own discriminant, not folded into the timeout"
    (decide (KernelError.toDiscriminant .ipcCancelled = 57
             ∧ KernelError.toDiscriminant .ipcTimeout = 42
             ∧ KernelError.ofDiscriminant? 57 = some KernelError.ipcCancelled))
  -- The endpoint-blocked victim.
  match stCallBlockedStale? with
  | some st =>
      let tcb := victimTcb st
      assertBool "setup: the blocked victim still holds its stale request window"
        (decide (Architecture.readReturnFrame st victimTid
                   ≠ Architecture.cancelledIpcFrame)
         && decide ((Architecture.readReturnFrame st victimTid).x0 = 0xBAD0))
      let (st', _) := cancelIpcBlockingOnCore victimTid tcb bootCoreId st
      assertBool "an endpoint-blocked victim reads back .ipcCancelled after cancellation"
        (decide (Architecture.readReturnFrame st' victimTid
                   = Architecture.cancelledIpcFrame))
      assertBool "…and the stale window is GONE (x0 no longer the spilled argument)"
        (decide ((Architecture.readReturnFrame st' victimTid).x0 ≠ 0xBAD0))
      assertBool "…while x7 and pc/sp are untouched (staging writes x0-x5 only)"
        (match st'.getTcb? victimTid with
         | some t => decide (t.registerContext.gpr ⟨7⟩ = staleRequestRegs.gpr ⟨7⟩
                             ∧ t.registerContext.pc = staleRequestRegs.pc
                             ∧ t.registerContext.sp = staleRequestRegs.sp)
         | none => false)
      -- The bystander is untouched: staging is confined to the victim.
      assertBool "the bystander's register context is untouched by the victim's staging"
        (decide (Architecture.readReturnFrame st' bystanderTid
                   = Architecture.readReturnFrame st bystanderTid))
  | none => assertBool "setup: endpointCallOnCore block path succeeded (stale-reg fixture)" false
  -- The notification-blocked victim: the fourth arm, and the one whose return
  -- would otherwise have been a badge.
  match stNtfnBlockedStale? with
  | some st =>
      let tcb := victimTcb st
      let (st', _) := cancelIpcBlockingOnCore victimTid tcb bootCoreId st
      assertBool "a notification-blocked victim reads back .ipcCancelled (never a stale badge)"
        (decide (Architecture.readReturnFrame st' victimTid
                   = Architecture.cancelledIpcFrame))
  | none => assertBool "setup: notificationWaitOnCore block path succeeded (stale-reg fixture)" false
  -- NEGATIVE: the `.ready` arm is a no-op and stages NOTHING.  A thread that
  -- was not blocked has a live register window of its own; overwriting it would
  -- destroy a return value the kernel had already staged.
  let stReady : SystemState :=
    (BootstrapBuilder.empty
      |>.withObject victimTid.toObjId (.tcb (mkTcbWithStaleRegs 710 30 (some core1)))
      |>.withRunnable [victimTid]
      |>.build)
  let readyTcb := victimTcb stReady
  assertBool "setup: the .ready victim is not blocked"
    (decide (readyTcb.ipcState = ThreadIpcState.ready))
  assertBool "NEGATIVE: cancelling a .ready thread stages no frame — its window survives"
    (decide (Architecture.readReturnFrame (cancelIpcBlocking stReady victimTid readyTcb) victimTid
               = Architecture.readReturnFrame stReady victimTid)
     && decide (Architecture.readReturnFrame (cancelIpcBlocking stReady victimTid readyTcb)
                  victimTid ≠ Architecture.cancelledIpcFrame))
  -- NEGATIVE: `restoreToReady` (the RESUME spelling) stages nothing either — a
  -- resumed thread restarts where it was, so its window must survive.
  assertBool "NEGATIVE: restoreToReady (the resume spelling) stages no frame"
    (decide (Architecture.readReturnFrame (restoreToReady stReady victimTid) victimTid
               = Architecture.readReturnFrame stReady victimTid))
  assertBool "…and it is the SAME field clear as the cancellation spelling, frame aside"
    (match (restoreToReady stReady victimTid).getTcb? victimTid,
           (restoreToReadyCancelled stReady victimTid).getTcb? victimTid with
     | some a, some b =>
         decide (a.ipcState = b.ipcState ∧ a.queuePrev = b.queuePrev
                 ∧ a.queueNext = b.queueNext ∧ a.queuePPrev = b.queuePPrev
                 ∧ a.pendingReceiveReply = b.pendingReceiveReply
                 ∧ b.registerContext.gpr ⟨1⟩ ≠ a.registerContext.gpr ⟨1⟩)
     | _, _ => false)

/-- **WS-OD OD5.3 / OD6.3**: the suspend pipeline pops TWICE at call depth >= 2,
so its scheduler-domain replenish segment is a **triple**.

The G2 teardown's reply arm can rebind the victim `.donated scId outer`, and the
arm selector below it re-reads the binding from the *post*-teardown TCB, so the
`.donated` arm fires on a victim that entered `.unbound` and its migration's
destination is the **outer caller's** home core -- a core not resolvable from
the victim's pre-state binding, because at the pre-state the victim has none.
Relation, not presence: the negative keeps every core in the call and moves the
outer home onto the owner's, which is exactly the pair-shaped footprint the row
replaced. -/
private def runDonationDoublePopFootprintChecks : IO Unit := do
  IO.println "--- §3.17 WS-OD OD5.3 the suspend replenish segment is a triple ---"
  let core3 : CoreId := ⟨3, by decide⟩
  assertBool "the victim's own home replenish lock is declared"
    (decide ((SchedLockId.replenishQueue ⟨core1⟩, Concurrency.AccessMode.write)
      ∈ suspendThreadOnCoreSchedLockSet core1 bootCoreId core2 core3 (some core1)))
  assertBool "...so is the donation owner's home"
    (decide ((SchedLockId.replenishQueue ⟨core2⟩, Concurrency.AccessMode.write)
      ∈ suspendThreadOnCoreSchedLockSet core1 bootCoreId core2 core3 (some core1)))
  assertBool "...and so is the OUTER caller's home, which the second pop migrates to"
    (decide ((SchedLockId.replenishQueue ⟨core3⟩, Concurrency.AccessMode.write)
      ∈ suspendThreadOnCoreSchedLockSet core1 bootCoreId core2 core3 (some core1)))
  assertBool "NEGATIVE: a footprint whose outer home is the owner's declares no third"
    (decide ((SchedLockId.replenishQueue ⟨core3⟩, Concurrency.AccessMode.write)
      ∉ suspendThreadOnCoreSchedLockSet core1 bootCoreId core2 core2 (some core1)))
  -- The segment is sorted, which is what the scheduler bracket acquires in
  -- (WS-OD OD3's `lockAcquireSequence` correction, one domain over).
  assertBool "the three replenish locks are declared without duplication"
    (decide (((suspendThreadOnCoreSchedLockSet core1 bootCoreId core2 core3 (some core1)).filter
      (fun p => p.1 matches SchedLockId.replenishQueue _)).length = 3))

-- ----------------------------------------------------------------------------
-- Scenario P (WS-HP HP5): the head-driven reclaim, and the state on which the
-- two candidate triggers disagree.
-- ----------------------------------------------------------------------------

/-- **WS-HP HP5**: the *superseded* binding-driven trigger, spelled here and
nowhere else.

A second production spelling of "which donation does this cancellation reclaim"
would be the duplication this project retires — but a witness that cannot name what
it replaced cannot show that the replacement changed anything, which is the whole
point of the pair below.  So the retired reading lives in the test that refutes it,
exactly as `FrozenOpsSuite`'s `FO-042` keeps the retired reply-side trigger. -/
private def bindingDrivenCancelledCallerDonation? (st : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB) : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId) :=
  match tcb.ipcState with
  | .blockedOnReply _ (some holder) =>
    match lookupTcb st holder with
    | some holderTcb =>
      match holderTcb.schedContextBinding with
      | .donated scId owner => if owner == tid then some (scId, holder) else none
      | _ => none
    | none => none
  | _ => none

/-- A scheduling context bound to `bound`, heading the reply stack at `head?`. -/
private def mkStackedSc (bound : Option SeLe4n.ThreadId)
    (head? : Option SeLe4n.ReplyId) : SchedContext :=
  { mkSc bound true with scReply := head? }

/-- **The seL4-MCS shape both triggers agree on**: the victim Called a passive
server, donating its reservation, so its own reply object heads the context and the
server holds `.donated scId victim`.  Home cores differ (victim core 1, server
core 2) so the replenishment migration is observable, and the server is `.ready`
so OD1.4's abort prefix is inert and the reclaim's own writes are what the
assertions see. -/
private def stFrameHeadReclaim : SystemState :=
  let base :=
    (BootstrapBuilder.empty
      |>.withObject epId (.endpoint {})
      |>.withObject rId.toObjId (.reply
          { replyId := rId, caller := some victimTid, next := some (.head scId) })
      |>.withObject victimTid.toObjId (.tcb { mkTcb 710 30 (some core1) with
          ipcState := .blockedOnReply epId (some serverTid),
          replyObject := some rId,
          schedContextBinding := .unbound })
      |>.withObject serverTid.toObjId (.tcb { mkTcb 716 50 (some core2) with
          schedContextBinding := .donated scId victimTid })
      |>.withObject scId.toObjId (.schedContext (mkStackedSc (some serverTid) (some rId)))
      |>.build)
  let rq2 := (base.scheduler.replenishQueueOnCore core2).insert scId 42
  { base with scheduler := base.scheduler.setReplenishQueueOnCore core2 rq2 }

/-- **The shape on which the two triggers disagree** — and the reason HP5 has to
land before HP6.

Everything is as above except *who* holds the donation: the victim's recorded reply
target (`serverTid`) has given its own binding up, and the context is bound to a
third thread (`runnerTid`) which holds `.donated scId victim`.  Every conjunct of
`donationOwnerValid` holds — the context is bound to its holder, and the owner is an
`.unbound`, reply-blocked thread — and so does `donatedContextIsOwnerFrameHead`: the
victim's frame still heads the context.

The binding-driven reclaim reads the *recorded reply target*, finds no donation
there and declines, leaving `.donated scId victim` live across a cancellation that
made the victim `.ready` — which is exactly the `donationOwnerValid` break WS-RR
RR7.22 was written to close, reappearing at the one place that reading cannot see.
The head-driven reclaim follows the frame and reclaims it.

**Not a live defect when this fixture was written, which is why it is hand-built.**
Under the sever in force until `v0.35.44` a *pop* left no orphan head — the proved
half was `severAtCut_pop_leaves_no_head` (HP2.3), retired with the policy — which
is why the two readings agreed everywhere the reply path could put the state and
why HP4 and HP5 both preserved behaviour (the golden trace is byte-identical across
each).  **HP6.8 (`v0.35.45`) makes this shape reachable**: the splice re-heads the
frame below a cut, whose recorded reply server is by then `.unbound`.  So the
fixture now stands for a state the kernel produces rather than one it could only
be handed, and HP5 landing first is what stopped it arriving together with a
reclaim that cannot see it. -/
private def stOrphanHeadReclaim : SystemState :=
  let base :=
    (BootstrapBuilder.empty
      |>.withObject epId (.endpoint {})
      |>.withObject rId.toObjId (.reply
          { replyId := rId, caller := some victimTid, next := some (.head scId) })
      |>.withObject victimTid.toObjId (.tcb { mkTcb 710 30 (some core1) with
          ipcState := .blockedOnReply epId (some serverTid),
          replyObject := some rId,
          schedContextBinding := .unbound })
      |>.withObject serverTid.toObjId (.tcb (mkTcb 716 50 (some core2)))
      |>.withObject runnerTid.toObjId (.tcb { mkTcb 715 40 (some core2) with
          schedContextBinding := .donated scId victimTid })
      |>.withObject scId.toObjId (.schedContext (mkStackedSc (some runnerTid) (some rId)))
      |>.build)
  let rq2 := (base.scheduler.replenishQueueOnCore core2).insert scId 42
  { base with scheduler := base.scheduler.setReplenishQueueOnCore core2 rq2 }

/-- **WS-HP HP5: the reclaim's trigger, measured on both shapes.**

The decisive half is (iv): a state on which the two readings *differ*, with both
answers computed here — the head-driven one from production, the binding-driven one
from the local copy above — so the assertions are known to discriminate rather than
assumed to.

**On the mutation discipline.**  Reverting `cancelledCallerDonation?` to the binding
reading does not reach these assertions: it fails to elaborate four theorems in
`Lifecycle/Suspend.lean` first (`_independent_of_victim`,
`_eq_answeredFrameHeadContext?` and the two `rfl`s inside it), because HP5 states the
head reading rather than merely computing it.  That is the stronger outcome — a
behavioural revert is refused by the proof surface before any test runs — and it is
why the discrimination is exhibited *inside* the witness instead of by mutating
production. -/
private def runFrameHeadReclaimChecks : IO Unit := do
  IO.println "--- §3.20 WS-HP HP5 the head-driven cancellation reclaim ---"
  -- (i) The agreeing shape: the trigger fires, and it fires on the same pair the
  -- retired reading would have found.  That is the measurement that the flip is
  -- behaviour-preserving on every state `severAtCut` can produce.
  let tcb := victimTcb stFrameHeadReclaim
  assertBool "setup: the victim's reply frame heads the context, bound to the server"
    (decide (replyFrameHeadContext? stFrameHeadReclaim rId = some scId
      ∧ replyFrameHeadHolder? stFrameHeadReclaim rId = some (scId, serverTid)))
  assertBool "the head-driven trigger resolves (context, holder)"
    (decide (Lifecycle.Suspend.cancelledCallerDonation? stFrameHeadReclaim victimTid tcb
      = some (scId, serverTid)))
  assertBool "...and the RETIRED binding-driven reading agrees on this shape"
    (decide (bindingDrivenCancelledCallerDonation? stFrameHeadReclaim victimTid tcb
      = some (scId, serverTid)))
  -- (ii) HP5.4: the head the pop clears IS the victim's own reply object, and the
  -- two removal members are `none` — both theorems now, not fixture observations.
  assertBool "the head the pop clears is the victim's own reply object"
    (decide (cancelReclaimHead? stFrameHeadReclaim victimTid tcb = some rId
      ∧ cancelReclaimHead? stFrameHeadReclaim victimTid tcb = tcb.replyObject))
  assertBool "a reclaim excludes both removal members (no frame above, no frame below)"
    (decide (cancelSplicedFrameAbove? stFrameHeadReclaim tcb = none
      ∧ cancelSplicedFrameBelow? stFrameHeadReclaim tcb = none))
  -- (iii) The reclaim runs: the reservation comes back to the victim, the server
  -- is unbound, the stack head is popped and the replenishment migrates home.
  let (st', sgi) := cancelIpcBlockingOnCore victimTid tcb bootCoreId stFrameHeadReclaim
  assertBool "cancelling the donating caller surfaces no SGI (it was not current)"
    (decide (sgi = none))
  assertBool "the reservation comes back to the victim, .bound at the stack bottom"
    (match st'.getTcb? victimTid with
     | some t => decide (t.schedContextBinding = .bound scId ∧ t.ipcState = .ready)
     | none => false)
  assertBool "the server is left holding nothing"
    (match st'.getTcb? serverTid with
     | some t => decide (t.schedContextBinding = .unbound)
     | none => false)
  assertBool "the context is bound to the victim and heads nothing"
    (match st'.getSchedContext? scId with
     | some sc => decide (sc.boundThread = some victimTid ∧ sc.scReply = none)
     | none => false)
  assertBool "the popped frame keeps neither its stack link nor its caller"
    (match st'.getReply? rId with
     | some r => decide (r.next = none ∧ r.caller = none)
     | none => false)
  assertBool "the replenishment migrates off the server's home core"
    (!(st'.scheduler.replenishQueueOnCore core2).entries.any (fun e => e.1 == scId))
  assertBool "...and lands on the victim's home core at its original time"
    ((st'.scheduler.replenishQueueOnCore core1).entries.any
      (fun e => e.1 == scId && e.2 == 42))
  -- (iv) **The decisive case**: on the orphan-head shape the two triggers answer
  -- differently, and only the head-driven one reclaims.  The mutation keeps every
  -- object in the state and moves the donation off the recorded reply target.
  let orphanTcb := victimTcb stOrphanHeadReclaim
  assertBool "setup: the recorded reply target holds no donation"
    (match stOrphanHeadReclaim.getTcb? serverTid with
     | some t => decide (t.schedContextBinding = .unbound)
     | none => false)
  assertBool "setup: the frame still heads the context, bound to a third thread"
    (decide (replyFrameHeadHolder? stOrphanHeadReclaim rId = some (scId, runnerTid)))
  assertBool "the RETIRED binding-driven reading declines here"
    (decide (bindingDrivenCancelledCallerDonation? stOrphanHeadReclaim victimTid orphanTcb
      = none))
  assertBool "the head-driven trigger resolves the real holder"
    (decide (Lifecycle.Suspend.cancelledCallerDonation? stOrphanHeadReclaim victimTid orphanTcb
      = some (scId, runnerTid)))
  let (stOrphan', _) :=
    cancelIpcBlockingOnCore victimTid orphanTcb bootCoreId stOrphanHeadReclaim
  assertBool "the reclaim reaches the real holder and unbinds it"
    (match stOrphan'.getTcb? runnerTid with
     | some t => decide (t.schedContextBinding = .unbound)
     | none => false)
  assertBool "PAYOFF: no thread is left holding a context donated by the victim"
    ([victimTid, serverTid, runnerTid, ownerTid].all (fun t =>
      match stOrphan'.getTcb? t with
      | some tcbT => !(tcbT.schedContextBinding == .donated scId victimTid)
      | none => true))
  assertBool "...and the reservation is the victim's again"
    (match stOrphan'.getTcb? victimTid with
     | some t => decide (t.schedContextBinding = .bound scId)
     | none => false)

-- ----------------------------------------------------------------------------
-- §3.25  WS-RR RR8.11 — the replenishment migration's destination is the fact
-- ----------------------------------------------------------------------------

/-- A second scheduling context, so the cancelled caller can hold a binding of its
own and make HP4.6's recipient guard refuse the reclaim. -/
private def scIdOther : SeLe4n.SchedContextId := SeLe4n.SchedContextId.ofNat 704

/-- **The RETIRED destination**, computed here and nowhere else: until WS-RR RR8.11
`cancelIpcBlockingMigrated` aimed the migration at `determineTargetCore st victim` —
the home of the thread the reclaim is *about to* bind the context to — rather than
at the home of the thread it is bound to **after** the teardown.  Kept beside the
live reading so the assertions below are known to discriminate rather than merely to
pass. -/
private def retiredVictimHomeMigration (st : SystemState) (victim : SeLe4n.ThreadId)
    (tcb : TCB) : SystemState :=
  match Lifecycle.Suspend.cancelledCallerDonation? st victim tcb with
  | some (scId₀, holder) =>
      migrateSchedContextReplenishment (Lifecycle.Suspend.cancelIpcBlocking st victim tcb) scId₀
        (determineTargetCore st holder) (determineTargetCore st victim)
  | none => Lifecycle.Suspend.cancelIpcBlocking st victim tcb

/-- **The shape on which a refused reclaim and the retired destination part
company.**

`stFrameHeadReclaim`'s state with one field changed: the cancelled caller holds a
scheduling context of its **own** (`.bound scIdOther`), which is a state
`donationOwnerValid` permits — nothing names the victim as a donation's owner here,
because the holder's binding is `.donated scId victim`… and that is precisely what
the guard exists for.  HP4.6's `donationRecipientAcceptable` refuses to overwrite a
binding the recipient already has, so the reclaim commits nothing and `scId` stays
bound to the holder, homed on core 2, with its replenishment on core 2's queue.

Reachable with ordinary syscalls: a caller answered out of order is woken `.ready`
and `.unbound` and may bind a second reservation while its frame is still on a
stack (the HP10.7 discussion records the same window for the redirect's
rebindability guard).  The fixture is hand-built because driving it needs a
delegated reply, which is a longer scenario than the one fact being measured. -/
private def stRefusedReclaimRemoteHolder : SystemState :=
  let base :=
    (BootstrapBuilder.empty
      |>.withObject epId (.endpoint {})
      |>.withObject rId.toObjId (.reply
          { replyId := rId, caller := some victimTid, next := some (.head scId) })
      |>.withObject victimTid.toObjId (.tcb { mkTcb 710 30 (some core1) with
          ipcState := .blockedOnReply epId (some serverTid),
          replyObject := some rId,
          schedContextBinding := .bound scIdOther })
      |>.withObject serverTid.toObjId (.tcb { mkTcb 716 50 (some core2) with
          schedContextBinding := .donated scId victimTid })
      |>.withObject scId.toObjId (.schedContext (mkStackedSc (some serverTid) (some rId)))
      |>.build)
  let rq2 := (base.scheduler.replenishQueueOnCore core2).insert scId 42
  { base with scheduler := base.scheduler.setReplenishQueueOnCore core2 rq2 }

/-- Does core `c`'s replenish queue hold an entry for `sc`? -/
private def replenishHolds (st : SystemState) (c : CoreId) (sc : SeLe4n.SchedContextId) : Bool :=
  (st.scheduler.replenishQueueOnCore c).entries.any (fun e => e.1 == sc)

/-- **WS-RR RR8.11: the migration's destination is the bound thread's home, not the
victim's.**

The decisive comparison is (iii) against (iv): one state, two destinations, opposite
outcomes.  The retired reading moves `scId`'s replenishment to core 1 while `scId` is
still bound to a thread homed on core 2 — which is
`replenishQueueAffinityConsistentOnCore`'s own negation at core 1 — and the live
reading leaves it where the invariant says it belongs.

**On the mutation discipline.**  Reverting the destination to
`determineTargetCore st victim` does not reach these assertions: it fails to
elaborate `cancelIpcBlockingMigrated_eq_teardown_of_reclaim_inert` and
`cancelIpcBlockingMigrated_establishes_replenishQueueAffinityConsistent_smp` first,
because RR8.11 *states* the destination rather than merely computing it.  That is
the stronger outcome, and it is why the discrimination is exhibited inside the
witness rather than by mutating production. -/
private def runReplenishDestinationChecks : IO Unit := do
  IO.println "--- §3.25 WS-RR RR8.11 the replenishment destination is the fact ---"
  let st := stRefusedReclaimRemoteHolder
  let tcb := victimTcb st
  -- (i) The trigger fires on the holder, whose home differs from the victim's.
  assertBool "setup: the reclaim's trigger resolves the holder off the victim's frame"
    (decide (Lifecycle.Suspend.cancelledCallerDonation? st victimTid tcb
      = some (scId, serverTid)))
  assertBool "setup: the holder is homed on core 2 and the victim on core 1"
    (decide (determineTargetCore st serverTid = core2)
      && decide (determineTargetCore st victimTid = core1))
  assertBool "setup: the context's replenishment sits on the holder's home core"
    (replenishHolds st core2 scId && !replenishHolds st core1 scId)
  -- (ii) The reclaim REFUSES: the recipient guard will not overwrite the victim's
  -- own binding, so the context is still bound to the holder afterwards.
  assertBool "the reclaim commits nothing — `scId` is still bound to the holder"
    (decide (((Lifecycle.Suspend.returnDonationToCancelledCaller st victimTid
        tcb).getSchedContext? scId).bind (·.boundThread) = some serverTid))
  assertBool "...and so is it after the whole teardown"
    (decide (((Lifecycle.Suspend.cancelIpcBlocking st victimTid
        tcb).getSchedContext? scId).bind (·.boundThread) = some serverTid))
  -- (iii) The RETIRED destination moves the replenishment to the victim's home,
  -- where no thread bound to `scId` is homed.
  let retired := retiredVictimHomeMigration st victimTid tcb
  assertBool "the RETIRED victim-home destination moves the replenishment to core 1"
    (replenishHolds retired core1 scId && !replenishHolds retired core2 scId)
  assertBool "...and that breaks affinity consistency: the context is bound to a \
core-2 thread"
    (decide ((retired.getSchedContext? scId).bind (·.boundThread) = some serverTid)
      && decide (determineTargetCore retired serverTid = core2))
  -- (iv) The LIVE destination is the bound thread's home, so the migration is its
  -- own no-op and the replenishment stays put.
  let live := cancelIpcBlockingMigrated victimTid tcb st
  assertBool "the LIVE bound-thread destination leaves the replenishment on core 2"
    (replenishHolds live core2 scId && !replenishHolds live core1 scId)
  assertBool "the live destination resolves to the holder's home"
    (decide (replenishHomeOfSchedContext (Lifecycle.Suspend.cancelIpcBlocking st victimTid tcb)
      scId (determineTargetCore st serverTid) = core2))

def runSmpCancellationChecks : IO Unit := do
  IO.println "=== SmpCancellationSuite (WS-SM SM6.E cancellation across cores) ==="
  runEndpointCancelChecks
  runNotificationCancelChecks
  runReplyCancelChecks
  runRemoteRunningCancelChecks
  runLocalRunningCancelChecks
  runBoundDonationCancelChecks
  runDonatedDonationCancelChecks
  runDispatcherEdgeChecks
  runNotificationStateCorrectionChecks
  runMidQueueSpliceChecks
  runMirrorSgiChecks
  runPerCoreSuspendChecks
  runSendReceiveCancelChecks
  runPipDonationDropChecks
  runDisinheritanceSchedulingChecks
  runUnboundRunningSuspendChecks
  runPlacementDescheduleChecks
  runDiffSeamEdfChecks
  runUnblockFrameStagingChecks
  runDonationDoublePopFootprintChecks
  runFrameHeadReclaimChecks
  runReplenishDestinationChecks
  IO.println "SmpCancellationSuite: all checks passed."

end SeLe4n.Testing.SmpCancellation

def main : IO Unit :=
  SeLe4n.Testing.SmpCancellation.runSmpCancellationChecks
