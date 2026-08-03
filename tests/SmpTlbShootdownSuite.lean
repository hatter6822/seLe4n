-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Architecture.TlbShootdown
import SeLe4n.Kernel.Architecture.TlbShootdownProtocol
import SeLe4n.Kernel.Architecture.TlbShootdownWait
import SeLe4n.Kernel.Architecture.TlbShootdownLockSet
-- SM7.C: the per-core TLB model (§5 scenario groups + §1 anchors below).
import SeLe4n.Kernel.Architecture.PerCoreTlbModel
-- SM7.E.4: the sharing-domain dispatcher (`SharingDomain.toTag`) the
-- cross-cluster mock (§7) pins as the ONLY thing a multi-cluster port changes.
import SeLe4n.Kernel.Architecture.TlbiForSharing
import SeLe4n.Kernel.Lifecycle.Operations.RetypeWrappers
import SeLe4n.Kernel.SyscallDispatchEntry
import SeLe4n.Kernel.Concurrency.Runtime
-- SM7.B completion cut: §4.10 drives the live `.vspaceUnmap` syscall
-- through the full public dispatch (CSpace resolution + authority gate
-- + shootdown posting).
import SeLe4n.Kernel.API
import SeLe4n.Model.State
import SeLe4n.Platform.RPi5.Contract
import SeLe4n.Testing.StateBuilder

/-!
# WS-SM SM7.A + SM7.B — TLB shootdown descriptor, state + protocol suite

Tier-2 (runtime) + Tier-3 (surface anchor) coverage for the WS-SM Phase
SM7.A "Shootdown descriptor + state", SM7.B "Shootdown protocol", and
SM7.C "Per-core TLB model" deliverables
(`docs/planning/SMP_TLB_SHOOTDOWN_PLAN.md` §5, sub-tasks SM7.A.1–A.6,
SM7.B.1–B.12, and SM7.C.1–C.8).  The SM7.C per-core-TLB-model scenario
groups are §5.1–§5.2 (SM7.E.1): the accessors / local ops
(`tlbInsertOnCore` / `tlbInvalidateOnCore`) exposing the SMP staleness
hazard, and the cross-core `tlbInvalidateOnAllCores` broadcast realising
Theorem 3.3.1 (`tlbShootdown_invalidates_perCore`) + the
`tlbConsistency_cross_subsystem` capstone on the mounted `perCoreTlb`.

* **§1 Surface anchors** — every public SM7.A symbol resolves at
  elaboration time (rename/removal fails the build).
* **§2 Elaboration-time examples** — decidable examples + theorem
  application witnesses for the headline SM7.A facts (quiescent boot
  state, capacity bound, FIFO append, fold-to-`allAcked`).
* **§3 Runtime assertions** — `lake exe smp_tlb_shootdown_suite`
  exercises the actual `enqueueShootdown` / `drainShootdowns` /
  `acknowledgeShootdown` / `beginShootdownRound` computations on the
  SM7.A scenarios: descriptor operand round-trips, the quiescent boot
  state, FIFO enqueue + cross-core framing, the fail-closed capacity
  bound, exhaustive drains, the ack-round lifecycle, and a full
  4-core state-level shootdown round trip.
-/

namespace SeLe4n.Testing.SmpTlbShootdown

open SeLe4n.Model
open SeLe4n.Kernel.Architecture
open SeLe4n.Kernel.Concurrency

-- ============================================================================
-- §1  Surface anchors (Tier-3): every SM7.A public symbol resolves
-- ============================================================================

-- SM7.A.1 descriptor:
#check @TlbShootdownDescriptor
#check @TlbShootdownDescriptor.op
#check @TlbShootdownDescriptor.initiator

-- SM7.A.2 + SM7.A.3 state, boot state, path-a accessors:
#check @TlbShootdownState
#check @TlbShootdownState.pendingShootdowns
#check @TlbShootdownState.shootdownAck
#check @TlbShootdownState.initial
#check @TlbShootdownState.pendingOnCore
#check @TlbShootdownState.ackOnCore
#check @TlbShootdownState.setPendingOnCore
#check @TlbShootdownState.setAckedGenOnCore

-- SM7.A.2 store/load reduction algebra + extensionality:
#check @TlbShootdownState.setPendingOnCore_pendingOnCore_self
#check @TlbShootdownState.setPendingOnCore_pendingOnCore_ne
#check @TlbShootdownState.setPendingOnCore_ackOnCore
#check @TlbShootdownState.setAckedGenOnCore_ackedGenOnCore_self
#check @TlbShootdownState.setAckedGenOnCore_ackedGenOnCore_ne
#check @TlbShootdownState.setAckedGenOnCore_pendingOnCore
#check @TlbShootdownState.ext_perCore
#check @TlbShootdownState.initial_pendingOnCore
#check @TlbShootdownState.initial_ackOnCore

-- SM7.A.6 capacity bound + invariants:
#check @maxPendingPerCore
#check @maxPendingPerCore_pos
#check @pendingBounded
#check @allAcked
#check @shootdownQuiescent
#check @initial_pendingBounded
#check @initial_allAcked
#check @initial_shootdownQuiescent
#check @pendingBounded_of_shootdownQuiescent

-- SM7.A.4 enqueueShootdown + theorems:
#check @enqueueShootdown
#check @enqueueShootdown_isSome_iff
#check @enqueueShootdown_eq_none_iff
#check @enqueueShootdown_eq_none_of_full
#check @enqueueShootdown_pending_target
#check @enqueueShootdown_mem
#check @enqueueShootdown_length
#check @enqueueShootdown_frame_pending
#check @enqueueShootdown_frame_ack
#check @enqueueShootdown_preserves_pendingBounded

-- SM7.A.5 drainShootdowns + theorems:
#check @drainShootdowns
#check @drainShootdowns_fst
#check @mem_drainShootdowns_fst_iff
#check @drainShootdowns_pending_self
#check @drainShootdowns_frame_pending
#check @drainShootdowns_frame_ack
#check @drainShootdowns_preserves_pendingBounded
#check @drainShootdowns_drain_twice
#check @enqueueShootdown_isSome_after_drain
#check @drainShootdowns_after_enqueue

-- SM7.A.3 acknowledgment ops + round initialization:
#check @acknowledgeShootdown
#check @acknowledgeShootdown_ackOnCore_self
#check @acknowledgeShootdown_ackOnCore_ne
#check @acknowledgeShootdown_frame_pending
#check @acknowledgeShootdown_preserves_pendingBounded
#check @acknowledgeShootdown_monotone
#check @foldl_acknowledgeShootdown_monotone
#check @foldl_acknowledgeShootdown_sets
#check @allCores_foldl_acknowledgeShootdown_allAcked
#check @beginShootdownRound
#check @beginShootdownRound_ackOnCore_initiator
#check @beginShootdownRound_ackOnCore_target
#check @beginShootdownRound_ackOnCore_iff
#check @beginShootdownRound_frame_pending
#check @beginShootdownRound_preserves_pendingBounded

-- SM7.A completion cut — pure operand module (extracted from
-- TlbiForSharing; fully-qualified names unchanged):
#check @TlbInvalidation
#check @TlbInvalidation.toOpTag
#check @TlbInvalidation.toAsid
#check @TlbInvalidation.toVaddr
#check @TlbInvalidation.toOpTag_in_range
#check @TlbInvalidation.toOpTag_distinct_constructors

-- SM7.A completion cut — capacity sufficiency for a serialised round:
#check @enqueueShootdown_isSome_of_empty
#check @foldlM_enqueueShootdown_isSome
#check @foldlM_enqueueShootdown_frame_ack
#check @foldlM_enqueueShootdown_frame_pending

-- SM7.A completion cut — overflow-coalescing enqueue:
#check @enqueueShootdownOrCoalesce
#check @enqueueShootdownOrCoalesce_eq_enqueue
#check @enqueueShootdownOrCoalesce_of_full
#check @enqueueShootdownOrCoalesce_request_covered
#check @enqueueShootdownOrCoalesce_pending_covered
#check @enqueueShootdownOrCoalesce_preserves_pendingBounded
#check @enqueueShootdownOrCoalesce_frame_pending
#check @enqueueShootdownOrCoalesce_frame_ack

-- SM7.A audit cut — the global round-lock seam (the round-serialisation
-- contract's serialiser):
#check @ShootdownRoundLockId
#check @ShootdownRoundLockId.singleton

-- SM7.A PR #838 review P1 — target-masked round open (offline cores
-- born-acknowledged) + masked capstone:
#check @beginShootdownRoundFor
#check @beginShootdownRoundFor_ackOnCore_iff
#check @beginShootdownRoundFor_frame_pending
#check @beginShootdownRoundFor_preserves_pendingBounded
#check @beginShootdownRoundFor_allCores_eq
#check @foldl_setAckedGen_ackedGenOnCore
#check @foldl_setAckedGen_pendingOnCore
#check @beginRoundFor_foldlM_enqueueShootdown_isSome
#check @shootdownRoundFor_restores_quiescent

-- SM7.A completion cut — round-level composition + the quiescence
-- capstone:
#check @completeShootdownOnCore
#check @completeShootdownOnCore_eq
#check @completeShootdownOnCore_pendingOnCore_self
#check @completeShootdownOnCore_ackOnCore_self
#check @completeShootdownOnCore_frame_pending
#check @completeShootdownOnCore_frame_ack
#check @foldl_completeShootdownOnCore_pendingOnCore
#check @foldl_completeShootdownOnCore_ackOnCore
#check @beginRound_foldlM_enqueueShootdown_isSome
#check @shootdownRound_restores_quiescent

-- SM7.A completion cut — per-core pending-queue lock identifier (the
-- SM7.B.7 seam):
#check @ShootdownQueueLockId
#check @ShootdownQueueLockId.core
#check @ShootdownQueueLockId.le_refl
#check @ShootdownQueueLockId.le_trans
#check @ShootdownQueueLockId.le_antisymm
#check @ShootdownQueueLockId.le_total
#check @ShootdownQueueLockId.lt_or_gt_of_ne

-- SM7.A completion cut — SystemState mount (the plan §4.1
-- "ConcurrencyState" placement) + default-state theorems:
#check @SeLe4n.Model.SystemState.tlbShootdown
#check @SeLe4n.Model.default_tlbShootdown_initial
#check @SeLe4n.Model.default_tlbShootdown_quiescent
#check @SeLe4n.Model.default_tlbShootdown_pendingBounded

-- SM7.A completion cut — FFI seam (Rust SHOOTDOWN_ACK realisation):
#check @SeLe4n.Platform.FFI.ffiShootdownAckRound
#check @SeLe4n.Platform.FFI.ffiShootdownAckedGeneration
#check @SeLe4n.Platform.FFI.ffiShootdownAllAckedForRound
#check @SeLe4n.Platform.FFI.ffiShootdownSelfServiceRound
#check @SeLe4n.Kernel.Concurrency.shootdownAckRound
#check @SeLe4n.Kernel.Concurrency.shootdownAckedGeneration
#check @SeLe4n.Kernel.Concurrency.shootdownAllAckedForRound
#check @SeLe4n.Kernel.Concurrency.shootdownSelfServiceRound
#check @SeLe4n.Kernel.Concurrency.shootdownAckRound_eq_ffi
#check @SeLe4n.Kernel.Concurrency.shootdownSelfServiceRound_eq_ffi
#check @SeLe4n.Kernel.Concurrency.shootdownAck_ffi_core_in_range

-- SM7.B — invalidation-effect semantics + encoders:
#check @tlbEntryMatches
#check @applyTlbInvalidation
#check @mem_applyTlbInvalidation_iff
#check @applyTlbInvalidation_removes
#check @applyTlbInvalidation_preserves_other
#check @applyTlbInvalidation_idempotent
#check @applyTlbInvalidation_vmalle1
#check @applyTlbInvalidations
#check @applyTlbInvalidations_removes
#check @encodePageInvalidation
#check @encodeAsidInvalidation
#check @encodePageInvalidation_matches
#check @encodeAsidInvalidation_matches

-- SM7.B.1 + B.2 — local invalidation, target set, broadcast:
#check @tlbShootdownLocal
#check @tlbShootdownLocal_frame
#check @tlbShootdownLocal_removes
#check @shootdownTargets
#check @mem_shootdownTargets_iff
#check @initiator_not_mem_shootdownTargets
#check @shootdownTargets_cover
#check @shootdownTargets_nodup
#check @tlbShootdownBroadcast
#check @tlbShootdownBroadcast_isSome_of_quiescent
#check @tlbShootdownBroadcast_sgis
#check @tlbShootdownBroadcast_sgis_kind
#check @tlbShootdownBroadcast_frame
#check @tlbShootdownBroadcast_posts_singleton
#check @tlbShootdownBroadcast_ack_iff
#check @tlbShootdownBroadcast_preserves_pendingBounded

-- SM7.B.3 — the .tlbShootdownReq handler transitions:
#check @tlbShootdownDrainOnCore
#check @tlbShootdownAckOnCore
#check @handleTlbShootdownReqOnCore
#check @handleTlbShootdownReqOnCore_tlbShootdown_eq
#check @handleTlbShootdownReqOnCore_tlb_eq
#check @handleTlbShootdownReqOnCore_frame
#check @handleTlbShootdownReqOnCore_applies_posted_op
#check @handleTlbShootdownReqOnCore_idempotent

-- SM7.B.8 — round composition + Theorem 3.3.1:
#check @shootdownRound
#check @shootdownRound_isSome_of_quiescent
#check @shootdownRound_quiescent
#check @shootdownRound_allAcked
#check @shootdownRound_tlb_no_matching_entry
#check @setTlbViewOnCore
#check @shootdownRoundViews
#check @shootdownRoundViews_get
#check @tlbShootdownBroadcast_invalidatesAllCores
#check @tlbShootdownBroadcast_invalidates_unmap_target

-- SM7.B.12 — cross-cluster domain invariance:
#check @tlbShootdownBroadcastIn
#check @tlbShootdown_outer_correct

-- SM7.B.9 / B.10 — coalescing posting + shootdown-aware operations:
#check @postShootdownRoundCoalescing
#check @tlbShootdownBroadcastCoalescing
#check @tlbShootdownBroadcastCoalescing_eq_strict
#check @tlbShootdownBroadcastCoalescing_frame
#check @postShootdownRoundCoalescing_preserves_pendingBounded
#check @postShootdownRoundCoalescing_ack_iff
#check @postShootdownRoundCoalescing_covered
#check @withShootdownRound
#check @vspaceUnmapPageWithShootdown
#check @vspaceUnmapPageWithShootdown_error_iff
#check @vspaceUnmapPageWithShootdown_ok
#check @vspaceUnmapPageWithShootdown_posts
#check @vspaceMapPageCheckedWithShootdownFromState
#check @tlbFlushByASIDWithShootdown
#check @tlbFlushByPageWithShootdown
#check @asidAllocateWithShootdown
#check @asidAllocateWithShootdown_requiresFlush
#check @asidAllocateWithShootdown_fresh_inert

-- SM7.B.11 — retype-with-page-free shootdown:
#check @SeLe4n.Kernel.lifecycleRetypeDirectWithCleanupShootdown
#check @SeLe4n.Kernel.lifecycleRetypeDirectWithCleanupShootdown_non_vspace
#check @SeLe4n.Kernel.lifecycleRetypeDirectWithCleanupShootdown_vspace_posts

-- SM7.B.4 — release-acquire synchronization (vs the SM2.A model):
#check @AtomicLocation.shootdownAckOf
#check @AtomicLocation.shootdownAckOf_injective
#check @shootdownAck_release_acquire
#check @shootdownAckReleaseStore
#check @shootdownAckAcquireLoad
#check @shootdownAck_release_acquire_witness

-- SM7.B.5 + B.6 — wait-loop termination + timeout:
#check @ackMonotone
#check @ackMonotone_stable
#check @shootdown_wait_loop_terminates
#check @waitAllAckedFrom
#check @waitAllAckedBounded
#check @waitAllAckedFrom_some_spec
#check @waitAllAckedFrom_none_spec
#check @shootdown_timeout_handling
#check @waitAllAckedBounded_isSome
#check @shootdownWaitTimeoutTicks
#check @shootdownWaitTimeoutTicks_value

-- SM7.B.7 — the round's cross-domain lock-set:
#check @TlbShootdownLockId
#check @TlbShootdownLockId.object_lt_round
#check @TlbShootdownLockId.round_lt_queue
#check @TlbShootdownLockId.object_lt_queue
#check @TlbShootdownLockId.queue_lt_queue_iff
#check @lockSet_tlbShootdown
#check @allCores_pairwise_lt
#check @shootdownTargets_pairwise_lt
#check @lockSet_tlbShootdown_correct
#check @lockSet_tlbShootdown_nodup
#check @lockSet_tlbShootdown_round_mem
#check @lockSet_tlbShootdown_object_mem
#check @lockSet_tlbShootdown_queue_mem
#check @lockSet_tlbShootdown_covers_commit
#check @lockSet_tlbShootdown_length

-- SM7.B — runtime-seam diff recovery + live entry:
#check @shootdownChangedTargets
#check @mem_shootdownChangedTargets_iff
#check @shootdownChangedTargets_nil_of_eq
#check @shootdownPostedOps
#check @SeLe4n.Kernel.shootdownSharingDomain
#check @SeLe4n.Kernel.acquireShootdownRoundLockServicingSelf
#check @SeLe4n.Kernel.completeShootdownRounds
#check @SeLe4n.Kernel.Concurrency.shootdownRoundLockTryAcquire
#check @SeLe4n.Kernel.Concurrency.shootdownRoundLockRelease
#check @SeLe4n.Kernel.Concurrency.shootdownWaitAllAcked
#check @SeLe4n.Kernel.Concurrency.shootdownCoreOnline
#check @SeLe4n.Platform.FFI.ffiShootdownRoundLockTryAcquire
#check @SeLe4n.Platform.FFI.ffiShootdownRoundLockRelease
#check @SeLe4n.Platform.FFI.ffiShootdownWaitAllAcked
#check @SeLe4n.Platform.FFI.ffiShootdownOnlineMask

-- SM7.B completion cut — invariant-bundle carriage (`pendingBounded`,
-- the 12th `proofLayerInvariantBundle` conjunct) across every live
-- shootdown-aware transition:
#check @proofLayerInvariantBundle
#check @default_system_state_proofLayerInvariantBundle
#check @completeShootdownOnCore_preserves_pendingBounded
#check @tlbShootdownLocal_preserves_pendingBounded
#check @handleTlbShootdownReqOnCore_preserves_pendingBounded
#check @withShootdownRound_preserves_pendingBounded
#check @vspaceUnmapPageWithShootdown_preserves_pendingBounded
#check @vspaceMapPageCheckedWithShootdownFromState_preserves_pendingBounded
#check @tlbFlushByASIDWithShootdown_preserves_pendingBounded
#check @tlbFlushByPageWithShootdown_preserves_pendingBounded
#check @asidAllocateWithShootdown_preserves_pendingBounded
#check @SeLe4n.Kernel.lifecycleRetypeDirectWithCleanupShootdown_preserves_pendingBounded
#check @SeLe4n.Model.storeObject_tlbShootdown_eq
#check @SeLe4n.Model.default_tlbShootdown_pendingBounded
#check @vspaceUnmapPageWithFlush_tlbShootdown_eq
#check @SeLe4n.Kernel.lifecyclePreRetypeCleanup_tlbShootdown_eq
#check @SeLe4n.Kernel.lifecycleRetypeWithCleanup_tlbShootdown_eq

-- SM7.B completion cut — the CSpaceAddr retype-with-shootdown sibling
-- (the storeObject-sweep closure):
#check @SeLe4n.Kernel.lifecycleRetypeWithCleanupShootdown
#check @SeLe4n.Kernel.lifecycleRetypeWithCleanupShootdown_non_vspace
#check @SeLe4n.Kernel.lifecycleRetypeWithCleanupShootdown_vspace_posts
#check @SeLe4n.Kernel.lifecycleRetypeWithCleanupShootdown_preserves_pendingBounded

-- SM7.B completion cut — handler commutativity + coalesced coverage +
-- diff characterization + coalescing-round capstones:
#check @applyTlbInvalidation_comm
#check @applyTlbInvalidations_comm
#check @completeShootdownOnCore_comm
#check @handleTlbShootdownReqOnCore_comm
#check @foldl_handleTlbShootdownReqOnCore_swap
#check @tlbEntryMatches_vmalle1
#check @applyTlbInvalidations_of_mem_vmalle1
#check @coveredQueueRetire_removes
#check @vspaceUnmapPageWithShootdown_remote_retire_removes
#check @shootdownChangedTargets_coalescing_of_quiescent
#check @coalescingRound_restores_quiescent
#check @coalescingRound_allAcked
#check @mem_adapterFlushTlbByVAddr_of_mem_applyTlbInvalidation_encodePage
#check @mem_adapterFlushTlbByAsid_of_mem_applyTlbInvalidation_encodeAsid

-- SM7.B completion cut — least-index wait + round-lock CAS model +
-- publication witnesses:
#check @waitAllAckedFrom_first
#check @waitAllAckedBounded_least
#check @shootdown_wait_loop_terminates_least
#check @AtomicLocation.shootdownRoundLockAt
#check @AtomicLocation.shootdownRoundLockAt_ne_shootdownAckOf
#check @roundLockTryAcquire
#check @roundLockRelease
#check @roundLockTryAcquire_success_iff
#check @roundLockTryAcquire_post_held
#check @roundLockTryAcquire_mutex
#check @roundLockTryAcquire_after_release
#check @shootdownRoundLockReleaseStore
#check @shootdownRoundLockAcquireCas
#check @shootdownRoundLock_release_acquire
#check @shootdownRoundLock_release_acquire_witness
#check @shootdownAck_release_acquire_multi_pair_witness

-- SM7.B completion cut — remap-only map rounds + operand collapse +
-- entry-surface constants:
#check @vspaceHasTranslation
#check @vspaceMapPageCheckedWithShootdownFromState_fresh_inert
#check @vspaceMapPageCheckedWithFlushFromState_ok_fresh
#check @vspaceMapPageCheckedWithShootdownFromState_never_posts
#check @vspaceMapPageCheckedWithShootdownFromState_remap_posts
#check @collapseShootdownOps
#check @collapseShootdownOps_effect_eq
#check @collapseShootdownOps_no_vmalle1
#check @SeLe4n.Kernel.completeShootdownRounds_nil
#check @SeLe4n.Kernel.shootdownRoundLockAcquireFuel
#check @SeLe4n.Kernel.shootdownRoundLockAcquireFuel_value
#check @SeLe4n.Kernel.shootdownSharingDomain_rpi5
#check @SeLe4n.Kernel.Concurrency.shootdownOnlineMask
#check @SeLe4n.Kernel.Concurrency.coreOnlineInMask
#check @SeLe4n.Kernel.Concurrency.shootdownCoreOnline_eq_mask_test
#check @SeLe4n.Kernel.Concurrency.tlbiLocalFullFlush
#check @SeLe4n.Platform.FFI.ffiTlbiAll

-- SM7.B debt-closure cut — per-descriptor handler operand mailbox (debt (1))
-- + the withLockSet pendingBounded carriage slice (debt (5)):
#check @SeLe4n.Kernel.publishShootdownOps
#check @SeLe4n.Kernel.Concurrency.shootdownPublishBegin
#check @SeLe4n.Kernel.Concurrency.shootdownPublishSlot
#check @SeLe4n.Kernel.Concurrency.shootdownPublishCommit
#check @SeLe4n.Platform.FFI.ffiShootdownPublishBegin
#check @SeLe4n.Platform.FFI.ffiShootdownPublishSlot
#check @SeLe4n.Platform.FFI.ffiShootdownPublishCommit
#check @SeLe4n.Kernel.Concurrency.withLockSet_preserves_pendingBounded
#check @SeLe4n.Kernel.Concurrency.withLockSet_tlbShootdown_eq
#check @SeLe4n.Kernel.Concurrency.acquireLockOnObject_tlbShootdown_eq
#check @SeLe4n.Kernel.Concurrency.releaseLockOnObject_tlbShootdown_eq

-- SM7.C.1 per-core TLB mount + accessors (SM4.B path-a discipline):
#check @SeLe4n.Model.SystemState.perCoreTlb
#check @SeLe4n.Model.default_perCoreTlb
#check @tlbOnCore
#check @setTlbOnCore
#check @setTlbOnCore_tlbOnCore_self
#check @setTlbOnCore_tlbOnCore_ne
#check @default_tlbOnCore
-- SM7.C.2 tlbInsertOnCore (hardware translation walker):
#check @tlbInsertOnCore
#check @tlbInsertOnCore_mem
#check @tlbInsertOnCore_tlbOnCore_ne
-- SM7.C.3 tlbInvalidateOnCore (local, this-core invalidation):
#check @tlbInvalidateOnCore
#check @tlbInvalidateOnCore_removes
#check @tlbInvalidateOnCore_tlbOnCore_ne
#check @tlbInvalidateOnCore_subset
-- SM7.C.4 tlbInvalidateOnAllCores (cross-core broadcast via the protocol):
#check @tlbInvalidateOnAllCores
#check @tlbInvalidateOnAllCores_spec
#check @tlbInvalidateOnAllCores_perCoreTlb
#check @tlbInvalidateOnAllCores_sgis
#check @tlbInvalidateOnAllCores_objects
#check @tlbInvalidateOnAllCores_asidTable
#check @tlbInvalidateOnAllCores_isSome_of_quiescent
-- SM7.C.5 tlbInvalidationConsistent_perCore (the per-core TLB invariant,
-- the 13th proofLayerInvariantBundle conjunct):
#check @tlbInvalidationConsistent_perCore
#check @default_tlbInvalidationConsistent_perCore
#check @tlbInvalidationConsistent_perCore_bootCore
#check @tlbConsistent_of_subset_of_state_frame
#check @tlbInvalidateOnCore_preserves_tlbInvalidationConsistent_perCore
-- SM7.C.6 tlbShootdown_invalidates_perCore (Theorem 3.3.1, mounted):
#check @tlbShootdown_invalidates_perCore
-- SM7.C.7 tlbConsistency_cross_subsystem (the memory-subsystem capstone):
#check @tlbConsistency_cross_subsystem
-- SM7.C: the 13th proofLayerInvariantBundle conjunct is live:
#check @SeLe4n.Kernel.Architecture.default_system_state_proofLayerInvariantBundle
-- SM7.C completeness: insert-preservation (the walker half of the safety
-- story), the total coalescing form, and the runtime-decidable checker:
#check @tlbInsertOnCore_preserves_tlbInvalidationConsistent_perCore
#check @tlbInvalidateOnAllCoresCoalescing
#check @tlbInvalidateOnAllCoresCoalescing_eq_strict
-- SM7.F (PR #844 review-3): the faithful coalescing view (full flush on overflow):
#check @shootdownRoundViewsCoalescing
#check @shootdownRoundViewsCoalescing_eq_shootdownRoundViews
#check @foldlM_enqueueShootdown_pre_lt
#check @tlbConsistentCheck
#check @tlbConsistentCheck_iff
#check @tlbInvalidationConsistentCheck_perCore
#check @tlbInvalidationConsistentCheck_perCore_iff
-- SM7.C operational layer (the per-core drain the live seam runs):
#check @handleTlbShootdownReqOnCorePerCore
#check @handleTlbShootdownReqOnCorePerCore_tlb_eq
#check @handleTlbShootdownReqOnCorePerCore_tlbShootdown_eq
#check @handleTlbShootdownReqOnCorePerCore_applies_posted_op
#check @tlbShootdownLocalPerCore
#check @foldl_handleTlbShootdownReqOnCorePerCore_perCoreTlb
#check @foldl_handleTlbShootdownReqOnCorePerCore_agrees
#check @shootdownRoundPerCore
#check @shootdownRoundPerCore_perCoreTlb
#check @shootdownRoundPerCore_tlb_eq
#check @shootdownRoundPerCore_invalidates_perCore
#check @shootdownRoundPerCore_preserves_tlbInvalidationConsistent_perCore
-- SM7.C live catch-up incl. the initiator's own drain (PR #844 P1) + the
-- operative cross-subsystem capstone (PR #844 P2):
#check @drainInitiatorPerCoreView
#check @drainInitiatorPerCoreView_tlbOnCore_self
#check @drainInitiatorPerCoreView_tlbOnCore_ne
#check @drainInitiatorPerCoreView_preserves_tlbInvalidationConsistent_perCore
#check @foldl_handleTlbShootdownReqOnCorePerCore_tlbOnCore_notMem
#check @foldl_handleTlbShootdownReqOnCorePerCore_preserves_consistent
#check @shootdownCatchUpPerCore
#check @shootdownCatchUpPerCore_agrees_singleView
#check @shootdownCatchUpPerCore_initiator_view
#check @shootdownCatchUpPerCore_preserves_tlbInvalidationConsistent_perCore
#check @shootdownRoundPerCore_cross_subsystem
-- SM7.F.3: round-generation-tagged descriptors — a commit's catch-up drains
-- ONLY the rounds its own commit opened, so a concurrently-posted round's
-- work survives for its own catch-up (the SM7.B v0.32.79 fidelity debt):
#check @SeLe4n.Kernel.Architecture.roundDescriptor
#check @SeLe4n.Kernel.Architecture.roundDescriptor_generation
#check @SeLe4n.Kernel.Architecture.roundDescriptor_generation_eq_opened
#check @SeLe4n.Kernel.Architecture.roundDescriptor_inRoundWindow
#check @SeLe4n.Kernel.Architecture.inRoundWindow
#check @SeLe4n.Kernel.Architecture.inRoundWindow_iff
#check @SeLe4n.Kernel.Architecture.inRoundWindow_empty
#check @SeLe4n.Kernel.Architecture.inRoundWindow_succ_self
#check @SeLe4n.Kernel.Architecture.drainShootdownsInWindow
#check @SeLe4n.Kernel.Architecture.drainShootdownsInWindow_fst
#check @SeLe4n.Kernel.Architecture.mem_drainShootdownsInWindow_fst_iff
#check @SeLe4n.Kernel.Architecture.drainShootdownsInWindow_preserves_foreign
#check @SeLe4n.Kernel.Architecture.drainShootdownsInWindow_drains_own
#check @SeLe4n.Kernel.Architecture.drainShootdownsInWindow_preserves_pendingBounded
#check @SeLe4n.Kernel.Architecture.drainShootdownsInWindow_eq_drainShootdowns
#check @SeLe4n.Kernel.Architecture.completeShootdownOnCoreInWindow
#check @SeLe4n.Kernel.Architecture.completeShootdownOnCoreInWindow_preserves_foreign
#check @SeLe4n.Kernel.Architecture.completeShootdownOnCoreInWindow_eq_complete
#check @SeLe4n.Kernel.Architecture.beginShootdownRoundFor_roundGeneration
#check @SeLe4n.Kernel.Architecture.beginShootdownRoundFor_roundGeneration_gt
#check @handleTlbShootdownReqOnCoreInWindow
#check @handleTlbShootdownReqOnCoreInWindow_tlbShootdown_eq
#check @handleTlbShootdownReqOnCoreInWindow_tlb_eq
#check @handleTlbShootdownReqOnCoreInWindow_eq_handle
#check @handleTlbShootdownReqOnCoreInWindow_preserves_foreign
#check @handleTlbShootdownReqOnCoreInWindow_empty_window_tlb
#check @handleTlbShootdownReqOnCorePerCoreInWindow
#check @handleTlbShootdownReqOnCorePerCoreInWindow_eq_handle
#check @handleTlbShootdownReqOnCorePerCoreInWindow_preserves_foreign
#check @handleTlbShootdownReqOnCorePerCoreInWindow_preserves_tlbInvalidationConsistent_perCore
#check @foldl_handleTlbShootdownReqOnCorePerCoreInWindow_preserves_foreign
#check @shootdownCatchUpPerCoreInWindow
#check @shootdownCatchUpPerCoreInWindow_eq_catchUp
#check @shootdownCatchUpPerCoreInWindow_initiator_view
#check @shootdownCatchUpPerCoreInWindow_preserves_foreign
#check @shootdownCatchUpPerCoreInWindow_preserves_tlbInvalidationConsistent_perCore
-- The 12th `proofLayerInvariantBundle` conjunct (`pendingBounded`) carried
-- across the transition the live catch-up seam actually runs:
#check @handleTlbShootdownReqOnCoreInWindow_preserves_pendingBounded
#check @handleTlbShootdownReqOnCorePerCore_preserves_pendingBounded
#check @handleTlbShootdownReqOnCorePerCoreInWindow_preserves_pendingBounded
#check @foldl_handleTlbShootdownReqOnCorePerCoreInWindow_preserves_pendingBounded
#check @shootdownCatchUpPerCore_preserves_pendingBounded
#check @shootdownCatchUpPerCoreInWindow_preserves_pendingBounded
#check @shootdownRoundWindow
#check @shootdownRoundWindow_empty_of_eq
#check @mem_shootdownPostedOps_iff
#check @SeLe4n.Kernel.Architecture.mem_eraseDups_of_mem
#check @SeLe4n.Kernel.Architecture.mem_of_mem_eraseDups
-- SM7.F.1: the translation-walk fill seam (perCoreTlb made fillable):
#check @tlbWalkEntry
#check @tlbWalkEntry_matches
#check @tlbFillOnCore
#check @tlbFillOnCore_frame
#check @tlbFillOnCore_tlbOnCore_ne
#check @tlbFillOnCore_preserves_tlbInvalidationConsistent_perCore
-- SM7.F.2: the pending-aware (honest) invariant — every cached entry consistent
-- OR covered by a pending shootdown descriptor for its core:
#check @tlbEntryConsistent
#check @tlbEntryOk
#check @tlbEntryOk_of_frame
#check @tlbEntryOk_of_frame_eq
#check @tlbEntryConsistent_of_frame
#check @tlbEntryConsistent_of_ok_of_quiescent
#check @applyTlbInvalidations_survivor_not_matched
#check @tlbEntryConsistentCheck
#check @tlbEntryOkCheck
#check @tlbEntryOkCheck_iff
-- SM7.F.2a: the initiator-atomic unmap seam + its preservation (PR #844 P2):
#check @vspaceUnmapPageWithShootdownPerCore
#check @vspaceUnmapPageWithShootdownPerCore_preserves_tlbInvalidationConsistent_perCore
#check @vspaceUnmapPageWithFlush_tlbEntryConsistent_frame
#check @SeLe4n.Kernel.Architecture.vspaceUnmapPageWithFlush_perCoreTlb_eq
#check @SeLe4n.Model.storeObject_perCoreTlb_eq
-- SM7.F (PR #844 review-3): the unmap never unbinds an ASID (resolution half
-- of the conjunction-form `tlbEntryConsistent`):
#check @SeLe4n.Kernel.Architecture.vspaceUnmapPage_resolveAsidRoot_isSome
-- SM7.C NI: a per-core TLB write is projection-invisible (no covert channel):
#check @SeLe4n.Kernel.perCoreTlb_write_preserves_projection
-- SM7.F.4(a)+(b)(ii): the initiator-atomic map seam + live fill + its
-- preservation, plus the map-side frames (perCoreTlb frame, ASID-resolution
-- preservation, conjunction-form entry-consistency frame):
#check @SeLe4n.Kernel.Architecture.vspaceMapPageCheckedWithShootdownFromStatePerCore
#check @SeLe4n.Kernel.Architecture.vspaceMapPageCheckedWithShootdownFromStatePerCore_preserves_tlbInvalidationConsistent_perCore
#check @SeLe4n.Kernel.Architecture.vspaceMapPageCheckedWithFlushFromState_tlbEntryConsistent_frame
#check @SeLe4n.Kernel.Architecture.vspaceMapPageCheckedWithFlushFromState_perCoreTlb_eq
#check @SeLe4n.Kernel.Architecture.vspaceMapPage_resolveAsidRoot_isSome
-- SM7.F.4(b)(i)/(a): the live dispatch routes both VSpace arms through the
-- per-core wrappers (the delegation theorems pin the exact call targets):
#check @SeLe4n.Kernel.dispatchWithCap_vspaceUnmap_delegates
#check @SeLe4n.Kernel.dispatchWithCap_vspaceMap_delegates
-- SM7.F.4(b)(iii): the retype seam — the per-core wrapper drains the
-- initiator's view for the destroyed ASID (proven `_initiator_drained`), and
-- the live `.lifecycleRetype` dispatch routes through it:
#check @SeLe4n.Kernel.lifecycleRetypeDirectWithCleanupShootdownPerCore
#check @SeLe4n.Kernel.lifecycleRetypeDirectWithCleanupShootdownPerCore_initiator_drained
#check @SeLe4n.Kernel.dispatchWithCap_lifecycleRetype_delegates
-- SM7.F.4(b)(iii): the shared initiator drain + the CSpaceAddr retype sibling
-- (both production retype-with-shootdown entry points are initiator-atomic):
#check @SeLe4n.Kernel.retypeInitiatorDrain
#check @SeLe4n.Kernel.retypeInitiatorDrain_drained
#check @SeLe4n.Kernel.lifecycleRetypeWithCleanupShootdownPerCore
#check @SeLe4n.Kernel.lifecycleRetypeWithCleanupShootdownPerCore_initiator_drained
-- SM7.F.4(b)(iii) residual CLOSED: the WHOLE-invariant retype preservation
-- (both wrappers preserve `tlbInvalidationConsistent_perCore` for a VSpaceRoot
-- target, under `hNoRebind` — the necessary no-ASID-collision precondition):
#check @SeLe4n.Kernel.lifecycleRetypeDirectWithCleanupShootdownPerCore_preserves_tlbInvalidationConsistent_perCore
#check @SeLe4n.Kernel.lifecycleRetypeWithCleanupShootdownPerCore_preserves_tlbInvalidationConsistent_perCore
-- The live catch-up fold's ORDER-INDEPENDENCE (the §6 stress group's
-- concurrency claim): SM7.B proved commutativity for the single-view handler,
-- but the live `completeShootdownRounds` seam folds the PER-CORE handler, so
-- the claim must hold for that one — otherwise the model's one deterministic
-- visit order would not represent every hardware interleaving.
#check @SeLe4n.Kernel.Architecture.setTlbOnCore_comm
#check @SeLe4n.Kernel.Architecture.handleTlbShootdownReqOnCore_setTlbOnCore_comm
#check @SeLe4n.Kernel.Architecture.handleTlbShootdownReqOnCorePerCore_comm
#check @SeLe4n.Kernel.Architecture.foldl_handleTlbShootdownReqOnCorePerCore_swap
-- The cross-cluster portability seam the §7 mock exercises: the domain-tagged
-- round, its state-identity, the FFI domain tag, and the barrier selector.
#check @SeLe4n.Kernel.Architecture.tlbShootdownBroadcastIn
#check @SeLe4n.Kernel.Architecture.tlbShootdown_outer_correct
#check @SeLe4n.Kernel.Concurrency.SharingDomain.toTag
#check @SeLe4n.Kernel.Concurrency.SharingDomain.toTag_injective
#check @SeLe4n.Kernel.Concurrency.dsbForSharing
#check @SeLe4n.Kernel.shootdownSharingDomain

-- ============================================================================
-- §2  Elaboration-time examples
-- ============================================================================

-- SM7.A.6: the capacity bound is the plan §4.1 literal.
example : maxPendingPerCore = 16 := rfl

-- SM7.A.2/A.3: the boot state is quiescent, fully acknowledged, and
-- bounded — evaluated by the Decidable instances over all 4 cores.
example : shootdownQuiescent TlbShootdownState.initial := by decide
example : allAcked TlbShootdownState.initial := by decide
example : pendingBounded TlbShootdownState.initial := by decide

-- SM7.A.2/A.3: theorem-application witnesses for the boot-state facts
-- (the general proofs, not just the `decide` evaluations).
example : shootdownQuiescent TlbShootdownState.initial :=
  initial_shootdownQuiescent
example : pendingBounded TlbShootdownState.initial :=
  pendingBounded_of_shootdownQuiescent initial_shootdownQuiescent

-- SM7.A.3: acknowledging every core reaches `allAcked` from ANY state —
-- the SM7.B.5 wait-loop-termination anchor applied to a worst-case
-- start (a fresh round opened by core 0, so three flags are down).
example :
    allAcked (allCores.foldl
      (fun s x => acknowledgeShootdown s x
        (beginShootdownRound TlbShootdownState.initial bootCoreId).roundGeneration)
      (beginShootdownRound TlbShootdownState.initial bootCoreId)) :=
  allCores_foldl_acknowledgeShootdown_allAcked _ (Nat.le_refl _)

-- SM7.A.4: enqueue-success is exactly the strict capacity test.
example (st : TlbShootdownState) (c : CoreId) (d : TlbShootdownDescriptor) :
    (enqueueShootdown st c d).isSome ↔
      (st.pendingOnCore c).length < maxPendingPerCore :=
  enqueueShootdown_isSome_iff st c d

-- SM7.A.5: draining a just-enqueued descriptor returns it FIFO-appended.
example {st st' : TlbShootdownState} {c : CoreId} {d : TlbShootdownDescriptor}
    (h : enqueueShootdown st c d = some st') :
    (drainShootdowns st' c).1 = st.pendingOnCore c ++ [d] :=
  drainShootdowns_after_enqueue h

-- SM7.A completion cut: a round's posting fold from a quiescent state
-- always succeeds (the formal plan-§4.1 capacity argument) …
example {st : TlbShootdownState} (hq : shootdownQuiescent st)
    (initiator : CoreId) {targets : List CoreId} (hnd : targets.Nodup)
    (d : TlbShootdownDescriptor) :
    (targets.foldlM (fun s c => enqueueShootdown s c d)
      (beginShootdownRound st initiator)).isSome :=
  beginRound_foldlM_enqueueShootdown_isSome hq initiator hnd d

-- … and a complete round restores quiescence (the SM7.A capstone), so
-- the *next* round's posting fold succeeds too — the induction that
-- keeps maxPendingPerCore sufficient forever.
example {st : TlbShootdownState} (hq : shootdownQuiescent st)
    (initiator : CoreId) {targets : List CoreId}
    (hcov : ∀ c : CoreId, c ≠ initiator → c ∈ targets)
    {d : TlbShootdownDescriptor} {posted : TlbShootdownState}
    (hpost : targets.foldlM (fun s c => enqueueShootdown s c d)
      (beginShootdownRound st initiator) = some posted) :
    shootdownQuiescent (targets.foldl completeShootdownOnCore posted) :=
  shootdownRound_restores_quiescent hq initiator hcov hpost

-- SM7.A completion cut: the coalescing enqueue keeps the capacity
-- invariant with no success hypothesis.
example {st : TlbShootdownState} (hB : pendingBounded st) (target : CoreId)
    (d : TlbShootdownDescriptor) :
    pendingBounded (enqueueShootdownOrCoalesce st target d) :=
  enqueueShootdownOrCoalesce_preserves_pendingBounded hB target d

-- SM7.A audit cut: the coalescing enqueue loses neither the new
-- request nor any previously queued descriptor.
example (st : TlbShootdownState) (target : CoreId)
    (d : TlbShootdownDescriptor) :
    ∀ dOld ∈ st.pendingOnCore target,
      dOld ∈ (enqueueShootdownOrCoalesce st target d).pendingOnCore target ∨
        ∃ d' ∈ (enqueueShootdownOrCoalesce st target d).pendingOnCore target,
          d'.op = TlbInvalidation.vmalle1 :=
  enqueueShootdownOrCoalesce_pending_covered st target d

-- SM7.A audit cut: the global shootdown-round lock is provably unique —
-- "at most one round in flight" is structural.
example (a b : ShootdownRoundLockId) : a = b :=
  ShootdownRoundLockId.singleton a b

-- SM7.A PR #838 review P1: a masked round (targets = the online
-- non-initiator cores) restores quiescence with NO coverage
-- hypothesis — offline cores are born-acknowledged, never waited on.
example {st : TlbShootdownState} (hq : shootdownQuiescent st)
    (initiator : CoreId) {targets : List CoreId}
    {d : TlbShootdownDescriptor} {posted : TlbShootdownState}
    (hpost : targets.foldlM (fun s c => enqueueShootdown s c d)
      (beginShootdownRoundFor st initiator targets) = some posted) :
    shootdownQuiescent (targets.foldl completeShootdownOnCore posted) :=
  shootdownRoundFor_restores_quiescent hq initiator hpost

-- SM7.A completion cut: the default SystemState mounts the quiescent
-- shootdown state (decidable + theorem forms).
example : SeLe4n.Model.SystemState.tlbShootdown default =
    TlbShootdownState.initial := SeLe4n.Model.default_tlbShootdown_initial
example : shootdownQuiescent (SeLe4n.Model.SystemState.tlbShootdown default) := by
  decide

-- SM7.A completion cut: the FFI seam's typed wrappers hand the Rust
-- side only in-range core ids (the fail-closed panic arm is
-- structurally unreachable).
example : ∀ c : CoreId, (UInt64.ofNat c.val).toNat < numCores :=
  SeLe4n.Kernel.Concurrency.shootdownAck_ffi_core_in_range

-- SM7.B.8: Theorem 3.3.1 applied — with full coverage no core's view
-- retains a covered entry (the plan §3.3 headline, as an application
-- witness).
example (views : Vector SeLe4n.Model.TlbState numCores) (initiator : CoreId)
    (op : TlbInvalidation) (c : CoreId) {e : SeLe4n.Model.TlbEntry}
    (he : tlbEntryMatches op e = true) :
    e ∉ ((shootdownRoundViews views initiator (shootdownTargets initiator)
      op).get c).entries :=
  tlbShootdownBroadcast_invalidatesAllCores views initiator
    (shootdownTargets_cover initiator) op c he

-- SM7.B.8: the unmap instantiation — the caller's typed (asid, vaddr)
-- is gone from every core, unconditionally.
example (views : Vector SeLe4n.Model.TlbState numCores) (initiator : CoreId)
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) (c : CoreId)
    {e : SeLe4n.Model.TlbEntry} (hA : e.asid = asid) (hV : e.vaddr = vaddr) :
    e ∉ ((shootdownRoundViews views initiator (shootdownTargets initiator)
      (encodePageInvalidation asid vaddr)).get c).entries :=
  tlbShootdownBroadcast_invalidates_unmap_target views initiator asid vaddr
    c hA hV

-- SM7.B: a completed protocol round restores quiescence and reaches
-- the wait loop's exit condition.
example {st final : SeLe4n.Model.SystemState} {initiator : CoreId}
    {targets : List CoreId} {op : TlbInvalidation}
    (hq : shootdownQuiescent st.tlbShootdown)
    (h : shootdownRound st initiator targets op = some final) :
    allAcked final.tlbShootdown :=
  shootdownRound_allAcked hq h

-- SM7.B.4: the publication chain — the target's TLBI retirement
-- happens-before everything the initiator does after observing the ack.
example (t : MemoryTrace) {e_tlbi e_rel e_acq e_obs : MemoryEvent}
    (h₁ : sequencedBefore t e_tlbi e_rel)
    (h₂ : synchronizesWith t e_rel e_acq)
    (h₃ : sequencedBefore t e_acq e_obs) :
    happensBefore t e_tlbi e_obs :=
  shootdownAck_release_acquire t h₁ h₂ h₃

-- SM7.B.6: the bounded wait's verdict is exact in both directions.
example (fuel : Nat) (states : Nat → TlbShootdownState) :
    (∀ n : Nat, waitAllAckedBounded fuel states = some n →
      allAcked (states n) ∧ n < fuel) ∧
    (waitAllAckedBounded fuel states = none →
      ∀ j : Nat, j < fuel → ¬ allAcked (states j)) :=
  shootdown_timeout_handling fuel states

-- SM7.B.12: the cross-cluster round is state-identical to the
-- single-cluster round — every round theorem carries over verbatim.
example (st : SeLe4n.Model.SystemState) (initiator : CoreId)
    (targets : List CoreId) (op : TlbInvalidation) :
    tlbShootdownBroadcastIn .outer st initiator targets op =
      tlbShootdownBroadcastIn .inner st initiator targets op :=
  tlbShootdown_outer_correct st initiator targets op

-- SM7.B.12 (runtime pin): the live entry issues its TLBIs in the
-- platform's sharing domain — `.inner` on the single-cluster RPi5.
example : SeLe4n.Kernel.shootdownSharingDomain =
    SeLe4n.Platform.PlatformBinding.sharingDomain
      (platform := SeLe4n.Platform.RPi5.RPi5Platform) := rfl

-- SM7.B.7: the round's acquisition sequence is strictly ascending
-- (deadlock-freedom shape) and duplicate-free (2PL growing phase).
example (l : SeLe4n.Kernel.Concurrency.LockId) (initiator : CoreId) :
    List.Pairwise (· < ·) (lockSet_tlbShootdown l initiator) :=
  lockSet_tlbShootdown_correct l initiator

-- SM7.B.6: the Lean wait budget mirrors the HAL constant (10 ms at
-- the 54 MHz generic timer; Rust side pinned by
-- `sm7b_wait_timeout_matches_wfe_default`).
example : shootdownWaitTimeoutTicks = 540000 :=
  shootdownWaitTimeoutTicks_value

-- SM7.C.5: at boot every core's TLB view is empty, so the per-core TLB
-- consistency invariant holds — the 13th proofLayerInvariantBundle
-- conjunct's boot witness.
example : tlbInvalidationConsistent_perCore (default : SeLe4n.Model.SystemState) :=
  default_tlbInvalidationConsistent_perCore

-- SM7.C.7 (theorem-application witness): the cross-subsystem capstone —
-- a covering cross-core invalidation of a per-core-consistent state both
-- removes every stale entry on every core AND preserves per-core
-- consistency (VSpace × TLB-model × shootdown coherence).
example (st : SeLe4n.Model.SystemState) (initiator : CoreId)
    (targets : List CoreId) (hq : shootdownQuiescent st.tlbShootdown)
    (hcov : ∀ c : CoreId, c ≠ initiator → c ∈ targets)
    (op : TlbInvalidation) (hC : tlbInvalidationConsistent_perCore st)
    (st' : SeLe4n.Model.SystemState) (sgis : List (CoreId × SgiKind))
    (h : tlbInvalidateOnAllCores st initiator targets op = some (st', sgis)) :
    tlbInvalidationConsistent_perCore st' :=
  (tlbConsistency_cross_subsystem st initiator hq hcov op hC h).2

-- SM7.C.6 (theorem-application witness): after a covering broadcast no
-- core retains any entry the operand covers (Theorem 3.3.1, mounted).
example (st : SeLe4n.Model.SystemState) (initiator : CoreId)
    (targets : List CoreId) (hcov : ∀ c : CoreId, c ≠ initiator → c ∈ targets)
    (op : TlbInvalidation) (st' : SeLe4n.Model.SystemState)
    (sgis : List (CoreId × SgiKind))
    (h : tlbInvalidateOnAllCores st initiator targets op = some (st', sgis))
    (c : CoreId) (e : SeLe4n.Model.TlbEntry) (he : tlbEntryMatches op e = true) :
    e ∉ (tlbOnCore st' c).entries :=
  tlbShootdown_invalidates_perCore st initiator hcov op h c he

-- §6 (theorem-application witness): the live catch-up fold's visit order is a
-- convention — distinct cores' per-core handler steps commute, so the model's
-- single fold order represents every concurrent hardware interleaving.
example (st : SeLe4n.Model.SystemState) {c₁ c₂ : CoreId} (h : c₁ ≠ c₂) :
    handleTlbShootdownReqOnCorePerCore (handleTlbShootdownReqOnCorePerCore st c₁) c₂ =
      handleTlbShootdownReqOnCorePerCore (handleTlbShootdownReqOnCorePerCore st c₂) c₁ :=
  handleTlbShootdownReqOnCorePerCore_comm h st

-- §7 (theorem-application witness): the outer-shareable (cross-cluster) round
-- is state-identical to the inner one, so every SM7.B round theorem — posting
-- exactness, quiescence restoration, Theorem 3.3.1 — transports verbatim to a
-- multi-cluster port; only the emitted instruction variant changes.
example (st : SeLe4n.Model.SystemState) (initiator : CoreId)
    (targets : List CoreId) (op : TlbInvalidation) :
    tlbShootdownBroadcastIn .outer st initiator targets op =
      tlbShootdownBroadcastIn .inner st initiator targets op :=
  tlbShootdown_outer_correct st initiator targets op

-- ============================================================================
-- §3  Runtime assertions
-- ============================================================================

private def assertBool (name : String) (b : Bool) : IO Unit := do
  if b then IO.println s!"  PASS: {name}"
  else
    IO.println s!"  FAIL: {name}"
    throw (IO.userError s!"Assertion failed: {name}")

-- Concrete cores of the 4-core RPi5 topology.
private def core0 : CoreId := ⟨0, by decide⟩
private def core1 : CoreId := ⟨1, by decide⟩
private def core2 : CoreId := ⟨2, by decide⟩
private def core3 : CoreId := ⟨3, by decide⟩

-- Concrete descriptors covering every `TlbInvalidation` flavour the
-- SM7.B callers will post: page unmap, last-level unmap, ASID
-- retirement, full flush.
private def descUnmapPage : TlbShootdownDescriptor :=
  { op := .vae1 5 0x1000, initiator := core0, generation := 1 }
private def descLastLevel : TlbShootdownDescriptor :=
  { op := .vale1 5 0x2000, initiator := core0, generation := 1 }
private def descAsidRetire : TlbShootdownDescriptor :=
  { op := .aside1 7, initiator := core2, generation := 1 }
private def descFullFlush : TlbShootdownDescriptor :=
  { op := .vmalle1, initiator := core1, generation := 1 }

/-- Enqueue a batch of descriptors onto one target, failing (`none`) as
soon as any single enqueue fails — the shape of an SM7.B initiator
posting a round's descriptors. -/
private def enqueueMany (st : TlbShootdownState) (target : CoreId)
    (ds : List TlbShootdownDescriptor) : Option TlbShootdownState :=
  ds.foldlM (fun s d => enqueueShootdown s target d) st

/-- **WS-SM SM7.F.3**: does the queue hold a descriptor with exactly this
operand and initiator?

Generation-agnostic on purpose: since SM7.F.3 a descriptor also carries the
generation of the round that posted it, which is a function of how many rounds
the state has opened so far — an implementation detail these coverage checks do
not depend on.  What they assert is that the round's *invalidation obligation*
reached the target. -/
private def queueHasOp (q : List TlbShootdownDescriptor) (op : TlbInvalidation)
    (initiator : CoreId) : Bool :=
  q.any (fun d => d.op == op && d.initiator == initiator)

/-- **WS-SM SM7.F.3**: is the queue exactly one descriptor with this operand
and initiator?  The exact-posting form of `queueHasOp`. -/
private def queueIsExactly (q : List TlbShootdownDescriptor)
    (op : TlbInvalidation) (initiator : CoreId) : Bool :=
  q.map (fun d => (d.op, d.initiator)) == [(op, initiator)]

-- ----------------------------------------------------------------------------
-- §3.1  Descriptor construction + operand round-trips (SM7.A.1)
-- ----------------------------------------------------------------------------

private def runDescriptorChecks : IO Unit := do
  IO.println "-- §3.1 descriptor construction + operand round-trips"
  assertBool "page-unmap descriptor carries its ASID operand"
    (descUnmapPage.op.toAsid == 5)
  assertBool "page-unmap descriptor carries its VAddr operand"
    (descUnmapPage.op.toVaddr == 0x1000)
  assertBool "page-unmap descriptor encodes op tag 1 (vae1)"
    (descUnmapPage.op.toOpTag == 1)
  assertBool "ASID-retire descriptor carries its ASID, zero VAddr"
    (descAsidRetire.op.toAsid == 7 && descAsidRetire.op.toVaddr == 0)
  assertBool "full-flush descriptor has zero operands (vmalle1)"
    (descFullFlush.op.toAsid == 0 && descFullFlush.op.toVaddr == 0)
  assertBool "last-level descriptor encodes op tag 3 (vale1)"
    (descLastLevel.op.toOpTag == 3)
  assertBool "descriptor records its initiating core"
    (descAsidRetire.initiator == core2 && descUnmapPage.initiator == core0)
  assertBool "descriptor equality is decidable and structural"
    (descUnmapPage == descUnmapPage && !(descUnmapPage == descLastLevel))

-- ----------------------------------------------------------------------------
-- §3.2  Quiescent boot state (SM7.A.2 + SM7.A.3)
-- ----------------------------------------------------------------------------

private def runInitialStateChecks : IO Unit := do
  IO.println "-- §3.2 quiescent boot state"
  let st := TlbShootdownState.initial
  assertBool "every core boots with an empty pending queue"
    (allCores.all fun c => st.pendingOnCore c == [])
  assertBool "every core boots acknowledged"
    (allCores.all fun c => st.ackOnCore c)
  assertBool "boot state is quiescent (decidable instance)"
    (decide (shootdownQuiescent st))
  assertBool "boot state satisfies the capacity invariant"
    (decide (pendingBounded st))
  assertBool "boot state is fully acknowledged (decidable instance)"
    (decide (allAcked st))

-- ----------------------------------------------------------------------------
-- §3.3  FIFO enqueue + cross-core framing (SM7.A.4)
-- ----------------------------------------------------------------------------

private def runEnqueueChecks : IO Unit := do
  IO.println "-- §3.3 FIFO enqueue + cross-core framing"
  let st0 := TlbShootdownState.initial
  match enqueueShootdown st0 core1 descUnmapPage with
  | none => assertBool "enqueue onto an empty queue succeeds" false
  | some st1 => do
    assertBool "enqueued descriptor lands on the target queue"
      (st1.pendingOnCore core1 == [descUnmapPage])
    assertBool "other cores' queues are framed"
      ([core0, core2, core3].all fun c => st1.pendingOnCore c == [])
    assertBool "no ack flag is touched by an enqueue"
      (allCores.all fun c => st1.ackOnCore c == st0.ackOnCore c)
    match enqueueShootdown st1 core1 descAsidRetire with
    | none => assertBool "second enqueue onto the same queue succeeds" false
    | some st2 => do
      assertBool "second enqueue appends at the tail (FIFO)"
        (st2.pendingOnCore core1 == [descUnmapPage, descAsidRetire])
      assertBool "post-enqueue state stays bounded (decidable instance)"
        (decide (pendingBounded st2))
      match enqueueShootdown st2 core3 descFullFlush with
      | none => assertBool "enqueue onto a different core succeeds" false
      | some st3 => do
        assertBool "cross-core enqueues are independent"
          (st3.pendingOnCore core1 == [descUnmapPage, descAsidRetire] &&
           st3.pendingOnCore core3 == [descFullFlush] &&
           st3.pendingOnCore core0 == [] && st3.pendingOnCore core2 == [])

-- ----------------------------------------------------------------------------
-- §3.4  Fail-closed capacity bound (SM7.A.6)
-- ----------------------------------------------------------------------------

private def runCapacityChecks : IO Unit := do
  IO.println "-- §3.4 fail-closed capacity bound"
  let st0 := TlbShootdownState.initial
  match enqueueMany st0 core2 (List.replicate maxPendingPerCore descUnmapPage) with
  | none => assertBool "filling a queue to capacity succeeds" false
  | some full => do
    assertBool "queue holds exactly maxPendingPerCore descriptors"
      ((full.pendingOnCore core2).length == maxPendingPerCore)
    assertBool "the state at capacity still satisfies the invariant"
      (decide (pendingBounded full))
    assertBool "the 17th enqueue is rejected fail-closed"
      ((enqueueShootdown full core2 descAsidRetire).isNone)
    assertBool "a full queue on one core does not block another core"
      ((enqueueShootdown full core0 descAsidRetire).isSome)
    let (drained, cleared) := drainShootdowns full core2
    assertBool "the drain returns all 16 pending descriptors"
      (drained.length == maxPendingPerCore)
    assertBool "draining restores capacity: enqueue succeeds again"
      ((enqueueShootdown cleared core2 descAsidRetire).isSome)
  assertBool "over-filling by one descriptor fails the whole batch"
    ((enqueueMany st0 core2
      (List.replicate (maxPendingPerCore + 1) descUnmapPage)).isNone)

-- ----------------------------------------------------------------------------
-- §3.5  Exhaustive drain (SM7.A.5)
-- ----------------------------------------------------------------------------

private def runDrainChecks : IO Unit := do
  IO.println "-- §3.5 exhaustive drain"
  let st0 := TlbShootdownState.initial
  match enqueueMany st0 core1 [descUnmapPage, descAsidRetire, descFullFlush] with
  | none => assertBool "three-descriptor setup enqueue succeeds" false
  | some st => do
    let (drained, st') := drainShootdowns st core1
    assertBool "drain returns the whole queue in FIFO order"
      (drained == [descUnmapPage, descAsidRetire, descFullFlush])
    assertBool "the drained core's queue is empty"
      (st'.pendingOnCore core1 == [])
    assertBool "draining core 1 frames every other core's queue"
      ([core0, core2, core3].all fun c =>
        st'.pendingOnCore c == st.pendingOnCore c)
    assertBool "draining touches no ack flag"
      (allCores.all fun c => st'.ackOnCore c == st.ackOnCore c)
    assertBool "a second drain returns nothing (exhaustive)"
      ((drainShootdowns st' core1).1 == [])
    assertBool "the post-drain state stays bounded"
      (decide (pendingBounded st'))
  assertBool "draining a quiescent core returns nothing"
    ((drainShootdowns st0 core3).1 == [])

-- ----------------------------------------------------------------------------
-- §3.6  Acknowledgment round lifecycle (SM7.A.3)
-- ----------------------------------------------------------------------------

private def runAckRoundChecks : IO Unit := do
  IO.println "-- §3.6 acknowledgment round lifecycle"
  let st0 := TlbShootdownState.initial
  let opened := beginShootdownRound st0 core0
  assertBool "the initiator is born-acknowledged"
    (opened.ackOnCore core0)
  assertBool "every target starts the round unacknowledged"
    ([core1, core2, core3].all fun c => !(opened.ackOnCore c))
  assertBool "an open round is not allAcked"
    (!(decide (allAcked opened)))
  assertBool "opening a round touches no pending queue"
    (allCores.all fun c => opened.pendingOnCore c == st0.pendingOnCore c)
  let roundGen := opened.roundGeneration
  let ackedTwo := acknowledgeShootdown opened core2 roundGen
  assertBool "a target acknowledgment sets exactly its own flag"
    (ackedTwo.ackOnCore core2 && !(ackedTwo.ackOnCore core1) &&
     !(ackedTwo.ackOnCore core3) && ackedTwo.ackOnCore core0)
  assertBool "acknowledgment is monotone (initiator flag survives)"
    ((acknowledgeShootdown ackedTwo core1 roundGen).ackOnCore core0)
  assertBool "acknowledging every remaining target reaches allAcked"
    (decide (allAcked
      (acknowledgeShootdown (acknowledgeShootdown ackedTwo core1 roundGen) core3
        roundGen)))
  assertBool "folding acknowledgments over allCores reaches allAcked"
    (decide (allAcked (allCores.foldl
      (fun s x => acknowledgeShootdown s x roundGen) opened)))
  assertBool "a round opened by a non-boot core marks only that core"
    (allCores.all fun c =>
      (beginShootdownRound st0 core3).ackOnCore c == (c == core3))

-- ----------------------------------------------------------------------------
-- §3.7  Full 4-core state-level shootdown round trip (SM7.A.1–A.6)
-- ----------------------------------------------------------------------------

private def runFullRoundTripChecks : IO Unit := do
  IO.println "-- §3.7 full 4-core state-level shootdown round trip"
  -- Core 0 unmaps a page of ASID 5: open the round, post one page-unmap
  -- descriptor per remote core (the plan §3.2 step-2 loop).
  let desc : TlbShootdownDescriptor :=
    { op := .vae1 5 0x1000, initiator := core0, generation := 1 }
  let opened := beginShootdownRound TlbShootdownState.initial core0
  let posted? := [core1, core2, core3].foldlM
    (fun s c => enqueueShootdown s c desc) opened
  match posted? with
  | none => assertBool "posting one descriptor per target succeeds" false
  | some posted => do
    assertBool "each target sees exactly the round's descriptor"
      ([core1, core2, core3].all fun c => posted.pendingOnCore c == [desc])
    assertBool "the initiator's own queue stays empty"
      (posted.pendingOnCore core0 == [])
    assertBool "only the initiator is acknowledged while targets pend"
      (allCores.all fun c => posted.ackOnCore c == (c == core0))
    -- Each target's SGI handler: drain, (TLBI per descriptor — SM7.B),
    -- then acknowledge.
    let step := fun (s : TlbShootdownState) (c : CoreId) =>
      let (drained, s') := drainShootdowns s c
      (drained, acknowledgeShootdown s' c s.roundGeneration)
    let (d1, s1) := step posted core1
    let (d2, s2) := step s1 core2
    let (d3, s3) := step s2 core3
    assertBool "every handler drained exactly the posted descriptor"
      (d1 == [desc] && d2 == [desc] && d3 == [desc])
    assertBool "every drained descriptor carries the unmap operands"
      ((d1 ++ d2 ++ d3).all fun d =>
        d.op.toAsid == 5 && d.op.toVaddr == 0x1000 && d.initiator == core0)
    assertBool "after all handlers ran, the wait loop's exit holds"
      (decide (allAcked s3))
    assertBool "the completed round leaves the state quiescent"
      (decide (shootdownQuiescent s3))
    assertBool "the completed round satisfies the capacity invariant"
      (decide (pendingBounded s3))

-- ----------------------------------------------------------------------------
-- §3.8  Overflow-coalescing enqueue (SM7.A.6 completion cut)
-- ----------------------------------------------------------------------------

private def runCoalescingChecks : IO Unit := do
  IO.println "-- §3.8 overflow-coalescing enqueue"
  let st0 := TlbShootdownState.initial
  match enqueueShootdown st0 core1 descUnmapPage with
  | none => assertBool "baseline enqueue below capacity succeeds" false
  | some viaEnqueue =>
    assertBool "below capacity the coalescing enqueue is exactly enqueueShootdown"
      (enqueueShootdownOrCoalesce st0 core1 descUnmapPage == viaEnqueue)
  match enqueueMany st0 core2 (List.replicate maxPendingPerCore descUnmapPage) with
  | none => assertBool "filling a queue to capacity succeeds" false
  | some full => do
    let collapsed := enqueueShootdownOrCoalesce full core2 descAsidRetire
    assertBool "at capacity the queue collapses to a single full flush"
      (queueIsExactly (collapsed.pendingOnCore core2) .vmalle1
        descAsidRetire.initiator)
    assertBool "the collapsed descriptor carries the requesting initiator"
      ((collapsed.pendingOnCore core2).all fun d => d.initiator == core2)
    assertBool "the collapse frames every other core's queue"
      ([core0, core1, core3].all fun c =>
        collapsed.pendingOnCore c == full.pendingOnCore c)
    assertBool "the collapse touches no ack flag"
      (allCores.all fun c => collapsed.ackOnCore c == full.ackOnCore c)
    assertBool "the collapsed state satisfies the capacity invariant"
      (decide (pendingBounded collapsed))
    assertBool "dropped descriptors are superseded: a full flush is pending"
      ((collapsed.pendingOnCore core2).any fun d =>
        d.op == TlbInvalidation.vmalle1)
    assertBool "after the collapse a normal enqueue succeeds again"
      ((enqueueShootdown collapsed core2 descUnmapPage).isSome)

-- ----------------------------------------------------------------------------
-- §3.9  Round-level composition (the generic capstone, exercised)
-- ----------------------------------------------------------------------------

private def runRoundCompositionChecks : IO Unit := do
  IO.println "-- §3.9 round-level composition"
  -- completeShootdownOnCore is the drain+acknowledge composition.
  match enqueueShootdown (beginShootdownRound TlbShootdownState.initial core0)
      core2 descUnmapPage with
  | none => assertBool "round-step setup enqueue succeeds" false
  | some st => do
    let done := completeShootdownOnCore st core2
    assertBool "a completed core's queue is empty"
      (done.pendingOnCore core2 == [])
    assertBool "a completed core's flag is acknowledged"
      (done.ackOnCore core2)
    assertBool "completing a core equals drain-then-acknowledge"
      (done == acknowledgeShootdown (drainShootdowns st core2).2 core2
        st.roundGeneration)
    assertBool "completing core 2 frames core 1's flag (still down)"
      (!(done.ackOnCore core1))
  -- The full generic pipeline: begin → post (foldlM) → complete (foldl).
  let opened := beginShootdownRound TlbShootdownState.initial core0
  let targets := [core1, core2, core3]
  match targets.foldlM (fun s c => enqueueShootdown s c descUnmapPage) opened with
  | none => assertBool "the round's posting fold succeeds from quiescence" false
  | some posted => do
    let final := targets.foldl completeShootdownOnCore posted
    assertBool "the folded round ends quiescent (the capstone, computed)"
      (decide (shootdownQuiescent final))
    -- WS-SM SM7.F.3 (PR #854 review): a completed round returns every
    -- *queue* to its boot value, but neither the round-generation counter
    -- nor the acknowledgment vector — both are monotone by design.  Since
    -- v0.32.113 an acknowledgment names the round it discharged, so a
    -- completed round leaves every slot AT that round's generation rather
    -- than back at a boot flag; that is what makes the state quiescent
    -- (`roundGeneration ≤ ackedGenOnCore c` for every core) while keeping a
    -- later round distinguishable from this one.
    assertBool "the folded round empties every queue"
      (final == { TlbShootdownState.initial with
                    roundGeneration := final.roundGeneration,
                    shootdownAck := final.shootdownAck })
    assertBool "and leaves every core acknowledging exactly this round"
      (allCores.all fun c => final.ackedGenOnCore c == final.roundGeneration)
    assertBool "the completed round advanced the generation counter by exactly one"
      (final.roundGeneration == TlbShootdownState.initial.roundGeneration + 1)
    assertBool "the closed form: visited cores' queues empty, initiator's untouched"
      (targets.all (fun c => final.pendingOnCore c == []) &&
        final.pendingOnCore core0 == opened.pendingOnCore core0)
  assertBool "a duplicate target is harmless (drained twice, still quiescent)"
    (match [core1, core1, core2, core3].foldlM
        (fun s c => enqueueShootdown s c descUnmapPage)
        (beginShootdownRound TlbShootdownState.initial core0) with
      | none => false
      | some posted =>
        decide (shootdownQuiescent
          ([core1, core1, core2, core3].foldl completeShootdownOnCore posted)))

-- ----------------------------------------------------------------------------
-- §3.10  Pending-queue lock identifiers (the SM7.B.7 seam)
-- ----------------------------------------------------------------------------

private def runLockOrderChecks : IO Unit := do
  IO.println "-- §3.10 pending-queue lock identifiers"
  let l0 : ShootdownQueueLockId := ⟨core0⟩
  let l1 : ShootdownQueueLockId := ⟨core1⟩
  let l3 : ShootdownQueueLockId := ⟨core3⟩
  assertBool "queue locks order by core (0 ≤ 1, 1 ≤ 3)"
    (decide (l0 ≤ l1) && decide (l1 ≤ l3))
  assertBool "the order is strict across distinct cores"
    (decide (l0 < l1) && !(decide (l1 < l0)) && !(decide (l1 ≤ l0)))
  assertBool "every pair of queue locks is comparable (total order)"
    (allCores.all fun a => allCores.all fun b =>
      decide ((⟨a⟩ : ShootdownQueueLockId) ≤ ⟨b⟩) ||
      decide ((⟨b⟩ : ShootdownQueueLockId) ≤ ⟨a⟩))
  assertBool "distinct queue locks are strictly ordered one way"
    (allCores.all fun a => allCores.all fun b =>
      a == b ||
      (decide ((⟨a⟩ : ShootdownQueueLockId) < ⟨b⟩) ^^
        decide ((⟨b⟩ : ShootdownQueueLockId) < ⟨a⟩)))
  assertBool "the global round lock has exactly one value"
    ((⟨⟩ : ShootdownRoundLockId) == default &&
      default == (⟨⟩ : ShootdownRoundLockId))

-- ----------------------------------------------------------------------------
-- §3.11  SystemState mount (the plan §4.1 "ConcurrencyState" placement)
-- ----------------------------------------------------------------------------

private def runMountChecks : IO Unit := do
  IO.println "-- §3.11 SystemState mount"
  let st : SeLe4n.Model.SystemState := default
  assertBool "the default SystemState mounts the quiescent boot state"
    (st.tlbShootdown == TlbShootdownState.initial)
  assertBool "the mounted state is quiescent (decidable instance)"
    (decide (shootdownQuiescent st.tlbShootdown))
  assertBool "the mounted state satisfies the capacity invariant"
    (decide (pendingBounded st.tlbShootdown))
  assertBool "record updates elsewhere frame the mounted state"
    (({ st with tlb := SeLe4n.Model.TlbState.empty }).tlbShootdown ==
      st.tlbShootdown)

-- ----------------------------------------------------------------------------
-- §3.12  Partial-online (masked) round — PR #838 review P1
-- ----------------------------------------------------------------------------

private def runMaskedRoundChecks : IO Unit := do
  IO.println "-- §3.12 partial-online (masked) round"
  -- smp_max_cores=2 shape: cores 0 (initiator) and 1 online; 2, 3 offline.
  let opened := beginShootdownRoundFor TlbShootdownState.initial core0 [core1]
  assertBool "offline cores are born-acknowledged, online target is not"
    (opened.ackOnCore core0 && !(opened.ackOnCore core1) &&
      opened.ackOnCore core2 && opened.ackOnCore core3)
  assertBool "the masked round genuinely waits on the online target"
    (!(decide (allAcked opened)))
  match enqueueShootdown opened core1 descUnmapPage with
  | none => assertBool "posting to the online target succeeds" false
  | some posted => do
    let final := [core1].foldl completeShootdownOnCore posted
    assertBool "the round completes without cores 2/3 ever acknowledging"
      (decide (allAcked final))
    -- WS-SM SM7.F.3 (PR #854 review): queues return to boot; the
    -- round-generation counter and the acknowledgment vector stay advanced
    -- (both monotone by design — an acknowledgment now names its round).
    -- The masked round's point is that cores 2/3 reach quiescence without
    -- ever acknowledging: they are born at the round's generation.
    assertBool "the completed masked round is quiescent with queues at boot"
      (decide (shootdownQuiescent final) &&
        final == { TlbShootdownState.initial with
                     roundGeneration := final.roundGeneration,
                     shootdownAck := final.shootdownAck })
    assertBool "every core acknowledges the masked round, targets and non-targets alike"
      (allCores.all fun c => final.ackedGenOnCore c == final.roundGeneration)
    assertBool "the completed masked round advanced the generation by one"
      (final.roundGeneration == 1)
  assertBool "smp_enabled=false shape: a no-target round is immediately done"
    (decide (allAcked (beginShootdownRoundFor TlbShootdownState.initial core0 [])))
  assertBool "all-online masked round equals the unmasked round"
    (beginShootdownRoundFor TlbShootdownState.initial core2 allCores ==
      beginShootdownRound TlbShootdownState.initial core2)

-- ============================================================================
-- §4  SM7.B runtime assertions (protocol layer)
-- ============================================================================

-- The concrete page operand of the SM7.B scenarios: unmapping
-- (asid 5, vaddr 0x1000) — matching entry `entryTarget`, non-matching
-- neighbours `entryOtherVaddr` / `entryOtherAsid`.
private def asid5 : SeLe4n.ASID := ⟨5⟩
private def vaddrPage : SeLe4n.VAddr := SeLe4n.VAddr.ofNat 0x1000
private def opUnmapTarget : TlbInvalidation :=
  encodePageInvalidation asid5 vaddrPage

private def entryTarget : SeLe4n.Model.TlbEntry :=
  { asid := asid5, vaddr := vaddrPage,
    paddr := SeLe4n.PAddr.ofNat 0x2000,
    perms := SeLe4n.Model.PagePermissions.readOnly }
private def entryOtherVaddr : SeLe4n.Model.TlbEntry :=
  { asid := asid5, vaddr := SeLe4n.VAddr.ofNat 0x3000,
    paddr := SeLe4n.PAddr.ofNat 0x4000,
    perms := SeLe4n.Model.PagePermissions.readOnly }
private def entryOtherAsid : SeLe4n.Model.TlbEntry :=
  { asid := ⟨7⟩, vaddr := vaddrPage,
    paddr := SeLe4n.PAddr.ofNat 0x5000,
    perms := SeLe4n.Model.PagePermissions.readOnly }

private def seededTlb : SeLe4n.Model.TlbState :=
  { entries := [entryTarget, entryOtherVaddr, entryOtherAsid] }

private def tlbHasEntry (tlb : SeLe4n.Model.TlbState)
    (e : SeLe4n.Model.TlbEntry) : Bool :=
  tlb.entries.any fun x =>
    x.asid == e.asid && x.vaddr == e.vaddr && x.paddr == e.paddr

-- ----------------------------------------------------------------------------
-- §4.1  Invalidation-effect semantics (SM7.B)
-- ----------------------------------------------------------------------------

private def runInvalidationSemanticsChecks : IO Unit := do
  IO.println "-- §4.1 invalidation-effect semantics"
  assertBool "the encoded page operand covers the caller's entry"
    (tlbEntryMatches opUnmapTarget entryTarget)
  assertBool "a different vaddr of the same ASID is not covered"
    (!(tlbEntryMatches opUnmapTarget entryOtherVaddr))
  assertBool "the same vaddr of a different ASID is not covered"
    (!(tlbEntryMatches opUnmapTarget entryOtherAsid))
  assertBool "an ASID operand covers every entry of that ASID only"
    (tlbEntryMatches (encodeAsidInvalidation asid5) entryTarget &&
     tlbEntryMatches (encodeAsidInvalidation asid5) entryOtherVaddr &&
     !(tlbEntryMatches (encodeAsidInvalidation asid5) entryOtherAsid))
  assertBool "a full flush covers everything"
    ([entryTarget, entryOtherVaddr, entryOtherAsid].all
      (tlbEntryMatches .vmalle1 ·))
  let applied := applyTlbInvalidation seededTlb opUnmapTarget
  assertBool "applying the page operand removes exactly the covered entry"
    (!(tlbHasEntry applied entryTarget) &&
     tlbHasEntry applied entryOtherVaddr &&
     tlbHasEntry applied entryOtherAsid)
  assertBool "invalidation is idempotent"
    ((applyTlbInvalidation applied opUnmapTarget).entries.length ==
      applied.entries.length)
  assertBool "a full flush empties the view"
    ((applyTlbInvalidation seededTlb .vmalle1).entries.isEmpty)
  assertBool "a drained-queue fold removes every operand's coverage"
    (let folded := applyTlbInvalidations seededTlb
      [opUnmapTarget, encodeAsidInvalidation ⟨7⟩]
     !(tlbHasEntry folded entryTarget) &&
     tlbHasEntry folded entryOtherVaddr &&
     !(tlbHasEntry folded entryOtherAsid))

-- ----------------------------------------------------------------------------
-- §4.2  Broadcast round: open + post + SGI emission (SM7.B.2)
-- ----------------------------------------------------------------------------

private def runBroadcastChecks : IO Unit := do
  IO.println "-- §4.2 broadcast round (open + post + SGI emission)"
  let st : SeLe4n.Model.SystemState :=
    { (default : SeLe4n.Model.SystemState) with tlb := seededTlb }
  match tlbShootdownBroadcast st core0 (shootdownTargets core0)
      opUnmapTarget with
  | none => assertBool "the broadcast succeeds from quiescence" false
  | some (posted, sgis) => do
    assertBool "one .tlbShootdownReq SGI per target, in order"
      (sgis == [(core1, .tlbShootdownReq), (core2, .tlbShootdownReq),
                (core3, .tlbShootdownReq)])
    assertBool "each target's queue holds exactly the round descriptor"
      ([core1, core2, core3].all fun c =>
        queueIsExactly (posted.tlbShootdown.pendingOnCore c) opUnmapTarget core0)
    assertBool "the initiator's own queue stays empty"
      (posted.tlbShootdown.pendingOnCore core0 == [])
    assertBool "only the initiator is acknowledged after posting"
      (allCores.all fun c =>
        posted.tlbShootdown.ackOnCore c == (c == core0))
    assertBool "the broadcast frames the TLB view and the object store"
      (tlbHasEntry posted.tlb entryTarget &&
        posted.objects.size == st.objects.size)
    assertBool "the posted state satisfies the capacity invariant"
      (decide (pendingBounded posted.tlbShootdown))

-- ----------------------------------------------------------------------------
-- §4.3  The .tlbShootdownReq handler transitions (SM7.B.3)
-- ----------------------------------------------------------------------------

private def runHandlerChecks : IO Unit := do
  IO.println "-- §4.3 .tlbShootdownReq handler transitions"
  let st0 : SeLe4n.Model.SystemState :=
    { (default : SeLe4n.Model.SystemState) with tlb := seededTlb }
  match tlbShootdownBroadcast st0 core0 (shootdownTargets core0)
      opUnmapTarget with
  | none => assertBool "handler-scenario setup broadcast succeeds" false
  | some (posted, _) => do
    -- drain half: queue emptied, nothing else
    let (drainSt, drained) := tlbShootdownDrainOnCore posted core2
    assertBool "the drain half returns the posted descriptor"
      (queueIsExactly drained opUnmapTarget core0)
    assertBool "the drain half does not acknowledge"
      (!(drainSt.tlbShootdown.ackOnCore core2))
    assertBool "the drain half does not touch the TLB view"
      (tlbHasEntry drainSt.tlb entryTarget)
    -- ack half: TLB effect + flag
    let ackSt := tlbShootdownAckOnCore drainSt core2 drained
      posted.tlbShootdown.roundGeneration
    assertBool "the ack half retires the drained operand on the view"
      (!(tlbHasEntry ackSt.tlb entryTarget) &&
        tlbHasEntry ackSt.tlb entryOtherVaddr)
    assertBool "the ack half sets exactly the handling core's flag"
      (ackSt.tlbShootdown.ackOnCore core2 &&
        !(ackSt.tlbShootdown.ackOnCore core1))
    -- composed handler = drain + retire + ack
    let handled := handleTlbShootdownReqOnCore posted core2
    assertBool "the composed handler equals its two halves"
      (handled.tlbShootdown == ackSt.tlbShootdown &&
        handled.tlb.entries.length == ackSt.tlb.entries.length &&
        !(tlbHasEntry handled.tlb entryTarget) &&
        tlbHasEntry handled.tlb entryOtherVaddr)
    assertBool "a duplicate SGI is harmless (handler idempotent)"
      (let again := handleTlbShootdownReqOnCore handled core2
       again.tlbShootdown == handled.tlbShootdown &&
         again.tlb.entries.length == handled.tlb.entries.length)

-- ----------------------------------------------------------------------------
-- §4.4  The full protocol round + Theorem 3.3.1, computed (SM7.B.8)
-- ----------------------------------------------------------------------------

private def runProtocolRoundChecks : IO Unit := do
  IO.println "-- §4.4 full protocol round + Theorem 3.3.1 (computed)"
  let st0 : SeLe4n.Model.SystemState :=
    { (default : SeLe4n.Model.SystemState) with tlb := seededTlb }
  match shootdownRound st0 core1 (shootdownTargets core1)
      opUnmapTarget with
  | none => assertBool "the protocol round completes from quiescence" false
  | some final => do
    assertBool "the completed round is quiescent (queues + acks)"
      (decide (shootdownQuiescent final.tlbShootdown))
    assertBool "the completed round reaches the wait loop's exit"
      (decide (allAcked final.tlbShootdown))
    assertBool "no covered entry survives in the mounted TLB view"
      (!(tlbHasEntry final.tlb entryTarget))
    assertBool "uncovered entries survive the round (selectivity)"
      (tlbHasEntry final.tlb entryOtherVaddr &&
        tlbHasEntry final.tlb entryOtherAsid)
  -- Theorem 3.3.1, computed over the per-core views: seed every core
  -- with the covered entry; after the round no core retains it.
  let views : Vector SeLe4n.Model.TlbState numCores :=
    Vector.replicate numCores seededTlb
  let post := shootdownRoundViews views core1 (shootdownTargets core1)
    opUnmapTarget
  assertBool "3.3.1: no core's view retains the covered entry"
    (allCores.all fun c => !(tlbHasEntry (post.get c) entryTarget))
  assertBool "3.3.1 selectivity: every core keeps uncovered entries"
    (allCores.all fun c =>
      tlbHasEntry (post.get c) entryOtherVaddr &&
      tlbHasEntry (post.get c) entryOtherAsid)
  assertBool "a non-participating core's view is untouched (masked round)"
    (let maskedViews := shootdownRoundViews views core0 [core1] opUnmapTarget
     tlbHasEntry (maskedViews.get core2) entryTarget &&
     !(tlbHasEntry (maskedViews.get core0) entryTarget) &&
     !(tlbHasEntry (maskedViews.get core1) entryTarget))

-- ----------------------------------------------------------------------------
-- §4.5  Coalescing posting + shootdown-aware kernel operations (SM7.B.9/B.10)
-- ----------------------------------------------------------------------------

private def vspaceScenarioState : SeLe4n.Model.SystemState :=
  (BootstrapBuilder.empty.withObject ⟨20⟩
    (.vspaceRoot { asid := asid5, mappings := {} })).build

private def runCallerWrapperChecks : IO Unit := do
  IO.println "-- §4.5 coalescing posting + shootdown-aware operations"
  -- the real unmap pipeline: map, then unmap-with-shootdown
  match vspaceMapPageWithFlush asid5 vaddrPage
      (SeLe4n.PAddr.ofNat 0x2000) .readOnly vspaceScenarioState with
  | .error _ => assertBool "scenario map succeeds" false
  | .ok ((), stMapped) =>
    match vspaceUnmapPageWithShootdown core0 asid5 vaddrPage
        stMapped with
    | .error _ => assertBool "unmap-with-shootdown succeeds" false
    | .ok ((), stUnmapped) => do
      assertBool "the unmap posts the page operand to every other core"
        ([core1, core2, core3].all fun c =>
          queueIsExactly (stUnmapped.tlbShootdown.pendingOnCore c) opUnmapTarget
            core0)
      assertBool "the unmap opens a round waited on every target"
        (allCores.all fun c =>
          stUnmapped.tlbShootdown.ackOnCore c == (c == core0))
      assertBool "the page-table mapping is gone"
        (match vspaceLookup asid5 vaddrPage stUnmapped with
          | .error _ => true
          | .ok _ => false)
  -- error transparency: no shootdown state is touched on failure
  assertBool "unmap of an unbound ASID fails exactly like the flush op"
    (match vspaceUnmapPageWithShootdown core0 ⟨9⟩ vaddrPage
        vspaceScenarioState with
      | .error e => e == SeLe4n.Model.KernelError.asidNotBound
      | .ok _ => false)
  -- ASID allocate (SM7.B.10): fresh allocation is inert; reuse rounds
  assertBool "a fresh ASID allocation posts no round"
    (match asidAllocateWithShootdown core0 AsidPool.initial
        vspaceScenarioState with
      | .ok (result, st') =>
          !result.requiresFlush &&
            allCores.all (fun c => st'.tlbShootdown.pendingOnCore c == [])
      | .error _ => false)
  let reusePool : AsidPool :=
    { AsidPool.initial with freeList := [⟨5⟩], activeCount := 0 }
  assertBool "a reused ASID allocation posts the .aside1 round"
    (match asidAllocateWithShootdown core2 reusePool
        vspaceScenarioState with
      | .ok (result, st') =>
          result.requiresFlush &&
            [core0, core1, core3].all (fun c =>
              queueHasOp (st'.tlbShootdown.pendingOnCore c)
                (encodeAsidInvalidation ⟨5⟩) core2)
      | .error _ => false)
  -- capacity overflow: 17 rounds without a runtime catch-up coalesce
  let overflow := (List.range 17).foldl
    (fun s i => tlbShootdownBroadcastCoalescing s core0
      (shootdownTargets core0)
      (encodePageInvalidation ⟨5⟩ (SeLe4n.VAddr.ofNat (4096 * (i + 1)))))
    vspaceScenarioState
  assertBool "17 uncaught rounds coalesce to a bounded full flush"
    (decide (pendingBounded overflow.tlbShootdown) &&
      [core1, core2, core3].all (fun c =>
        (overflow.tlbShootdown.pendingOnCore c).any
          (fun d => d.op == TlbInvalidation.vmalle1)))

-- ----------------------------------------------------------------------------
-- §4.6  Wait loop + timeout verdicts (SM7.B.5/B.6)
-- ----------------------------------------------------------------------------

private def runWaitLoopChecks : IO Unit := do
  IO.println "-- §4.6 wait loop + timeout verdicts"
  let opened := beginShootdownRound TlbShootdownState.initial core0
  -- poll trace: one more target acks per poll index
  let states : Nat → TlbShootdownState := fun n =>
    (allCores.take n).foldl
      (fun s x => acknowledgeShootdown s x opened.roundGeneration) opened
  match waitAllAckedBounded 10 states with
  | none => assertBool "the wait observes the completing round" false
  | some n => do
    assertBool "the wait exits at a genuinely all-acked poll"
      (decide (allAcked (states n)))
    assertBool "the wait exits at the first all-acked poll"
      (n == 4 && !(decide (allAcked (states 3))))
  assertBool "a never-acked round is a genuine timeout (none)"
    ((waitAllAckedBounded 6 (fun _ => opened)).isNone)
  assertBool "an already-quiescent state satisfies the wait at once"
    (waitAllAckedBounded 3 (fun _ => TlbShootdownState.initial) == some 0)

-- ----------------------------------------------------------------------------
-- §4.7  The round's cross-domain lock-set (SM7.B.7)
-- ----------------------------------------------------------------------------

private def runProtocolLockSetChecks : IO Unit := do
  IO.println "-- §4.7 protocol lock-set"
  let rootLock : SeLe4n.Kernel.Concurrency.LockId :=
    { kind := .vspaceRoot, objId := ⟨20⟩ }
  let seq := lockSet_tlbShootdown rootLock core1
  assertBool "the acquisition sequence is strictly ascending"
    (decide (List.Pairwise (· < ·) seq))
  assertBool "the acquisition sequence is duplicate-free"
    (decide seq.Nodup)
  assertBool "object lock first, round lock second, queues after"
    (seq.head? == some (.object rootLock) &&
      seq[1]? == some (.round ⟨⟩))
  assertBool "one queue lock per non-initiator core"
    (seq.length == 2 + (numCores - 1))
  assertBool "every changed queue of a live commit is in the footprint"
    ([core0, core2, core3].all fun c =>
      seq.contains (.queue ⟨c⟩))
  assertBool "cross-domain edges: object < round < queue (decidable)"
    (decide ((TlbShootdownLockId.object rootLock) <
        (TlbShootdownLockId.round ⟨⟩)) &&
      decide ((TlbShootdownLockId.round ⟨⟩) <
        (TlbShootdownLockId.queue ⟨core0⟩)))

-- ----------------------------------------------------------------------------
-- §4.8  Runtime-seam diff recovery + live-entry constants (SM7.B)
-- ----------------------------------------------------------------------------

private def runDiffRecoveryChecks : IO Unit := do
  IO.println "-- §4.8 runtime-seam diff recovery + live-entry constants"
  let pre : SeLe4n.Model.SystemState := default
  assertBool "an untouched commit pokes nobody"
    (shootdownChangedTargets pre pre == [])
  let post := tlbShootdownBroadcastCoalescing pre core0
    (shootdownTargets core0) opUnmapTarget
  assertBool "a posting commit's changed targets are the round targets"
    (shootdownChangedTargets pre post == [core1, core2, core3])
  assertBool "the posted operands dedup to the round's operand"
    (shootdownPostedOps pre post == [opUnmapTarget])
  assertBool "the live entry issues TLBIs in the platform sharing domain"
    (SeLe4n.Kernel.shootdownSharingDomain == .inner)
  assertBool "the wait budget matches the pinned HAL constant"
    (shootdownWaitTimeoutTicks == 540000)

-- ----------------------------------------------------------------------------
-- §4.9  Completion cut: bundle carriage, commutativity, capstones,
--        remap detection, operand collapse, round-lock model (SM7.B)
-- ----------------------------------------------------------------------------

/-- The live `.vspaceRoot` a retype destroys — carrying `asid5`. -/
private def rtVsp : SeLe4n.ObjId := ⟨891⟩

/-- The non-VSpace retype target (the negative control: posts nothing). -/
private def rtEp : SeLe4n.ObjId := ⟨892⟩

/-- The CNode holding the two retype capabilities. -/
private def rtCn : SeLe4n.ObjId := ⟨890⟩

/-- The retype-capable state driven by §4.9's CSpaceAddr sweep-closure check and
by §8's multi-round-window group, so both exercise the same objects through the
same production entry point (`lifecycleRetypeWithCleanupShootdown{,PerCore}`).
The retype path's type-lockstep gate reads lifecycle metadata, hence the
`withLifecycleObjectType` rows. -/
private def rtMultiState : SeLe4n.Model.SystemState :=
  let capVsp : Capability :=
    { target := .object rtVsp, rights := AccessRightSet.ofList [.retype] }
  let capEp : Capability :=
    { target := .object rtEp, rights := AccessRightSet.ofList [.retype] }
  (BootstrapBuilder.empty
    |>.withObject rtVsp (.vspaceRoot { asid := asid5, mappings := {} })
    |>.withObject rtEp (.endpoint {})
    |>.withObject rtCn (.cnode
        { depth := 4, guardWidth := 0, guardValue := 0, radixWidth := 4,
          slots := SeLe4n.UniqueSlotMap.ofListWF
            [(SeLe4n.Slot.ofNat 0, capVsp), (SeLe4n.Slot.ofNat 1, capEp)] })
    |>.withLifecycleObjectType rtVsp .vspaceRoot
    |>.withLifecycleObjectType rtEp .endpoint
    |>.withLifecycleObjectType rtCn .cnode
    |>.buildChecked)

private def runCompletionCutChecks : IO Unit := do
  IO.println "-- §4.9 completion cut: bundle carriage + commutativity + capstones"
  let quiescent : SeLe4n.Model.SystemState :=
    { (default : SeLe4n.Model.SystemState) with tlb := seededTlb }
  -- (a) the 12th proofLayerInvariantBundle conjunct at boot
  assertBool "the boot state satisfies the bundle's shootdown capacity conjunct"
    (decide (pendingBounded (default : SeLe4n.Model.SystemState).tlbShootdown))
  -- (b) positive diff characterization + coalescing-round capstones, computed
  let posted := tlbShootdownBroadcastCoalescing quiescent core0
    (shootdownTargets core0) opUnmapTarget
  assertBool "the coalescing diff is exactly the round's target set"
    (shootdownChangedTargets quiescent posted == shootdownTargets core0)
  let final := (shootdownTargets core0).foldl handleTlbShootdownReqOnCore
    (tlbShootdownLocal posted opUnmapTarget)
  assertBool "the live coalescing round restores quiescence"
    (decide (shootdownQuiescent final.tlbShootdown))
  assertBool "the live coalescing round reaches allAcked"
    (decide (allAcked final.tlbShootdown))
  assertBool "the completed round preserves the capacity conjunct"
    (decide (pendingBounded final.tlbShootdown))
  assertBool "the completed round removed the unmapped translation"
    (!(tlbHasEntry final.tlb entryTarget))
  -- (c) handler commutativity, computed on the posted state
  let ab := handleTlbShootdownReqOnCore
    (handleTlbShootdownReqOnCore posted core1) core2
  let ba := handleTlbShootdownReqOnCore
    (handleTlbShootdownReqOnCore posted core2) core1
  assertBool "distinct-core handler steps commute (shootdown projection)"
    (decide (ab.tlbShootdown = ba.tlbShootdown))
  assertBool "distinct-core handler steps commute (TLB view)"
    (ab.tlb.entries.length == ba.tlb.entries.length &&
     ab.tlb.entries.all (tlbHasEntry ba.tlb) &&
     ba.tlb.entries.all (tlbHasEntry ab.tlb))
  -- (d) the vmalle1-dominance operand collapse
  assertBool "a vmalle1-free operand list is returned unchanged"
    (collapseShootdownOps [opUnmapTarget] == [opUnmapTarget])
  assertBool "a vmalle1-carrying list collapses to the single full flush"
    (collapseShootdownOps [opUnmapTarget, .vmalle1] == [.vmalle1])
  assertBool "the collapse is effect-exact on the seeded view"
    (let collapsed := applyTlbInvalidations seededTlb
       (collapseShootdownOps [opUnmapTarget, .vmalle1])
     let full := applyTlbInvalidations seededTlb [opUnmapTarget, .vmalle1]
     collapsed.entries.length == full.entries.length &&
       collapsed.entries.isEmpty)
  -- (e) round-lock CAS model walks
  assertBool "the CAS acquires a free round lock" (roundLockTryAcquire false).1
  assertBool "a held round lock rejects the CAS" (!(roundLockTryAcquire true).1)
  assertBool "two consecutive CAS attempts never both succeed"
    (!((roundLockTryAcquire false).1 &&
       (roundLockTryAcquire (roundLockTryAcquire false).2).1))
  assertBool "a release re-enables acquisition"
    (roundLockTryAcquire (roundLockRelease true)).1
  -- (f) the bounded wait returns the least all-acked poll index
  let states : Nat → TlbShootdownState := fun n =>
    if n < 2 then beginShootdownRound TlbShootdownState.initial core0
    else TlbShootdownState.initial
  assertBool "the bounded wait returns the least all-acked poll index"
    (waitAllAckedBounded 5 states == some 2)
  -- (g) typed-flush bridge probe: encoded survivors ⊆ typed survivors
  assertBool "encoded-operand survivors also survive the typed flush"
    ((applyTlbInvalidation seededTlb opUnmapTarget).entries.all fun e =>
      tlbHasEntry (adapterFlushTlbByVAddr seededTlb asid5 vaddrPage) e)
  -- (h) remap-only map rounds: a fresh map is inert, a remap posts
  assertBool "a fresh map posts no round (no prior translation)"
    (!(vspaceHasTranslation vspaceScenarioState asid5 vaddrPage) &&
     (match vspaceMapPageCheckedWithShootdownFromState core0 asid5 vaddrPage
        (SeLe4n.PAddr.ofNat 0x2000) .readOnly vspaceScenarioState with
      | .ok ((), st') => allCores.all fun c =>
          st'.tlbShootdown.pendingOnCore c == []
      | .error _ => false))
  -- The model's remap discipline: a one-step replace is a
  -- .mappingConflict (`vspaceMapPageCheckedWithFlushFromState_ok_fresh`),
  -- so the round rides the unmap of the unmap-then-map sequence and the
  -- re-map is fresh again (`…_never_posts`).
  assertBool "a one-step replace of a live translation fails with mappingConflict"
    (match vspaceMapPageWithFlush asid5 vaddrPage (SeLe4n.PAddr.ofNat 0x2000)
        .readOnly vspaceScenarioState with
     | .error _ => false
     | .ok ((), stMapped) =>
        vspaceHasTranslation stMapped asid5 vaddrPage &&
        (match vspaceMapPageCheckedWithShootdownFromState core1 asid5 vaddrPage
            (SeLe4n.PAddr.ofNat 0x6000) .readOnly stMapped with
         | .error .mappingConflict => true | _ => false))
  assertBool "unmap-then-map: the round rides the unmap; the re-map posts nothing new"
    (match vspaceMapPageWithFlush asid5 vaddrPage (SeLe4n.PAddr.ofNat 0x2000)
        .readOnly vspaceScenarioState with
     | .error _ => false
     | .ok ((), stMapped) =>
        match vspaceUnmapPageWithShootdown core0 asid5 vaddrPage stMapped with
        | .error _ => false
        | .ok ((), stUnmapped) =>
            ([core1, core2, core3].all fun c =>
              queueHasOp (stUnmapped.tlbShootdown.pendingOnCore c) opUnmapTarget
                core0) &&
            (match vspaceMapPageCheckedWithShootdownFromState core0 asid5
                vaddrPage (SeLe4n.PAddr.ofNat 0x6000) .readOnly stUnmapped with
             | .ok ((), stRemapped) =>
                 decide (stRemapped.tlbShootdown = stUnmapped.tlbShootdown) &&
                 decide (pendingBounded stRemapped.tlbShootdown)
             | .error _ => false))
  -- (i) the CSpaceAddr retype-with-shootdown sibling (sweep closure).  The
  -- state is `rtMultiState` (top level, §8) so this group and §8's
  -- multi-round-window group drive the same objects through the same entry.
  let rtSt := rtMultiState
  assertBool "the CSpaceAddr retype of a live vspaceRoot posts the .aside1 round"
    (match SeLe4n.Kernel.lifecycleRetypeWithCleanupShootdown core0
        { cnode := rtCn, slot := SeLe4n.Slot.ofNat 0 } rtVsp
        (.endpoint {}) rtSt with
     | .ok ((), st') =>
         [core1, core2, core3].all (fun c =>
           queueHasOp (st'.tlbShootdown.pendingOnCore c)
             (encodeAsidInvalidation asid5) core0) &&
         decide (pendingBounded st'.tlbShootdown)
     | .error _ => false)
  let rtNewNtfn : SeLe4n.Model.KernelObject :=
    .notification
      { state := .idle, waitingThreads := SeLe4n.NoDupList.empty,
        pendingBadge := none }
  assertBool "a non-vspaceRoot CSpaceAddr retype posts nothing"
    (match SeLe4n.Kernel.lifecycleRetypeWithCleanupShootdown core0
        { cnode := rtCn, slot := SeLe4n.Slot.ofNat 1 } rtEp rtNewNtfn rtSt with
     | .ok ((), st') => allCores.all fun c =>
         st'.tlbShootdown.pendingOnCore c == []
     | .error _ => false)

-- ----------------------------------------------------------------------------
-- §4.10  Live dispatch: `.vspaceUnmap` through the full public entry
--         (CSpace resolution + authority gate + shootdown posting)
-- ----------------------------------------------------------------------------

private def udVsp : SeLe4n.ObjId := ⟨881⟩
private def udCn : SeLe4n.ObjId := ⟨880⟩
private def udCaller : SeLe4n.ThreadId := ⟨882⟩
private def udCap : Capability :=
  { target := .object udVsp, rights := AccessRightSet.ofList [.write] }
private def udCapRO : Capability :=
  { target := .object udVsp, rights := AccessRightSet.ofList [.read] }

/-- A `.vspaceUnmap` decode: primary cap at CPtr 0; msgRegs carry
(asid 5, vaddr 0x1000) — the suite's scenario operand. -/
private def udDecoded : SyscallDecodeResult :=
  { capAddr := SeLe4n.CPtr.ofNat 0,
    msgInfo := { length := 2, extraCaps := 0, label := 0 },
    syscallId := .vspaceUnmap,
    msgRegs := #[SeLe4n.RegValue.ofNat 5, SeLe4n.RegValue.ofNat 0x1000] }

private def udState (slots : List (SeLe4n.Slot × Capability)) :
    SeLe4n.Model.SystemState :=
  (BootstrapBuilder.empty
    |>.withObject udVsp (.vspaceRoot { asid := asid5, mappings := {} })
    |>.withObject udCn (.cnode
        { depth := 4, guardWidth := 0, guardValue := 0, radixWidth := 4,
          slots := SeLe4n.UniqueSlotMap.ofListWF slots })
    |>.withObject udCaller.toObjId (.tcb
        { tid := udCaller, priority := ⟨40⟩, domain := ⟨0⟩,
          cspaceRoot := udCn, vspaceRoot := udVsp,
          ipcBuffer := SeLe4n.VAddr.ofNat 4096, ipcState := .ready })
    |>.withRunnable [udCaller]
    |>.build)

/-- Map the scenario page, then dispatch the caller's `.vspaceUnmap`
through the full public entry. -/
private def udDispatch (slots : List (SeLe4n.Slot × Capability)) :
    Except KernelError (Unit × SeLe4n.Model.SystemState) :=
  match vspaceMapPageWithFlush asid5 vaddrPage (SeLe4n.PAddr.ofNat 0x2000)
      .readOnly (udState slots) with
  | .error e => .error e
  | .ok ((), stMapped) =>
      SeLe4n.Kernel.dispatchSyscall udDecoded udCaller stMapped

private def runLiveDispatchChecks : IO Unit := do
  IO.println "-- §4.10 live dispatch (.vspaceUnmap: CSpace lookup + authority + round)"
  -- AUTHORIZED: a `.write` cap at slot 0 → the unmap runs and posts.
  match udDispatch [(SeLe4n.Slot.ofNat 0, udCap)] with
  | .error _ => assertBool "authorized live .vspaceUnmap succeeds" false
  | .ok ((), st') => do
    assertBool "the live unmap removes the translation"
      (match vspaceLookup asid5 vaddrPage st' with
        | .error _ => true
        | .ok _ => false)
    assertBool "the live unmap posts the page operand to every other core"
      ([core1, core2, core3].all fun c =>
        queueHasOp (st'.tlbShootdown.pendingOnCore c) opUnmapTarget core0)
    assertBool "the live unmap keeps the initiator's queue empty"
      (st'.tlbShootdown.pendingOnCore core0 == [])
    assertBool "the live unmap preserves the capacity conjunct"
      (decide (pendingBounded st'.tlbShootdown))
  -- NO CAP: empty slot 0 → the CSpace lookup fails closed.
  assertBool "a live .vspaceUnmap with no cap fails with invalidCapability"
    (match udDispatch [] with
      | .error .invalidCapability => true | _ => false)
  -- READ-ONLY cap: the authority gate rejects (.vspaceUnmap needs .write).
  assertBool "a live .vspaceUnmap with a read-only cap fails with illegalAuthority"
    (match udDispatch [(SeLe4n.Slot.ofNat 0, udCapRO)] with
      | .error .illegalAuthority => true | _ => false)

-- ----------------------------------------------------------------------------
-- §4.11  Debt-closure cut: per-descriptor mailbox operand encoding
--        conformance + withLockSet pendingBounded carriage
-- ----------------------------------------------------------------------------

private def runDebtClosureChecks : IO Unit := do
  IO.println "-- §4.11 debt closure: operand-encoding conformance + withLockSet carriage"
  -- The Lean half of the SM7.B debt-(1) op-tag pairing: each operand
  -- transmits the (op_tag, asid, vaddr) triple the Rust
  -- `decode_tlb_invalidation` round-trips.  Pins the encoding the live
  -- `publishShootdownOps` sends per descriptor.
  assertBool "vmalle1 encodes to (op_tag 0, asid 0, vaddr 0)"
    (TlbInvalidation.vmalle1.toOpTag == 0 &&
     TlbInvalidation.vmalle1.toAsid == 0 &&
     TlbInvalidation.vmalle1.toVaddr == 0)
  assertBool "the page unmap operand encodes to (op_tag 1, asid 5, vaddr 0x1000)"
    (opUnmapTarget.toOpTag == 1 &&
     opUnmapTarget.toAsid == UInt16.ofNat 5 &&
     opUnmapTarget.toVaddr == UInt64.ofNat 0x1000)
  assertBool "the ASID-retire operand encodes to (op_tag 2, asid 5, vaddr 0)"
    ((encodeAsidInvalidation asid5).toOpTag == 2 &&
     (encodeAsidInvalidation asid5).toAsid == UInt16.ofNat 5 &&
     (encodeAsidInvalidation asid5).toVaddr == 0)
  assertBool "every operand's op_tag is in the Rust decode's [0,4) range"
    ([TlbInvalidation.vmalle1, opUnmapTarget, encodeAsidInvalidation asid5,
      TlbInvalidation.vale1 (UInt16.ofNat 5) (UInt64.ofNat 0x1000)].all
      fun op => op.toOpTag.toNat < 4)
  -- withLockSet pendingBounded carriage (debt (5) slice): a 2PL bracket
  -- whose guarded action frames the shootdown state preserves the
  -- capacity conjunct.  Witness on a built state with the identity action.
  let lockSt : SeLe4n.Model.SystemState :=
    { (default : SeLe4n.Model.SystemState) with tlb := seededTlb }
  assertBool "withLockSet over a shootdown-framing action preserves pendingBounded"
    (decide (SeLe4n.Kernel.Architecture.pendingBounded
      ((SeLe4n.Kernel.Concurrency.withLockSet SeLe4n.Kernel.Concurrency.LockSet.empty
        core0 (fun s => (s, ())) lockSt).1).tlbShootdown))

-- ----------------------------------------------------------------------------
-- §5.1  Per-core TLB model: accessors + local ops (SM7.C.1-C.3)
-- ----------------------------------------------------------------------------

/-- A 4-core state whose every core caches the seeded translations —
`Vector.replicate` puts `seededTlb` on all cores, the pre-state for the
cross-core scenarios. -/
private def perCoreSeeded : SeLe4n.Model.SystemState :=
  { (default : SeLe4n.Model.SystemState) with
      perCoreTlb := _root_.Vector.replicate numCores seededTlb }

private def runPerCoreTlbLocalChecks : IO Unit := do
  IO.println "-- §5.1 per-core TLB model: accessors + local ops"
  -- SM7.C.1: every core's boot TLB view is empty.
  assertBool "every core's boot TLB view is empty"
    (allCores.all fun c =>
      (tlbOnCore (default : SeLe4n.Model.SystemState) c).entries.isEmpty)
  -- SM7.C.1: the store/load algebra writes exactly the target core.
  let stSet := setTlbOnCore (default : SeLe4n.Model.SystemState) core1 seededTlb
  assertBool "setTlbOnCore writes exactly the target core's view"
    (tlbHasEntry (tlbOnCore stSet core1) entryTarget &&
     (tlbOnCore stSet core2).entries.isEmpty)
  -- SM7.C.2: the hardware translation walker fills only one core.
  let stIns := tlbInsertOnCore (default : SeLe4n.Model.SystemState) core0 entryTarget
  assertBool "tlbInsertOnCore fills only the target core's view"
    (tlbHasEntry (tlbOnCore stIns core0) entryTarget &&
     (tlbOnCore stIns core1).entries.isEmpty)
  -- SM7.C.3: a local invalidation reaches EXACTLY this core — the precise
  -- SMP hazard the cross-core broadcast (§5.2) closes.
  let stInv := tlbInvalidateOnCore perCoreSeeded core0 opUnmapTarget
  assertBool "a local invalidation removes the target from THIS core"
    (!(tlbHasEntry (tlbOnCore stInv core0) entryTarget))
  assertBool "a local invalidation leaves the STALE entry on OTHER cores (the SMP hazard)"
    ([core1, core2, core3].all fun c => tlbHasEntry (tlbOnCore stInv c) entryTarget)
  assertBool "a local invalidation keeps the non-matching entries on this core"
    (tlbHasEntry (tlbOnCore stInv core0) entryOtherVaddr &&
     tlbHasEntry (tlbOnCore stInv core0) entryOtherAsid)

-- ----------------------------------------------------------------------------
-- §5.2  Per-core TLB model: cross-core broadcast + Theorem 3.3.1 (SM7.C.4-C.7)
-- ----------------------------------------------------------------------------

private def runPerCoreTlbBroadcastChecks : IO Unit := do
  IO.println "-- §5.2 per-core TLB model: cross-core invalidation + Theorem 3.3.1"
  match tlbInvalidateOnAllCores perCoreSeeded core0 (shootdownTargets core0)
      opUnmapTarget with
  | none =>
    assertBool "cross-core invalidation from a quiescent state succeeds" false
  | some (st', sgis) => do
    -- SM7.C.6 (Theorem 3.3.1, mounted): no core retains the covered entry.
    assertBool "after a covering broadcast NO core retains the unmapped translation"
      (allCores.all fun c => !(tlbHasEntry (tlbOnCore st' c) entryTarget))
    -- selectivity: the non-matching entries survive on every core.
    assertBool "the broadcast preserves the non-matching entries on every core"
      (allCores.all fun c =>
        tlbHasEntry (tlbOnCore st' c) entryOtherVaddr &&
        tlbHasEntry (tlbOnCore st' c) entryOtherAsid)
    -- SM7.C.4: one .tlbShootdownReq SGI per target, in order.
    assertBool "the broadcast emits one .tlbShootdownReq SGI per target"
      (sgis == [(core1, .tlbShootdownReq), (core2, .tlbShootdownReq),
                (core3, .tlbShootdownReq)])
    -- SM7.C.4: the round posts to the SM7.A shootdown state (the wiring
    -- that makes perCoreTlb a genuine consumer of tlbShootdown).
    assertBool "the broadcast posts the operand to every target's shootdown queue"
      ([core1, core2, core3].all fun c =>
        queueHasOp (st'.tlbShootdown.pendingOnCore c) opUnmapTarget core0)
    assertBool "the broadcast keeps the initiator's shootdown queue empty"
      (st'.tlbShootdown.pendingOnCore core0 == [])
    -- SM7.B/C: the shootdown capacity conjunct (12th) is preserved.
    assertBool "the broadcast preserves the shootdown capacity conjunct"
      (decide (pendingBounded st'.tlbShootdown))
    -- SM7.C.4/C.7: the broadcast frames the page-table subsystem
    -- (objects unchanged ⇒ resolveAsidRoot preserved).
    assertBool "the broadcast frames the object store"
      (st'.objects.size == perCoreSeeded.objects.size)
  -- SM7.C.4: from the quiescent boot state the broadcast always succeeds.
  assertBool "cross-core invalidation from the quiescent boot state succeeds"
    ((tlbInvalidateOnAllCores perCoreSeeded core0 (shootdownTargets core0)
      opUnmapTarget).isSome)

-- ----------------------------------------------------------------------------
-- §5.3  Per-core TLB: the operational round (the live drain), the total
--        coalescing form, and the runtime-decidable consistency checker
-- ----------------------------------------------------------------------------

private def runPerCoreTlbOperationalChecks : IO Unit := do
  IO.println "-- §5.3 per-core TLB: operational round + coalescing + decidable checker"
  -- SM7.C operational Theorem 3.3.1: the REAL per-core drain — the round the
  -- live `completeShootdownRounds` seam runs (`handleTlbShootdownReqOnCorePerCore`
  -- per target + the initiator local step) — removes the covered entry from
  -- every core's view, and the non-matching entries survive.
  match shootdownRoundPerCore perCoreSeeded core0 (shootdownTargets core0)
      opUnmapTarget with
  | none => assertBool "the operational per-core round succeeds from quiescence" false
  | some final => do
    assertBool "the operational per-core drain removes the covered entry from EVERY core"
      (allCores.all fun c => !(tlbHasEntry (tlbOnCore final c) entryTarget))
    assertBool "the operational drain preserves the non-matching entries on every core"
      (allCores.all fun c =>
        tlbHasEntry (tlbOnCore final c) entryOtherVaddr &&
        tlbHasEntry (tlbOnCore final c) entryOtherAsid)
    -- The bridge (A4): the per-core round's `tlb` / `tlbShootdown` effect
    -- equals the SM7.B single-view `shootdownRound`'s — trace-safety.
    match shootdownRound perCoreSeeded core0 (shootdownTargets core0)
        opUnmapTarget with
    | some singleFinal => do
      assertBool "the per-core round's tlb effect equals the single-view round's (bridge)"
        (final.tlb.entries.length == singleFinal.tlb.entries.length &&
         final.tlb.entries.all (tlbHasEntry singleFinal.tlb) &&
         singleFinal.tlb.entries.all (tlbHasEntry final.tlb))
      assertBool "the per-core round's shootdown state equals the single-view round's"
        (decide (final.tlbShootdown = singleFinal.tlbShootdown))
    | none => assertBool "the single-view round also succeeds" false
  -- SM7.C.4 total form: never fails, agrees with the strict form, and drains
  -- every core's view.
  let coRound := tlbInvalidateOnAllCoresCoalescing perCoreSeeded core0
    (shootdownTargets core0) opUnmapTarget
  assertBool "the coalescing form removes the covered entry from every core"
    (allCores.all fun c => !(tlbHasEntry (tlbOnCore coRound.1 c) entryTarget))
  assertBool "the coalescing form emits one .tlbShootdownReq per target"
    (coRound.2 == [(core1, .tlbShootdownReq), (core2, .tlbShootdownReq),
                   (core3, .tlbShootdownReq)])
  -- SM7.C.5 runtime-decidable checker (the 13th bundle conjunct made
  -- executable, as the 12th `pendingBounded` is).
  assertBool "the runtime checker confirms per-core consistency at boot"
    (tlbInvalidationConsistentCheck_perCore (default : SeLe4n.Model.SystemState))
  assertBool "the decidable per-core invariant instance agrees at boot"
    (decide (tlbInvalidationConsistent_perCore (default : SeLe4n.Model.SystemState)))
  -- SM7.C.5 (SM7.F, PR #844 review-3): the conjunction form of
  -- `tlbEntryConsistent` rejects an unresolvable-ASID entry.  A RAW insert of an
  -- entry whose ASID does not resolve on the (VSpaceRoot-free) boot state is a
  -- stale / use-after-retype entry, so the checker now flags it RED — the old
  -- implication form accepted it *vacuously*.  (A genuine walker fill,
  -- `tlbFillOnCore` in §5.4, never installs such an entry: the walk only caches
  -- a translation it actually resolved through the page tables.)
  assertBool "a raw insert of an unresolvable-ASID entry FAILS the checker (SM7.F: no vacuity)"
    (!(tlbInvalidationConsistentCheck_perCore
      (tlbInsertOnCore (default : SeLe4n.Model.SystemState) core1 entryTarget)))
  -- PR #844 P1: the live catch-up (`shootdownCatchUpPerCore`, what
  -- `completeShootdownRounds` runs) drains the INITIATOR's own view too — the
  -- `tlbiForSharing` broadcast reaches the issuing PE, and `shootdownTargets`
  -- excludes it.  Seed a posted round, then run the catch-up.
  match tlbShootdownBroadcast perCoreSeeded core0 (shootdownTargets core0)
      opUnmapTarget with
  | none => assertBool "the round posts from the quiescent seed" false
  | some (posted, _) => do
    -- Sanity: the initiator's pre-catch-up view still HOLDS the target entry
    -- (the broadcast only posts to `tlbShootdown`; it does not touch views),
    -- so the drain below is non-vacuous.
    assertBool "the initiator still holds the stale entry before the catch-up"
      (tlbHasEntry (tlbOnCore posted core0) entryTarget)
    let caught := shootdownCatchUpPerCore posted core0 [opUnmapTarget]
    assertBool "the live catch-up retires the operand on the INITIATOR's own view (PR #844 P1)"
      (!(tlbHasEntry (tlbOnCore caught core0) entryTarget))
    assertBool "the live catch-up also drains every remote target's view"
      ([core1, core2, core3].all fun c => !(tlbHasEntry (tlbOnCore caught c) entryTarget))
    -- Trace-safety (computed): the catch-up's `tlbShootdown` effect equals the
    -- SM7.B single-view target fold's — the initiator drain is perCoreTlb-only.
    assertBool "the catch-up is trace-safe (shootdown state = single-view target fold)"
      (decide (caught.tlbShootdown =
        ((shootdownTargets core0).foldl handleTlbShootdownReqOnCore posted).tlbShootdown))
    -- PR #844 P2: the operative cross-subsystem capstone on the real round.
    match shootdownRoundPerCore perCoreSeeded core0 (shootdownTargets core0)
        opUnmapTarget with
    | none => assertBool "the operative round succeeds" false
    | some final =>
      assertBool "the operative round removes the covered entry from every core (capstone)"
        (allCores.all fun c => !(tlbHasEntry (tlbOnCore final c) entryTarget))

-- ----------------------------------------------------------------------------
-- §5.4  SM7.F.1 — the translation-walk fill seam (perCoreTlb made fillable)
-- ----------------------------------------------------------------------------

private def runPerCoreTlbFillChecks : IO Unit := do
  IO.println "-- §5.4 per-core TLB: translation-walk fill (SM7.F.1)"
  -- Map (asid5, vaddrPage) into a real page-table-backed state, then walk-fill it.
  match vspaceMapPageWithFlush asid5 vaddrPage (SeLe4n.PAddr.ofNat 0x2000)
      .readOnly (udState []) with
  | .error _ => assertBool "the fill scenario maps the page" false
  | .ok ((), stMapped) => do
    -- Before the walk, core0's view is empty (the live model only drained until SM7.F.1).
    assertBool "core0's view is empty before the translation-walk fill"
      ((tlbOnCore stMapped core0).entries.isEmpty)
    let stFilled := tlbFillOnCore stMapped core0 asid5 vaddrPage
    -- The walk resolved the live mapping and cached it — perCoreTlb is now genuinely
    -- NON-empty on a real page-table-backed state (the SM7.F Comment-2 ask).
    assertBool "the translation-walk fill caches the mapped translation on core0 (SM7.F.1)"
      ((tlbOnCore stFilled core0).entries.any (fun e => e.asid == asid5 && e.vaddr == vaddrPage))
    -- Locality: a walk is a this-core event (the SMP asymmetry).
    assertBool "the fill is local — other cores' views stay empty"
      ([core1, core2, core3].all fun c => (tlbOnCore stFilled c).entries.isEmpty)
    -- Consistency-safety: the cached entry matches the page tables by construction.
    assertBool "the fill keeps the per-core consistency checker green (consistent by construction)"
      (tlbInvalidationConsistentCheck_perCore stFilled)
    -- An unmapped address caches nothing (the walk misses → no-op): core0's
    -- view stays empty, whereas the mapped walk above populated it.
    assertBool "a walk of an unmapped address caches nothing (no-op)"
      ((tlbOnCore (tlbFillOnCore stMapped core0 asid5 (SeLe4n.VAddr.ofNat 0xDEAD000))
        core0).entries.isEmpty)

-- ----------------------------------------------------------------------------
-- §5.5  SM7.F.2 — the pending-aware (honest) invariant: a stale cached entry
--        is admissible iff a shootdown is already pending to retire it.
-- ----------------------------------------------------------------------------

private def runPerCoreTlbPendingAwareChecks : IO Unit := do
  IO.println "-- §5.5 per-core TLB: pending-aware invariant (SM7.F.2)"
  match vspaceMapPageWithFlush asid5 vaddrPage (SeLe4n.PAddr.ofNat 0x2000)
      .readOnly (udState []) with
  | .error _ => assertBool "the scenario maps the page" false
  | .ok ((), stMapped) => do
    -- Fill core0 with the (consistent) translation, then UNMAP the page from
    -- the page tables — core0's cached entry is now genuinely STALE.
    let stFilled := tlbFillOnCore stMapped core0 asid5 vaddrPage
    match vspaceUnmapPageWithFlush asid5 vaddrPage stFilled with
    | .error _ => assertBool "the scenario unmaps the page" false
    | .ok ((), stStale) => do
      -- No shootdown pending ⇒ the stale entry is INADMISSIBLE (the honest
      -- invariant rejects it; the old unconditional form would have too, but
      -- only because it never allowed a real stale entry at all).
      assertBool "a stale cached entry with NO pending shootdown FAILS the check (F.2)"
        (!(tlbInvalidationConsistentCheck_perCore stStale))
      -- Post a shootdown descriptor covering the page on core0 ⇒ the SAME
      -- stale entry becomes ADMISSIBLE (the pending disjunct) — the exact
      -- behaviour the honest invariant adds over the unconditional one.
      match enqueueShootdown stStale.tlbShootdown core0 descUnmapPage with
      | none => assertBool "the covering descriptor enqueues" false
      | some sd =>
        let stPending := { stStale with tlbShootdown := sd }
        assertBool "the same stale entry becomes admissible once a covering shootdown is pending (F.2)"
          (tlbInvalidationConsistentCheck_perCore stPending)

-- ----------------------------------------------------------------------------
-- §5.6  SM7.F.2a — the initiator-atomic unmap: the initiator's own view is
--        retired atomically with the round posting (PR #844 review-2 P2).
-- ----------------------------------------------------------------------------

private def runPerCoreTlbInitiatorAtomicChecks : IO Unit := do
  IO.println "-- §5.6 per-core TLB: initiator-atomic unmap (SM7.F.2a, PR #844 P2)"
  match vspaceMapPageWithFlush asid5 vaddrPage (SeLe4n.PAddr.ofNat 0x2000)
      .readOnly (udState []) with
  | .error _ => assertBool "the scenario maps the page" false
  | .ok ((), stMapped) => do
    -- Fill the initiator (core0) AND a remote (core1) with the translation.
    let stFilled := tlbFillOnCore (tlbFillOnCore stMapped core0 asid5 vaddrPage)
      core1 asid5 vaddrPage
    assertBool "both the initiator and a remote core cache the translation pre-unmap"
      ((tlbOnCore stFilled core0).entries.any (fun e => e.asid == asid5 && e.vaddr == vaddrPage) &&
       (tlbOnCore stFilled core1).entries.any (fun e => e.asid == asid5 && e.vaddr == vaddrPage))
    -- The initiator-atomic unmap: erase the page, post to remote targets, AND
    -- retire the initiator's own view — all in one committed transition.
    match vspaceUnmapPageWithShootdownPerCore core0 asid5 vaddrPage stFilled with
    | .error _ => assertBool "the initiator-atomic unmap succeeds" false
    | .ok ((), stAtomic) => do
      -- The initiator's own stale entry is GONE (retired atomically).
      assertBool "the initiator's own view no longer holds the unmapped translation (retired atomically)"
        (!((tlbOnCore stAtomic core0).entries.any (fun e => e.asid == asid5 && e.vaddr == vaddrPage)))
      -- A remote keeps the (now-stale) entry, but the round posted a covering descriptor to it.
      assertBool "a remote core keeps its cached entry but is covered by the posted descriptor"
        ((tlbOnCore stAtomic core1).entries.any (fun e => e.asid == asid5 && e.vaddr == vaddrPage) &&
         (stAtomic.tlbShootdown.pendingOnCore core1).contains descUnmapPage)
      -- The whole committed state satisfies the pending-aware per-core invariant:
      -- initiator consistent (retired), remotes stale-but-covered.
      assertBool "the committed initiator-atomic state keeps the per-core checker GREEN (F.2a)"
        (tlbInvalidationConsistentCheck_perCore stAtomic)
    -- Contrast: the plain unmap-with-shootdown leaves the initiator stale-and-uncovered
    -- (shootdownTargets EXCLUDES the initiator), so the checker is RED — the exact
    -- gap the PerCore wrapper closes.
    match vspaceUnmapPageWithShootdown core0 asid5 vaddrPage stFilled with
    | .error _ => assertBool "the plain unmap-with-shootdown succeeds" false
    | .ok ((), stPlain) => do
      assertBool "the plain unmap leaves the initiator's own view stale (no local retirement)"
        ((tlbOnCore stPlain core0).entries.any (fun e => e.asid == asid5 && e.vaddr == vaddrPage))
      assertBool "the plain unmap posts NO covering descriptor to the initiator's own queue"
        ((stPlain.tlbShootdown.pendingOnCore core0).isEmpty)
      assertBool "so the plain unmap leaves the per-core checker RED — the gap the PerCore wrapper closes"
        (!(tlbInvalidationConsistentCheck_perCore stPlain))

-- ----------------------------------------------------------------------------
-- §5.7  SM7.F (PR #844 review-3) — a cached entry whose ASID no longer resolves
--        (use-after-retype) is STALE, not vacuously consistent.
-- ----------------------------------------------------------------------------

private def runPerCoreTlbUseAfterRetypeChecks : IO Unit := do
  IO.println "-- §5.7 per-core TLB: use-after-retype (unresolvable ASID) rejected (SM7.F)"
  match vspaceMapPageWithFlush asid5 vaddrPage (SeLe4n.PAddr.ofNat 0x2000)
      .readOnly (udState []) with
  | .error _ => assertBool "the scenario maps the page" false
  | .ok ((), stMapped) => do
    let stFilled := tlbFillOnCore stMapped core0 asid5 vaddrPage
    -- While asid5 resolves, the cached entry is genuinely consistent (checker GREEN).
    assertBool "a walk-filled entry with a resolvable ASID passes the checker"
      (tlbInvalidationConsistentCheck_perCore stFilled)
    -- Model a retype: asid5 no longer resolves (the VSpaceRoot is gone / rebound),
    -- but the old translation is still cached on core0.  Carry the filled view onto
    -- the VSpaceRoot-free base state.
    let stRetyped : SeLe4n.Model.SystemState :=
      { (udState []) with perCoreTlb := stFilled.perCoreTlb }
    -- The OLD implication form accepted this VACUOUSLY (unresolvable ASID ⇒ premise
    -- unsatisfiable ⇒ trivially consistent).  The conjunction form (SM7.F) flags it
    -- as the stale use-after-retype entry it is — checker RED, no pending cover.
    assertBool "a cached entry whose ASID no longer resolves FAILS the checker (use-after-retype)"
      (!(tlbInvalidationConsistentCheck_perCore stRetyped))
    -- ...unless a covering shootdown is already pending for its core (the pending
    -- disjunct): then the stale entry is admissible (scheduled for retirement).
    match enqueueShootdown stRetyped.tlbShootdown core0 descUnmapPage with
    | none => assertBool "the covering descriptor enqueues" false
    | some sd =>
      let stRetypedPending := { stRetyped with tlbShootdown := sd }
      assertBool "the same use-after-retype entry becomes admissible once a covering shootdown is pending"
        (tlbInvalidationConsistentCheck_perCore stRetypedPending)

-- ----------------------------------------------------------------------------
-- §5.8  SM7.F (PR #844 review-3) — the coalescing eager view FULL-FLUSHES an
--        overflowed target, matching the coalesced `.vmalle1` it posts.
-- ----------------------------------------------------------------------------

private def runPerCoreTlbCoalescingOverflowChecks : IO Unit := do
  IO.println "-- §5.8 per-core TLB: coalescing view full-flushes an overflowed target (SM7.F)"
  -- Fill core1's pending queue to capacity, so THIS round's post coalesces to `.vmalle1`.
  match enqueueMany TlbShootdownState.initial core1
      (List.replicate maxPendingPerCore descUnmapPage) with
  | none => assertBool "the capacity fill succeeds" false
  | some sdFull => do
    -- Seed core1's view with an entry the round's op does NOT cover (a different vaddr).
    let stSeed : SeLe4n.Model.SystemState :=
      { (default : SeLe4n.Model.SystemState) with
          tlbShootdown := sdFull
          perCoreTlb := setTlbViewOnCore (default : SeLe4n.Model.SystemState).perCoreTlb
            core1 { entries := [entryOtherVaddr] } }
    assertBool "core1's queue is at capacity (so the round coalesces to a full flush)"
      ((stSeed.tlbShootdown.pendingOnCore core1).length == maxPendingPerCore)
    assertBool "the round's op does NOT cover the seeded entry (a different vaddr)"
      (!(tlbEntryMatches opUnmapTarget entryOtherVaddr))
    let coRound := tlbInvalidateOnAllCoresCoalescing stSeed core0
      (shootdownTargets core0) opUnmapTarget
    -- The overflowed target is FULL-FLUSHED — even the op-UNRELATED entry is gone,
    -- matching the coalesced `.vmalle1` the round posted (the SM7.F fix).
    assertBool "the coalescing view full-flushes the overflowed target (removes even op-unrelated entries)"
      ((tlbOnCore coRound.1 core1).entries.isEmpty)
    -- Contrast: the plain op-only `shootdownRoundViews` would have KEPT the entry
    -- (op doesn't cover it) — the exact under-invalidation Finding 2 closes.
    assertBool "the plain op-only view would have kept the op-unrelated entry (the gap Finding 2 closes)"
      (tlbHasEntry ((shootdownRoundViews stSeed.perCoreTlb core0
        (shootdownTargets core0) opUnmapTarget).get core1) entryOtherVaddr)
  -- PR #844 review-3 Finding 4: a DUPLICATE target that only reaches capacity on
  -- its SECOND visit must still be full-flushed — the threaded coalescing fold
  -- consults the EVOLVING queue, not the fixed pre-round state.  Seed core1 one
  -- below capacity and one op-unrelated entry, then post to [core1, core1].
  match enqueueMany TlbShootdownState.initial core1
      (List.replicate (maxPendingPerCore - 1) descUnmapPage) with
  | none => assertBool "the near-capacity fill succeeds" false
  | some sdNearFull => do
    let viewsSeeded := setTlbViewOnCore (default : SeLe4n.Model.SystemState).perCoreTlb
      core1 { entries := [entryOtherVaddr] }
    -- First visit: queue is (max-1) < max ⇒ op (keeps the op-unrelated entry).
    -- Second visit: the fold's evolved queue is now = max ⇒ coalesce ⇒ full flush.
    let dupView := shootdownRoundViewsCoalescing viewsSeeded sdNearFull
      (roundDescriptor sdNearFull core0 opUnmapTarget) core0
      [core1, core1] opUnmapTarget
    assertBool "a duplicate target that overflows on its second visit is full-flushed (Finding 4)"
      ((dupView.get core1).entries.isEmpty)
    -- With a single visit (no overflow) the same seed keeps the op-unrelated entry —
    -- confirming the full flush above is genuinely the second-visit coalesce.
    let singleView := shootdownRoundViewsCoalescing viewsSeeded sdNearFull
      (roundDescriptor sdNearFull core0 opUnmapTarget) core0
      [core1] opUnmapTarget
    assertBool "a single (non-overflowing) visit keeps the op-unrelated entry"
      (tlbHasEntry (singleView.get core1) entryOtherVaddr)

-- ----------------------------------------------------------------------------
-- §5.10  SM7.F.4 — the operative live lifecycle: a live map FILLS a real
--         per-core entry, a live cross-core unmap POSTS a covering round, and
--         the deferred catch-up REMOVES the (now-stale) remote entry — under
--         the pending-aware invariant, with a single serialized round.  The
--         two wrappers exercised here are exactly what the live `.vspaceMap` /
--         `.vspaceUnmap` dispatch routes through (per the `dispatchWithCap_*
--         _delegates` theorems), so this is the end-to-end acceptance scenario.
-- ----------------------------------------------------------------------------

private def runPerCoreTlbLiveLifecycleChecks : IO Unit := do
  IO.println "-- §5.10 per-core TLB: live map→fill→cross-core unmap→catch-up (SM7.F.4)"
  -- core1 performs the LIVE map wrapper: it maps (asid5, vaddrPage) into the
  -- page tables AND caches the freshly-established, consistent-by-construction
  -- translation on its OWN perCoreTlb view (the live fill — SM7.F.4(a)).
  match vspaceMapPageCheckedWithShootdownFromStatePerCore core1 asid5 vaddrPage
      (SeLe4n.PAddr.ofNat 0x2000) .readOnly (udState []) with
  | .error _ => assertBool "the live per-core map succeeds" false
  | .ok ((), stMapB) => do
    -- (1) the fill is OPERATIVE: perCoreTlb now holds a REAL entry on the live
    -- syscall path (the whole point of F.4 — the model is no longer vacuous),
    -- and the fill is a this-core event.
    assertBool "the live map caches the translation on the mapping core's own view (F.4(a) fill)"
      ((tlbOnCore stMapB core1).entries.any (fun e => e.asid == asid5 && e.vaddr == vaddrPage))
    assertBool "the fill is core-local — no other core cached it"
      ([core0, core2, core3].all fun c => (tlbOnCore stMapB c).entries.isEmpty)
    assertBool "the map+fill keeps the per-core checker green + shootdown quiescent"
      (tlbInvalidationConsistentCheck_perCore stMapB
        && decide (shootdownQuiescent stMapB.tlbShootdown))
    -- core0 performs the LIVE cross-core unmap wrapper: erases the mapping,
    -- posts a covering `.vae1` descriptor to every remote core (incl. core1),
    -- and retires its OWN view atomically (SM7.F.4(b)(i)).
    match vspaceUnmapPageWithShootdownPerCore core0 asid5 vaddrPage stMapB with
    | .error _ => assertBool "the live cross-core unmap succeeds" false
    | .ok ((), stUnmapA) => do
      -- (2) core1's cached entry is now STALE (its page-table mapping is gone),
      -- still present — but COVERED by the descriptor the round posted, so the
      -- pending-aware checker stays GREEN (the honest invariant's whole point).
      assertBool "the remote mapping core still holds the (now-stale) entry before catch-up"
        ((tlbOnCore stUnmapA core1).entries.any (fun e => e.asid == asid5 && e.vaddr == vaddrPage))
      assertBool "the unmap posts a covering descriptor to the remote mapping core"
        ((stUnmapA.tlbShootdown.pendingOnCore core1).any
          (fun d => d.op == opUnmapTarget && d.initiator == core0))
      assertBool "the initiator's own view was retired atomically with the unmap (F.4(b)(i))"
        (!((tlbOnCore stUnmapA core0).entries.any (fun e => e.asid == asid5 && e.vaddr == vaddrPage)))
      assertBool "the committed post-unmap state keeps the per-core checker GREEN (pending disjunct)"
        (tlbInvalidationConsistentCheck_perCore stUnmapA)
      -- (3) the deferred catch-up (exactly what `completeShootdownRounds` runs)
      -- drains every remote target's queue onto its own view — core1's stale
      -- entry is now PROVABLY REMOVED (the SMP-C4 use-after-unmap closure made
      -- operative on a real cached entry).  A single serialized round: no
      -- cross-round draining.
      let stFinal := shootdownCatchUpPerCore stUnmapA core0 [opUnmapTarget]
      assertBool "the catch-up removes the stale entry from the remote mapping core (F.4 acceptance)"
        (!((tlbOnCore stFinal core1).entries.any (fun e => e.asid == asid5 && e.vaddr == vaddrPage)))
      assertBool "the catch-up drains the remote target's shootdown queue"
        ((stFinal.tlbShootdown.pendingOnCore core1).isEmpty)
      assertBool "after the catch-up the per-core checker is GREEN"
        (tlbInvalidationConsistentCheck_perCore stFinal)

-- ----------------------------------------------------------------------------
-- §6  Concurrent-unmap stress: four cores, four rounds in flight
--
--     The model is deterministic and sequential, so genuine concurrency shows
--     up in exactly two places: (a) rounds *posted* before any catch-up drains
--     — the state the runtime reaches when four cores issue unmaps inside one
--     another's round window — and (b) the *order* the targets' handlers run
--     in.  This group drives both on a REAL page-table-backed state with REAL
--     cached translations (the SM7.F walk fills), and pins that neither the
--     pending-aware invariant nor the drained end state depends on either.
-- ----------------------------------------------------------------------------

/-- The storm's four pages — core `i` unmaps page `i`, all in `asid5`, with VA
and PA page-aligned (the v0.32.102 mapping-boundary guard). -/
private def stressAssignments : List (CoreId × SeLe4n.VAddr × SeLe4n.PAddr) :=
  [(core0, SeLe4n.VAddr.ofNat 0x1000, SeLe4n.PAddr.ofNat 0x10000),
   (core1, SeLe4n.VAddr.ofNat 0x2000, SeLe4n.PAddr.ofNat 0x11000),
   (core2, SeLe4n.VAddr.ofNat 0x3000, SeLe4n.PAddr.ofNat 0x12000),
   (core3, SeLe4n.VAddr.ofNat 0x4000, SeLe4n.PAddr.ofNat 0x13000)]

/-- The page operand core `c` posts in the storm (its assigned page).  Every
core of the 4-core topology is assigned, so the fallback is unreachable — and
it is deliberately an operand that covers **nothing** in this scenario (ASID 0,
address 0) rather than the full flush: a `.vmalle1` fallback would retire every
entry and so let a lost assignment pass the drain assertions instead of failing
them. -/
private def stressOpOf (c : CoreId) : TlbInvalidation :=
  match stressAssignments.find? (fun a => a.1 == c) with
  | some (_, va, _) => encodePageInvalidation asid5 va
  | none => encodePageInvalidation ⟨0⟩ (SeLe4n.VAddr.ofNat 0)

/-- All four storm pages mapped into a real VSpace — `none` if any map is
rejected, which keeps the scenario honest rather than silently vacuous. -/
private def stressMapped? : Option SeLe4n.Model.SystemState :=
  stressAssignments.foldlM
    (fun st a =>
      match vspaceMapPageWithFlush asid5 a.2.1 a.2.2 .readOnly st with
      | .error _ => none
      | .ok ((), st') => some st')
    (udState [])

/-- Every core walk-fills every storm page — the pre-state of a real storm, in
which each PE has translated through all four mappings. -/
private def stressFilled? : Option SeLe4n.Model.SystemState :=
  stressMapped?.map fun st =>
    allCores.foldl
      (fun s c =>
        stressAssignments.foldl (fun s' a => tlbFillOnCore s' c asid5 a.2.1) s)
      st

/-- The storm itself: each core runs the LIVE initiator-atomic unmap wrapper
(what `.vspaceUnmap` dispatches to) for its own page, with **no** catch-up in
between — four rounds in flight at once. -/
private def stressStormed? : Option SeLe4n.Model.SystemState :=
  match stressFilled? with
  | none => none
  | some st =>
    stressAssignments.foldlM
      (fun s a =>
        match vspaceUnmapPageWithShootdownPerCore a.1 asid5 a.2.1 s with
        | .error _ => none
        | .ok ((), s') => some s')
      st

/-- Does core `c`'s view still cache a translation for `vaddr` in `asid5`? -/
private def viewCaches (st : SeLe4n.Model.SystemState) (c : CoreId)
    (vaddr : SeLe4n.VAddr) : Bool :=
  (tlbOnCore st c).entries.any fun e => e.asid == asid5 && e.vaddr == vaddr

/-- Two states agree on every core's TLB view — mutual containment plus length,
the set comparison the §5.3 bridge check uses (entry order is an artefact of
the fill order, not an observable). -/
private def sameViews (a b : SeLe4n.Model.SystemState) : Bool :=
  allCores.all fun c =>
    (tlbOnCore a c).entries.length == (tlbOnCore b c).entries.length &&
    (tlbOnCore a c).entries.all (fun e => (tlbOnCore b c).entries.contains e) &&
    (tlbOnCore b c).entries.all (fun e => (tlbOnCore a c).entries.contains e)

/-- §6, part 3 of 3: rounds posted faster than the catch-up drains them
(backpressure to the capacity bound and past it), and a storm mixing operand
kinds — the drain must retire exactly what each core queued, neither less
(under-invalidation, unsafe) nor more (a blanket flush would mask a defect).

The three parts are defined in reverse call order (part 3, then 2, then the
`runConcurrentUnmapStressChecks` entry point) because Lean requires a
definition before its use; they are split at all per the thin-dispatcher
convention, since one deep `do`-chain blows clang's bracket-nesting limit. -/
private def runShootdownBackpressureChecks
    (stFilled : SeLe4n.Model.SystemState) : IO Unit := do
  -- (5) BACKPRESSURE.  The caller-facing (total, coalescing) posting the live
  -- wrappers use never fails and never breaches the bound: at capacity a
  -- target's queue collapses to one full flush that supersedes every dropped
  -- descriptor (over-invalidation is safe; under-invalidation never is).
  let stormN := fun (n : Nat) =>
    (List.range n).foldl
      (fun s _ =>
        tlbShootdownBroadcastCoalescing s core0 (shootdownTargets core0)
          (stressOpOf core0))
      stFilled
  let at16 := stormN maxPendingPerCore
  assertBool "sixteen un-drained rounds fill each remote queue exactly to capacity"
    ([core1, core2, core3].all fun c =>
      (at16.tlbShootdown.pendingOnCore c).length == maxPendingPerCore)
  assertBool "the strict posting fails closed at capacity (never silently drops)"
    ((tlbShootdownBroadcast at16 core0 (shootdownTargets core0)
      (stressOpOf core0)).isNone)
  let at17 :=
    tlbShootdownBroadcastCoalescing at16 core0 (shootdownTargets core0)
      (stressOpOf core0)
  assertBool "the seventeenth round collapses each full queue to one full flush"
    ([core1, core2, core3].all fun c =>
      (at17.tlbShootdown.pendingOnCore c).map (·.op) == [TlbInvalidation.vmalle1] &&
        (at17.tlbShootdown.pendingOnCore c).all (fun d => d.initiator == core0))
  assertBool "backpressure never breaches the capacity conjunct"
    (decide (pendingBounded at16.tlbShootdown) &&
      decide (pendingBounded at17.tlbShootdown))
  assertBool "draining the collapsed queue empties every remote view"
    (let drained :=
      (shootdownTargets core0).foldl handleTlbShootdownReqOnCorePerCore at17
     [core1, core2, core3].all fun c => (tlbOnCore drained c).entries.isEmpty)
  -- (6) MIXED operands in flight: core 0 posts a page unmap, core 1 an ASID
  -- retirement.  Each core's drain retires exactly ITS queue — core 1 never
  -- saw the `.aside1` (it initiated it), so its three remaining translations
  -- survive.  A blanket-flush regression in the handler fails right here.
  let mixed :=
    tlbShootdownBroadcastCoalescing
      (tlbShootdownBroadcastCoalescing stFilled core0 (shootdownTargets core0)
        (stressOpOf core0))
      core1 (shootdownTargets core1) (encodeAsidInvalidation asid5)
  assertBool "a mixed storm queues the page operand and the ASID operand in order"
    ((mixed.tlbShootdown.pendingOnCore core2).map (·.op) ==
      [stressOpOf core0, encodeAsidInvalidation asid5])
  let mixedDrained := allCores.foldl handleTlbShootdownReqOnCorePerCore mixed
  assertBool "the ASID operand empties every core that queued it"
    ([core0, core2, core3].all fun c =>
      (tlbOnCore mixedDrained c).entries.isEmpty)
  assertBool "the ASID initiator's own view retires only the page it queued"
    ((tlbOnCore mixedDrained core1).entries.length == 3 &&
      !(viewCaches mixedDrained core1 (SeLe4n.VAddr.ofNat 0x1000)))
  assertBool "the mixed storm ends quiescent and bounded"
    (decide (shootdownQuiescent mixedDrained.tlbShootdown) &&
      decide (pendingBounded mixedDrained.tlbShootdown))

/-- §6, part 2 of 3: the deferred catch-ups, and the visit-order independence
that makes one deterministic model fold stand for every hardware interleaving;
chains on to part 3 (`runShootdownBackpressureChecks`). -/
private def runConcurrentUnmapDrainChecks
    (stFilled stStorm : SeLe4n.Model.SystemState) : IO Unit := do
  -- (3) the deferred catch-ups — exactly what `completeShootdownRounds` runs,
  -- one per round.  Round 0's catch-up drains every OTHER core's queue
  -- completely (each had already retired its own operand), while the
  -- initiator's own queue waits for the NEXT round's catch-up to drain it.
  let stAfter0 := shootdownCatchUpPerCore stStorm core0 [stressOpOf core0]
  assertBool "round 0's catch-up leaves every remote core's view clean"
    ([core1, core2, core3].all fun c => (tlbOnCore stAfter0 c).entries.isEmpty)
  assertBool "round 0's catch-up leaves the initiator's own queue pending (covered)"
    ((stAfter0.tlbShootdown.pendingOnCore core0).length == 3 &&
      tlbInvalidationConsistentCheck_perCore stAfter0)
  let stAfter1 := shootdownCatchUpPerCore stAfter0 core1 [stressOpOf core1]
  assertBool "round 1's catch-up drains the last queue: every view is clean"
    (allCores.all fun c => (tlbOnCore stAfter1 c).entries.isEmpty)
  assertBool "after the storm drains the state is quiescent again"
    (decide (shootdownQuiescent stAfter1.tlbShootdown))
  assertBool "the drained state is consistent with no pending cover left"
    (tlbInvalidationConsistentCheck_perCore stAfter1)
  let stAfter3 :=
    shootdownCatchUpPerCore
      (shootdownCatchUpPerCore stAfter1 core2 [stressOpOf core2]) core3
      [stressOpOf core3]
  assertBool "the remaining rounds' catch-ups are inert (handler idempotence)"
    (sameViews stAfter1 stAfter3 &&
      decide (stAfter1.tlbShootdown = stAfter3.tlbShootdown))
  -- (4) ORDER INDEPENDENCE — the concurrency claim.  On hardware the four
  -- targets take their `.tlbShootdownReq` SGIs and retire in whatever order the
  -- GIC delivers them; the model commits ONE fold order.  Folding the live
  -- per-core handler over three different visit orders computes the identical
  -- state (`handleTlbShootdownReqOnCorePerCore_comm`), so the model's order is
  -- a faithful representative of every hardware interleaving.
  let drainIn := fun (order : List CoreId) =>
    order.foldl handleTlbShootdownReqOnCorePerCore stStorm
  let ascending := drainIn [core0, core1, core2, core3]
  let descending := drainIn [core3, core2, core1, core0]
  let interleaved := drainIn [core2, core0, core3, core1]
  assertBool "every visit order drains every core's view identically"
    (sameViews ascending descending && sameViews ascending interleaved)
  assertBool "every visit order commits the identical shootdown state"
    (decide (ascending.tlbShootdown = descending.tlbShootdown) &&
      decide (ascending.tlbShootdown = interleaved.tlbShootdown))
  assertBool "every visit order commits the identical single-view TLB"
    (ascending.tlb.entries == descending.tlb.entries &&
      ascending.tlb.entries == interleaved.tlb.entries)
  assertBool "a full 4-core drain ends quiescent with every view clean"
    (decide (shootdownQuiescent ascending.tlbShootdown) &&
      (allCores.all fun c => (tlbOnCore ascending c).entries.isEmpty))
  runShootdownBackpressureChecks stFilled

private def runConcurrentUnmapStressChecks : IO Unit := do
  IO.println "-- §6 concurrent-unmap stress: 4 cores, 4 rounds in flight"
  match stressFilled? with
  | none =>
    assertBool "the storm scenario builds (4 maps + 16 walk fills)" false
  | some stFilled => do
    -- (0) the pre-state is real: four page-table-backed mappings, cached on
    -- every core, quiescent and per-core consistent.
    assertBool "every core caches all four translations before the storm"
      (allCores.all fun c =>
        stressAssignments.all fun a => viewCaches stFilled c a.2.1)
    assertBool "the pre-state is quiescent and per-core consistent"
      (decide (shootdownQuiescent stFilled.tlbShootdown) &&
        tlbInvalidationConsistentCheck_perCore stFilled)
    match stressStormed? with
    | none =>
      assertBool "all four concurrent unmaps commit" false
    | some stStorm => do
      -- (1) posting exactness: each core's queue holds exactly the three
      -- descriptors the OTHER three initiators posted, in initiation order.
      assertBool "each core queues exactly the three remote initiators' descriptors"
        (allCores.all fun c =>
          (stStorm.tlbShootdown.pendingOnCore c).map (fun d => (d.op, d.initiator)) ==
            (stressAssignments.filter (fun a => a.1 != c)).map
              (fun a => (encodePageInvalidation asid5 a.2.1, a.1)))
      assertBool "no core queues its own round (the initiator is never a target)"
        (allCores.all fun c =>
          !((stStorm.tlbShootdown.pendingOnCore c).any fun d => d.initiator == c))
      assertBool "four rounds in flight never breach the capacity conjunct"
        (decide (pendingBounded stStorm.tlbShootdown))
      -- (2) initiator-atomicity: each core retired its OWN operand with its own
      -- unmap; the other three pages are stale on it — but covered by pending
      -- descriptors, so the honest invariant stays GREEN mid-storm.
      assertBool "each initiator retired its own page atomically with its unmap"
        (stressAssignments.all fun a => !(viewCaches stStorm a.1 a.2.1))
      assertBool "each core still holds the other three (now stale) translations"
        (stressAssignments.all fun a =>
          (stressAssignments.filter (fun b => b.1 != a.1)).all fun b =>
            viewCaches stStorm a.1 b.2.1)
      assertBool "the page tables no longer resolve any of the four pages"
        (stressAssignments.all fun a =>
          match vspaceLookup asid5 a.2.1 stStorm with
          | .error _ => true
          | .ok _ => false)
      assertBool "mid-storm the pending-aware per-core invariant is GREEN"
        (tlbInvalidationConsistentCheck_perCore stStorm)
      runConcurrentUnmapDrainChecks stFilled stStorm

-- ----------------------------------------------------------------------------
-- §8  SM7.F.3 — round-generation-tagged descriptors: a commit's catch-up
--     drains ONLY its own rounds
--
--     The model posting and the model catch-up are two separate atomic
--     commits, and only the *hardware* round runs under `SHOOTDOWN_ROUND_LOCK`.
--     So a concurrently-committed round can post descriptors between them.  A
--     whole-queue catch-up would swallow that round's freshly-queued work and
--     declare the model quiescent before its SGIs had fired — the model
--     claiming a core clean of an invalidation the hardware had not yet
--     performed.  Keying the drain on the commit's own round-generation window
--     closes it; this group exercises the closure on the SAME real
--     page-table-backed storm state §6 builds.
-- ----------------------------------------------------------------------------

/-- The generation window a commit that opened exactly the rounds between
`pre` and `post` recovers from its own state diff — what the live seam passes
to `shootdownCatchUpPerCoreInWindow`. -/
private def windowOf (pre post : SeLe4n.Model.SystemState) : Nat × Nat :=
  shootdownRoundWindow pre post

/-- §8 part (10): the second ASID of a **multi-round** retype.  Retyping a live
`.vspaceRoot` into a *different* `.vspaceRoot` puts two distinct ASIDs in the
flush set (`retypeShootdownAsidList`), and the wrapper opens one round per ASID
— the only production path whose single commit opens more than one round, and
therefore the only one whose recovered window is wider than a single
generation. -/
private def rtAsidNew : SeLe4n.ASID := ⟨9⟩

/-- §8 part (10): the object a multi-round retype installs — a fresh
`.vspaceRoot` under `rtAsidNew`, so the destroyed (`asid5`) and installed
(`rtAsidNew`) ASIDs differ and neither is deduplicated away. -/
private def rtNewVsp : SeLe4n.Model.KernelObject :=
  .vspaceRoot { asid := rtAsidNew, mappings := {} }


private def runRoundWindowChecks : IO Unit := do
  -- (1) Generation allocation: the counter boots at 0, a round open advances
  -- it by exactly one, and the round's descriptors carry that value.
  assertBool "the boot shootdown state is at generation 0"
    (TlbShootdownState.initial.roundGeneration == 0)
  let opened := beginShootdownRoundFor TlbShootdownState.initial core0
    (shootdownTargets core0)
  assertBool "a round open allocates the next generation"
    (opened.roundGeneration == 1)
  assertBool "the posted descriptor carries the opened round's generation"
    ((roundDescriptor TlbShootdownState.initial core0 opUnmapTarget).generation
      == opened.roundGeneration)
  assertBool "opening a round never touches a pending queue"
    (allCores.all fun c => opened.pendingOnCore c == [])
  -- (2) The window predicate: a commit that opened one round admits exactly
  -- that generation; a commit that opened none admits nothing.
  assertBool "the round's own generation is inside its commit's window"
    (inRoundWindow 0 1 1)
  assertBool "an earlier round's generation is outside the window"
    (!(inRoundWindow 1 2 1))
  assertBool "a later round's generation is outside the window"
    (!(inRoundWindow 0 1 2))
  assertBool "a commit that opened no round has an empty window"
    ([0, 1, 2, 3, 7].all fun g => !(inRoundWindow 5 5 g))
  -- (3) The race, on the real storm state.  Core 0's commit opened round 1;
  -- cores 1..3 then committed rounds 2..4 before any catch-up ran.
  match stressFilled?, stressStormed? with
  | none, _ => assertBool "the storm scenario builds" false
  | _, none => assertBool "all four concurrent unmaps commit" false
  | some stFilled, some stStorm => do
    assertBool "four concurrent commits allocated four distinct generations"
      (stFilled.tlbShootdown.roundGeneration == 0 &&
        stStorm.tlbShootdown.roundGeneration == 4)
    assertBool "each queued descriptor carries its own initiator's generation"
      (allCores.all fun c =>
        (stStorm.tlbShootdown.pendingOnCore c).all fun d =>
          match stressAssignments.findIdx? (fun a => a.1 == d.initiator) with
          | some i => d.generation == i + 1
          | none => false)
    -- Core 0's catch-up: its own commit's window is (0, 1].
    let window0 : Nat × Nat := (0, 1)
    let caught0 := shootdownCatchUpPerCoreInWindow stStorm core0
      [stressOpOf core0] window0.1 window0.2
    assertBool "core 0's catch-up drains its OWN round's descriptors"
      ([core1, core2, core3].all fun c =>
        !((caught0.tlbShootdown.pendingOnCore c).any fun d => d.generation == 1))
    assertBool "core 0's catch-up leaves every CONCURRENT round's work pending"
      ([core2, core3].all fun c =>
        (caught0.tlbShootdown.pendingOnCore c).length == 2)
    assertBool "the surviving descriptors are exactly the other rounds'"
      ([core2, core3].all fun c =>
        (caught0.tlbShootdown.pendingOnCore c).all fun d => d.generation > 1)
    -- The contrast: the pre-SM7.F.3 whole-queue catch-up drains everything,
    -- so the model would report quiescence with three rounds' SGIs unfired.
    let caughtAll := shootdownCatchUpPerCore stStorm core0 [stressOpOf core0]
    assertBool "a whole-queue catch-up would have swallowed the concurrent rounds"
      ([core1, core2, core3].all fun c =>
        (caughtAll.tlbShootdown.pendingOnCore c).isEmpty)
    assertBool "the window catch-up and the whole-queue catch-up genuinely differ here"
      (!(caught0.tlbShootdown == caughtAll.tlbShootdown))
    -- (4) The window catch-up is still SOUND: it removes exactly its own
    -- round's covered entries, and the pending-aware invariant holds.
    assertBool "core 0's round is retired on every remote view by its own catch-up"
      ([core1, core2, core3].all fun c =>
        !(viewCaches caught0 c (SeLe4n.VAddr.ofNat 0x1000)))
    assertBool "the other rounds' pages survive on the cores that did not initiate them"
      (viewCaches caught0 core1 (SeLe4n.VAddr.ofNat 0x3000))
    assertBool "after the window catch-up the pending-aware checker is GREEN"
      (tlbInvalidationConsistentCheck_perCore caught0)
    -- (5) Every round's own catch-up, run in turn, ends quiescent — nothing is
    -- lost by refusing to drain a foreign round.
    let allCaught :=
      (List.range 4).foldl
        (fun st i =>
          let c := (stressAssignments[i]?).map (·.1) |>.getD core0
          shootdownCatchUpPerCoreInWindow st c [stressOpOf c] i (i + 1))
        stStorm
    assertBool "running every commit's own catch-up drains every queue"
      (allCores.all fun c => (allCaught.tlbShootdown.pendingOnCore c).isEmpty)
    assertBool "and leaves no core caching any of the four unmapped pages"
      (allCores.all fun c =>
        stressAssignments.all fun a => !(viewCaches allCaught c a.2.1))
    assertBool "the fully-caught-up state is per-core consistent"
      (tlbInvalidationConsistentCheck_perCore allCaught)
  -- (6) The bridge: with a SINGLE round in flight (the serialised regime), the
  -- window catch-up IS the whole-queue catch-up — nothing about an ordinary
  -- one-round commit changes.
  match stressFilled? with
  | none => assertBool "the storm scenario builds" false
  | some stFilled => do
    match vspaceUnmapPageWithShootdownPerCore core0 asid5
        (SeLe4n.VAddr.ofNat 0x1000) stFilled with
    | .error _ => assertBool "the single live unmap commits" false
    | .ok ((), stOne) => do
      let w := windowOf stFilled stOne
      assertBool "a single-round commit's window is exactly one generation wide"
        (w.1 == 0 && w.2 == 1)
      -- `SystemState` has no `BEq`, so compare the fields the two catch-ups
      -- can differ on: the shootdown queues/flags and every core's TLB view.
      let inWin := shootdownCatchUpPerCoreInWindow stOne core0 [stressOpOf core0] w.1 w.2
      let whole := shootdownCatchUpPerCore stOne core0 [stressOpOf core0]
      assertBool "under round serialisation the window catch-up IS the whole-queue catch-up"
        (inWin.tlbShootdown == whole.tlbShootdown && sameViews inWin whole)
      -- (7) Diff-recovery precision: the operands the runtime broadcasts and
      -- publishes are exactly this commit's own window's.
      assertBool "the diff-recovered operand list is this commit's own round's"
        (shootdownPostedOps stFilled stOne == [stressOpOf core0])
      assertBool "the diff-recovered changed-target set is every remote core"
        (shootdownChangedTargets stFilled stOne == shootdownTargets core0)
  -- (8) Inertness: a commit that opened no round recovers an empty window and
  -- its catch-up is a no-op on every queue and view.
  match stressFilled? with
  | none => assertBool "the storm scenario builds" false
  | some stFilled => do
    let w := windowOf stFilled stFilled
    assertBool "a no-round commit recovers an empty window"
      (w.1 == w.2)
    assertBool "a no-round commit changes no target"
      (shootdownChangedTargets stFilled stFilled == [])
    let inert := shootdownCatchUpPerCoreInWindow stFilled core0 [] w.1 w.2
    assertBool "an empty-window catch-up drains nothing"
      (allCores.all fun c =>
        inert.tlbShootdown.pendingOnCore c == stFilled.tlbShootdown.pendingOnCore c)
    assertBool "an empty-window catch-up retires nothing from any view"
      (allCores.all fun c =>
        (tlbOnCore inert c).entries.length == (tlbOnCore stFilled c).entries.length)

/-- §8, part 2 of 3: the 12th `proofLayerInvariantBundle` conjunct
(`pendingBounded`) across the window catch-up.  Split out per the CLAUDE.md
thin-dispatcher guidance — a single `do`-block holding all three parts runs
past the ~150-line bracket-depth threshold. -/
private def runRoundWindowBoundChecks : IO Unit := do
  -- (9) Invariant-bundle carriage: the 12th `proofLayerInvariantBundle`
  -- conjunct (`pendingBounded`) survives the window catch-up — the transition
  -- the live seam actually runs.  A window drain deliberately leaves foreign
  -- descriptors queued, so unlike a whole-queue drain it does NOT trivially
  -- empty the queues; the bound has to be carried, and
  -- `shootdownCatchUpPerCoreInWindow_preserves_pendingBounded` is what carries
  -- it.  Checked at the exact point the drain is weakest: mid-storm, with three
  -- concurrent rounds' work still pending.
  match stressStormed? with
  | none => assertBool "all four concurrent unmaps commit" false
  | some stStorm => do
    assertBool "the mid-storm state satisfies the shootdown capacity conjunct"
      (decide (pendingBounded stStorm.tlbShootdown))
    let caught0 := shootdownCatchUpPerCoreInWindow stStorm core0
      [stressOpOf core0] 0 1
    assertBool "the window catch-up preserves the shootdown capacity conjunct"
      (decide (pendingBounded caught0.tlbShootdown))
    assertBool "and it did so with foreign descriptors genuinely left queued"
      ([core2, core3].all fun c =>
        !(caught0.tlbShootdown.pendingOnCore c).isEmpty)
    assertBool "the whole-queue catch-up preserves it too"
      (decide (pendingBounded
        (shootdownCatchUpPerCore stStorm core0 [stressOpOf core0]).tlbShootdown))
    assertBool "every commit's own catch-up, run in turn, keeps the bound"
      (decide (pendingBounded
        ((List.range 4).foldl
          (fun st i =>
            let c := (stressAssignments[i]?).map (·.1) |>.getD core0
            shootdownCatchUpPerCoreInWindow st c [stressOpOf c] i (i + 1))
          stStorm).tlbShootdown))

/-- §8, part 3 of 3: a round window WIDER than one generation — the live
two-ASID retype.  Split out per the CLAUDE.md thin-dispatcher guidance. -/
private def runRoundWindowWidthChecks : IO Unit := do
  -- (10) A window WIDER than one generation.  Every other group here exercises
  -- a one-round commit, where `roundGen := window.2` and a width-1 window would
  -- be indistinguishable from a correct one.  Retyping a live `.vspaceRoot` into
  -- a *different* `.vspaceRoot` is the production path that breaks that tie: its
  -- flush set holds two distinct ASIDs, so ONE commit opens TWO rounds and the
  -- recovered window must admit both.  A width-1 window would strand the first
  -- round's descriptors on every remote core — the model reporting quiescence
  -- with an ASID's translations still cached.
  let stPre := rtMultiState
  assertBool "a two-ASID retype's flush set holds both the destroyed and installed ASID"
    (SeLe4n.Kernel.retypeShootdownAsidList stPre rtVsp rtNewVsp == [asid5, rtAsidNew])
  match SeLe4n.Kernel.lifecycleRetypeWithCleanupShootdownPerCore core0
      { cnode := rtCn, slot := SeLe4n.Slot.ofNat 0 } rtVsp rtNewVsp stPre with
  | .error _ => assertBool "the two-ASID retype commits" false
  | .ok ((), stPost) => do
    let w := windowOf stPre stPost
    assertBool "one commit opened two rounds, so its window is two generations wide"
      (w.1 == 0 && w.2 == 2)
    assertBool "both rounds' descriptors are queued on every remote core"
      ([core1, core2, core3].all fun c =>
        queueHasOp (stPost.tlbShootdown.pendingOnCore c)
          (encodeAsidInvalidation asid5) core0 &&
        queueHasOp (stPost.tlbShootdown.pendingOnCore c)
          (encodeAsidInvalidation rtAsidNew) core0)
    assertBool "the two queued descriptors carry generations 1 and 2"
      ([core1, core2, core3].all fun c =>
        ((stPost.tlbShootdown.pendingOnCore c).map (·.generation)) == [1, 2])
    assertBool "a two-round commit still respects the capacity bound"
      (decide (pendingBounded stPost.tlbShootdown))
    -- The commit's own catch-up drains BOTH of its rounds.
    let caught := shootdownCatchUpPerCoreInWindow stPost core0
      (shootdownPostedOps stPre stPost) w.1 w.2
    assertBool "the commit's own catch-up drains both of its rounds"
      (allCores.all fun c => (caught.tlbShootdown.pendingOnCore c).isEmpty)
    assertBool "and the fully-drained state satisfies the capacity conjunct"
      (decide (pendingBounded caught.tlbShootdown))
    -- The tie-breaker: a width-1 window (the bug a single-round test cannot
    -- see) strands the FIRST round's descriptors on every remote core.
    let narrow := shootdownCatchUpPerCoreInWindow stPost core0
      (shootdownPostedOps stPre stPost) 1 2
    assertBool "a width-1 window would strand the first round on every remote core"
      ([core1, core2, core3].all fun c =>
        (narrow.tlbShootdown.pendingOnCore c).map (·.generation) == [1])
    -- Diff recovery is window-restricted too: the runtime broadcasts and
    -- publishes BOTH operands, deduplicated, and nothing else.
    assertBool "the diff-recovered operand list is both rounds' operands"
      (shootdownPostedOps stPre stPost ==
        [encodeAsidInvalidation asid5, encodeAsidInvalidation rtAsidNew])
    assertBool "the diff-recovered changed-target set is every remote core"
      (shootdownChangedTargets stPre stPost == shootdownTargets core0)

/-- §8.4 (PR #854 review): the model acknowledgment names the round it
discharged.

Until v0.32.113 `shootdownAck` was a `Vector Bool` and the window
catch-up set it unconditionally, so a catch-up that deliberately drained
only its own generation window still claimed every concurrently-posted
round as acknowledged: the queues were generation-selective but the
acknowledgment was not, and `allAcked` could read true with a foreign
round's descriptors still pending.  These checks are the model-side
counterpart of the Rust
`sm7f3_newer_round_acks_cannot_satisfy_an_older_unexecuted_round`. -/
private def runGenerationAwareAckChecks : IO Unit := do
  IO.println "-- §8.4 SM7.F.3 generation-aware model acknowledgment"
  -- Round A (generation 1, initiator core0) posts to the other three.
  let opened := beginShootdownRound TlbShootdownState.initial core0
  let descA : TlbShootdownDescriptor :=
    { op := .vae1 5 0x1000, initiator := core0, generation := 1 }
  let postedA := ((([core1, core2, core3]).foldlM
    (fun s c => enqueueShootdown s c descA) opened).getD opened)
  -- Round B (generation 2, initiator core1) commits before A's deferred
  -- catch-up runs — the interleaving the whole SM7.F.3 cut is about.
  let openedB := beginShootdownRound postedA core1
  let descB : TlbShootdownDescriptor :=
    { op := .vae1 9 0x2000, initiator := core1, generation := 2 }
  let postedB := ((([core0, core2, core3]).foldlM
    (fun s c => enqueueShootdown s c descB) openedB).getD openedB)
  assertBool "core2 holds both rounds' descriptors before any catch-up"
    ((postedB.pendingOnCore core2).length == 2)
  -- A's catch-up runs its own window (0, 1] on core2.
  let afterA := completeShootdownOnCoreInWindow postedB core2 0 1
  assertBool "A's catch-up drains only A's descriptor"
    ((afterA.pendingOnCore core2).length == 1 &&
      (afterA.pendingOnCore core2).all fun d => d.generation == 2)
  -- THE fix: A's catch-up acknowledged generation 1, so B's round — the
  -- round currently open — is still genuinely owed on core2.
  assertBool "A's catch-up acknowledges exactly its own window"
    (afterA.ackedGenOnCore core2 == 1)
  assertBool "A's catch-up does NOT acknowledge B's round"
    (!(afterA.ackOnCore core2))
  assertBool "so the round in flight is not reported all-acknowledged"
    (!(decide (allAcked afterA)))
  -- The load-bearing negative: the pre-fix unconditional acknowledgment
  -- would have marked core2 acknowledged here, and with the other two
  -- targets' catch-ups likewise it would have reported B's round complete
  -- with B's descriptors still queued.
  -- A's catch-up over ALL of A's targets, plus A's own initiator core0
  -- (which holds only B's descriptor) — the whole commit's catch-up.
  let afterAllA :=
    completeShootdownOnCoreInWindow
      (completeShootdownOnCoreInWindow
        (completeShootdownOnCoreInWindow afterA core1 0 1) core3 0 1) core0 0 1
  assertBool "A's catch-up drained every A descriptor"
    (allCores.all fun c =>
      (afterAllA.pendingOnCore c).all fun d => d.generation == 2)
  assertBool "no combination of A-window catch-ups completes B's round"
    (!(decide (allAcked afterAllA)))
  assertBool "and B's descriptors are all still pending"
    (allCores.all fun c =>
      c == core1 || (afterAllA.pendingOnCore c).any fun d => d.generation == 2)
  -- B's own catch-up is what completes B's round.
  let afterB :=
    completeShootdownOnCoreInWindow
      (completeShootdownOnCoreInWindow
        (completeShootdownOnCoreInWindow afterAllA core0 1 2) core2 1 2) core3 1 2
  assertBool "B's catch-up acknowledges B's round on every target"
    (decide (allAcked afterB))
  assertBool "and leaves the state quiescent"
    (decide (shootdownQuiescent afterB))
  -- Well-formedness holds throughout: no slot ever names an unopened round.
  assertBool "every state on the path is ack-bounded"
    (decide (ackBounded opened) && decide (ackBounded postedB) &&
      decide (ackBounded afterA) && decide (ackBounded afterB))
  -- Monotonicity: an acknowledgment never retracts a newer one.
  assertBool "a late older-round acknowledgment cannot retract a newer one"
    ((acknowledgeShootdown afterB core2 1).ackedGenOnCore core2 == 2)

/-- §8 dispatcher (the CLAUDE.md thin-dispatcher pattern): C-scope nesting
depth resets at each function boundary in the Lean codegen, so the four
parts each stay well inside clang's `-fbracket-depth` limit. -/
private def runRoundGenerationChecks : IO Unit := do
  IO.println "-- §8 SM7.F.3 round-generation-tagged catch-up"
  runRoundWindowChecks
  runRoundWindowBoundChecks
  runRoundWindowWidthChecks
  runGenerationAwareAckChecks

-- ----------------------------------------------------------------------------
-- §7  Cross-cluster mock: the `.outer` portability seam, exercised
--
--     BCM2712 is a single Cortex-A76 cluster, so `TLBI VAE1IS` alone already
--     reaches every PE and the explicit-ack protocol is (on this target)
--     redundant.  It exists so a MULTI-cluster port stays correct: there the
--     Inner Shareable domain stops covering every core (plan §3.4).  This group
--     mocks that topology over the same four PEs — cluster A = {0,1}, cluster
--     B = {2,3} — and pins three things: the domain tag is the ONLY thing a
--     port changes (`tlbShootdown_outer_correct`); a bare IS broadcast leaves
--     the other cluster stale (the hazard); and the SGI + per-core-ack round
--     retires the entry on every PE regardless of the cluster boundary.
-- ----------------------------------------------------------------------------

/-- Mock cluster A of the two-cluster topology — the initiator's cluster. -/
private def mockClusterA : List CoreId := [core0, core1]

/-- Mock cluster B — the cores a single Inner Shareable broadcast would miss on
a multi-cluster SoC. -/
private def mockClusterB : List CoreId := [core2, core3]

/-- §7, part 2 of 2 (defined first — Lean requires a definition before its
use): the hazard a bare Inner Shareable broadcast leaves on a multi-cluster
SoC, the explicit-ack round that closes it across the boundary, and the hybrid
(IS-locally + SGI-remotely) protocol such a port would run — which the masked
round-open already supports without a protocol change. -/
private def runCrossClusterHazardChecks : IO Unit := do
  -- (3) THE HAZARD.  Model a bare IS broadcast on a two-cluster SoC as the
  -- per-core invalidation applied to the initiator's cluster alone: the remote
  -- cluster keeps the stale translation — the SMP-C4 use-after-unmap window
  -- that would reopen if the port dropped the explicit-ack round.
  let isOnly :=
    mockClusterA.foldl (fun s c => tlbInvalidateOnCore s c opUnmapTarget)
      perCoreSeeded
  assertBool "a cluster-local IS broadcast cleans the initiator's own cluster"
    (mockClusterA.all fun c => !(tlbHasEntry (tlbOnCore isOnly c) entryTarget))
  assertBool "a cluster-local IS broadcast leaves the REMOTE cluster stale"
    (mockClusterB.all fun c => tlbHasEntry (tlbOnCore isOnly c) entryTarget)
  -- (4) the explicit-ack round closes it: SGI + per-core handler + ack retires
  -- the entry on every PE, cluster boundary notwithstanding.
  match shootdownRoundPerCore perCoreSeeded core0 (shootdownTargets core0)
      opUnmapTarget with
  | none => assertBool "the cross-cluster round opens from quiescence" false
  | some final => do
    assertBool "the explicit-ack round retires the entry in BOTH mock clusters"
      (allCores.all fun c => !(tlbHasEntry (tlbOnCore final c) entryTarget))
    assertBool "the cross-cluster round ends quiescent and bounded"
      (decide (shootdownQuiescent final.tlbShootdown) &&
        decide (pendingBounded final.tlbShootdown))
  -- (5) THE HYBRID a real multi-cluster port would run: keep the IS broadcast
  -- for the initiator's own cluster and use the SGI round for the remote
  -- cluster only.  The masked round-open already supports the narrowed target
  -- set, so the port is a target-set + domain-tag change, not a protocol one.
  match tlbShootdownBroadcast perCoreSeeded core0 mockClusterB opUnmapTarget with
  | none => assertBool "the narrowed (remote-cluster-only) round opens" false
  | some (posted, sgis) => do
    assertBool "the narrowed round fires SGIs only at the remote cluster"
      (sgis == mockClusterB.map (fun c => (c, SgiKind.tlbShootdownReq)))
    assertBool "the narrowed round waits only on the remote cluster's acks"
      (posted.tlbShootdown.ackOnCore core0 && posted.tlbShootdown.ackOnCore core1 &&
        !(posted.tlbShootdown.ackOnCore core2) &&
        !(posted.tlbShootdown.ackOnCore core3))
  match shootdownRoundPerCore perCoreSeeded core0 mockClusterB opUnmapTarget with
  | none => assertBool "the narrowed round completes" false
  | some remoteOnly => do
    assertBool "the narrowed round retires the entry across the boundary"
      (mockClusterB.all fun c => !(tlbHasEntry (tlbOnCore remoteOnly c) entryTarget))
    assertBool "the narrowed round leaves the cluster-mate to the IS broadcast"
      (tlbHasEntry (tlbOnCore remoteOnly core1) entryTarget)
    assertBool "IS-locally + SGI-remotely cleans every PE of both clusters"
      (let hybrid := tlbInvalidateOnCore remoteOnly core1 opUnmapTarget
       allCores.all fun c => !(tlbHasEntry (tlbOnCore hybrid c) entryTarget))
  -- (6) symmetry: a round initiated inside the remote cluster reaches back.
  match shootdownRoundPerCore perCoreSeeded core2 (shootdownTargets core2)
      opUnmapTarget with
  | none => assertBool "a round initiated in cluster B opens" false
  | some fromB =>
    assertBool "a cluster-B round retires the entry in cluster A too"
      (allCores.all fun c => !(tlbHasEntry (tlbOnCore fromB c) entryTarget))

private def runCrossClusterMockChecks : IO Unit := do
  IO.println "-- §7 cross-cluster mock: the .outer portability seam"
  -- (0) the mock is a MOCK: today's binding is single-cluster and the real
  -- target set already spans both mock clusters.
  assertBool "the live platform binding issues inner-shareable maintenance"
    (decide (SeLe4n.Kernel.shootdownSharingDomain = .inner))
  assertBool "the real target set crosses the mock cluster boundary"
    (shootdownTargets core0 == [core1, core2, core3])
  -- (1) the sharing domain changes the emitted instruction variant and the
  -- barrier — and nothing else.
  assertBool "the domain tags are distinct and inside the Rust decoder's range"
    (SeLe4n.Kernel.Concurrency.SharingDomain.inner.toTag == 0 &&
      SeLe4n.Kernel.Concurrency.SharingDomain.outer.toTag == 1)
  assertBool "the domain selects ISH vs OSH for the completing barrier"
    (decide (SeLe4n.Kernel.Concurrency.dsbForSharing .inner = .dsbIsh) &&
      decide (SeLe4n.Kernel.Concurrency.dsbForSharing .outer = .dsbOsh))
  -- (2) `tlbShootdown_outer_correct`, computed: the outer-shareable round is
  -- state-identical to the inner one — every SM7.B round theorem transports.
  match tlbShootdownBroadcastIn .inner perCoreSeeded core0
      (shootdownTargets core0) opUnmapTarget,
    tlbShootdownBroadcastIn .outer perCoreSeeded core0
      (shootdownTargets core0) opUnmapTarget with
  | some (innerSt, innerSgis), some (outerSt, outerSgis) => do
    assertBool "the outer round posts the identical shootdown state"
      (decide (innerSt.tlbShootdown = outerSt.tlbShootdown))
    assertBool "the outer round emits the identical SGI list"
      (innerSgis == outerSgis &&
        innerSgis == (shootdownTargets core0).map
          (fun c => (c, SgiKind.tlbShootdownReq)))
    assertBool "the outer round evolves the identical per-core views"
      (sameViews innerSt outerSt)
  | _, _ =>
    assertBool "both sharing domains open a round from quiescence" false
  runCrossClusterHazardChecks

-- ----------------------------------------------------------------------------
-- §8  Deterministic 4-core shootdown trace + golden fixture
--
--     Every line is COMPUTED from the live `vspaceMapPageCheckedWithShootdown
--     FromStatePerCore` / `vspaceUnmapPageWithShootdownPerCore` /
--     `shootdownCatchUpPerCore` decisions on a real page-table-backed state, so
--     a shootdown-logic regression diverges the fixture byte-for-byte.  The
--     `[smp-tlb-shootdown]` prefix is the fixture extraction key.
-- ----------------------------------------------------------------------------

/-- The trace's live pipeline: core 1 maps + caches the page, core 0 unmaps it
across cores, and the deferred catch-up drains every target.  `none` if any
live transition rejects — which the trace surfaces rather than hides. -/
private def tracePipeline? :
    Option (SeLe4n.Model.SystemState × SeLe4n.Model.SystemState ×
      SeLe4n.Model.SystemState) :=
  match vspaceMapPageCheckedWithShootdownFromStatePerCore core1 asid5 vaddrPage
      (SeLe4n.PAddr.ofNat 0x2000) .readOnly (udState []) with
  | .error _ => none
  | .ok ((), stMap) =>
    match vspaceUnmapPageWithShootdownPerCore core0 asid5 vaddrPage stMap with
    | .error _ => none
    | .ok ((), stUnmap) =>
      some (stMap, stUnmap, shootdownCatchUpPerCore stUnmap core0 [opUnmapTarget])

/-- Per-core view size + queue length + ack flag — the observable triple the
trace reports for each core at each stage. -/
private def coreLine (tag : String) (st : SeLe4n.Model.SystemState)
    (c : CoreId) : String :=
  s!"[smp-tlb-shootdown] {tag} core {c.val}: {(tlbOnCore st c).entries.length} \
entries, {(st.tlbShootdown.pendingOnCore c).length} pending, ack \
{st.tlbShootdown.ackOnCore c}"

/-- The green/red verdict of the pending-aware per-core invariant. -/
private def checkerVerdict (st : SeLe4n.Model.SystemState) : String :=
  if tlbInvalidationConsistentCheck_perCore st then "GREEN" else "RED"

private def shootdownTraceLines : List String :=
  match tracePipeline?, stressStormed? with
  | some (stMap, stUnmap, stFinal), some stStorm =>
    let storm := allCores.foldl handleTlbShootdownReqOnCorePerCore stStorm
    [ s!"[smp-tlb-shootdown] live map on core 1 caches \
{(tlbOnCore stMap core1).entries.length} entry; the map posts no round \
(quiescent {decide (shootdownQuiescent stMap.tlbShootdown)})" ]
    ++ allCores.map (coreLine "after map" stMap)
    ++ [ s!"[smp-tlb-shootdown] core 0 unmap: page tables resolve (asid 5, va \
0x1000) = {match vspaceLookup asid5 vaddrPage stUnmap with
  | .error _ => "unmapped" | .ok _ => "STILL MAPPED"}"
       , s!"[smp-tlb-shootdown] posted operand (raw FFI encoding): op_tag \
{opUnmapTarget.toOpTag} asid {opUnmapTarget.toAsid} vaddr {opUnmapTarget.toVaddr}"
       , s!"[smp-tlb-shootdown] round SGIs: {(shootdownTargets core0).length} × \
tlbShootdownReq" ]
    ++ allCores.map (coreLine "after unmap" stUnmap)
    ++ [ s!"[smp-tlb-shootdown] pending-aware invariant after unmap: \
{checkerVerdict stUnmap}" ]
    ++ allCores.map (coreLine "after catch-up" stFinal)
    ++ [ s!"[smp-tlb-shootdown] round complete: quiescent \
{decide (shootdownQuiescent stFinal.tlbShootdown)}, allAcked \
{decide (allAcked stFinal.tlbShootdown)}, bounded \
{decide (pendingBounded stFinal.tlbShootdown)}, invariant \
{checkerVerdict stFinal}"
       , s!"[smp-tlb-shootdown] storm: 4 concurrent rounds leave pending \
{allCores.map (fun c => (stStorm.tlbShootdown.pendingOnCore c).length)} and \
cached {allCores.map (fun c => (tlbOnCore stStorm c).entries.length)}, bounded \
{decide (pendingBounded stStorm.tlbShootdown)}, invariant \
{checkerVerdict stStorm}"
       , s!"[smp-tlb-shootdown] storm drained: quiescent \
{decide (shootdownQuiescent storm.tlbShootdown)}, cached entries left \
{(allCores.map (fun c => (tlbOnCore storm c).entries.length)).sum}"
       , s!"[smp-tlb-shootdown] cross-cluster: outer tag \
{SeLe4n.Kernel.Concurrency.SharingDomain.outer.toTag} vs inner tag \
{SeLe4n.Kernel.Concurrency.SharingDomain.inner.toTag}, round state-identical \
{decide ((tlbShootdownBroadcastIn .outer perCoreSeeded core0
    (shootdownTargets core0) opUnmapTarget).map (fun r => r.1.tlbShootdown) =
  (tlbShootdownBroadcastIn .inner perCoreSeeded core0
    (shootdownTargets core0) opUnmapTarget).map (fun r => r.1.tlbShootdown))}" ]
  | _, _ => ["[smp-tlb-shootdown] PIPELINE ERROR: a live shootdown transition failed"]

private def traceFixturePath : String := "tests/fixtures/smp_tlb_shootdown.expected"

/-- §8: print the deterministic 4-core shootdown trace and verify it
byte-for-byte against the golden fixture.  The lines print before the (strict)
verification, so the fixture is regenerable via
`lake exe smp_tlb_shootdown_suite | grep '^\[smp-tlb-shootdown\]'` (the
brackets MUST be escaped — unescaped they form a regex character class that
also matches the suite's `--` section headers, corrupting the fixture). -/
private def runTraceFixtureCheck : IO Unit := do
  IO.println "-- §8 deterministic 4-core shootdown trace (golden fixture)"
  for l in shootdownTraceLines do
    IO.println l
  let expectedContent := String.intercalate "\n" shootdownTraceLines ++ "\n"
  let fixtureExists ← System.FilePath.pathExists traceFixturePath
  if !fixtureExists then
    IO.println s!"  FAIL: golden fixture {traceFixturePath} not found"
    IO.println s!"        regenerate: lake exe smp_tlb_shootdown_suite | \
grep '^\\[smp-tlb-shootdown\\]' > {traceFixturePath}"
    throw (IO.userError s!"missing fixture {traceFixturePath}")
  let actual ← IO.FS.readFile traceFixturePath
  if actual == expectedContent then
    IO.println s!"  PASS: shootdown trace matches golden fixture {traceFixturePath}"
  else
    IO.println s!"  FAIL: shootdown trace differs from golden fixture {traceFixturePath}"
    IO.println "        the live trace is printed above; regenerate with:"
    IO.println s!"          lake exe smp_tlb_shootdown_suite | \
grep '^\\[smp-tlb-shootdown\\]' > {traceFixturePath}"
    IO.println s!"          (then refresh {traceFixturePath}.sha256 — see tests/fixtures/README.md)"
    throw (IO.userError "shootdown trace fixture mismatch")

-- ----------------------------------------------------------------------------
-- Runner
-- ----------------------------------------------------------------------------

def runSmpTlbShootdownChecks : IO Unit := do
  IO.println "WS-SM SM7.A + SM7.B + SM7.C — TLB shootdown state + protocol + per-core model suite"
  IO.println "===================================================="
  runDescriptorChecks
  runInitialStateChecks
  runEnqueueChecks
  runCapacityChecks
  runDrainChecks
  runAckRoundChecks
  runFullRoundTripChecks
  runCoalescingChecks
  runRoundCompositionChecks
  runLockOrderChecks
  runMountChecks
  runMaskedRoundChecks
  runInvalidationSemanticsChecks
  runBroadcastChecks
  runHandlerChecks
  runProtocolRoundChecks
  runCallerWrapperChecks
  runWaitLoopChecks
  runProtocolLockSetChecks
  runDiffRecoveryChecks
  runCompletionCutChecks
  runDebtClosureChecks
  runLiveDispatchChecks
  runPerCoreTlbLocalChecks
  runPerCoreTlbBroadcastChecks
  runPerCoreTlbOperationalChecks
  runPerCoreTlbFillChecks
  runPerCoreTlbPendingAwareChecks
  runPerCoreTlbInitiatorAtomicChecks
  runPerCoreTlbUseAfterRetypeChecks
  runPerCoreTlbCoalescingOverflowChecks
  runPerCoreTlbLiveLifecycleChecks
  runConcurrentUnmapStressChecks
  runRoundGenerationChecks
  runCrossClusterMockChecks
  runTraceFixtureCheck
  IO.println "===================================================="
  IO.println "All SM7.A + SM7.B + SM7.C TLB shootdown + per-core model checks PASS."

end SeLe4n.Testing.SmpTlbShootdown

def main : IO Unit :=
  SeLe4n.Testing.SmpTlbShootdown.runSmpTlbShootdownChecks
