-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.Invariant.LookupCongruence
import SeLe4n.Kernel.IPC.Invariant.DonationPreservation
import SeLe4n.Kernel.IPC.Invariant.PerCoreBundlePreservation
import SeLe4n.Kernel.Architecture.SyscallReturn
import SeLe4n.Kernel.Architecture.PerCoreCacheModel
import SeLe4n.Kernel.Architecture.IpcBufferValidation
import SeLe4n.Kernel.IPC.Operations.NotificationBind
import SeLe4n.Kernel.SchedContext.PriorityManagementPerCore

import SeLe4n.Kernel.Capability.Operations
import SeLe4n.Kernel.Capability.Invariant.Preservation.CopyMoveMutate
import SeLe4n.Kernel.SchedContext.OperationsPerCore
import SeLe4n.Kernel.SchedContext.SchedControl
import SeLe4n.Kernel.Scheduler.Operations.PerCoreCbs
import SeLe4n.Kernel.Service.Registry
import SeLe4n.Kernel.IPC.CrossCore.Cancellation
import SeLe4n.Kernel.IPC.Operations.Fault
import SeLe4n.Kernel.Capability.FrameFinalise
import SeLe4n.Kernel.Lifecycle.Operations.SetSpace
import SeLe4n.Kernel.Architecture.PageTableInstall

/-!
# `ipcInvariantFull` bundles for the non-IPC dispatch arms

`dispatchWithCap` routes twenty-five syscalls, and before this module only the
IPC and donation arms carried `ipcInvariantFull` bundles — the capability,
VSpace, service, sched-context, lifecycle and TCB arms had per-invariant
fragments at best, so no theorem could carry the bundle across a syscall.
This module holds the whole-bundle preservation theorem for each such arm's
terminal transition, one per operation the dispatcher actually calls.

Every theorem here concludes an IPC-subsystem predicate (`ipcInvariantFull`),
which is why the module lives in `IPC/Invariant/` rather than in each
operation's own subsystem: it is the IPC bundle's view of the rest of the
kernel, exactly as `Capability/Invariant/Preservation/` holds the capability
bundle's view of the IPC operations.  The levers are:

* `ipcInvariantFull_of_objects_eq` (`LookupCongruence` §5) — arms that leave
  the object store untouched (cache maintenance, service-registry writes);
* `ipcInvariantFull_of_readViewAgreement` (`LookupCongruence` §5) — arms that
  rewrite only objects the bundle never reads (CNodes, VSpaceRoots, untyped
  memory), with `capabilityBadgesWellFormed` supplied for the post-state;
* `ipcInvariantFull_of_tcbFieldUpdate` (`DonationPreservation`) — arms that
  rewrite one TCB leaving every conjunct-read field intact (return-frame
  staging, IPC-buffer/affinity/priority updates).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Model.SystemState
open SeLe4n.Kernel.Concurrency (CoreId bootCoreId)

-- ============================================================================
-- §1  Shared frame helpers
-- ============================================================================

/-- The reschedule-pending flags (the KSC-1 accumulator) are read by no conjunct
of the bundle: a write that moves nothing but them — and leaves every object,
run queue and current slot in place — carries it whole. -/
theorem ipcInvariantFull_of_flagOnlyWrite {s1 s2 : SystemState}
    (hObj : s2.objects = s1.objects)
    (h : ipcInvariantFull s1) : ipcInvariantFull s2 :=
  ipcInvariantFull_of_getElem_eq (fun oid => by rw [hObj])
    h

/-- The key-change hook writes a flag or nothing. -/
theorem markKeyChangeFor_preserves_ipcInvariantFull (st : SystemState)
    (tid : SeLe4n.ThreadId) (k : SeLe4n.Priority × SeLe4n.Deadline × SeLe4n.DomainId)
    (h : ipcInvariantFull st) : ipcInvariantFull (markKeyChangeFor st tid k) :=
  ipcInvariantFull_of_flagOnlyWrite (markKeyChangeFor_objects _ _ _)
    h

/-- The candidacy hook writes a flag or nothing. -/
theorem markCandidacyGainFor_preserves_ipcInvariantFull (st : SystemState)
    (tid : SeLe4n.ThreadId) (b : Bool)
    (h : ipcInvariantFull st) : ipcInvariantFull (markCandidacyGainFor st tid b) :=
  ipcInvariantFull_of_flagOnlyWrite (markCandidacyGainFor_objects _ _ _)
    h

/-- A reschedule-pending mark writes a flag and nothing else. -/
theorem markReschedulePendingOnCore_preserves_ipcInvariantFull (st : SystemState)
    (c : CoreId) (h : ipcInvariantFull st) :
    ipcInvariantFull (st.markReschedulePendingOnCore c) :=
  ipcInvariantFull_of_flagOnlyWrite (s1 := st) rfl h

/-- The pre-state form of the hook writes a flag or nothing. -/
theorem markKeyChangeFrom_preserves_ipcInvariantFull (pre st : SystemState)
    (tid : SeLe4n.ThreadId) (h : ipcInvariantFull st) :
    ipcInvariantFull (markKeyChangeFrom pre st tid) :=
  ipcInvariantFull_of_flagOnlyWrite (markKeyChangeFrom_objects _ _ _)
    h

/-- A scheduling point's closing clear writes a flag and nothing else. -/
theorem clearReschedulePendingOnCore_preserves_ipcInvariantFull (st : SystemState)
    (c : CoreId) (h : ipcInvariantFull st) :
    ipcInvariantFull (st.clearReschedulePendingOnCore c) :=
  ipcInvariantFull_of_flagOnlyWrite (s1 := st) rfl h

-- ============================================================================
-- §2  Service-registry arms (`.serviceRegister`, `.serviceRevoke`)
-- ============================================================================

/-- The registry's one object write — an endpoint's service record — is outside
the IPC bundle's read view: every endpoint-reading conjunct reads the queues,
and the rewrite keeps every other object. -/
theorem ipcInvariantFull_of_serviceRecordRewrite {st st' : SystemState}
    (hW : ServiceRecordRewrite st.objects st'.objects) (hObjInv : st.objects.invExt)
    (hInv : ipcInvariantFull st) : ipcInvariantFull st' := by
  have hL := hW.lookup hObjInv
  have hView : ipcReadViewAgreement st st' := by
    refine ⟨fun oid t ht => ?_, fun oid t ht => ?_, fun oid ep he => ?_, fun oid ep he => ?_,
      fun oid n hn => ?_, fun oid r => ?_, fun oid sc hsc => ?_⟩ <;>
      rcases hL oid with hE | ⟨ep0, c, h0, h1⟩
    · rw [hE] at ht; exact ⟨t, ht, rfl⟩
    · rw [h1] at ht; cases ht
    · rw [← hE] at ht; exact ⟨t, ht, rfl⟩
    · rw [h0] at ht; cases ht
    · rw [hE] at he; exact ⟨ep.service, he⟩
    · rw [h1] at he; cases he; exact ⟨ep0.service, h0⟩
    · rw [← hE] at he; exact ⟨ep.service, he⟩
    · rw [h0] at he; cases he; exact ⟨c, h1⟩
    · rw [hE] at hn; exact ⟨n, hn, rfl, rfl, rfl⟩
    · rw [h1] at hn; cases hn
    · rw [hE]
    · rw [h0, h1]; simp
    · rw [← hE] at hsc; exact ⟨sc, hsc, rfl⟩
    · rw [h0] at hsc; cases hsc
  have hCodes : sameNotificationBindings st st' := fun k => by
    rcases hL k with hE | ⟨_, _, h0, h1⟩
    · rw [hE]
    · rw [h0, h1]; rfl
  have hCap : capabilityBadgesWellFormed st' :=
    capabilityBadgesWellFormed_of_slotCap_back hInv.badgeWellFormed.2 fun oid o' hO => by
      rcases hL oid with hE | ⟨ep0, _, h0, h1⟩
      · rw [hE] at hO; exact ⟨o', hO, rfl⟩
      · rw [h1] at hO; cases hO; exact ⟨_, h0, rfl⟩
  exact ipcInvariantFull_of_readViewAgreement hView hCodes hCap hInv

/-- `.serviceRegister`: the registration writes the service registry and its
endpoint's `serviceRegistered`, which the bundle does not read. -/
theorem registerService_preserves_ipcInvariantFull
    (st st' : SystemState) (reg : ServiceRegistration)
    (hObjInv : st.objects.invExt)
    (hInv : ipcInvariantFull st)
    (hStep : registerService reg st = .ok ((), st')) :
    ipcInvariantFull st' :=
  ipcInvariantFull_of_serviceRecordRewrite (registerService_serviceRecordRewrite hStep) hObjInv hInv

/-- `.serviceRevoke`: revocation removes registry entries and dependency
edges and clears its endpoint's `serviceRegistered`, which the bundle does not read. -/
theorem revokeService_preserves_ipcInvariantFull
    (st st' : SystemState) (sid : ServiceId)
    (hObjInv : st.objects.invExt)
    (hInv : ipcInvariantFull st)
    (hStep : revokeService sid st = .ok ((), st')) :
    ipcInvariantFull st' :=
  ipcInvariantFull_of_serviceRecordRewrite (revokeService_serviceRecordRewrite hStep) hObjInv hInv

-- ============================================================================
-- §3  Cache-maintenance arm (`.vspaceUnifyInstruction`)
-- ============================================================================

/-- `.vspaceUnifyInstruction`: pure cache maintenance — no page table, no
object, no scheduler state moves, so the whole bundle transports. -/
theorem vspaceUnifyInstructionPage_preserves_ipcInvariantFull
    {st st' : SystemState} {asid : SeLe4n.ASID} {vaddr : SeLe4n.VAddr}
    (hInv : ipcInvariantFull st)
    (hStep : Architecture.vspaceUnifyInstructionPage asid vaddr st = .ok ((), st')) :
    ipcInvariantFull st' := by
  obtain ⟨hObjs, _, hSched, _⟩ := Architecture.vspaceUnifyInstructionPage_frame hStep
  exact ipcInvariantFull_of_objects_eq hObjs hInv

-- ============================================================================
-- §4  Return-frame staging (`.serviceQuery`'s answer, and every arm that
--     stages a result register)
-- ============================================================================

/-- Return-frame staging is one object-store insert or the identity, so the
object-store invariant transports. -/
theorem writeReturnFrameToTcb_preserves_objects_invExt
    (st : SystemState) (tid : SeLe4n.ThreadId) (frame : Architecture.SyscallReturnFrame)
    (hObjInv : st.objects.invExt) :
    (Architecture.writeReturnFrameToTcb st tid frame).objects.invExt := by
  unfold Architecture.writeReturnFrameToTcb
  exact SystemState.updateTcb_preserves_objects_invExt st tid _ hObjInv

/-- Return-frame staging rewrites exactly one TCB's `registerContext` — a
field no conjunct reads — so the whole bundle transports.  This is the lever
under `.serviceQuery`'s answer and under every dispatch arm that stages a
result into the caller's saved frame. -/
theorem writeReturnFrameToTcb_preserves_ipcInvariantFull
    (st : SystemState) (tid : SeLe4n.ThreadId) (frame : Architecture.SyscallReturnFrame)
    (hObjInv : st.objects.invExt)
    (hInv : ipcInvariantFull st) :
    ipcInvariantFull (Architecture.writeReturnFrameToTcb st tid frame) := by
  cases hT : st.getTcb? tid with
  | none =>
      rw [Architecture.writeReturnFrameToTcb_id_when_not_tcb st tid frame hT]
      exact hInv
  | some tcb =>
      have hPre : st.objects[tid.toObjId]? = some (.tcb tcb) :=
        (SystemState.getTcb?_eq_some_iff st tid tcb).mp hT
      have hAt : (Architecture.writeReturnFrameToTcb st tid frame).objects[tid.toObjId]?
          = some (.tcb (tcb.withReturnFrame frame)) := by
        unfold Architecture.writeReturnFrameToTcb
        rw [SystemState.updateTcb_eq_of_some hT]
        exact RobinHood.RHTable.getElem?_insert_self st.objects tid.toObjId _ hObjInv
      have hFrame : ∀ oid : SeLe4n.ObjId, oid ≠ tid.toObjId →
          (Architecture.writeReturnFrameToTcb st tid frame).objects[oid]? = st.objects[oid]? :=
        fun oid hNe => Architecture.writeReturnFrameToTcb_objects_ne st tid frame oid hNe hObjInv
      have hSched := Architecture.writeReturnFrameToTcb_scheduler_eq st tid frame
      exact ipcInvariantFull_of_tcbFieldUpdate st _ tid.toObjId tcb (tcb.withReturnFrame frame)
        hInv hPre hAt hFrame rfl rfl rfl rfl rfl rfl rfl rfl rfl

/-- **WS-ZA ZA4.7**: the delivery write keeps the object-store invariant. -/
theorem writeDeliveredFrameToTcb_preserves_objects_invExt
    (st : SystemState) (tid : SeLe4n.ThreadId) (frame : Architecture.SyscallReturnFrame)
    (hObjInv : st.objects.invExt) :
    (Architecture.writeDeliveredFrameToTcb st tid frame).objects.invExt :=
  SystemState.updateTcb_preserves_objects_invExt st tid _ hObjInv

/-- **WS-ZA ZA4.7**: the delivery write on a `.ready` thread keeps the bundle.  It
rewrites the saved registers, which no conjunct reads, and drops the message,
which no conjunct asks of a ready thread (`pendingMessageReadAgrees_ready_none`). -/
theorem writeDeliveredFrameToTcb_preserves_ipcInvariantFull
    (st : SystemState) (tid : SeLe4n.ThreadId) (frame : Architecture.SyscallReturnFrame)
    (hObjInv : st.objects.invExt)
    (hReady : ∀ tcb, st.getTcb? tid = some tcb → tcb.ipcState = .ready)
    (hInv : ipcInvariantFull st) :
    ipcInvariantFull (Architecture.writeDeliveredFrameToTcb st tid frame) := by
  cases hT : st.getTcb? tid with
  | none =>
      unfold Architecture.writeDeliveredFrameToTcb
      rw [SystemState.updateTcb_eq_self_of_none hT]
      exact hInv
  | some tcb =>
      have hPre : st.objects[tid.toObjId]? = some (.tcb tcb) :=
        (SystemState.getTcb?_eq_some_iff st tid tcb).mp hT
      have hAt : (Architecture.writeDeliveredFrameToTcb st tid frame).objects[tid.toObjId]?
          = some (.tcb (tcb.withDeliveredFrame frame)) := by
        unfold Architecture.writeDeliveredFrameToTcb
        rw [SystemState.updateTcb_eq_of_some hT]
        exact RobinHood.RHTable.getElem?_insert_self st.objects tid.toObjId _ hObjInv
      have hFrame : ∀ oid : SeLe4n.ObjId, oid ≠ tid.toObjId →
          (Architecture.writeDeliveredFrameToTcb st tid frame).objects[oid]? = st.objects[oid]? :=
        fun oid hNe => Architecture.writeDeliveredFrameToTcb_objects_ne st tid frame oid hNe hObjInv
      have hSched := Architecture.writeDeliveredFrameToTcb_scheduler_eq st tid frame
      have hMsg : pendingMessageReadAgrees tcb.ipcState (tcb.withDeliveredFrame frame).pendingMessage
          tcb.pendingMessage := by
        rw [hReady tcb hT]; exact pendingMessageReadAgrees_ready_none _
      exact ipcInvariantFull_of_tcbFieldUpdateAgree st _ tid.toObjId tcb
        (tcb.withDeliveredFrame frame) hInv hPre hAt hFrame rfl hMsg rfl rfl rfl rfl rfl rfl rfl

-- ============================================================================
-- §5  One-TCB field stores (`.tcbSetIPCBuffer` and friends)
-- ============================================================================

/-- The store-level instance of the one-TCB-rewrite lever: a transition whose
success is exactly `storeObject tid.toObjId (.tcb tcb')` over a looked-up
`tcb`, with `tcb'` agreeing on every conjunct-read field, preserves the whole
bundle. -/
theorem storeObject_tcbFieldUpdate_preserves_ipcInvariantFull
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (tcb tcb' : TCB)
    (hObjInv : st.objects.invExt)
    (hInv : ipcInvariantFull st)
    (hPre : st.objects[tid.toObjId]? = some (.tcb tcb))
    (hStore : storeObject tid.toObjId (.tcb tcb') st = .ok ((), st'))
    (hIpc : tcb'.ipcState = tcb.ipcState)
    (hMsg : tcb'.pendingMessage = tcb.pendingMessage)
    (hNext : tcb'.queueNext = tcb.queueNext)
    (hPrev : tcb'.queuePrev = tcb.queuePrev)
    (hPPrev : tcb'.queuePPrev = tcb.queuePPrev)
    (hBudget : tcb'.timeoutBudget = tcb.timeoutBudget)
    (hReply : tcb'.replyObject = tcb.replyObject)
    (hStash : tcb'.pendingReceiveReply = tcb.pendingReceiveReply)
    (hBind : tcb'.schedContextBinding = tcb.schedContextBinding)
    (hSlots : ∀ (sl : SeLe4n.Slot) (c : Capability) (b : SeLe4n.Badge),
      tcb'.spaceSlotCap sl = some c → c.badge = some b → tcb.spaceSlotCap sl = some c :=
      by intro _ _ _ h _; exact h)
    (hBnc : tcb'.boundNotificationCode = tcb.boundNotificationCode := by rfl) :
    ipcInvariantFull st' := by
  have hAt : st'.objects[tid.toObjId]? = some (.tcb tcb') :=
    storeObject_objects_eq st st' tid.toObjId (.tcb tcb') hObjInv hStore
  have hFrame : ∀ oid : SeLe4n.ObjId, oid ≠ tid.toObjId →
      st'.objects[oid]? = st.objects[oid]? :=
    fun oid hNe => storeObject_objects_ne st st' tid.toObjId oid (.tcb tcb') hNe hObjInv hStore
  have hSched := storeObject_scheduler_eq st st' tid.toObjId (.tcb tcb') hStore
  exact ipcInvariantFull_of_tcbFieldUpdate st st' tid.toObjId tcb tcb'
    hInv hPre hAt hFrame hIpc hMsg hNext hPrev hPPrev hBudget hReply hStash hBind
    hSlots hBnc

/-- `.tcbSetIPCBuffer`: rewrites one TCB's `ipcBuffer` — a field no conjunct
reads — so the whole bundle transports. -/
theorem setIPCBufferOp_preserves_ipcInvariantFull
    (st st' : SystemState) (vtid : SeLe4n.ValidThreadId) (addr : SeLe4n.VAddr)
    (hObjInv : st.objects.invExt)
    (hInv : ipcInvariantFull st)
    (hStep : Architecture.IpcBufferValidation.setIPCBufferOp st vtid addr = .ok st') :
    ipcInvariantFull st' := by
  unfold Architecture.IpcBufferValidation.setIPCBufferOp at hStep
  split at hStep
  · contradiction
  · split at hStep
    · rename_i tcb hTcb
      dsimp only [] at hStep
      split at hStep
      · rename_i hStore
        cases hStep
        exact storeObject_tcbFieldUpdate_preserves_ipcInvariantFull st _ vtid.val
          tcb { tcb with ipcBuffer := addr } hObjInv hInv
          ((SystemState.getTcb?_eq_some_iff st vtid.val tcb).mp hTcb)
          hStore rfl rfl rfl rfl rfl rfl rfl rfl rfl
      · contradiction
    · contradiction

-- ============================================================================
-- §6  Notification-binding arms (`.tcbBindNotification`, `.tcbUnbindNotification`)
-- ============================================================================

/-- A notification store keeps the capability half of the badge conjunct: a
notification holds no capability slot. -/
theorem capabilityBadgesWellFormed_of_notificationStore {st st1 : SystemState}
    {nid : SeLe4n.ObjId} {ntfn ntfn' : Notification}
    (hObjInv : st.objects.invExt) (h : capabilityBadgesWellFormed st)
    (hPre : st.objects[nid]? = some (.notification ntfn))
    (hStore : storeObject nid (.notification ntfn') st = .ok ((), st1)) :
    capabilityBadgesWellFormed st1 :=
  capabilityBadgesWellFormed_of_slotCap_back h
    (slotCap_back_of_storeObject hObjInv hPre hStore rfl)

/-- A thread store that keeps the thread's capability slots keeps the capability
half of the badge conjunct. -/
theorem capabilityBadgesWellFormed_of_tcbSlotsStore {st st1 : SystemState}
    {key : SeLe4n.ObjId} {t t' : TCB}
    (hObjInv : st.objects.invExt) (h : capabilityBadgesWellFormed st)
    (hPre : st.objects[key]? = some (.tcb t))
    (hStore : storeObject key (.tcb t') st = .ok ((), st1))
    (hCells : t'.spaceCells = t.spaceCells) :
    capabilityBadgesWellFormed st1 :=
  capabilityBadgesWellFormed_of_slotCap_back h
    (slotCap_back_of_storeObject hObjInv hPre hStore (by
      funext sl; simp only [KernelObject.slotCap, TCB.spaceSlotCap, hCells]))

/-- An absent bound-thread code is the zero code. -/
theorem Notification.boundTCBCode_eq_zero {n : Notification} (h : n.boundTCB.isSome = false) :
    n.boundTCBCode = 0 := by
  cases hc : n.boundTCBCode with
  | zero => rfl
  | succ k => simp [Notification.boundTCB, hc, SeLe4n.ThreadId.ofOptCode] at h

/-- An absent bound-notification code is the zero code. -/
theorem TCB.boundNotificationCode_eq_zero {t : TCB} (h : t.boundNotification.isSome = false) :
    t.boundNotificationCode = 0 := by
  cases hc : t.boundNotificationCode with
  | zero => rfl
  | succ k => simp [TCB.boundNotification, hc, SeLe4n.ObjId.ofOptCode] at h

/-- A bound notification is the code's object. -/
theorem TCB.boundNotificationCode_eq_succ {t : TCB} {nid : SeLe4n.ObjId}
    (h : t.boundNotification = some nid) : t.boundNotificationCode = nid.val + 1 := by
  cases hc : t.boundNotificationCode with
  | zero => simp [TCB.boundNotification, hc, SeLe4n.ObjId.ofOptCode] at h
  | succ k =>
    simp only [TCB.boundNotification, hc, SeLe4n.ObjId.ofOptCode, Option.some.injEq] at h
    rw [← h]

/-- `.tcbBindNotification`: the bind writes the notification's bound-thread code
and the thread's bound-notification code — fields only the reciprocity reads —
so the other conjuncts transport across both stores, and the reciprocity holds
of the post-state because the two codes now name each other and both were zero
before (`notificationBindingReciprocal.of_bindCodes`). -/
theorem bindNotification_preserves_ipcInvariantFull
    (st st' : SystemState) (nid : SeLe4n.ObjId) (tcbId : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hStep : bindNotification nid tcbId st = .ok ((), st')) :
    ipcInvariantFull st' := by
  unfold bindNotification at hStep
  split at hStep
  · rename_i ntfn hN
    split at hStep
    · contradiction
    · rename_i tcb hT
      split at hStep
      · contradiction
      · rename_i hFree
        split at hStep
        · contradiction
        · rename_i st1 hStore1
          split at hStep
          · contradiction
          · rename_i st2 hStore2
            cases hStep
            simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hFree
            have hNraw := (SystemState.getNotification?_eq_some_iff st nid ntfn).mp hN
            have hTraw := lookupTcb_some_objects st tcbId tcb hT
            have hNeIds : tcbId.toObjId ≠ nid := by
              intro hEq
              rw [hEq, hNraw] at hTraw
              exact absurd (Option.some.inj hTraw) (fun hx => KernelObject.noConfusion hx)
            have hObjInv1 := storeObject_preserves_objects_invExt st _ nid _ hObjInv hStore1
            have hAt1 := storeObject_objects_eq st _ nid _ hObjInv hStore1
            have hNe1 : ∀ oid : SeLe4n.ObjId, oid ≠ nid → st1.objects[oid]? = st.objects[oid]? :=
              fun oid h => storeObject_objects_ne st _ nid oid _ h hObjInv hStore1
            have hT1 : st1.objects[tcbId.toObjId]? = some (.tcb tcb) := (hNe1 _ hNeIds).trans hTraw
            have hAt2 := storeObject_objects_eq _ _ tcbId.toObjId _ hObjInv1 hStore2
            have hNe2 : ∀ oid : SeLe4n.ObjId, oid ≠ tcbId.toObjId →
                st'.objects[oid]? = st1.objects[oid]? :=
              fun oid h => storeObject_objects_ne _ _ tcbId.toObjId oid _ h hObjInv1 hStore2
            have hView := (ipcReadViewAgreement.of_notification_content_write hNraw hAt1 hNe1
              rfl rfl rfl).trans (ipcReadViewAgreement.of_tcb_ipcReadView_write hT1 hAt2 hNe2 rfl)
            have hCap := capabilityBadgesWellFormed_of_tcbSlotsStore hObjInv1
              (capabilityBadgesWellFormed_of_notificationStore hObjInv hInv.badgeWellFormed.2 hNraw
                hStore1) hT1 hStore2 rfl
            have hNBR : notificationBindingReciprocal st' :=
              notificationBindingReciprocal.of_bindCodes hInv.notificationBindingReciprocal hNeIds
                (by rw [hTraw]; simp only [notificationBindingCodes, KernelObject.bindingCodes,
                  TCB.boundNotificationCode_eq_zero hFree.2])
                (by rw [hNraw]; simp only [notificationBindingCodes, KernelObject.bindingCodes,
                  Notification.boundTCBCode_eq_zero hFree.1])
                (by rw [hAt2]; rfl)
                (by rw [hNe2 _ (Ne.symm hNeIds), hAt1]; rfl)
                (fun k hk1 hk2 => by rw [hNe2 k hk1, hNe1 k hk2])
            exact ipcInvariantFull_of_readViewAgreement_of_reciprocal hView hCap hNBR hInv
  · split at hStep <;> contradiction

/-- `.tcbUnbindNotification`: the unbind clears both directions of the binding.
The reciprocity is what makes the notification present: the thread's bound
notification names it back, so the fail-safe arm (notification gone) is
unreachable from a state satisfying the bundle, and the two cleared codes were
exactly each other's (`notificationBindingReciprocal.of_unbindCodes`). -/
theorem unbindNotification_preserves_ipcInvariantFull
    (st st' : SystemState) (tcbId : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hStep : unbindNotification tcbId st = .ok ((), st')) :
    ipcInvariantFull st' := by
  unfold unbindNotification at hStep
  split at hStep
  · contradiction
  · rename_i tcb hT
    split at hStep
    · contradiction
    · rename_i nid hBound
      split at hStep
      · contradiction
      · rename_i st1 hStore1
        have hTraw := lookupTcb_some_objects st tcbId tcb hT
        have hCode := TCB.boundNotificationCode_eq_succ hBound
        obtain ⟨n0, hN0, hN0c⟩ :=
          hInv.notificationBindingReciprocal.tcb hTraw (c := nid.val) hCode
        have hNraw : st.objects[nid]? = some (.notification n0) := hN0
        have hNeIds : tcbId.toObjId ≠ nid := by
          intro hEq
          rw [hEq, hNraw] at hTraw
          exact absurd (Option.some.inj hTraw) (fun hx => KernelObject.noConfusion hx)
        have hObjInv1 := storeObject_preserves_objects_invExt st _ tcbId.toObjId _
          hObjInv hStore1
        have hAt1 := storeObject_objects_eq st _ tcbId.toObjId _ hObjInv hStore1
        have hNe1 : ∀ oid : SeLe4n.ObjId, oid ≠ tcbId.toObjId →
            st1.objects[oid]? = st.objects[oid]? :=
          fun oid h => storeObject_objects_ne st _ tcbId.toObjId oid _ h hObjInv hStore1
        have hN1 : st1.objects[nid]? = some (.notification n0) :=
          (hNe1 _ (Ne.symm hNeIds)).trans hNraw
        split at hStep
        · rename_i ntfn hN1'
          have hN1raw := (SystemState.getNotification?_eq_some_iff _ nid ntfn).mp hN1'
          rw [hN1] at hN1raw; cases hN1raw
          split at hStep
          · contradiction
          · rename_i st2 hStore2
            cases hStep
            have hAt2 := storeObject_objects_eq _ _ nid _ hObjInv1 hStore2
            have hNe2 : ∀ oid : SeLe4n.ObjId, oid ≠ nid → st'.objects[oid]? = st1.objects[oid]? :=
              fun oid h => storeObject_objects_ne _ _ nid oid _ h hObjInv1 hStore2
            have hView := (ipcReadViewAgreement.of_tcb_ipcReadView_write hTraw hAt1 hNe1 rfl).trans
              (ipcReadViewAgreement.of_notification_content_write hN1 hAt2 hNe2 rfl rfl rfl)
            have hCap := capabilityBadgesWellFormed_of_notificationStore hObjInv1
              (capabilityBadgesWellFormed_of_tcbSlotsStore hObjInv hInv.badgeWellFormed.2 hTraw
                hStore1 rfl) hN1 hStore2
            have hNBR : notificationBindingReciprocal st' :=
              notificationBindingReciprocal.of_unbindCodes hInv.notificationBindingReciprocal
                (t := tcbId.toObjId) (n := nid)
                (by rw [hTraw]; simp only [notificationBindingCodes, KernelObject.bindingCodes,
                  hCode])
                (by rw [hNraw]; simp only [notificationBindingCodes, KernelObject.bindingCodes,
                  hN0c])
                (by rw [hNe2 _ hNeIds, hAt1]; rfl)
                (by rw [hAt2]; rfl)
                (fun k hk1 hk2 => by rw [hNe2 k hk2, hNe1 k hk1])
            exact ipcInvariantFull_of_readViewAgreement_of_reciprocal hView hCap hNBR hInv
        · rename_i hNone
          rw [(SystemState.getNotification?_eq_some_iff _ nid n0).mpr hN1] at hNone
          cases hNone

-- ============================================================================
-- §7  Priority arms (`.tcbSetPriority`, `.tcbSetMCPriority`)
-- ============================================================================

/-- Self-lookup on the raw record update several priority-path operations use
in place of `storeObject`. -/
theorem insertObjects_getElem_self (st : SystemState) (k : SeLe4n.ObjId)
    (v : KernelObject) (hObjInv : st.objects.invExt) :
    ({ st with objects := st.objects.insert k v } : SystemState).objects[k]? = some v := by
  simp only [RHTable_getElem?_eq_get?]
  exact RobinHood.RHTable.getElem?_insert_self st.objects k v hObjInv

/-- Off-key lookups on the raw record update are untouched. -/
theorem insertObjects_getElem_ne (st : SystemState) (k : SeLe4n.ObjId)
    (v : KernelObject) (oid : SeLe4n.ObjId) (hNe : oid ≠ k)
    (hObjInv : st.objects.invExt) :
    ({ st with objects := st.objects.insert k v } : SystemState).objects[oid]?
      = st.objects[oid]? := by
  simp only [RHTable_getElem?_eq_get?]
  exact RobinHood.RHTable.getElem?_insert_ne st.objects k oid v
    (by simp only [beq_iff_eq]; exact fun h => hNe h.symm) hObjInv

/-- WS-RR RR2.16 (helper): a TCB store that leaves `replyObject` and `ipcState`
alone preserves the bidirectional reply linkage.  Neither clause can move: the
forward clause reads the stored thread's `replyObject` (unchanged) and the Reply
object (a different key, so untouched), and the backward clause reads the Reply
and then the thread's `replyObject` and `ipcState` (both unchanged).

The reply-linkage counterpart of
`storeObject_tcb_preserveIpc_preserves_endpointQueueTailBlockedConsistent`; it
did not exist because until RR2.16 no bundle needed a *stash-only* TCB store to
carry the linkage. -/
theorem storeObject_tcb_preserveReplyLinkFields_preserves_replyCallerLinkage
    (st st' : SystemState) (tid₀ : SeLe4n.ThreadId) (oldTcb newTcb : TCB)
    (hObjInv : st.objects.invExt)
    (hOld : st.getTcb? tid₀ = some oldTcb)
    (hSameReply : newTcb.replyObject = oldTcb.replyObject)
    (hSameIpc : newTcb.ipcState = oldTcb.ipcState)
    (hInv : replyCallerLinkage st)
    (hStore : storeObject tid₀.toObjId (.tcb newTcb) st = .ok ((), st')) :
    replyCallerLinkage st' := by
  have hEqAt := storeObject_objects_eq st st' tid₀.toObjId (.tcb newTcb) hObjInv hStore
  have hOldRaw := (getTcb?_eq_some_iff st tid₀ oldTcb).mp hOld
  have hFrame : ∀ x, x ≠ tid₀.toObjId → st'.objects[x]? = st.objects[x]? :=
    fun x hNe => storeObject_objects_ne st st' tid₀.toObjId x (.tcb newTcb) hNe hObjInv hStore
  -- Every post-state TCB has a pre-state twin agreeing on `replyObject` / `ipcState`.
  have hBack : ∀ (t : SeLe4n.ThreadId) (tcbT : TCB),
      st'.getTcb? t = some tcbT →
      ∃ tcbT', st.getTcb? t = some tcbT' ∧
        tcbT'.replyObject = tcbT.replyObject ∧ tcbT'.ipcState = tcbT.ipcState := by
    intro t tcbT hTt
    have hT := (getTcb?_eq_some_iff st' t tcbT).mp hTt
    by_cases hEq : t.toObjId = tid₀.toObjId
    · rw [hEq, hEqAt] at hT
      obtain rfl : newTcb = tcbT := by
        simpa only [Option.some.injEq, KernelObject.tcb.injEq] using hT
      exact ⟨oldTcb, by rw [getTcb?_eq_some_iff, hEq]; exact hOldRaw,
        hSameReply.symm, hSameIpc.symm⟩
    · rw [hFrame t.toObjId hEq] at hT
      exact ⟨tcbT, (getTcb?_eq_some_iff st t tcbT).mpr hT, rfl, rfl⟩
  -- And every pre-state TCB has a post-state twin agreeing on the same two fields.
  have hFwd : ∀ (t : SeLe4n.ThreadId) (tcbT : TCB),
      st.getTcb? t = some tcbT →
      ∃ tcbT', st'.getTcb? t = some tcbT' ∧
        tcbT'.replyObject = tcbT.replyObject ∧ tcbT'.ipcState = tcbT.ipcState := by
    intro t tcbT hTt
    have hT := (getTcb?_eq_some_iff st t tcbT).mp hTt
    by_cases hEq : t.toObjId = tid₀.toObjId
    · rw [hEq] at hT
      obtain rfl : oldTcb = tcbT := by
        simpa only [Option.some.injEq, KernelObject.tcb.injEq] using hOldRaw.symm.trans hT
      exact ⟨newTcb, by rw [getTcb?_eq_some_iff, hEq]; exact hEqAt, hSameReply, hSameIpc⟩
    · exact ⟨tcbT, by rw [getTcb?_eq_some_iff, hFrame t.toObjId hEq]; exact hT, rfl, rfl⟩
  -- Reply objects live at a different key from the stored TCB, so they read through.
  have hReplyFrame : ∀ (rid : SeLe4n.ReplyId) (r : Reply),
      st'.objects[rid.toObjId]? = some (.reply r) ↔ st.objects[rid.toObjId]? = some (.reply r) := by
    intro rid r
    by_cases hEq : rid.toObjId = tid₀.toObjId
    · rw [hEq, hEqAt, hOldRaw]
      constructor <;> (intro h; cases h)
    · rw [hFrame rid.toObjId hEq]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro tid tcb rid hTcb' hRO
    obtain ⟨tcb0, hTcb0, hRO0, _⟩ := hBack tid tcb ((getTcb?_eq_some_iff st' tid tcb).mpr hTcb')
    obtain ⟨r, hr, hrc⟩ := hInv.1.1 tid tcb0 rid ((getTcb?_eq_some_iff st tid tcb0).mp hTcb0)
      (hRO0.trans hRO)
    exact ⟨r, (hReplyFrame rid r).mpr hr, hrc⟩
  · intro rid r tid hr' hrc
    obtain ⟨tcb0, hTcb0, hRO0, hBlk0⟩ := hInv.1.2 rid r tid ((hReplyFrame rid r).mp hr') hrc
    obtain ⟨tcb', hTcb', hROeq, hIpcEq⟩ :=
      hFwd tid tcb0 ((getTcb?_eq_some_iff st tid tcb0).mpr hTcb0)
    obtain ⟨ep, rt, hIpc⟩ := hBlk0
    exact ⟨tcb', (getTcb?_eq_some_iff st' tid tcb').mp hTcb', hROeq.trans hRO0,
      ⟨ep, rt, hIpcEq.trans hIpc⟩⟩
  · intro tid tcb ep rt hTcb' hBlk
    obtain ⟨tcb0, hTcb0, hRO0, hIpc0⟩ := hBack tid tcb ((getTcb?_eq_some_iff st' tid tcb).mpr hTcb')
    obtain ⟨rid, hRid⟩ := hInv.2 tid tcb0 ep rt ((getTcb?_eq_some_iff st tid tcb0).mp hTcb0)
      (hIpc0.trans hBlk)
    exact ⟨rid, hRO0 ▸ hRid⟩

/-- **Clearing a thread's reply stash keeps the bundle**: one TCB stored with
`pendingReceiveReply := none` and nothing else changed.  The structural
conjuncts read no stash (`storeObject_tcb_pendingReceiveReply_preserves_ipcInvariantCore`);
the reply linkage reads `replyObject` and `ipcState`, both kept; and
`pendingReceiveReplyWellFormed`, the one conjunct that reads the stash, only
loses an obligation.  The dispatch's post-wake clear
(`clearWokenReceiverStash`) and a stashed reply's finalisation
(`finaliseReplyUnstash`) are both this store. -/
theorem storeObject_stashCleared_preserves_ipcInvariantFull
    (st st' : SystemState) (receiver : SeLe4n.ThreadId) (rTcb : TCB)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hTcb : st.getTcb? receiver = some rTcb)
    (hStep : storeObject receiver.toObjId (.tcb { rTcb with pendingReceiveReplyCode := 0 }) st =
      .ok ((), st')) :
    ipcInvariantFull st' :=
  have hRaw := (getTcb?_eq_some_iff st receiver rTcb).mp hTcb
  ipcInvariantFull_of_core_replyCallerLinkage
    (storeObject_tcb_pendingReceiveReply_preserves_ipcInvariantCore st st'
      receiver.toObjId rTcb none hInv.toCore hObjInv hRaw hStep)
    (storeObject_tcb_preserveReplyLinkFields_preserves_replyCallerLinkage st st'
      receiver rTcb { rTcb with pendingReceiveReplyCode := 0 } hObjInv hTcb rfl rfl
      hInv.replyCallerLinkage hStep)
    (storeObject_tcb_preserves_pendingReceiveReplyWellFormed st st' receiver rTcb
      { rTcb with pendingReceiveReplyCode := 0 } hObjInv hTcb
      hInv.pendingReceiveReplyWellFormed
      (fun rid' h => by cases h) (fun rid' h => by cases h) (fun rid' h => by cases h) hStep)
    (donationOwnerUnique_of_sameSchedContextBindings
      (storeObject_modifiedTcb_sameSchedContextBindings st st' receiver.toObjId rTcb
        { rTcb with pendingReceiveReplyCode := 0 } hRaw rfl hObjInv hStep)
      hInv.donationOwnerUnique)
    (storeObject_tcb_preserveIpc_preserves_endpointQueueTailBlockedConsistent st st'
      receiver rTcb { rTcb with pendingReceiveReplyCode := 0 } hObjInv hRaw rfl
      hInv.endpointQueueTailBlockedConsistent hStep)
    (storeObject_tcb_preserveIpcAndQueueNext_preserves_queueNextTargetBlocked st st'
      receiver rTcb { rTcb with pendingReceiveReplyCode := 0 } hObjInv hRaw rfl rfl
      hInv.queueNextTargetBlocked hStep)
    (notificationBindingReciprocal.of_codes
      (sameNotificationBindings.of_storeObject_tcb
        (t' := { rTcb with pendingReceiveReplyCode := 0 }) hObjInv hRaw rfl hStep)
      hInv.notificationBindingReciprocal)
    (storeObject_tcb_preserveIpcAndQueueNext_preserves_endpointQueueLinksOnlyBlocked st st'
      receiver rTcb { rTcb with pendingReceiveReplyCode := 0 } hObjInv hRaw rfl rfl
      hInv.endpointQueueLinksOnlyBlocked hStep)

/-- Raw-insert form of the one-TCB-rewrite bundle lever. -/
theorem insertObjects_tcbFieldUpdate_preserves_ipcInvariantFull
    (st : SystemState) (tid : SeLe4n.ThreadId) (tcb tcb' : TCB)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hPre : st.objects[tid.toObjId]? = some (.tcb tcb))
    (hIpc : tcb'.ipcState = tcb.ipcState)
    (hMsg : tcb'.pendingMessage = tcb.pendingMessage)
    (hNext : tcb'.queueNext = tcb.queueNext)
    (hPrev : tcb'.queuePrev = tcb.queuePrev)
    (hPPrev : tcb'.queuePPrev = tcb.queuePPrev)
    (hBudget : tcb'.timeoutBudget = tcb.timeoutBudget)
    (hReply : tcb'.replyObject = tcb.replyObject)
    (hStash : tcb'.pendingReceiveReply = tcb.pendingReceiveReply)
    (hBind : tcb'.schedContextBinding = tcb.schedContextBinding)
    (hSlots : ∀ (sl : SeLe4n.Slot) (c : Capability) (b : SeLe4n.Badge),
      tcb'.spaceSlotCap sl = some c → c.badge = some b → tcb.spaceSlotCap sl = some c :=
      by intro _ _ _ h _; exact h)
    (hBnc : tcb'.boundNotificationCode = tcb.boundNotificationCode := by rfl) :
    ipcInvariantFull { st with objects := st.objects.insert tid.toObjId (.tcb tcb') } := by
  have hAt := insertObjects_getElem_self st tid.toObjId (.tcb tcb') hObjInv
  have hFrame : ∀ oid : SeLe4n.ObjId, oid ≠ tid.toObjId →
      ({ st with objects := st.objects.insert tid.toObjId (.tcb tcb') }
        : SystemState).objects[oid]? = st.objects[oid]? :=
    fun oid hNe => insertObjects_getElem_ne st tid.toObjId (.tcb tcb') oid hNe hObjInv
  exact ipcInvariantFull_of_tcbFieldUpdate st _ tid.toObjId tcb tcb'
    hInv hPre hAt hFrame hIpc hMsg hNext hPrev hPPrev hBudget hReply hStash hBind
    hSlots hBnc

/-- Raw-insert form of the SchedContext-content bundle lever. -/
theorem insertObjects_schedContextContentUpdate_preserves_ipcInvariantFull
    (st : SystemState) (scId : SeLe4n.SchedContextId)
    (sc sc' : SeLe4n.Kernel.SchedContext)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hPre : st.objects[scId.toObjId]? = some (.schedContext sc))
    (hBound : sc'.boundThread = sc.boundThread) :
    ipcInvariantFull
      { st with objects := st.objects.insert scId.toObjId (.schedContext sc') } := by
  have hAt := insertObjects_getElem_self st scId.toObjId (.schedContext sc') hObjInv
  have hNe : ∀ oid : SeLe4n.ObjId, oid ≠ scId.toObjId →
      ({ st with objects := st.objects.insert scId.toObjId (.schedContext sc') }
        : SystemState).objects[oid]? = st.objects[oid]? :=
    fun oid h => insertObjects_getElem_ne st scId.toObjId (.schedContext sc') oid h hObjInv
  have hView := ipcReadViewAgreement.of_schedContext_content_write hPre hAt hNe hBound
  have hCodes := sameNotificationBindings.of_schedContext_content_write hPre hAt hNe hBound
  have hBack : ∀ (tid : SeLe4n.ThreadId) (tcb' : TCB),
      ({ st with objects := st.objects.insert scId.toObjId (.schedContext sc') }
        : SystemState).objects[tid.toObjId]? = some (.tcb tcb') →
      ∃ tcb, st.objects[tid.toObjId]? = some (.tcb tcb) ∧
        tcb.ipcState = tcb'.ipcState ∧ tcb.schedContextBinding = tcb'.schedContextBinding := by
    intro tid tcb' h
    by_cases hK : tid.toObjId = scId.toObjId
    · rw [hK, hAt] at h
      exact absurd (Option.some.inj h) (fun hx => KernelObject.noConfusion hx)
    · rw [hNe _ hK] at h
      exact ⟨tcb', h, rfl, rfl⟩
  have hCap : capabilityBadgesWellFormed
      { st with objects := st.objects.insert scId.toObjId (.schedContext sc') } := by
    intro oid cn slot cap badge hCn hLk hB
    by_cases hK : oid = scId.toObjId
    · rw [hK, hAt] at hCn
      cases Option.some.inj hCn; simp [KernelObject.slotCap] at hLk
    · rw [hNe _ hK] at hCn
      exact hInv.badgeWellFormed.2 oid cn slot cap badge hCn hLk hB
  exact ipcInvariantFull_of_readViewAgreement hView hCodes hCap hInv

/-- Reduction of `updatePrioritySource` at a binding with **no** priority
source — `.unbound` and, since WS-OD (v0.35.3), `.donated`.  Both write the
thread's own TCB — through the typed rewrite since `v0.35.71`, so the reduction
takes the store's witness for the record the operation was handed. -/
private theorem updatePrioritySource_tcbTarget_eq (st : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (p : SeLe4n.Priority)
    (hB : tcb.schedContextBinding.ownScId? = none)
    (hPre : st.objects[tid.toObjId]? = some (.tcb tcb)) :
    SchedContext.PriorityManagement.updatePrioritySource st tid tcb p
      = { st with objects := st.objects.insert tid.toObjId (.tcb { tcb with priority := p }) } := by
  unfold SchedContext.PriorityManagement.updatePrioritySource
  rw [hB]
  exact SystemState.updateTcb_eq_of_some
    ((SystemState.getTcb?_eq_some_iff st tid tcb).mpr hPre) _

/-- Reduction of `updatePrioritySource` at a binding that **does** name a
priority source — `.bound scId`, and only that since WS-OD (v0.35.3).

**`v0.35.98`: that arm is a PAIR of writes**, the reservation and the thread,
because the base priority of a `.bound` thread has two homes and the syscall
must move both (see the operation's own docstring).  The reduction is therefore
to the composed typed updates rather than to a single insert; each half is an
identity where its object is absent, so no presence hypothesis is needed here
and the two `_sc_eq` / `_sc_none_eq` reductions this replaces — which described
a one-object write — are gone rather than given a second object. -/
private theorem updatePrioritySource_bound_eq (st : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (p : SeLe4n.Priority)
    (scId : SeLe4n.SchedContextId)
    (hB : tcb.schedContextBinding.ownScId? = some scId) :
    SchedContext.PriorityManagement.updatePrioritySource st tid tcb p
      = (st.updateSchedContext scId fun sc => { sc with priority := p }).updateTcb tid
          fun t => { t with priority := p } := by
  unfold SchedContext.PriorityManagement.updatePrioritySource
  rw [hB]

/-- `updatePrioritySource` writes a priority field — on the thread's own TCB
unless the binding names a priority source, in which case on that SchedContext —
and priority is a field no conjunct reads.  The case split is on the classifier
rather than on the binding, so the two arms are exactly the operation's. -/
theorem updatePrioritySource_preserves_ipcInvariantFull
    (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB) (p : SeLe4n.Priority)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hPre : st.objects[tid.toObjId]? = some (.tcb tcb)) :
    ipcInvariantFull (SchedContext.PriorityManagement.updatePrioritySource st tid tcb p) := by
  cases hB : tcb.schedContextBinding.ownScId? with
  | none =>
      rw [updatePrioritySource_tcbTarget_eq st tid tcb p hB hPre]
      exact insertObjects_tcbFieldUpdate_preserves_ipcInvariantFull st tid tcb
        { tcb with priority := p } hObjInv hInv hPre rfl rfl rfl rfl rfl rfl rfl rfl rfl
  | some scId =>
      -- `v0.35.98`: two writes, so two preservation steps — the reservation at
      -- `st`, the thread at the reservation-written state.  The thread's record
      -- survives the first because a SchedContext rewrite is invisible to every
      -- TCB lookup **at every key** (`updateSchedContext_getTcb?`), so no
      -- key-distinctness side condition enters the argument.
      have hObjInv1 :
          (st.updateSchedContext scId fun sc => { sc with priority := p }).objects.invExt :=
        SystemState.updateSchedContext_preserves_objects_invExt st scId _ hObjInv
      have hGet1 :
          (st.updateSchedContext scId fun sc => { sc with priority := p }).getTcb? tid
            = some tcb := by
        rw [SystemState.updateSchedContext_getTcb? st scId _ hObjInv tid]
        exact (SystemState.getTcb?_eq_some_iff st tid tcb).mpr hPre
      have hPre1 :
          (st.updateSchedContext scId fun sc => { sc with priority := p }).objects[tid.toObjId]?
            = some (.tcb tcb) :=
        (SystemState.getTcb?_eq_some_iff _ tid tcb).mp hGet1
      have hInv1 :
          ipcInvariantFull (st.updateSchedContext scId fun sc => { sc with priority := p }) := by
        cases hSc : st.getSchedContext? scId with
        | some sc =>
            rw [SystemState.updateSchedContext_eq_of_some hSc]
            exact insertObjects_schedContextContentUpdate_preserves_ipcInvariantFull st scId
              sc { sc with priority := p } hObjInv hInv
              ((SystemState.getSchedContext?_eq_some_iff st scId sc).mp hSc) rfl
        | none => rw [SystemState.updateSchedContext_eq_self_of_none hSc]; exact hInv
      rw [updatePrioritySource_bound_eq st tid tcb p scId hB,
        SystemState.updateTcb_eq_of_some hGet1]
      exact insertObjects_tcbFieldUpdate_preserves_ipcInvariantFull _ tid tcb
        { tcb with priority := p } hObjInv1 hInv1 hPre1 rfl rfl rfl rfl rfl rfl rfl rfl rfl

/-- The bucket re-key changes no thread's run-queue membership on any core. -/
theorem migrateRunQueueBucketOnCore_mem_runQueueOnCore (st : SystemState)
    (tid : SeLe4n.ThreadId) (p : SeLe4n.Priority) (c c' : CoreId) (x : SeLe4n.ThreadId) :
    x ∈ (SchedContext.PriorityManagement.migrateRunQueueBucketOnCore
          st tid p c).scheduler.runQueueOnCore c'
      ↔ x ∈ st.scheduler.runQueueOnCore c' := by
  simp only [SchedContext.PriorityManagement.migrateRunQueueBucketOnCore]
  split
  · rw [SystemState.runRequeueOnCore_scheduler]
    by_cases hcc : c = c'
    · subst hcc
      rw [SchedulerState.setRunQueueOnCore_runQueueOnCore_self, RunQueue.mem_rekey]
    · rw [SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ c c' _ hcc,
        SchedulerState.setRunQueueEndsOnCore_runQueueOnCore]
  · exact Iff.rfl

/-- The bucket re-key repoints no core's `current` slot. -/
theorem migrateRunQueueBucketOnCore_currentOnCore (st : SystemState)
    (tid : SeLe4n.ThreadId) (p : SeLe4n.Priority) (c c' : CoreId) :
    (SchedContext.PriorityManagement.migrateRunQueueBucketOnCore
        st tid p c).scheduler.currentOnCore c'
      = st.scheduler.currentOnCore c' := by
  simp only [SchedContext.PriorityManagement.migrateRunQueueBucketOnCore]
  split <;> simp

/-- The bucket re-key preserves the whole bundle: no object and no membership
moves, only a queue's internal keying. -/
theorem migrateRunQueueBucketOnCore_preserves_ipcInvariantFull (st : SystemState)
    (tid : SeLe4n.ThreadId) (p : SeLe4n.Priority) (c : CoreId)
    (hInv : ipcInvariantFull st) :
    ipcInvariantFull (SchedContext.PriorityManagement.migrateRunQueueBucketOnCore
      st tid p c) := by
  have hA := SchedContext.PriorityManagement.migrateRunQueueBucketOnCore_objectsAgreeOffRunLinks
    st tid p c
  exact ipcInvariantFull_of_objectsAgreeOffRunLinks hA hInv

-- ============================================================================
-- §8  Affinity arm (`.tcbSetAffinity`)
-- ============================================================================

-- RETIRED at WS-RR RR8.16 (`v0.35.197`): `migrateSchedContextReplenishment_currentOnCore`
-- was a second answer to a question `SchedContext/ReplenishAffinity.lean` -- the
-- module that declares the migration -- already answers as
-- `migrateSchedContextReplenishment_runQueue_current_eq`, whose `.2` is this
-- statement verbatim.  It had one consumer, in this module, and it sat outside
-- the closure of every asker upstream: `Scheduler/Invariant/PerCore.lean` needed
-- exactly this fact for the base-invariant lift and could not see it, which is
-- how the duplicate was found.  Callers use `(…_runQueue_current_eq …).2`.

/-- The replenishment migration preserves the whole bundle: it writes
release-queue links alone, which the bundle does not read. -/
theorem migrateSchedContextReplenishment_preserves_ipcInvariantFull (st : SystemState)
    (scId : SeLe4n.SchedContextId) (fromCore toCore : CoreId)
    (hInv : ipcInvariantFull st) :
    ipcInvariantFull (migrateSchedContextReplenishment st scId fromCore toCore) := by
  exact ipcInvariantFull_of_objectsAgreeOffSchedulerLinks
    (.of_releaseLinks (migrateSchedContextReplenishment_agree st scId fromCore toCore)) hInv

/-- The affinity run-queue migration preserves the whole bundle: it moves only
run-queue links and queue membership, which no conjunct reads. -/
theorem migrateRunQueueOnAffinityChange_preserves_ipcInvariantFull (st : SystemState)
    (tid : SeLe4n.ThreadId) (fromCore toCore : CoreId)
    (hInv : ipcInvariantFull st) :
    ipcInvariantFull (migrateRunQueueOnAffinityChange st tid fromCore toCore) := by
  have hA := migrateRunQueueOnAffinityChange_objectsAgreeOffRunLinks st tid fromCore toCore
  exact ipcInvariantFull_of_objectsAgreeOffRunLinks hA hInv

/-- `.tcbSetAffinity`: the affinity write is a one-TCB rewrite of a field no
conjunct reads; the replenishment and run-queue migrations that follow the
thread to its new home core move only run-queue links, so the whole bundle
transports. -/
theorem setThreadCpuAffinityWithMigration_preserves_ipcInvariantFull
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (affinity : Option CoreId)
    (ec : CoreId) (sgi : Option (CoreId × Concurrency.SgiKind))
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hStep : setThreadCpuAffinityWithMigration st tid affinity ec = .ok (st', sgi)) :
    ipcInvariantFull st' := by
  obtain ⟨tcb, stSet, hT, -, -, -, hSet, rfl, -⟩ := setThreadCpuAffinityWithMigration_ok_shape hStep
  -- WS-ZA ZA6.3: the vacate writes the scheduler alone.
  have hInvV := ipcInvariantFull_of_objectsAgreeOffRunLinks
    (vacateForAffinityChange_objectsAgreeOffRunLinks st tid
      (determineTargetCore st tid) (affinity.getD bootCoreId)) hInv
  have hObjInvV : (vacateForAffinityChange st tid (determineTargetCore st tid)
      (affinity.getD bootCoreId)).objects.invExt := by
    rw [vacateForAffinityChange_objects]; exact hObjInv
  have hTV : (vacateForAffinityChange st tid (determineTargetCore st tid)
      (affinity.getD bootCoreId)).getTcb? tid = some tcb := by
    rw [vacateForAffinityChange_getTcb?]; exact hT
  generalize vacateForAffinityChange st tid (determineTargetCore st tid)
    (affinity.getD bootCoreId) = sv at hSet hInvV hObjInvV hTV
  have hSetEq : stSet =
      { sv with objects := sv.objects.insert tid.toObjId (.tcb { tcb with cpuAffinity := affinity }) } := by
    unfold setThreadCpuAffinity at hSet
    rw [SystemState.getTcbWitnessed?_eq_some hTV] at hSet
    exact (Except.ok.inj hSet).symm
  subst hSetEq
  have hPreRaw := (SystemState.getTcb?_eq_some_iff _ tid tcb).mp hTV
  have hInvSet := insertObjects_tcbFieldUpdate_preserves_ipcInvariantFull _ tid
    tcb { tcb with cpuAffinity := affinity } hObjInvV hInvV hPreRaw
    rfl rfl rfl rfl rfl rfl rfl rfl rfl
  apply ipcInvariantFull_of_objectsAgreeOffRunLinks
    (requeueVacatedOnNewHome_objectsAgreeOffRunLinks _ _ _ _)
  cases hScid : tcb.schedContextBinding.scId? with
  | some scId =>
      exact migrateRunQueueOnAffinityChange_preserves_ipcInvariantFull _ _ _ _
        (migrateSchedContextReplenishment_preserves_ipcInvariantFull _ _ _ _ hInvSet)
  | none =>
      exact migrateRunQueueOnAffinityChange_preserves_ipcInvariantFull _ _ _ _ hInvSet

theorem setThreadCpuAffinityOnCore_preserves_ipcInvariantFull
    (st st' : SystemState) (vtid : SeLe4n.ValidThreadId) (affinity : Option CoreId)
    (ec : CoreId) (sgi : Option (CoreId × Concurrency.SgiKind))
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hStep : setThreadCpuAffinityOnCore st vtid affinity ec = .ok (st', sgi)) :
    ipcInvariantFull st' :=
  setThreadCpuAffinityWithMigration_preserves_ipcInvariantFull st st' vtid.val affinity ec sgi
    hObjInv hInv hStep

-- ============================================================================
-- §9  Capability arms (`.cspaceDelete`, `.cspaceMint`, `.cspaceCopy`,
--     `.cspaceMove`, `.mintReplyCap`)
-- ============================================================================

-- **WS-RR RR8.16** (`v0.35.201`): `cspaceInsertSlot_cnode_shape` was declared
-- here, `private`, re-deriving the insert's success shape from the operation's
-- own `match` tree.  It is `SeLe4n.Kernel.cspaceInsertSlot_objects_eq` now, in
-- `Kernel/Capability/Operations.lean` beside the primitive and beside the
-- "every other key" half of the same frame.

/-- `cspaceInsertSlot` preserves the whole bundle: its one object write is a
CNode, and the inserted capability's badge is valid. -/
theorem cspaceInsertSlot_preserves_ipcInvariantFull
    (st st' : SystemState) (addr : CSpaceAddr) (cap : Capability)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hCapValid : ∀ b, cap.badge = some b → b.valid)
    (hStep : cspaceInsertSlot addr cap st = .ok ((), st')) :
    ipcInvariantFull st' := by
  obtain ⟨cn, hPre, hAt⟩ := cspaceInsertSlot_objects_eq st st' addr cap hObjInv hStep
  have hNe : ∀ oid : SeLe4n.ObjId, oid ≠ addr.cnode →
      st'.objects[oid]? = st.objects[oid]? :=
    fun oid h => cspaceInsertSlot_preserves_objects_ne st st' addr cap oid h hObjInv hStep
  have hSched := cspaceInsertSlot_preserves_scheduler st st' addr cap hStep
  have hView := ipcReadViewAgreement.of_single_inert_write hNe
    (by rw [hPre]; trivial) (by rw [hAt]; trivial)
  have hCodes := sameNotificationBindings.of_single_inert_write hNe
    (by rw [hPre]; trivial) (by rw [hAt]; trivial)
  have hBack : ∀ (tid : SeLe4n.ThreadId) (tcb' : TCB),
      st'.objects[tid.toObjId]? = some (.tcb tcb') →
      ∃ tcb, st.objects[tid.toObjId]? = some (.tcb tcb) ∧
        tcb.ipcState = tcb'.ipcState ∧ tcb.schedContextBinding = tcb'.schedContextBinding := by
    intro tid tcb' h
    by_cases hK : tid.toObjId = addr.cnode
    · rw [hK, hAt] at h
      exact absurd (Option.some.inj h) (fun hx => KernelObject.noConfusion hx)
    · rw [hNe _ hK] at h
      exact ⟨tcb', h, rfl, rfl⟩
  have hBadge := cspaceInsertSlot_preserves_badgeWellFormed st st' addr cap
    hInv.badgeWellFormed hObjInv hCapValid hStep
  exact ipcInvariantFull_of_readViewAgreement hView hCodes
    hBadge.2 hInv

/-- Success shape of `cspaceDeleteSlotCore`: the object at the address held
slots, the post-state holds it with the slot emptied, off-key objects, the
scheduler and the store invariant are untouched.

The store invariant is a conjunct rather than a separate lemma because the
revocation fold (`v0.35.190`) needs it *between* iterations: each
`cspaceDeleteSlotCore` takes `st.objects.invExt` as a hypothesis, so a fold over
descendants has to carry it forward from the step that just ran. -/
theorem cspaceDeleteSlotCore_shape
    (st st' : SystemState) (addr : CSpaceAddr)
    (hObjInv : st.objects.invExt)
    (hStep : cspaceDeleteSlotCore addr st = .ok ((), st')) :
    ∃ o : KernelObject, st.objects[addr.cnode]? = some o ∧ o.holdsSlots = true ∧
      st'.objects[addr.cnode]? = some (o.removeSlotCap addr.slot) ∧
      (∀ oid : SeLe4n.ObjId, oid ≠ addr.cnode → st'.objects[oid]? = st.objects[oid]?) ∧
      st'.scheduler = st.scheduler ∧ st'.objects.invExt := by
  obtain ⟨o, hO, hH, hS⟩ := cspaceDeleteSlotCore_ok hStep
  exact ⟨o, hO, hH, storeObject_objects_eq st st' _ _ hObjInv hS,
    fun oid hNe => storeObject_objects_ne st st' _ oid _ hNe hObjInv hS,
    storeObject_scheduler_eq st st' _ _ hS,
    storeObject_preserves_objects_invExt st st' _ _ hObjInv hS⟩

/-- `cspaceDeleteSlotCore` preserves the whole bundle: removal shrinks the
slots' contents, so the badge clause carries from the pre-state; a thread's
emptied space slot moves no field the bundle reads. -/
theorem cspaceDeleteSlotCore_preserves_ipcInvariantFull
    (st st' : SystemState) (addr : CSpaceAddr)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hStep : cspaceDeleteSlotCore addr st = .ok ((), st')) :
    ipcInvariantFull st' := by
  rcases cspaceDeleteSlotCore_ok_cases hStep with ⟨cn, hPre, hS⟩ | ⟨t, hPre, hS⟩
  case inr =>
    -- A thread's space slot emptied: no field the bundle reads moves, and the
    -- emptied thread holds no capability it did not.
    exact storeObject_tcbFieldUpdate_preserves_ipcInvariantFull st st'
      (SeLe4n.ThreadId.ofObjId addr.cnode) t (t.removeSpaceCap addr.slot) hObjInv hInv hPre hS
      rfl rfl rfl rfl rfl rfl rfl rfl rfl
      (fun _ _ _ h _ => TCB.spaceSlotCap_removeSpaceCap_back h)
  have hAt := storeObject_objects_eq st st' _ _ hObjInv hS
  have hNe : ∀ oid : SeLe4n.ObjId, oid ≠ addr.cnode → st'.objects[oid]? = st.objects[oid]? :=
    fun oid h => storeObject_objects_ne st st' _ oid _ h hObjInv hS
  have hSched := storeObject_scheduler_eq st st' _ _ hS
  have hView := ipcReadViewAgreement.of_single_inert_write hNe
    (by rw [hPre]; trivial) (by rw [hAt]; trivial)
  have hCodes := sameNotificationBindings.of_single_inert_write hNe
    (by rw [hPre]; trivial) (by rw [hAt]; trivial)
  have hBack : ∀ (tid : SeLe4n.ThreadId) (tcb' : TCB),
      st'.objects[tid.toObjId]? = some (.tcb tcb') →
      ∃ tcb, st.objects[tid.toObjId]? = some (.tcb tcb) ∧
        tcb.ipcState = tcb'.ipcState ∧ tcb.schedContextBinding = tcb'.schedContextBinding := by
    intro tid tcb' h
    by_cases hK : tid.toObjId = addr.cnode
    · rw [hK, hAt] at h
      exact absurd (Option.some.inj h) (fun hx => KernelObject.noConfusion hx)
    · rw [hNe _ hK] at h
      exact ⟨tcb', h, rfl, rfl⟩
  have hCap : capabilityBadgesWellFormed st' := by
    intro oid cn' slot cap badge hCn hLk hB
    by_cases hK : oid = addr.cnode
    · rw [hK, hAt] at hCn
      obtain rfl : KernelObject.cnode (cn.remove addr.slot) = cn' := Option.some.inj hCn
      simp only [KernelObject.slotCap] at hLk
      by_cases hSlot : addr.slot = slot
      · rw [← hSlot, CNode.lookup_remove_eq_none cn addr.slot
          (CNode.slotsUnique_holds cn)] at hLk
        cases hLk
      · rw [CNode.lookup_remove_ne cn addr.slot slot hSlot
          (CNode.slotsUnique_holds cn)] at hLk
        exact hInv.badgeWellFormed.2 addr.cnode (.cnode cn) slot cap badge (hK ▸ hPre) hLk hB
    · rw [hNe _ hK] at hCn
      exact hInv.badgeWellFormed.2 oid cn' slot cap badge hCn hLk hB
  exact ipcInvariantFull_of_readViewAgreement hView hCodes
    hCap hInv

/-- **A step that rewrites only derivation state keeps the IPC bundle.**  The
bundle reads no derivation tree and no link word: every object it reads through
the store is a non-CNode, which the step leaves as it was up to a thread's
space-slot links, and its slot clause (`capabilityBadgesWellFormed`) reads slot
contents, which the step keeps. -/
theorem ipcInvariantFull_of_agreeOffDerivationLinks {st st' : SystemState}
    (h : SystemState.objectsAgreeOffDerivationLinks st' st)
    (hInv : ipcInvariantFull st) : ipcInvariantFull st' := by
  have hView : ipcReadViewAgreement st st' := ipcReadViewAgreement.of_objectsAgreeOffDerivationLinks h
  have hCodes : sameNotificationBindings st st' := sameNotificationBindings.of_objectsAgreeOffDerivationLinks h
  have hBack : ∀ (tid : SeLe4n.ThreadId) (tcb' : TCB),
      st'.objects[tid.toObjId]? = some (.tcb tcb') →
      ∃ tcb, st.objects[tid.toObjId]? = some (.tcb tcb) ∧
        tcb.ipcState = tcb'.ipcState ∧ tcb.schedContextBinding = tcb'.schedContextBinding :=
    fun _ tcb' hT => (h.tcb_back hT).elim fun t ht =>
      ⟨t, ht.1, TCB.of_withoutLinks_eq ht.2 (fun _ => Iff.rfl) rfl,
        TCB.of_withoutLinks_eq ht.2 (fun _ => Iff.rfl) rfl⟩
  have hCap : capabilityBadgesWellFormed st' :=
    capabilityBadgesWellFormed_of_slotCap_back hInv.badgeWellFormed.2
      fun _ _ hO => (h.obj_slots_back hO).elim fun o ho => ⟨o, ho.1, ho.2.1⟩
  exact ipcInvariantFull_of_readViewAgreement hView hCodes
    hCap hInv

/-- A run of slot-link writes keeps the IPC bundle: it changes only CNode
derivation links, which no IPC conjunct reads. -/
theorem ipcInvariantFull_of_linkReach {st₀ st : SystemState} (hR : SystemState.linkReach st₀ st)
    (hObjInv : st₀.objects.invExt) (hInv : ipcInvariantFull st₀) : ipcInvariantFull st :=
  ipcInvariantFull_of_agreeOffDerivationLinks (hR.agree hObjInv)
    hInv

/-- `.cspaceDelete`: the core delete and the splice touch no IPC state. -/
theorem cspaceDeleteSlot_preserves_ipcInvariantFull
    (st st' : SystemState) (addr : CSpaceAddr)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hStep : cspaceDeleteSlot addr st = .ok ((), st')) :
    ipcInvariantFull st' := by
  obtain ⟨stC, hCore, rfl⟩ := cspaceDeleteSlot_ok_decompose addr st st' hStep
  have hC := cspaceDeleteSlotCore_preserves_ipcInvariantFull st stC addr hObjInv hInv hCore
  exact ipcInvariantFull_of_agreeOffDerivationLinks
    (spliceDeletedCdtNode_agree (cspaceDeleteSlotCore_invExt _ _ _ hObjInv hCore) addr).1 hC

/-- `.cspaceDelete`'s store invariant: the delete writes one CNode and the CDT,
so `objects.invExt` carries — what the finalising delete's teardown, which runs on
the delete's post-state, needs. -/
theorem cspaceDeleteSlot_preserves_objects_invExt
    (st st' : SystemState) (addr : CSpaceAddr) (hObjInv : st.objects.invExt)
    (hStep : cspaceDeleteSlot addr st = .ok ((), st')) : st'.objects.invExt := by
  obtain ⟨stC, hCore, rfl⟩ := cspaceDeleteSlot_ok_decompose addr st st' hStep
  exact (spliceDeletedCdtNode_agree (cspaceDeleteSlotCore_invExt _ _ _ hObjInv hCore) addr).2

-- ============================================================================
-- WS-RR RR8.16 (`v0.35.190`): the revocation family preserves `ipcInvariantFull`
-- ============================================================================

/-! `seL4_CNode_Revoke` needed an arm, and an arm needs its place in the
capability-only dispatch payoff.  The family's own preservation surface is
stated against `capabilityInvariantBundle` (`Capability/Invariant/Preservation/
Revoke.lean`); what it had never had is the *IPC* bundle, which is what
`dispatchCapabilityOnly_preserves_ipcInvariantFull` composes.

The argument is the delete's, folded.  Every write the family performs is a
CNode store (`ipcReadInert` on both sides, so `ipcReadViewAgreement` carries the
eighteen object conjuncts), a CDT-field update (which the bundle does not read
at all), or the in-flight sweep's `pendingMessage` rewrite — and that last one is
the only place the bundle has something to say, which is why it gets a frame of
its own rather than riding the read view. -/

/-- Success shape of `cspaceRevoke`: the target CNode existed, the post-state
holds it with the revoked siblings filtered out, and off-key objects, the
scheduler and the store invariant are untouched. -/
private theorem cspaceRevoke_shape
    (st st' : SystemState) (addr : CSpaceAddr)
    (hObjInv : st.objects.invExt)
    (hStep : cspaceRevoke addr st = .ok ((), st')) :
    ∃ (cn : CNode) (parent : Capability) (stS : SystemState),
      st' = detachRevokedSlots stS addr.cnode cn addr.slot parent.target ∧
      st.objects[addr.cnode]? = some (.cnode cn) ∧
      stS.objects[addr.cnode]? = some (.cnode (cn.revokeTargetLocal addr.slot parent.target)) ∧
      (∀ oid : SeLe4n.ObjId, oid ≠ addr.cnode → stS.objects[oid]? = st.objects[oid]?) ∧
      stS.scheduler = st.scheduler ∧ stS.objects.invExt := by
  obtain ⟨parent, cn, stS, _, hCn, hStore, rfl⟩ := cspaceRevoke_ok_decompose addr st st' hStep
  have hPre : st.objects[addr.cnode]? = some (.cnode cn) := by
    unfold SystemState.getCNode? at hCn
    split at hCn <;> simp_all
  exact ⟨cn, parent, stS, rfl, hPre,
    storeObject_objects_eq st stS addr.cnode _ hObjInv hStore,
    fun oid hNe => storeObject_objects_ne st stS addr.cnode oid _ hNe hObjInv hStore,
    storeObject_scheduler_eq st stS addr.cnode _ hStore,
    storeObject_preserves_objects_invExt st stS addr.cnode _ hObjInv hStore⟩

/-- `cspaceRevoke` preserves the bundle: local revocation only *removes* slots
(`CNode.lookup_revokeTargetLocal_sub`), so the badge clause carries from the
pre-state exactly as it does across the delete. -/
theorem cspaceRevoke_preserves_ipcInvariantFull
    (st st' : SystemState) (addr : CSpaceAddr)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hStep : cspaceRevoke addr st = .ok ((), st')) :
    ipcInvariantFull st' := by
  obtain ⟨cn, parent, stS, rfl, hPre, hAt, hNe, hSched, hInvS⟩ :=
    cspaceRevoke_shape st st' addr hObjInv hStep
  refine ipcInvariantFull_of_agreeOffDerivationLinks
    (detachRevokedSlots_agree hInvS _ _ _ _).1 ?_
  have hView := ipcReadViewAgreement.of_single_inert_write hNe
    (by rw [hPre]; trivial) (by rw [hAt]; trivial)
  have hCodes := sameNotificationBindings.of_single_inert_write hNe
    (by rw [hPre]; trivial) (by rw [hAt]; trivial)
  have hBack : ∀ (tid : SeLe4n.ThreadId) (tcb' : TCB),
      stS.objects[tid.toObjId]? = some (.tcb tcb') →
      ∃ tcb, st.objects[tid.toObjId]? = some (.tcb tcb) ∧
        tcb.ipcState = tcb'.ipcState ∧ tcb.schedContextBinding = tcb'.schedContextBinding := by
    intro tid tcb' h
    by_cases hK : tid.toObjId = addr.cnode
    · rw [hK, hAt] at h
      exact absurd (Option.some.inj h) (fun hx => KernelObject.noConfusion hx)
    · rw [hNe _ hK] at h
      exact ⟨tcb', h, rfl, rfl⟩
  have hCap : capabilityBadgesWellFormed stS := by
    intro oid cn' slot cap badge hCn hLk hB
    by_cases hK : oid = addr.cnode
    · rw [hK, hAt] at hCn
      obtain rfl : KernelObject.cnode (cn.revokeTargetLocal addr.slot parent.target) = cn' := Option.some.inj hCn
      simp only [KernelObject.slotCap] at hLk
      exact hInv.badgeWellFormed.2 addr.cnode (.cnode cn) slot cap badge (hK ▸ hPre)
        (CNode.lookup_revokeTargetLocal_sub cn addr.slot parent.target slot cap
          (CNode.slotsUnique_holds cn) hLk) hB
    · rw [hNe _ hK] at hCn
      exact hInv.badgeWellFormed.2 oid cn' slot cap badge hCn hLk hB
  exact ipcInvariantFull_of_readViewAgreement hView hCodes
    hCap hInv


/-- Inversion of a successful `toNonNull?`: the promoted value is the input. -/
private theorem toNonNull?_val_eq {cap : Capability} {capNN : NonNullCap}
    (hNN : cap.toNonNull? = some capNN) : capNN.val = cap := by
  unfold Capability.toNonNull? at hNN
  split at hNN
  · cases hNN; rfl
  · cases hNN

/-- `.cspaceMint` (core): lookup, attenuate, insert — the minted badge is the
argument badge, so the insert's badge obligation is the decode-level fact. -/
theorem cspaceMint_preserves_ipcInvariantFull
    (st st' : SystemState) (src dst : CSpaceAddr) (rights : AccessRightSet)
    (badge : Option SeLe4n.Badge)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hBadgeValid : ∀ b, badge = some b → b.valid)
    (hStep : cspaceMint src dst rights badge st = .ok ((), st')) :
    ipcInvariantFull st' := by
  unfold cspaceMint at hStep
  split at hStep
  · contradiction
  · rename_i parent stMid hLk
    have hMid : stMid = st := cspaceLookupSlot_state_eq st stMid src parent hLk
    split at hStep
    · contradiction
    · rename_i parentNN hNN
      split at hStep
      · contradiction
      · rename_i child hMint
        have hChildBadge : child.badge = badge := by
          unfold mintDerivedCap at hMint
          split at hMint
          · split at hMint
            · contradiction
            · cases hMint; simp
          · contradiction
        exact cspaceInsertSlot_preserves_ipcInvariantFull stMid st' dst child
          (hMid.symm ▸ hObjInv) (hMid.symm ▸ hInv)
          (fun b hb => hBadgeValid b (hChildBadge ▸ hb)) hStep

/-- The CDT-recording tail every `WithCdt` form ends in touches neither
objects nor the scheduler. -/
private theorem cdtRecord_bundle_frame (stM : SystemState) (src dst : CSpaceAddr)
    (kind : DerivationOp) (hObjInvM : stM.objects.invExt)
    (hInvM : ipcInvariantFull stM) :
    ipcInvariantFull (stM.cdtAddChild src dst kind) :=
  ipcInvariantFull_of_linkReach (SystemState.cdtAddChild_reach stM src dst kind) hObjInvM
    (ipcInvariantFull_of_objects_eq (st := stM) rfl hInvM)

/-- `.cspaceMove`: insert at the destination, delete at the source, repoint
the CDT — every object write is a CNode. -/
theorem cspaceMove_preserves_ipcInvariantFull
    (st st' : SystemState) (src dst : CSpaceAddr)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hStep : cspaceMove src dst st = .ok ((), st')) :
    ipcInvariantFull st' := by
  unfold cspaceMove at hStep
  split at hStep
  · contradiction
  · split at hStep
    · contradiction
    · rename_i cap stMid hLk
      have hMid : stMid = st := cspaceLookupSlot_state_eq st stMid src cap hLk
      split at hStep
      · contradiction
      · rename_i capNN hNN
        split at hStep
        · contradiction
        · rename_i st2 hIns
          have hBadgeSrc := lookupSlotCap_badge_valid st src cap hInv.badgeWellFormed.2
            ((cspaceLookupSlot_ok_iff_lookupSlotCap st src cap).mp (hMid ▸ hLk))
          have hInv2 := cspaceInsertSlot_preserves_ipcInvariantFull stMid st2 dst capNN.val
            (hMid.symm ▸ hObjInv) (hMid.symm ▸ hInv)
            (fun b hb => hBadgeSrc b (toNonNull?_val_eq hNN ▸ hb)) hIns
          have hObjInv2 := cspaceInsertSlot_preserves_objects_invExt stMid st2 dst capNN.val
            (hMid.symm ▸ hObjInv) hIns
          split at hStep
          · contradiction
          · rename_i st3 hDel
            have hInv3 := cspaceDeleteSlotCore_preserves_ipcInvariantFull st2 st3 src
              hObjInv2 hInv2 hDel
            cases hStep
            exact ipcInvariantFull_of_linkReach (SystemState.cdtMove_reach st3 src dst)
              (cspaceDeleteSlotCore_invExt st2 st3 src hObjInv2 hDel)
              (ipcInvariantFull_of_objects_eq (st := st3) rfl hInv3)

/-- `.mintReplyCap` (core): the derived reply capability carries no badge, so
the insert's badge obligation is vacuous. -/
theorem mintReplyCap_preserves_ipcInvariantFull
    (st st' : SystemState) (src dst : CSpaceAddr)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hStep : mintReplyCap src dst st = .ok ((), st')) :
    ipcInvariantFull st' := by
  unfold mintReplyCap at hStep
  split at hStep
  · contradiction
  · rename_i parent stMid hLk
    have hMid : stMid = st := cspaceLookupSlot_state_eq st stMid src parent hLk
    split at hStep
    · rename_i target
      dsimp only [] at hStep
      split at hStep
      · exact cspaceInsertSlot_preserves_ipcInvariantFull stMid st' dst _
          (hMid.symm ▸ hObjInv) (hMid.symm ▸ hInv)
          (fun b hb => by simp at hb) hStep
      · contradiction
    · contradiction

/-- `.mintReplyCap`: the CDT-tracked form the dispatch routes through. -/
theorem mintReplyCapWithCdt_preserves_ipcInvariantFull
    (st st' : SystemState) (src dst : CSpaceAddr)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hStep : mintReplyCapWithCdt src dst st = .ok ((), st')) :
    ipcInvariantFull st' := by
  unfold mintReplyCapWithCdt at hStep
  split at hStep
  · contradiction
  · rename_i stM hMint
    cases hStep
    obtain ⟨_, _, _, hInsM, -⟩ := mintReplyCap_ok_decompose src dst st stM hMint
    exact cdtRecord_bundle_frame stM src dst DerivationOp.mint
      (cspaceInsertSlot_preserves_objects_invExt st stM dst _ hObjInv hInsM)
      (mintReplyCap_preserves_ipcInvariantFull st stM src dst hObjInv hInv hMint)

/-- **WS-BP BP7.1 (`v0.36.5`)**: a store at a key that held **no** object, or an
IPC-inert one, of an IPC-inert object that is not a CNode moves nothing any
conjunct reads.  The read view agrees (`of_fresh_inert_write` /
`of_single_inert_write`), the scheduler is framed, and the badge clause — the one
conjunct that reads CNodes — loses at most a CNode and gains none.  The two
stores an untyped carve performs on objects (the untyped's child list, the fresh
frame) are both this shape. -/
theorem storeObject_inertNonCNode_preserves_ipcInvariantFull
    (st st' : SystemState) (key : SeLe4n.ObjId) (obj : KernelObject)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hPre : st.objects[key]? = none ∨ ipcReadInert st.objects[key]?)
    (hObj : ipcReadInert (some obj)) (hNotCn : ∀ cn, obj ≠ .cnode cn)
    (hStep : storeObject key obj st = .ok ((), st')) :
    ipcInvariantFull st' := by
  have hAt : st'.objects[key]? = some obj := storeObject_objects_eq _ _ _ _ hObjInv hStep
  have hNe : ∀ oid : SeLe4n.ObjId, oid ≠ key → st'.objects[oid]? = st.objects[oid]? :=
    fun oid h => storeObject_objects_ne _ _ _ _ _ h hObjInv hStep
  have hSched := storeObject_scheduler_eq _ _ _ _ hStep
  have hView : ipcReadViewAgreement st st' := by
    rcases hPre with hNone | hIn
    · exact ipcReadViewAgreement.of_fresh_inert_write hNe hNone (by rw [hAt]; exact hObj)
    · exact ipcReadViewAgreement.of_single_inert_write hNe hIn (by rw [hAt]; exact hObj)
  have hCodes : sameNotificationBindings st st' := by
    rcases hPre with hNone | hIn
    · exact sameNotificationBindings.of_fresh_inert_write hNe hNone (by rw [hAt]; exact hObj)
    · exact sameNotificationBindings.of_single_inert_write hNe hIn (by rw [hAt]; exact hObj)
  have hNotTcb : ∀ t, obj ≠ .tcb t := by
    intro t h; subst h; simp [ipcReadInert] at hObj
  have hBack : ∀ (tid : SeLe4n.ThreadId) (tcb' : TCB),
      st'.objects[tid.toObjId]? = some (.tcb tcb') →
      ∃ tcb, st.objects[tid.toObjId]? = some (.tcb tcb) ∧
        tcb.ipcState = tcb'.ipcState ∧ tcb.schedContextBinding = tcb'.schedContextBinding := by
    intro tid tcb' h
    by_cases hK : tid.toObjId = key
    · rw [hK, hAt] at h
      exact absurd (Option.some.inj h) (hNotTcb tcb')
    · rw [hNe _ hK] at h
      exact ⟨tcb', h, rfl, rfl⟩
  have hCap : capabilityBadgesWellFormed st' := by
    intro oid cn slot cap badge hCn hLk hB
    by_cases hK : oid = key
    · rw [hK, hAt] at hCn
      cases Option.some.inj hCn
      rw [(KernelObject.slotCap_linkAt_of_not_slots hNotCn
        (by cases obj <;> simp_all [KernelObject.tcbSlots])).1] at hLk
      cases hLk
    · rw [hNe _ hK] at hCn
      exact hInv.badgeWellFormed.2 oid cn slot cap badge hCn hLk hB
  exact ipcInvariantFull_of_readViewAgreement hView hCodes
    hCap hInv

/-- **A capability rewritten in its slot, its badge kept, preserves the bundle**:
one CNode is stored back with one occupied slot's capability replaced by one
with the same badge — the only thing the bundle reads of a capability.  The
shape of the mapping record `.vspaceMap` writes and of a free-index write
(WS-ZA ZA5.4 part 13). -/
theorem storeObject_capRewrite_preserves_ipcInvariantFull
    (addr : CSpaceAddr) (cn : CNode) (cap cap' : Capability) (st st' : SystemState)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hPre : st.objects[addr.cnode]? = some (.cnode cn)) (hLk : cn.lookup addr.slot = some cap)
    (hBadge : cap'.badge = cap.badge)
    (hStore : storeObject addr.cnode (.cnode (cn.insert addr.slot cap')) st = .ok ((), st')) :
    ipcInvariantFull st' ∧ st'.objects.invExt := by
  have hAt := storeObject_objects_eq st st' addr.cnode _ hObjInv hStore
  have hNe : ∀ oid : SeLe4n.ObjId, oid ≠ addr.cnode → st'.objects[oid]? = st.objects[oid]? :=
    fun oid h => storeObject_objects_ne st st' addr.cnode oid _ h hObjInv hStore
  have hSched := storeObject_scheduler_eq st st' addr.cnode _ hStore
  have hView := ipcReadViewAgreement.of_single_inert_write hNe
    (by rw [hPre]; trivial) (by rw [hAt]; trivial)
  have hCodes := sameNotificationBindings.of_single_inert_write hNe
    (by rw [hPre]; trivial) (by rw [hAt]; trivial)
  have hBack : ∀ (tid : SeLe4n.ThreadId) (tcb' : TCB),
      st'.objects[tid.toObjId]? = some (.tcb tcb') →
      ∃ tcb, st.objects[tid.toObjId]? = some (.tcb tcb) ∧
        tcb.ipcState = tcb'.ipcState ∧ tcb.schedContextBinding = tcb'.schedContextBinding := by
    intro tid tcb' h
    by_cases hK : tid.toObjId = addr.cnode
    · rw [hK, hAt] at h
      exact absurd (Option.some.inj h) (fun hx => KernelObject.noConfusion hx)
    · rw [hNe _ hK] at h
      exact ⟨tcb', h, rfl, rfl⟩
  have hCap : capabilityBadgesWellFormed st' := by
    intro oid cn' slot cap'' badge hCn' hLk' hB
    by_cases hK : oid = addr.cnode
    · rw [hK, hAt] at hCn'
      obtain rfl : KernelObject.cnode (cn.insert addr.slot cap') = cn' := Option.some.inj hCn'
      simp only [KernelObject.slotCap] at hLk'
      by_cases hSlot : addr.slot = slot
      · subst hSlot
        rw [CNode.lookup_insert_eq cn addr.slot _ (CNode.slotsUnique_holds cn)
          (CNode.slotAddressable_of_lookup_insert _ _ _ _ _ hLk')] at hLk'
        cases hLk'
        exact hInv.badgeWellFormed.2 addr.cnode (.cnode cn) addr.slot cap badge (hK ▸ hPre) hLk
          (hBadge ▸ hB)
      · rw [CNode.lookup_insert_ne cn addr.slot slot _ hSlot
          (CNode.slotsUnique_holds cn)] at hLk'
        exact hInv.badgeWellFormed.2 addr.cnode (.cnode cn) slot cap'' badge (hK ▸ hPre) hLk' hB
    · rw [hNe _ hK] at hCn'
      exact hInv.badgeWellFormed.2 oid cn' slot cap'' badge hCn' hLk' hB
  exact ⟨ipcInvariantFull_of_readViewAgreement hView hCodes
    hCap hInv,
    storeObject_preserves_objects_invExt st st' addr.cnode _ hObjInv hStore⟩

/-- **A write of the memory kinds preserves `ipcInvariantFull`**: every key holds
what it held, or on each side nothing or a kind the bundle does not read
(`memoryKindOrAbsent`), so the read view agrees (`of_inertOrAbsentWrites`); with
no CNode written, the badge clause carries.  The final-delete retire's erase of a
carved object is such a write. -/
theorem ipcInvariantFull_of_memoryKindWrite {st st' : SystemState}
    (hW : ∀ oid : SeLe4n.ObjId, st'.objects[oid]? = st.objects[oid]? ∨
      (memoryKindOrAbsent st.objects[oid]? ∧ memoryKindOrAbsent st'.objects[oid]?))
    (hInv : ipcInvariantFull st) : ipcInvariantFull st' := by
  have hTouched : ∀ o : Option KernelObject, memoryKindOrAbsent o → o = none ∨ ipcReadInert o := by
    intro o h
    cases o with
    | none => exact Or.inl rfl
    | some obj =>
      right
      cases obj <;> first | trivial | exact absurd h (by simp [memoryKindOrAbsent])
  have hView : ipcReadViewAgreement st st' :=
    ipcReadViewAgreement.of_inertOrAbsentWrites fun oid => by
      rcases hW oid with e | ⟨t1, t2⟩
      · exact Or.inl e
      · exact Or.inr ⟨hTouched _ t1, hTouched _ t2⟩
  have hCodes : sameNotificationBindings st st' :=
    sameNotificationBindings.of_inertOrAbsentWrites fun oid => by
      rcases hW oid with e | ⟨t1, t2⟩
      · exact Or.inl e
      · exact Or.inr ⟨hTouched _ t1, hTouched _ t2⟩
  -- a CNode or TCB in the post-state is the pre-state's, unchanged
  have hBackObj : ∀ (oid : SeLe4n.ObjId) (o : KernelObject), ¬ memoryKindOrAbsent (some o) →
      st'.objects[oid]? = some o → st.objects[oid]? = some o := by
    intro oid o hNT hPost
    rcases hW oid with e | ⟨_, t2⟩
    · rw [← e]; exact hPost
    · rw [hPost] at t2; exact absurd t2 hNT
  have hCap : capabilityBadgesWellFormed st' := by
    intro oid o slot cap badge hCn hLk hB
    cases o with
    | cnode _ | tcb _ =>
      exact hInv.badgeWellFormed.2 oid _ slot cap badge
        (hBackObj _ _ (by simp [memoryKindOrAbsent]) hCn) hLk hB
    | _ => simp [KernelObject.slotCap] at hLk
  exact ipcInvariantFull_of_readViewAgreement hView hCodes hCap hInv

-- ============================================================================
-- WS-BP BP7.1 (`v0.36.7`): frame finalisation preserves `ipcInvariantFull`
-- ============================================================================

/-- **A VSpace-root-only write that keeps the scheduler preserves the bundle.**
Every key it touches holds a VSpace root on both sides, which the read view does
not read, and no TCB, CNode, endpoint, notification or Reply moves.  The shape of
every page teardown (`vspaceRootOnlyWrite`), stated once so the reset and the
finalising destroyers do not each re-derive it. -/
theorem ipcInvariantFull_of_vspaceRootOnlyWrite {st st' : SystemState}
    (hW : vspaceRootOnlyWrite st st')
    (hInv : ipcInvariantFull st) : ipcInvariantFull st' := by
  have hView : ipcReadViewAgreement st st' :=
    ipcReadViewAgreement.of_inertOrAbsentWrites fun oid => by
      rcases hW oid with e | ⟨⟨r, hr⟩, ⟨r', hr'⟩⟩
      · exact Or.inl e
      · exact Or.inr ⟨Or.inr (by rw [hr]; trivial), Or.inr (by rw [hr']; trivial)⟩
  have hCodes : sameNotificationBindings st st' :=
    sameNotificationBindings.of_inertOrAbsentWrites fun oid => by
      rcases hW oid with e | ⟨⟨r, hr⟩, ⟨r', hr'⟩⟩
      · exact Or.inl e
      · exact Or.inr ⟨Or.inr (by rw [hr]; trivial), Or.inr (by rw [hr']; trivial)⟩
  have hBackObj : ∀ (oid : SeLe4n.ObjId) (o : KernelObject), (∀ r, o ≠ .vspaceRoot r) →
      st'.objects[oid]? = some o → st.objects[oid]? = some o := by
    intro oid o hNR hPost
    rcases hW oid with e | ⟨_, ⟨r', hr'⟩⟩
    · rw [← e]; exact hPost
    · rw [hPost] at hr'; exact absurd (Option.some.inj hr') (hNR r')
  have hBack : ∀ (tid : SeLe4n.ThreadId) (tcb' : TCB),
      st'.objects[tid.toObjId]? = some (.tcb tcb') →
      ∃ tcb, st.objects[tid.toObjId]? = some (.tcb tcb) ∧
        tcb.ipcState = tcb'.ipcState ∧ tcb.schedContextBinding = tcb'.schedContextBinding :=
    fun tid tcb' h => ⟨tcb', hBackObj _ _ (fun _ hx => KernelObject.noConfusion hx) h, rfl, rfl⟩
  have hCap : capabilityBadgesWellFormed st' := by
    intro oid o slot cap badge hCn hLk hB
    cases o with
    | cnode _ | tcb _ =>
      exact hInv.badgeWellFormed.2 oid _ slot cap badge
        (hBackObj _ _ (fun _ hx => KernelObject.noConfusion hx) hCn) hLk hB
    | _ => simp [KernelObject.slotCap] at hLk
  exact ipcInvariantFull_of_readViewAgreement hView hCodes
    hCap hInv

/-- **The whole finalisation preserves the bundle** — the table detach and the
page teardown are both VSpace-root-only writes. -/
theorem finaliseDestroyedCapabilities_preserves_ipcInvariantFull
    (ec : Concurrency.CoreId) (named : List SeLe4n.ObjId) (pages : List MappedPage)
    (st st' : SystemState) (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hStep : finaliseDestroyedCapabilities ec named pages st = .ok ((), st')) :
    ipcInvariantFull st' ∧ st'.objects.invExt := by
  obtain ⟨hExt, hW, hSched⟩ :=
    finaliseDestroyedCapabilities_ok_frame ec named pages st st' hObjInv hStep
  exact ⟨ipcInvariantFull_of_vspaceRootOnlyWrite hW hInv, hExt⟩

/-- **PR #904 review (`v0.36.41`): the mapping-epoch tag preserves the bundle** —
it stores back one VSpace root and one frame, both kinds the bundle never reads. -/
theorem tagFrameMapping_preserves_ipcInvariantFull
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) (frameId : SeLe4n.ObjId)
    (st st' : SystemState) (e : Nat)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hStep : tagFrameMapping asid vaddr frameId st = .ok (e, st')) :
    ipcInvariantFull st' ∧ st'.objects.invExt := by
  obtain ⟨f, rootId, root, st1, hF, hR, -, h1, h2⟩ :=
    tagFrameMapping_ok asid vaddr frameId st st' e hStep
  have hRootPre := (Architecture.resolveAsidRoot_some_implies_obj st asid rootId root hR).2.1
  have hFramePre := (SystemState.getFrame?_eq_some_iff st frameId f).mp hF
  have hInv1Obj := storeObject_preserves_objects_invExt st st1 _ _ hObjInv h1
  have hInv1 := storeObject_inertNonCNode_preserves_ipcInvariantFull st st1 rootId
    (.vspaceRoot { root with mappingEpochs := root.mappingEpochs.insert vaddr f.mapEpoch })
    hObjInv hInv (Or.inr (by rw [hRootPre]; trivial)) trivial
    (fun cn h => KernelObject.noConfusion h) h1
  have hNe : frameId ≠ rootId := by
    intro hEq; rw [hEq, hRootPre] at hFramePre; cases hFramePre
  have hFrame1 : st1.objects[frameId]? = some (.frame f) := by
    rw [storeObject_objects_ne st st1 _ _ _ hNe hObjInv h1]; exact hFramePre
  exact ⟨storeObject_inertNonCNode_preserves_ipcInvariantFull st1 st' frameId
      (.frame { f with mapEpoch := f.mapEpoch + 1 }) hInv1Obj hInv1 (Or.inr (by rw [hFrame1]; trivial)) trivial
      (fun cn h => KernelObject.noConfusion h) h2,
    storeObject_preserves_objects_invExt st1 st' _ _ hInv1Obj h2⟩

/-- **The mapping record `.vspaceMap` writes preserves the bundle**: one CNode is
stored back with one capability's `mapping` field set, and the badge — the only
thing the bundle reads of a capability — is the one it had. -/
theorem cspaceRecordFrameMapping_preserves_ipcInvariantFull
    (addr : CSpaceAddr) (m : FrameMapping) (st st' : SystemState)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hStep : cspaceRecordFrameMapping addr m st = .ok ((), st')) :
    ipcInvariantFull st' ∧ st'.objects.invExt := by
  obtain ⟨cn, cap, hCn, hLk, hStore⟩ := cspaceRecordFrameMapping_ok_decompose addr m st st' hStep
  exact storeObject_capRewrite_preserves_ipcInvariantFull addr cn cap _ st st' hObjInv hInv
    ((SystemState.getCNode?_eq_some_iff st addr.cnode cn).mp hCn) hLk
    (by simp only [Capability.badge, Capability.withMapping_badgeWord,
      Capability.withMapping_badged]) hStore

/-- **A free-index write preserves the bundle** (WS-ZA ZA5.4 part 13): the
capability rewritten keeps its badge. -/
theorem setCapFreeIndex_preserves_ipcInvariantFull
    (addr : CSpaceAddr) (cn : CNode) (cap : Capability) (idx : Nat) (st : SystemState)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hPre : st.objects[addr.cnode]? = some (.cnode cn)) (hLk : cn.lookup addr.slot = some cap) :
    ipcInvariantFull (setCapFreeIndex st addr idx) ∧ (setCapFreeIndex st addr idx).objects.invExt := by
  have hS := setCapFreeIndex_eq_storeObject (idx := idx) hPre
  rw [CNode.setFreeIndex_of_lookup hLk] at hS
  exact storeObject_capRewrite_preserves_ipcInvariantFull addr cn cap _ st _ hObjInv hInv hPre hLk
    (Capability.withFreeIndex_badge _ _) hS

/-- WS-ZA ZA5.4: **the `.untypedReset` arm preserves `ipcInvariantFull`.**  The
reset rewinds the invoked slot's free index, a capability rewrite that keeps the
badge (`setCapFreeIndex_preserves_ipcInvariantFull`), and writes nothing else. -/
theorem untypedResetSlot_preserves_ipcInvariantFull {srcCnode : SeLe4n.ObjId}
    {srcSlot : SeLe4n.Slot} {st st' : SystemState}
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hStep : untypedResetSlot srcCnode srcSlot st = .ok ((), st')) :
    ipcInvariantFull st' := by
  obtain ⟨cap, -, -, -, hL, -, -, -, rfl⟩ := untypedResetSlot_ok hStep
  obtain ⟨cn, hO, hLk⟩ := SystemState.lookupSlotCap_cnode hL
  exact (setCapFreeIndex_preserves_ipcInvariantFull _ cn cap 0 st hObjInv hInv hO hLk).1

/-- WS-ZA ZA5.4: **setting a derivation's untyped source full preserves the
bundle**, given the source still holds a capability. -/
theorem untypedSourceSetFull_preserves_ipcInvariantFull
    (st : SystemState) (src : CSpaceAddr) (cn : CNode) (cap : Capability) {c : Capability}
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hPre : st.objects[src.cnode]? = some (.cnode cn)) (hLk : cn.lookup src.slot = some c) :
    ipcInvariantFull (untypedSourceSetFull st src cap) :=
  untypedSourceSetFull_of (P := ipcInvariantFull) hInv
    fun idx => (setCapFreeIndex_preserves_ipcInvariantFull src cn c idx st hObjInv hInv hPre hLk).1

/-- `.cspaceMint`: the CDT-tracked form the dispatch routes through — the mint,
its edge, and the source set full when it names an untyped. -/
theorem cspaceMintWithCdt_preserves_ipcInvariantFull
    (st st' : SystemState) (src dst : CSpaceAddr) (rights : AccessRightSet)
    (badge : Option SeLe4n.Badge)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hBadgeValid : ∀ b, badge = some b → b.valid)
    (hStep : cspaceMintWithCdt src dst rights badge st = .ok ((), st')) :
    ipcInvariantFull st' := by
  obtain ⟨_, stM, hMint, hLP, -, rfl⟩ := cspaceMintWithCdt_ok_decompose hStep
  obtain ⟨_, _, _, hInsM, -⟩ := cspaceMint_ok_decompose src dst rights badge st stM hMint
  have hInvM := cspaceInsertSlot_preserves_objects_invExt st stM dst _ hObjInv hInsM
  have hMid := cdtRecord_bundle_frame stM src dst DerivationOp.mint hInvM
    (cspaceMint_preserves_ipcInvariantFull st stM src dst rights badge
      hObjInv hInv hBadgeValid hMint)
  obtain ⟨cnS, hOS, hLS⟩ := cspaceInsertSlot_cdtAddChild_src .mint hObjInv hLP hInsM
  exact untypedSourceSetFull_preserves_ipcInvariantFull _ src cnS _
    (SystemState.cdtAddChild_agreeObjects hInvM src dst .mint).2 hMid hOS hLS

/-- `.cspaceCopy`: the copied capability's badge is valid because it was
already at rest in the source slot of a state satisfying the badge clause; the
source is then set full when it names an untyped. -/
theorem cspaceCopy_preserves_ipcInvariantFull
    (st st' : SystemState) (src dst : CSpaceAddr)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hStep : cspaceCopy src dst st = .ok ((), st')) :
    ipcInvariantFull st' := by
  obtain ⟨cap, st2, hL, -, hIns, -, rfl⟩ := cspaceCopy_ok_decompose hStep
  have hBadgeSrc := lookupSlotCap_badge_valid st src cap hInv.badgeWellFormed.2 hL
  have hInv2 := cspaceInsertSlot_preserves_objects_invExt st st2 dst _ hObjInv hIns
  have hMid := cdtRecord_bundle_frame st2 src dst DerivationOp.copy hInv2
    (cspaceInsertSlot_preserves_ipcInvariantFull st st2 dst cap.withoutMapping hObjInv hInv
      (fun b hb => hBadgeSrc b hb) hIns)
  obtain ⟨cnS, hOS, hLS⟩ := cspaceInsertSlot_cdtAddChild_src .copy hObjInv hL hIns
  exact untypedSourceSetFull_preserves_ipcInvariantFull _ src cnS cap
    (SystemState.cdtAddChild_agreeObjects hInv2 src dst .copy).2 hMid hOS hLS

-- ============================================================================
-- §10  Sched-context arm (`.schedContextConfigure`)
-- ============================================================================

/-- The replenishment purge writes release-queue links alone, which the bundle
does not read (WS-ZA ZA6.3). -/
theorem purgeReplenishment_preserves_ipcInvariantFull (st : SystemState)
    (scId : SeLe4n.SchedContextId) (hInv : ipcInvariantFull st) :
    ipcInvariantFull (SchedContextOps.purgeReplenishment st scId) :=
  ipcInvariantFull_of_objectsAgreeOffSchedulerLinks
    (.of_releaseLinks (SchedContextOps.purgeReplenishment_agree st scId)) hInv

/-- `storeObject` form of the SchedContext-content bundle lever. -/
theorem storeObject_schedContextContentUpdate_preserves_ipcInvariantFull
    (st st1 : SystemState) (oid : SeLe4n.ObjId)
    (sc sc' : SeLe4n.Kernel.SchedContext)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hPre : st.objects[oid]? = some (.schedContext sc))
    (hStore : storeObject oid (.schedContext sc') st = .ok ((), st1))
    (hBound : sc'.boundThread = sc.boundThread) :
    ipcInvariantFull st1 := by
  have hAt := storeObject_objects_eq st st1 oid (.schedContext sc') hObjInv hStore
  have hNe : ∀ o : SeLe4n.ObjId, o ≠ oid → st1.objects[o]? = st.objects[o]? :=
    fun o h => storeObject_objects_ne st st1 oid o (.schedContext sc') h hObjInv hStore
  have hView := ipcReadViewAgreement.of_schedContext_content_write hPre hAt hNe hBound
  have hCodes := sameNotificationBindings.of_schedContext_content_write hPre hAt hNe hBound
  have hCap : capabilityBadgesWellFormed st1 := by
    intro o cn slot cap badge hCn hLk hB
    by_cases hK : o = oid
    · rw [hK, hAt] at hCn
      cases Option.some.inj hCn; simp [KernelObject.slotCap] at hLk
    · rw [hNe _ hK] at hCn
      exact hInv.badgeWellFormed.2 o cn slot cap badge hCn hLk hB
  exact ipcInvariantFull_of_readViewAgreement hView hCodes hCap hInv

/-- Re-keying a queued thread's run-queue bucket through its TCB run-queue
links preserves the whole bundle: the objects agree off the run-queue links
(WS-ZA ZA4.5). -/
theorem ipcInvariantFull_of_runRequeueOnCore (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (p : SeLe4n.Priority)
    (hInv : ipcInvariantFull st) :
    ipcInvariantFull (st.runRequeueOnCore c tid p) := by
  have hA := SystemState.runRequeueOnCore_objectsAgreeOffRunLinks st c tid p
  exact ipcInvariantFull_of_objectsAgreeOffRunLinks hA hInv

/-- Domain alignment over any base state: a no-op or a one-TCB rewrite of a
field no conjunct reads. -/
private theorem domainAlignStep_preserves_ipcInvariantFull (stP : SystemState)
    (tid : SeLe4n.ThreadId) (tcbC : TCB) (domain : Nat) (gate : Prop) [Decidable gate]
    (hObjInv : stP.objects.invExt) (hInv : ipcInvariantFull stP)
    (hAt : stP.objects[tid.toObjId]? = some (.tcb tcbC)) :
    ipcInvariantFull (if tcbC.domain.val = domain ∨ gate then stP
      else { stP with objects := stP.objects.insert tid.toObjId (.tcb { tcbC with domain := ⟨domain⟩ }) }) := by
  -- WS-OD (v0.35.3): the domain write gained the ownership gate as a second
  -- disjunct, and the bundle argument is indifferent to it — either disjunct
  -- takes the no-write arm.  Stated over an opaque `gate` so this lemma cannot
  -- drift from whatever the operation's condition is.
  by_cases h : tcbC.domain.val = domain ∨ gate
  · rw [if_pos h]
    exact hInv
  · rw [if_neg h]
    exact insertObjects_tcbFieldUpdate_preserves_ipcInvariantFull stP tid tcbC
      { tcbC with domain := ⟨domain⟩ } hObjInv hInv hAt rfl rfl rfl rfl rfl rfl rfl rfl rfl

/-- The factored propagation tail preserves the whole bundle: the priority
write and domain write touch fields no conjunct reads, and the re-bucket
re-keys a queued thread in place. -/
theorem schedContextConfigureBoundPropagate_preserves_ipcInvariantFull
    (stStored : SystemState) (scId : SeLe4n.SchedContextId)
    (boundTid : SeLe4n.ThreadId) (boundTcb : TCB)
    (priority domain : Nat)
    (hObjInv : stStored.objects.invExt) (hInv : ipcInvariantFull stStored)
    (hBT : stStored.getTcb? boundTid = some boundTcb) :
    ipcInvariantFull (SchedContextOps.schedContextConfigureBoundPropagate stStored scId boundTid
      boundTcb hBT priority domain) := by
  have hBTRaw := (SystemState.getTcb?_eq_some_iff stStored boundTid boundTcb).mp hBT
  unfold SchedContextOps.schedContextConfigureBoundPropagate
  -- `v0.35.71`: both writes are `rewriteObject`, which unfolds to the record
  -- update the bundle levers below are stated over.
  dsimp only [SystemState.rewriteObject]
  -- WS-OD (v0.35.3): both propagations are gated on the bound thread OWNING this
  -- SchedContext, so the "no write" arms now also cover a donated binding.  The
  -- bundle argument is unchanged on every arm.
  by_cases hPrioEq : boundTcb.priority.val = priority ∨
      ¬ SchedContextOps.schedContextConfigurePropagates boundTcb scId
  · rw [if_pos hPrioEq]
    try dsimp only []
    split
    · rename_i currentTcb hCur _
      have hCEq : boundTcb = currentTcb := Option.some.inj (hBT.symm.trans hCur)
      subst hCEq
      exact domainAlignStep_preserves_ipcInvariantFull stStored boundTid boundTcb domain
        _ hObjInv hInv hBTRaw
    · exact hInv
  · rw [if_neg hPrioEq]
    try dsimp only []
    have hInvW := insertObjects_tcbFieldUpdate_preserves_ipcInvariantFull stStored
      boundTid boundTcb { boundTcb with priority := ⟨priority⟩ }
      hObjInv hInv hBTRaw rfl rfl rfl rfl rfl rfl rfl rfl rfl
    have hObjInvW := RobinHood.RHTable.insert_preserves_invExt stStored.objects
      boundTid.toObjId (.tcb { boundTcb with priority := ⟨priority⟩ }) hObjInv
    have hAtW := insertObjects_getElem_self stStored boundTid.toObjId
      (.tcb { boundTcb with priority := ⟨priority⟩ }) hObjInv
    have hSomeW := (SystemState.getTcb?_eq_some_iff
      { stStored with objects := stStored.objects.insert boundTid.toObjId (.tcb { boundTcb with priority := ⟨priority⟩ }) }
      boundTid { boundTcb with priority := ⟨priority⟩ }).mpr hAtW
    by_cases hMem : ({ stStored with objects := stStored.objects.insert boundTid.toObjId (.tcb { boundTcb with priority := ⟨priority⟩ }) } : SystemState).queuedOn
        (determineTargetCore { stStored with objects := stStored.objects.insert boundTid.toObjId (.tcb { boundTcb with priority := ⟨priority⟩ }) } boundTid) boundTid = true
    · rw [if_pos hMem]
      have hInvR := ipcInvariantFull_of_runRequeueOnCore
        { stStored with objects := stStored.objects.insert boundTid.toObjId (.tcb { boundTcb with priority := ⟨priority⟩ }) }
        (determineTargetCore { stStored with objects := stStored.objects.insert boundTid.toObjId (.tcb { boundTcb with priority := ⟨priority⟩ }) } boundTid)
        boundTid
        (match boundTcb.pipBoost with
          | none => ⟨priority⟩
          | some boostPri => ⟨Nat.max priority boostPri.val⟩)
        hInvW
      -- The re-key relinked the thread's run-queue fields, so the domain step
      -- reads the re-keyed record (WS-ZA ZA4.5).
      split
      · rename_i currentTcb hCur _
        exact domainAlignStep_preserves_ipcInvariantFull _ boundTid _ domain
          _ (SystemState.runRequeueOnCore_objects_invExt _ _ _ _ hObjInvW) hInvR
          ((SystemState.getTcb?_eq_some_iff _ _ _).mp hCur)
      · exact hInvR
    · rw [if_neg hMem]
      split
      · rename_i currentTcb hCur _
        have hCEq : { boundTcb with priority := ⟨priority⟩ } = currentTcb :=
          Option.some.inj (hSomeW.symm.trans hCur)
        subst hCEq
        exact domainAlignStep_preserves_ipcInvariantFull _ boundTid _ domain
          _ hObjInvW hInvW hAtW
      · exact hInvW

/-- `.schedContextConfigure`: the SC rewrite keeps `boundThread`, the optional
priority/domain propagation is the factored tail above. -/
theorem schedContextConfigure_preserves_ipcInvariantFull
    (st st' : SystemState) (vScId : SeLe4n.ValidObjId)
    (budget period priority deadline domain : Nat)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hStep : SchedContextOps.schedContextConfigure vScId budget period priority deadline
      domain st = .ok ((), st')) :
    ipcInvariantFull st' := by
  unfold SchedContextOps.schedContextConfigure at hStep
  split at hStep
  · contradiction
  · split at hStep
    · rename_i sc hSc
      dsimp only [] at hStep
      split at hStep
      · split at hStep
        · contradiction
        · rename_i stStored hStore
          have hScRaw := (SystemState.getSchedContext?_eq_some_iff st
            (SchedContextId.ofObjId vScId.val) sc).mp hSc
          -- The purge writes the context's release links alone: the store it
          -- leaves holds the context off them, with the same bound thread.
          have hA := SchedContextOps.purgeReplenishment_agree st ⟨vScId.val.toNat⟩
          have hInvCleaned := purgeReplenishment_preserves_ipcInvariantFull st ⟨vScId.val.toNat⟩ hInv
          have hObjInvCleaned :=
            SchedContextOps.purgeReplenishment_objects_invExt st ⟨vScId.val.toNat⟩ hObjInv
          obtain ⟨scP, hScP, hEP⟩ := hA.symm.getSchedContext?_some' hSc
          have hInvStored := storeObject_schedContextContentUpdate_preserves_ipcInvariantFull
            (SchedContextOps.purgeReplenishment st ⟨vScId.val.toNat⟩)
            stStored vScId.val scP _ hObjInvCleaned hInvCleaned
            ((SystemState.getSchedContext?_eq_some_iff _ _ scP).mp hScP) hStore
            (by
              have h := SeLe4n.Kernel.SchedContext.proj_eq_of_withoutRelease_eq (sc' := sc)
                (sc := scP) (fun x : SchedContext => x.boundThread) hEP
              exact (SchedContextOps.configuredSchedContext_boundThread _ _ _ _ _ _ _ _).trans h)
          have hObjInvStored0 := storeObject_preserves_objects_invExt
            (SchedContextOps.purgeReplenishment st ⟨vScId.val.toNat⟩)
            stStored vScId.val _ hObjInvCleaned hStore
          split at hStep
          · cases hStep
            exact hInvStored
          · rename_i boundTid hBound
            -- The release placement writes release links alone (WS-ZA ZA6.4).
            have hObjInvStored := SystemState.releasePlace_objects_invExt stStored
              (determineTargetCore st boundTid) ⟨vScId.val.toNat⟩ hObjInvStored0
            replace hInvStored := ipcInvariantFull_of_objectsAgreeOffSchedulerLinks
              (.of_releaseLinks (SystemState.releasePlace_agree stStored
                (determineTargetCore st boundTid) ⟨vScId.val.toNat⟩)) hInvStored
            generalize stStored.releasePlace (determineTargetCore st boundTid) ⟨vScId.val.toNat⟩ =
              stPlaced at hStep hObjInvStored hInvStored
            split at hStep
            · rename_i boundTcb hBT _
              cases hStep
              have hObjP : (markKeyChangeFor (markCandidacyGainFor
                  (SchedContextOps.schedContextConfigureBoundPropagate
                  stPlaced ⟨vScId.val.toNat⟩ boundTid boundTcb hBT priority domain) boundTid
                  (hasSufficientBudget st boundTcb)) boundTid
                  (effectiveSchedParams st boundTcb)).objects.invExt := by
                rw [markKeyChangeFor_objects, markCandidacyGainFor_objects]
                exact SchedContextOps.schedContextConfigureBoundPropagate_preserves_objects_invExt
                  _ _ _ _ _ _ _ hObjInvStored
              -- WS-ZA ZA6.4: the resume tail writes run-queue links alone.
              refine ipcInvariantFull_of_objectsAgreeOffSchedulerLinks
                (.of_runLinks (SchedContextOps.configureResumeBound_objectsAgreeOffRunLinks _ _ _)) ?_
              exact PriorityInheritance.repropagateFromWaiter_preserves ipcInvariantFull _ _ _ _
                (fun _ _ => propagatePipChainCrossCore_preserves_ipcInvariantFull _ _ _ _ hObjP
                  (markKeyChangeFor_preserves_ipcInvariantFull _ _ _
                    (markCandidacyGainFor_preserves_ipcInvariantFull _ _ _
                    (schedContextConfigureBoundPropagate_preserves_ipcInvariantFull stPlaced
                      _ boundTid boundTcb priority domain hObjInvStored hInvStored hBT))))
                (markKeyChangeFor_preserves_ipcInvariantFull _ _ _
                  (markCandidacyGainFor_preserves_ipcInvariantFull _ _ _
                  (schedContextConfigureBoundPropagate_preserves_ipcInvariantFull stPlaced
                    _ boundTid boundTcb priority domain hObjInvStored hInvStored hBT)))
            · cases hStep
              exact hInvStored
      · contradiction
    · contradiction

/-- WS-ZA ZA6.4: `.schedContextConfigure` through a core's control: the move of
the context's thread to the control's core, then the configure there. -/
theorem schedControlConfigure_preserves_ipcInvariantFull
    (st st' : SystemState) (core : CoreId) (vScId : SeLe4n.ValidObjId)
    (budget period priority deadline domain : Nat)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hStep : SchedContextOps.schedControlConfigure core vScId budget period priority deadline
      domain st = .ok ((), st')) :
    ipcInvariantFull st' := by
  rcases SchedContextOps.schedControlConfigure_ok_cases hStep with h | ⟨_, t, stM, sgi, -, -, -, hM, h⟩
  · exact schedContextConfigure_preserves_ipcInvariantFull st st' vScId _ _ _ _ _ hObjInv hInv h
  · exact schedContextConfigure_preserves_ipcInvariantFull stM st' vScId _ _ _ _ _
      (setThreadCpuAffinityWithMigration_preserves_objects_invExt _ _ _ _ hObjInv _ hM)
      (setThreadCpuAffinityWithMigration_preserves_ipcInvariantFull st stM t _ core sgi hObjInv hInv hM) h

-- ============================================================================
-- §11  Sched-context binding arms (`.schedContextBind`, `.schedContextUnbind`)
-- ============================================================================

/-- A TCB's binding pointing at a SchedContext is reciprocated by that
SchedContext's `boundThread`.  The bidirectional-binding discipline both
`schedContextBind` and the donation transitions maintain; consumed as a
pre-state hypothesis by the bind arm, whose no-other-holder obligation it
discharges against the bind guard. -/
def schedContextBindingBidirectional (st : SystemState) : Prop :=
  ∀ (t : SeLe4n.ThreadId) (tcb : TCB) (scId : SeLe4n.SchedContextId),
    st.objects[t.toObjId]? = some (.tcb tcb) →
    tcb.schedContextBinding.scId? = some scId →
    ∃ sc : SeLe4n.Kernel.SchedContext,
      st.objects[scId.toObjId]? = some (.schedContext sc) ∧ sc.boundThread = some t

/-- **The binding-rewrite lever**: a transition that rewrites exactly one
TCB's `schedContextBinding` and the reciprocating SchedContext's
`boundThread` — in either the bind direction (`.unbound → .bound scId`, the
SC previously free) or the unbind direction (`… → .unbound`, the SC
previously naming this thread) — preserves the whole bundle.  The fourteen
binding-free conjuncts ride `donationReadAgreement`; the five donation
conjuncts move and are discharged here, against the direction-specific side
conditions. -/
theorem ipcInvariantFull_of_schedBindingRewrite
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (scId : SeLe4n.SchedContextId)
    (tcb tcb' : TCB) (sc sc' : SeLe4n.Kernel.SchedContext)
    (hInv : ipcInvariantFull st)
    (hPreT : st.objects[tid.toObjId]? = some (.tcb tcb))
    (hAtT : st'.objects[tid.toObjId]? = some (.tcb tcb'))
    (hPreS : st.objects[scId.toObjId]? = some (.schedContext sc))
    (hAtS : st'.objects[scId.toObjId]? = some (.schedContext sc'))
    (hFrame : ∀ oid : SeLe4n.ObjId, oid ≠ tid.toObjId → oid ≠ scId.toObjId →
      st'.objects[oid]? = st.objects[oid]?)
    (hIpc : tcb'.ipcState = tcb.ipcState)
    (hMsg : tcb'.pendingMessage = tcb.pendingMessage)
    (hNext : tcb'.queueNext = tcb.queueNext)
    (hPrev : tcb'.queuePrev = tcb.queuePrev)
    (hPPrev : tcb'.queuePPrev = tcb.queuePPrev)
    (hBudget : tcb'.timeoutBudget = tcb.timeoutBudget)
    (hReply : tcb'.replyObject = tcb.replyObject)
    (hStash : tcb'.pendingReceiveReply = tcb.pendingReceiveReply)
    (hCase :
      (tcb.schedContextBinding = .unbound ∧ tcb'.schedContextBinding = .bound scId ∧
        sc.boundThread = none ∧ sc'.boundThread = some tid ∧
        (∀ (s : SeLe4n.ThreadId) (sTcb : TCB) (sc0 : SeLe4n.SchedContextId),
          st.objects[s.toObjId]? = some (.tcb sTcb) →
          sTcb.schedContextBinding ≠ .donated sc0 tid) ∧
        (∀ (t' : SeLe4n.ThreadId) (tcb2 : TCB), t' ≠ tid →
          st.objects[t'.toObjId]? = some (.tcb tcb2) →
          tcb2.schedContextBinding.scId? ≠ some scId)) ∨
      (tcb'.schedContextBinding = .unbound ∧
        sc.boundThread = some tid ∧ sc'.boundThread = none))
    (hSlots : ∀ (sl : SeLe4n.Slot) (c : Capability) (b : SeLe4n.Badge),
      tcb'.spaceSlotCap sl = some c → c.badge = some b → tcb.spaceSlotCap sl = some c :=
      by intro _ _ _ h _; exact h)
    (hBnc : tcb'.boundNotificationCode = tcb.boundNotificationCode := by rfl) :
    ipcInvariantFull st' := by
  have hNeIds : tid.toObjId ≠ scId.toObjId := by
    intro h
    rw [h, hPreS] at hPreT
    exact absurd (Option.some.inj hPreT) (fun hx => KernelObject.noConfusion hx)
  -- Backward transport of a post-state TCB with every read field but the
  -- binding, plus the binding itself for threads other than `tid`.
  have hBwd : ∀ (oid : SeLe4n.ObjId) (tx : TCB), st'.objects[oid]? = some (.tcb tx) →
      ∃ ty, st.objects[oid]? = some (.tcb ty) ∧
        tx.ipcState = ty.ipcState ∧ tx.pendingMessage = ty.pendingMessage ∧
        tx.queueNext = ty.queueNext ∧ tx.queuePrev = ty.queuePrev ∧
        tx.queuePPrev = ty.queuePPrev ∧
        tx.timeoutBudget = ty.timeoutBudget ∧ tx.replyObject = ty.replyObject ∧
        tx.pendingReceiveReply = ty.pendingReceiveReply ∧
        (oid ≠ tid.toObjId → tx.schedContextBinding = ty.schedContextBinding) := by
    intro oid tx hx
    by_cases hT : oid = tid.toObjId
    · rw [hT, hAtT] at hx
      obtain rfl : tcb' = tx := by
        simpa only [Option.some.injEq, KernelObject.tcb.injEq] using hx
      exact ⟨tcb, by rw [hT]; exact hPreT, hIpc, hMsg, hNext, hPrev, hPPrev,
        hBudget, hReply, hStash, fun h => absurd hT h⟩
    · by_cases hS : oid = scId.toObjId
      · rw [hS, hAtS] at hx
        exact absurd (Option.some.inj hx) (fun h => KernelObject.noConfusion h)
      · rw [hFrame oid hT hS] at hx
        exact ⟨tx, hx, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩
  have hFwd : ∀ (oid : SeLe4n.ObjId) (ty : TCB), st.objects[oid]? = some (.tcb ty) →
      ∃ tx, st'.objects[oid]? = some (.tcb tx) ∧
        tx.ipcState = ty.ipcState ∧
        (oid ≠ tid.toObjId → tx.schedContextBinding = ty.schedContextBinding) := by
    intro oid ty hy
    by_cases hT : oid = tid.toObjId
    · rw [hT, hPreT] at hy
      obtain rfl : tcb = ty := by
        simpa only [Option.some.injEq, KernelObject.tcb.injEq] using hy
      exact ⟨tcb', by rw [hT]; exact hAtT, hIpc, fun h => absurd hT h⟩
    · by_cases hS : oid = scId.toObjId
      · rw [hS, hPreS] at hy
        exact absurd (Option.some.inj hy) (fun h => KernelObject.noConfusion h)
      · exact ⟨ty, by rw [hFrame oid hT hS]; exact hy, rfl, fun _ => rfl⟩
  -- The post-state binding of `tid` is never `.donated`.
  have hTidNotDonated : ∀ (s0 : SeLe4n.SchedContextId) (o : SeLe4n.ThreadId),
      tcb'.schedContextBinding ≠ .donated s0 o := by
    intro s0 o h
    rcases hCase with ⟨_, hB, _⟩ | ⟨hB, _⟩ <;> rw [hB] at h <;> cases h
  -- SchedContext lookups off the rewritten one are unchanged.
  have hScNe : ∀ (oid : SeLe4n.ObjId) (x : SeLe4n.Kernel.SchedContext),
      oid ≠ scId.toObjId →
      (st'.objects[oid]? = some (.schedContext x) ↔
        st.objects[oid]? = some (.schedContext x)) := by
    intro oid x hS
    by_cases hT : oid = tid.toObjId
    · rw [hT, hAtT, hPreT]
      constructor
      · intro hx; exact absurd (Option.some.inj hx) (fun h => KernelObject.noConfusion h)
      · intro hx; exact absurd (Option.some.inj hx) (fun h => KernelObject.noConfusion h)
    · rw [hFrame oid hT hS]
  have hRA : ∀ (rid : SeLe4n.ReplyId) (r : Reply),
      (st').objects[rid.toObjId]? = some (.reply r) ↔ st.objects[rid.toObjId]? = some (.reply r) := by
    intro rid r
    by_cases hT : rid.toObjId = tid.toObjId
    · rw [hT, hAtT, hPreT]
      constructor
      · intro hx; cases hx
      · intro hx; cases hx
    · by_cases hS : rid.toObjId = scId.toObjId
      · rw [hS, hAtS, hPreS]
        constructor
        · intro hx; cases hx
        · intro hx; cases hx
      · rw [hFrame _ hT hS]
  have hAgree : donationReadAgreement st st' := by
    refine ⟨?_, ?_, ?_, replyCallerAgree_of_objectAgree hRA,
      replyStasherAgree_of_objectAgree hRA, ?_, ?_, ?_⟩
    · intro oid tx hx
      obtain ⟨ty, hy, h1, h2, h3, h4, h5, h6, h7, h8, _⟩ := hBwd oid tx hx
      exact ⟨ty, hy, h1, pendingMessageReadAgrees_of_eq h2, h3, h4, h5, h6, h7, h8⟩
    · intro oid ty hy
      by_cases hT : oid = tid.toObjId
      · rw [hT, hPreT] at hy
        obtain rfl : tcb = ty := by
          simpa only [Option.some.injEq, KernelObject.tcb.injEq] using hy
        exact ⟨tcb', by rw [hT]; exact hAtT, hIpc, pendingMessageReadAgrees_of_eq hMsg,
          hNext, hPrev, hPPrev, hBudget, hReply, hStash⟩
      · by_cases hS : oid = scId.toObjId
        · rw [hS, hPreS] at hy
          exact absurd (Option.some.inj hy) (fun h => KernelObject.noConfusion h)
        · exact ⟨ty, by rw [hFrame oid hT hS]; exact hy,
            rfl, pendingMessageReadAgrees_refl _, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · intro oid k hkT hkS _
      by_cases hT : oid = tid.toObjId
      · rw [hT, hAtT, hPreT]
        constructor
        · intro hx; exact absurd (Option.some.inj hx).symm (hkT tcb')
        · intro hx; exact absurd (Option.some.inj hx).symm (hkT tcb)
      · by_cases hS : oid = scId.toObjId
        · rw [hS, hAtS, hPreS]
          constructor
          · intro hx; exact absurd (Option.some.inj hx).symm (hkS sc')
          · intro hx; exact absurd (Option.some.inj hx).symm (hkS sc)
        · rw [hFrame oid hT hS]
    · intro oid x hx
      by_cases hS : oid = scId.toObjId
      · exact ⟨sc', by rw [hS]; exact hAtS⟩
      · exact ⟨x, (hScNe oid x hS).mpr hx⟩
    · intro oid o' sl c b hO hL hB
      by_cases hT : oid = tid.toObjId
      · rw [hT, hAtT] at hO; cases hO
        exact ⟨.tcb tcb, by rw [hT]; exact hPreT, hSlots sl c b hL hB⟩
      · by_cases hS : oid = scId.toObjId
        · rw [hS, hAtS] at hO; cases hO
          exact ⟨.schedContext sc, by rw [hS]; exact hPreS, hL⟩
        · exact ⟨o', by rw [← hFrame oid hT hS]; exact hO, hL⟩
    · intro oid
      by_cases hT : oid = tid.toObjId
      · rw [hT, hAtT, hPreT]
        simp only [notificationBindingCodes, KernelObject.bindingCodes, hBnc]
      · by_cases hS : oid = scId.toObjId
        · rw [hS, hAtS, hPreS]; rfl
        · rw [hFrame oid hT hS]
  refine ipcInvariantFull_of_donationReadAgreement st st' hInv hAgree ?_ ?_ ?_ ?_
  · -- donationChainAcyclic
    intro t1 t2 tcb1 tcb2 s1 s2 h1 h2 hB1 hB2
    obtain ⟨y1, hy1, _, _, _, _, _, _, _, _, hb1⟩ := hBwd t1.toObjId tcb1 h1
    obtain ⟨y2, hy2, _, _, _, _, _, _, _, _, hb2⟩ := hBwd t2.toObjId tcb2 h2
    by_cases hT1 : t1.toObjId = tid.toObjId
    · rw [hT1, hAtT] at h1
      obtain rfl : tcb' = tcb1 := by
        simpa only [Option.some.injEq, KernelObject.tcb.injEq] using h1
      exact absurd hB1 (hTidNotDonated s1 t2)
    · by_cases hT2 : t2.toObjId = tid.toObjId
      · rw [hT2, hAtT] at h2
        obtain rfl : tcb' = tcb2 := by
          simpa only [Option.some.injEq, KernelObject.tcb.injEq] using h2
        exact absurd hB2 (hTidNotDonated s2 t1)
      · exact hInv.donationChainAcyclic t1 t2 y1 y2 s1 s2 hy1 hy2
          ((hb1 hT1) ▸ hB1) ((hb2 hT2) ▸ hB2)
  · -- donationOwnerValid
    intro t tcbT s0 owner hT hB
    by_cases hTt : t.toObjId = tid.toObjId
    · rw [hTt, hAtT] at hT
      obtain rfl : tcb' = tcbT := by
        simpa only [Option.some.injEq, KernelObject.tcb.injEq] using hT
      exact absurd hB (hTidNotDonated s0 owner)
    · obtain ⟨y, hy, _, _, _, _, _, _, _, _, hb⟩ := hBwd t.toObjId tcbT hT
      have hBpre : y.schedContextBinding = .donated s0 owner := (hb hTt) ▸ hB
      obtain ⟨⟨scD, hScD, hBoundD⟩, oTcb, hO, hOU, hOB⟩ :=
        hInv.donationOwnerValid t y s0 owner hy hBpre
      constructor
      · by_cases hS0 : s0.toObjId = scId.toObjId
        · exfalso
          have hEq : scD = sc := by
            have := hScD
            rw [hS0, hPreS] at this
            simpa only [Option.some.injEq, KernelObject.schedContext.injEq] using this.symm
          rcases hCase with ⟨_, _, hFree, _⟩ | ⟨_, hSome, _⟩
          · rw [hEq, hFree] at hBoundD
            cases hBoundD
          · rw [hEq, hSome] at hBoundD
            have : tid = t := Option.some.inj hBoundD
            exact hTt (this ▸ rfl)
        · exact ⟨scD, (hScNe s0.toObjId scD hS0).mpr hScD, hBoundD⟩
      · by_cases hOt : owner.toObjId = tid.toObjId
        · have hOwnerIsTid : owner = tid := SeLe4n.ThreadId.toObjId_injective _ _ hOt
          rcases hCase with ⟨_, _, _, _, hNotOwner, _⟩ | ⟨hUnb, _, _⟩
          · exact absurd (hOwnerIsTid ▸ hBpre) (hNotOwner t y s0 hy)
          · subst hOwnerIsTid
            have hOEq : oTcb = tcb := by
              have h2 := hO
              rw [hOt] at h2
              have := h2.symm.trans (hOt ▸ hPreT)
              simpa only [Option.some.injEq, KernelObject.tcb.injEq] using this
            refine ⟨tcb', hOt ▸ hAtT, hUnb, ?_⟩
            rw [hIpc]
            exact hOEq ▸ hOB
        · obtain ⟨oTcb', hO', hOIpc, hOBind⟩ := hFwd owner.toObjId oTcb hO
          exact ⟨oTcb', hO', (hOBind hOt).trans hOU, by rw [hOIpc]; exact hOB⟩
  · -- donationBudgetTransfer
    intro t1 t2 tcb1 tcb2 s0 h1 h2 hNe12 hS1 hS2
    obtain ⟨y1, hy1, _, _, _, _, _, _, _, _, hb1⟩ := hBwd t1.toObjId tcb1 h1
    obtain ⟨y2, hy2, _, _, _, _, _, _, _, _, hb2⟩ := hBwd t2.toObjId tcb2 h2
    by_cases hT1 : t1.toObjId = tid.toObjId
    · have ht1 : t1 = tid := SeLe4n.ThreadId.toObjId_injective _ _ hT1
      rw [hT1, hAtT] at h1
      obtain rfl : tcb' = tcb1 := by
        simpa only [Option.some.injEq, KernelObject.tcb.injEq] using h1
      rcases hCase with ⟨_, hB, _, _, _, hNoOther⟩ | ⟨hB, _, _⟩
      · have hs0 : s0 = scId := by
          rw [hB] at hS1
          simp only [SchedContextBinding.scId?, Option.some.injEq] at hS1
          exact hS1.symm
        have hT2ne : t2 ≠ tid := fun h => hNe12 (ht1.trans h.symm)
        have hT2 : t2.toObjId ≠ tid.toObjId := fun h =>
          hT2ne (SeLe4n.ThreadId.toObjId_injective _ _ h)
        exact hNoOther t2 y2 hT2ne hy2 (hs0 ▸ (hb2 hT2) ▸ hS2)
      · rw [hB] at hS1
        cases hS1
    · by_cases hT2 : t2.toObjId = tid.toObjId
      · have ht2 : t2 = tid := SeLe4n.ThreadId.toObjId_injective _ _ hT2
        rw [hT2, hAtT] at h2
        obtain rfl : tcb' = tcb2 := by
          simpa only [Option.some.injEq, KernelObject.tcb.injEq] using h2
        rcases hCase with ⟨_, hB, _, _, _, hNoOther⟩ | ⟨hB, _, _⟩
        · have hs0 : s0 = scId := by
            rw [hB] at hS2
            simp only [SchedContextBinding.scId?, Option.some.injEq] at hS2
            exact hS2.symm
          have hT1ne : t1 ≠ tid := fun h => hNe12 (h.trans ht2.symm)
          exact hNoOther t1 y1 hT1ne hy1 (hs0 ▸ (hb1 hT1) ▸ hS1)
        · rw [hB] at hS2
          cases hS2
      · exact hInv.donationBudgetTransfer t1 t2 y1 y2 s0 hy1 hy2 hNe12
          ((hb1 hT1) ▸ hS1) ((hb2 hT2) ▸ hS2)
  · -- donationOwnerUnique
    intro t1 t2 tcb1 tcb2 s1 s2 owner h1 h2 hB1 hB2
    obtain ⟨y1, hy1, _, _, _, _, _, _, _, _, hb1⟩ := hBwd t1.toObjId tcb1 h1
    obtain ⟨y2, hy2, _, _, _, _, _, _, _, _, hb2⟩ := hBwd t2.toObjId tcb2 h2
    by_cases hT1 : t1.toObjId = tid.toObjId
    · rw [hT1, hAtT] at h1
      obtain rfl : tcb' = tcb1 := by
        simpa only [Option.some.injEq, KernelObject.tcb.injEq] using h1
      exact absurd hB1 (hTidNotDonated s1 owner)
    · by_cases hT2 : t2.toObjId = tid.toObjId
      · rw [hT2, hAtT] at h2
        obtain rfl : tcb' = tcb2 := by
          simpa only [Option.some.injEq, KernelObject.tcb.injEq] using h2
        exact absurd hB2 (hTidNotDonated s2 owner)
      · exact hInv.donationOwnerUnique t1 t2 y1 y2 s1 s2 owner hy1 hy2
          ((hb1 hT1) ▸ hB1) ((hb2 hT2) ▸ hB2)

/-- `.schedContextBind`: the bidirectional binding write over the
binding-rewrite lever, the optional re-bucket over the re-key lever, and the
thread-index write over the objects/scheduler frame.

The two donation-side conditions are pre-state facts: `hBidir` (with the
guard's "SC free") rules out another holder, and `hNotOwner` rules out
binding a thread that is the recorded owner of an in-flight donation — on
the seL4-MCS discipline such a thread is mid-`Call`, and handing it a fresh
SchedContext there would corrupt the donation bookkeeping the reply's
return path depends on. -/
theorem schedContextBind_preserves_ipcInvariantFull
    (st st' : SystemState) (vScId : SeLe4n.ValidObjId) (vThreadId : SeLe4n.ValidThreadId)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hBidir : schedContextBindingBidirectional st)
    (hNotOwner : ∀ (s : SeLe4n.ThreadId) (sTcb : TCB) (sc0 : SeLe4n.SchedContextId),
      st.objects[s.toObjId]? = some (.tcb sTcb) →
      sTcb.schedContextBinding ≠ .donated sc0 vThreadId.val)
    (hStep : SchedContextOps.schedContextBind vScId vThreadId st = .ok ((), st')) :
    ipcInvariantFull st' := by
  unfold SchedContextOps.schedContextBind at hStep
  split at hStep
  · rename_i sc hSc _
    split at hStep
    · contradiction
    · rename_i hFreeGuard
      -- `v0.35.4`: a context heading a reply stack is refused, so a successful
      -- bind saw none — the guard is discharged here rather than split, which
      -- keeps the arm structure below it what it was.
      have hNoHead : sc.scReply.isSome = false := by
        cases hH : sc.scReply.isSome with
        | false => rfl
        | true => rw [hH] at hStep; simp at hStep
      simp only [hNoHead, Bool.false_eq_true, if_false] at hStep
      split at hStep
      · rename_i tcb hT
        -- `v0.35.4`: and a thread whose reply frame is on a live stack is refused.
        have hNoLive : replyFrameOnLiveStack st tcb = false := by
          cases hL : replyFrameOnLiveStack st tcb with
          | false => rfl
          | true => rw [hL] at hStep; split at hStep <;> simp at hStep
        simp only [hNoLive, Bool.false_eq_true, if_false] at hStep
        split at hStep
        · contradiction
        · split at hStep
          · rename_i hUnbound
            try dsimp only [] at hStep
            -- `v0.35.71`: the two typed writes over `st`, reduced to the double
            -- insert under the pre-state's TCB witness -- the bundle levers
            -- below are stated over that literal.
            rw [SystemState.updateTcb_after_rewriteObject_schedContext st vScId.val _ _
              vThreadId.val tcb _ hObjInv hT] at hStep
            try dsimp only [] at hStep
            cases hStep
            have hFree : sc.boundThread = none := by
              cases hB : sc.boundThread with
              | none => rfl
              | some x => rw [hB] at hFreeGuard; simp at hFreeGuard
            have hPreT := (SystemState.getTcb?_eq_some_iff st vThreadId.val tcb).mp hT
            have hPreS : st.objects[(⟨vScId.val.toNat⟩ : SeLe4n.SchedContextId).toObjId]?
                = some (.schedContext sc) :=
              (SystemState.getSchedContext?_eq_some_iff st
                (SchedContextId.ofObjId vScId.val) sc).mp hSc
            have hNeIds : vThreadId.val.toObjId
                ≠ (⟨vScId.val.toNat⟩ : SeLe4n.SchedContextId).toObjId := by
              intro h
              rw [h, hPreS] at hPreT
              exact absurd (Option.some.inj hPreT) (fun hx => KernelObject.noConfusion hx)
            have hObjInv1 := RobinHood.RHTable.insert_preserves_invExt st.objects
              vScId.val (.schedContext { sc.releaseReadyHead st.machine.timer with boundThreadCode := SeLe4n.ThreadId.optCode (some vThreadId.val), donationOrigin := none }) hObjInv
            have hAtS2 : (( { st with objects := (st.objects.insert vScId.val (.schedContext { sc.releaseReadyHead st.machine.timer with boundThreadCode := SeLe4n.ThreadId.optCode (some vThreadId.val), donationOrigin := none })).insert vThreadId.val.toObjId (.tcb { tcb with scBindingScCode := SeLe4n.Kernel.SchedContextBinding.scCode (.bound ⟨vScId.val.toNat⟩), scBindingOwnerCode := 0, priority := sc.priority }) } : SystemState)).objects[(⟨vScId.val.toNat⟩ : SeLe4n.SchedContextId).toObjId]?
                = some (.schedContext { sc.releaseReadyHead st.machine.timer with boundThreadCode := SeLe4n.ThreadId.optCode (some vThreadId.val), donationOrigin := none }) := by
              have h1 : (st.objects.insert vScId.val (.schedContext { sc.releaseReadyHead st.machine.timer with boundThreadCode := SeLe4n.ThreadId.optCode (some vThreadId.val), donationOrigin := none }))[(⟨vScId.val.toNat⟩ : SeLe4n.SchedContextId).toObjId]? = some (.schedContext { sc.releaseReadyHead st.machine.timer with boundThreadCode := SeLe4n.ThreadId.optCode (some vThreadId.val), donationOrigin := none }) := by
                simp only [RHTable_getElem?_eq_get?]
                exact RobinHood.RHTable.getElem?_insert_self st.objects _ _ hObjInv
              simp only [RHTable_getElem?_eq_get?] at h1 ⊢
              rw [RobinHood.RHTable.getElem?_insert_ne _ vThreadId.val.toObjId _ _
                (by simp only [beq_iff_eq]; exact hNeIds) hObjInv1]
              exact h1
            have hAtT2 : (( { st with objects := (st.objects.insert vScId.val (.schedContext { sc.releaseReadyHead st.machine.timer with boundThreadCode := SeLe4n.ThreadId.optCode (some vThreadId.val), donationOrigin := none })).insert vThreadId.val.toObjId (.tcb { tcb with scBindingScCode := SeLe4n.Kernel.SchedContextBinding.scCode (.bound ⟨vScId.val.toNat⟩), scBindingOwnerCode := 0, priority := sc.priority }) } : SystemState)).objects[vThreadId.val.toObjId]?
                = some (.tcb { tcb with scBindingScCode := SeLe4n.Kernel.SchedContextBinding.scCode (.bound ⟨vScId.val.toNat⟩), scBindingOwnerCode := 0, priority := sc.priority }) := by
              simp only [RHTable_getElem?_eq_get?]
              exact RobinHood.RHTable.getElem?_insert_self _ _ _ hObjInv1
            have hFrame2 : ∀ oid : SeLe4n.ObjId, oid ≠ vThreadId.val.toObjId →
                oid ≠ (⟨vScId.val.toNat⟩ : SeLe4n.SchedContextId).toObjId →
                (( { st with objects := (st.objects.insert vScId.val (.schedContext { sc.releaseReadyHead st.machine.timer with boundThreadCode := SeLe4n.ThreadId.optCode (some vThreadId.val), donationOrigin := none })).insert vThreadId.val.toObjId (.tcb { tcb with scBindingScCode := SeLe4n.Kernel.SchedContextBinding.scCode (.bound ⟨vScId.val.toNat⟩), scBindingOwnerCode := 0, priority := sc.priority }) } : SystemState)).objects[oid]?
                  = st.objects[oid]? := by
              intro oid hNeT hNeS
              simp only [RHTable_getElem?_eq_get?]
              rw [RobinHood.RHTable.getElem?_insert_ne _ vThreadId.val.toObjId oid _
                (by simp only [beq_iff_eq]; exact fun h => hNeT h.symm) hObjInv1]
              rw [RobinHood.RHTable.getElem?_insert_ne st.objects vScId.val oid _
                (by simp only [beq_iff_eq]; exact fun h => hNeS (h.symm.trans rfl)) hObjInv]
            have hNoOther : ∀ (t' : SeLe4n.ThreadId) (tcb2 : TCB), t' ≠ vThreadId.val →
                st.objects[t'.toObjId]? = some (.tcb tcb2) →
                tcb2.schedContextBinding.scId? ≠ some ⟨vScId.val.toNat⟩ := by
              intro t' tcb2 _ hT2 hS2
              obtain ⟨scX, hScX, hBX⟩ := hBidir t' tcb2 ⟨vScId.val.toNat⟩ hT2 hS2
              have : scX = sc := by
                have := hScX.symm.trans hPreS
                simpa only [Option.some.injEq, KernelObject.schedContext.injEq] using this
              rw [this, hFree] at hBX
              cases hBX
            have hInv2 := ipcInvariantFull_of_schedBindingRewrite st _ vThreadId.val
              ⟨vScId.val.toNat⟩ tcb
              { tcb with scBindingScCode := SeLe4n.Kernel.SchedContextBinding.scCode (.bound ⟨vScId.val.toNat⟩), scBindingOwnerCode := 0, priority := sc.priority }
              sc { sc.releaseReadyHead st.machine.timer with boundThreadCode := SeLe4n.ThreadId.optCode (some vThreadId.val), donationOrigin := none }
              hInv hPreT hAtT2 hPreS hAtS2 hFrame2
              rfl rfl rfl rfl rfl rfl rfl rfl
              (Or.inl ⟨hUnbound, rfl, hFree, rfl, hNotOwner, hNoOther⟩)
            -- The release placement at the bind's end writes release links
            -- alone (WS-ZA ZA6.4); the key-change hook before it a flag or nothing.
            refine ipcInvariantFull_of_objectsAgreeOffSchedulerLinks
              (.of_releaseLinks (SystemState.releasePlace_agree _ _ _)) ?_
            refine markKeyChangeFor_preserves_ipcInvariantFull _ _ _ ?_
            split
            · -- The re-bucket arm: a re-key through the TCB run-queue links
              -- (WS-ZA ZA4.5).
              exact ipcInvariantFull_of_runRequeueOnCore _ _ _ _ hInv2
            · -- **WS-RR RR8.12 Cut B2 (`v0.35.182`)**: the two remaining arms — the
              -- placement of a parked runnable thread, and the identity.  The
              -- placement writes only run-queue links, which no conjunct reads,
              -- so the bundle survives for the same reason as the re-bucket.
              split
              · rename_i hPark
                refine markReschedulePendingOnCore_preserves_ipcInvariantFull _ _
                  (ipcInvariantFull_runEnqueueOnCore _ _ _ _ hInv2)
              · exact hInv2
          · contradiction
      · contradiction
  · contradiction

-- ============================================================================
-- §12  The scheduler switch chain (shared by the unbind, suspend and resume
--      arms' scheduling points)
-- ============================================================================

/-- `preemptCurrentOnCore` preserves the whole bundle: its one object write
saves the preempted thread's register context — a field no conjunct reads —
and its one queue write re-enqueues that thread (run-queue links only). -/
theorem preemptCurrentOnCore_preserves_ipcInvariantFull (st : SystemState)
    (c : CoreId) (incoming : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st) :
    ipcInvariantFull (preemptCurrentOnCore st c incoming) := by
  unfold preemptCurrentOnCore
  split
  · exact hInv
  · split
    · exact hInv
    · rename_i prevTid _ hPrev
      split
      · rename_i prevTcb hPrevTcb _
        -- The in-place rewrite IS the insert; the re-enqueue writes only
        -- run-queue links, so the proof below is stated over the rewritten
        -- pre-state.
        refine ipcInvariantFull_runEnqueueOnCore _ c prevTid _ ?_
        dsimp only [SystemState.rewriteObject]
        have hPreRaw := (SystemState.getTcb?_eq_some_iff st prevTid prevTcb).mp hPrevTcb
        have hAt := insertObjects_getElem_self st prevTid.toObjId
          (.tcb { prevTcb with registerContext := st.machine.regsOnCore c }) hObjInv
        refine ipcInvariantFull_of_tcbFieldUpdate st _ prevTid.toObjId prevTcb
          { prevTcb with registerContext := st.machine.regsOnCore c }
          hInv hPreRaw ?_ ?_ rfl rfl rfl rfl rfl rfl rfl rfl rfl
        · exact hAt
        · exact fun oid hNe => insertObjects_getElem_ne st prevTid.toObjId _ oid hNe hObjInv
      · exact hInv

/-- A preempted `current` thread with no TCB leaves the preempt a no-op. -/
theorem preemptCurrentOnCore_noop_of_prev_no_tcb (st : SystemState) (c : CoreId)
    (incoming prev : SeLe4n.ThreadId)
    (hCur : st.scheduler.currentOnCore c = some prev)
    (hne : ¬(prev == incoming) = true)
    (hNo : st.getTcb? prev = none) :
    preemptCurrentOnCore st c incoming = st := by
  unfold preemptCurrentOnCore
  rw [hCur]
  dsimp only []
  rw [if_neg hne, SystemState.getTcbWitnessed?_eq_none hNo]

/-- The preempted `current` thread is on the core's queue afterwards. -/
theorem preemptCurrentOnCore_prev_mem (st : SystemState) (c : CoreId)
    (incoming prev : SeLe4n.ThreadId) (ptcb : TCB)
    (hCur : st.scheduler.currentOnCore c = some prev)
    (hne : ¬(prev == incoming) = true)
    (hPT : st.getTcb? prev = some ptcb) (hObjInv : st.objects.invExt)
    (hAdm : st.runEnqueueAdmits c prev = true) :
    prev ∈ (preemptCurrentOnCore st c incoming).scheduler.runQueueOnCore c := by
  unfold preemptCurrentOnCore
  rw [hCur]
  dsimp only []
  rw [if_neg hne, SystemState.getTcbWitnessed?_eq_some hPT]
  dsimp only []
  rw [SystemState.runEnqueueOnCore_runQueueOnCore_self _ (by
    rw [SystemState.runEnqueueAdmits_rewriteObject_tcb
      (t' := { ptcb with registerContext := st.machine.regsOnCore c }) _ hObjInv hPT rfl]
    exact hAdm)]
  exact (RunQueue.mem_insert _ _ _ _).mpr (Or.inr rfl)

/-- `switchToThreadOnCore` preserves the whole bundle.  Objects move only in
the preempt stage; the queue removal and the incoming context restore write
only run-queue links and scheduler state, which no conjunct reads. -/
theorem switchToThreadOnCore_preserves_ipcInvariantFull (st : SystemState)
    (c : CoreId) (tid : SeLe4n.ThreadId) (st' : SystemState)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hStep : switchToThreadOnCore st c tid = .ok st') :
    ipcInvariantFull st' := by
  unfold switchToThreadOnCore at hStep
  split at hStep
  · rename_i tidTcb hTid
    split at hStep
    · rename_i hAdmit
      dsimp only [] at hStep
      cases hStep
      have hP := preemptCurrentOnCore_preserves_ipcInvariantFull st c tid hObjInv hInv
      have hA : ((preemptCurrentOnCore st c tid).runRemoveOnCore c tid).objectsAgreeOffRunLinks
          (preemptCurrentOnCore st c tid) := SystemState.runRemoveOnCore_objectsAgreeOffRunLinks _ _ _
      exact ipcInvariantFull_of_objectsAgreeOffRunLinks
        (s1 := preemptCurrentOnCore st c tid)
        (.trans (.of_objects_eq (restoreIncomingContextOnCoreUnlessCurrent_objects _ _ _)) hA) hP
    · contradiction
  · contradiction

/-- The handler's drop of an out-of-domain incumbent preserves the whole bundle:
the preempt re-queues the incumbent, and clearing the slot writes no object. -/
theorem dropCurrentOnCore_preserves_ipcInvariantFull (st : SystemState) (c : CoreId)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st) :
    ipcInvariantFull (dropCurrentOnCore st c) := by
  have hInv2 := preemptCurrentOnCore_preserves_ipcInvariantFull st c (idleThreadId c) hObjInv hInv
  exact ipcInvariantFull_of_getElem_eq (s1 := preemptCurrentOnCore st c (idleThreadId c))
    (fun _ => rfl) hInv2

/-- The reschedule SGI handler preserves the whole bundle: it is a pure
selection followed by (at most) a switch. -/
theorem handleRescheduleSgiOnCore_preserves_ipcInvariantFull (st : SystemState)
    (c : CoreId) (st' : SystemState)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hStep : handleRescheduleSgiOnCore st c = .ok st') :
    ipcInvariantFull st' := by
  unfold handleRescheduleSgiOnCore at hStep
  split at hStep
  · contradiction
  · split at hStep
    · rename_i hOut
      cases hStep
      exact clearReschedulePendingOnCore_preserves_ipcInvariantFull _ _
        (dropCurrentOnCore_preserves_ipcInvariantFull st c hObjInv hInv)
    · cases hStep
      exact clearReschedulePendingOnCore_preserves_ipcInvariantFull _ _ hInv
  · split at hStep
    · split at hStep
      · rename_i sSw hSw
        cases hStep
        exact clearReschedulePendingOnCore_preserves_ipcInvariantFull _ _
          (switchToThreadOnCore_preserves_ipcInvariantFull st c _ sSw hObjInv hInv hSw)
      · split at hStep
        · rename_i hOut
          cases hStep
          exact clearReschedulePendingOnCore_preserves_ipcInvariantFull _ _
            (dropCurrentOnCore_preserves_ipcInvariantFull st c hObjInv hInv)
        · cases hStep
          exact clearReschedulePendingOnCore_preserves_ipcInvariantFull _ _ hInv
    · cases hStep
      exact clearReschedulePendingOnCore_preserves_ipcInvariantFull _ _ hInv

/-- The per-core preemption seam preserves the whole bundle in every arm. -/
theorem priorityRescheduleOnCore_preserves_ipcInvariantFull (st : SystemState)
    (running? : Option CoreId) (ec : CoreId) (b : Bool)
    (st' : SystemState) (sgi : Option (CoreId × Concurrency.SgiKind))
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hStep : SchedContext.PriorityManagement.priorityRescheduleOnCore st running? ec b
      = .ok (st', sgi)) :
    ipcInvariantFull st' := by
  unfold SchedContext.PriorityManagement.priorityRescheduleOnCore at hStep
  split at hStep
  · split at hStep
    · split at hStep
      · split at hStep
        · rename_i hH
          cases hStep
          exact handleRescheduleSgiOnCore_preserves_ipcInvariantFull st ec _ hObjInv hInv hH
        · contradiction
      · cases hStep
        exact hInv
    · cases hStep
      exact hInv
  · cases hStep
    exact hInv

/-- `applyPriorityChangeOnCore` is the priority-source write, the bucket re-key,
and the preemption seam on the core running the thread.  WS-BP BP7.6: the seam
is live, so a local preemption switches the executing core — the SM10.1
obligation this proof used to defer, discharged by
`priorityRescheduleOnCore_preserves_ipcInvariantFull`. -/
theorem applyPriorityChangeOnCore_preserves_ipcInvariantFull
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (p : SeLe4n.Priority) (ec : CoreId) (b : Bool)
    (sgi : Option (CoreId × Concurrency.SgiKind))
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hPre : st.objects[tid.toObjId]? = some (.tcb tcb))
    (hStep : SchedContext.PriorityManagement.applyPriorityChangeOnCore
      st tid tcb p ec b = .ok (st', sgi)) :
    ipcInvariantFull st' := by
  unfold SchedContext.PriorityManagement.applyPriorityChangeOnCore at hStep
  have hObjMid : (markKeyChangeFor (SchedContext.PriorityManagement.migrateRunQueueBucketOnCore
      (SchedContext.PriorityManagement.updatePrioritySource st tid tcb p) tid p
      (determineTargetCore st tid)) tid (effectiveSchedParams st tcb)).objects.invExt := by
    rw [markKeyChangeFor_objects]
    exact SchedContext.PriorityManagement.migrateRunQueueBucketOnCore_objects_invExt _ _ _ _
      (SchedContext.PriorityManagement.updatePrioritySource_preserves_objects_invExt
        st tid tcb p hObjInv)
  have hInvMid : ipcInvariantFull (markKeyChangeFor
      (SchedContext.PriorityManagement.migrateRunQueueBucketOnCore
        (SchedContext.PriorityManagement.updatePrioritySource st tid tcb p) tid p
        (determineTargetCore st tid)) tid (effectiveSchedParams st tcb)) :=
    markKeyChangeFor_preserves_ipcInvariantFull _ _ _
    (migrateRunQueueBucketOnCore_preserves_ipcInvariantFull _ _ _ _
      (updatePrioritySource_preserves_ipcInvariantFull st tid tcb p hObjInv hInv hPre))
  exact priorityRescheduleOnCore_preserves_ipcInvariantFull _ _ _ _ _ _
    (PriorityInheritance.repropagateFromWaiter_preserves_objects_invExt _ _ _ _ hObjMid)
    (PriorityInheritance.repropagateFromWaiter_preserves ipcInvariantFull _ _ _ _
      (fun _ _ => propagatePipChainCrossCore_preserves_ipcInvariantFull _ _ _ _ hObjMid hInvMid)
      hInvMid) hStep

/-- `.tcbSetPriority`: authority check, then the priority write and bucket
re-key — no conjunct-read field or membership moves. -/
theorem setPriorityOnCore_preserves_ipcInvariantFull
    (st st' : SystemState) (vCallerTid vTargetTid : SeLe4n.ValidThreadId)
    (p : SeLe4n.Priority) (ec : CoreId) (sgi : Option (CoreId × Concurrency.SgiKind))
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hStep : SchedContext.PriorityManagement.setPriorityOnCore
      st vCallerTid vTargetTid p ec = .ok (st', sgi)) :
    ipcInvariantFull st' := by
  unfold SchedContext.PriorityManagement.setPriorityOnCore at hStep
  split at hStep
  · split at hStep
    · contradiction
    · split at hStep
      · rename_i targetTcb hTarget
        exact applyPriorityChangeOnCore_preserves_ipcInvariantFull st st' vTargetTid.val
          targetTcb p ec _ _ hObjInv hInv
          ((SystemState.getTcb?_eq_some_iff st vTargetTid.val targetTcb).mp hTarget) hStep
      · contradiction
  · contradiction

/-- `.tcbSetMCPriority`: the MCP write is a one-TCB rewrite of a field no
conjunct reads; when the new ceiling bites, the same priority-change chain
runs on top. -/
theorem setMCPriorityOnCore_preserves_ipcInvariantFull
    (st st' : SystemState) (vCallerTid vTargetTid : SeLe4n.ValidThreadId)
    (p : SeLe4n.Priority) (ec : CoreId) (sgi : Option (CoreId × Concurrency.SgiKind))
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hStep : SchedContext.PriorityManagement.setMCPriorityOnCore
      st vCallerTid vTargetTid p ec = .ok (st', sgi)) :
    ipcInvariantFull st' := by
  unfold SchedContext.PriorityManagement.setMCPriorityOnCore at hStep
  split at hStep
  · split at hStep
    · contradiction
    · split at hStep
      · rename_i targetTcb hTarget _
        dsimp only [SystemState.rewriteObject] at hStep
        have hPreRaw := (SystemState.getTcb?_eq_some_iff st vTargetTid.val targetTcb).mp hTarget
        have hInvMcp := insertObjects_tcbFieldUpdate_preserves_ipcInvariantFull st
          vTargetTid.val targetTcb { targetTcb with maxControlledPriority := p }
          hObjInv hInv hPreRaw rfl rfl rfl rfl rfl rfl rfl rfl rfl
        have hObjInvMcp := RobinHood.RHTable.insert_preserves_invExt st.objects
          vTargetTid.val.toObjId (.tcb { targetTcb with maxControlledPriority := p }) hObjInv
        have hAtMcp := insertObjects_getElem_self st vTargetTid.val.toObjId
          (.tcb { targetTcb with maxControlledPriority := p }) hObjInv
        split at hStep
        · exact applyPriorityChangeOnCore_preserves_ipcInvariantFull _ st' vTargetTid.val
            { targetTcb with maxControlledPriority := p } p ec _ _
            hObjInvMcp hInvMcp hAtMcp hStep
        · cases hStep
          exact hInvMcp
      · contradiction
  · contradiction

/-- Clearing a SchedContext's binding when **no** donation and no live TCB
references it preserves the whole bundle — the fail-safe arm of the unbind,
reached when the bound thread's TCB is already gone. -/
private theorem insertObjects_schedContextClear_preserves_ipcInvariantFull
    (st : SystemState) (scObj : SeLe4n.ObjId) (sc sc' : SeLe4n.Kernel.SchedContext)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hPre : st.objects[scObj]? = some (.schedContext sc))
    (hNoTcbRef : ∀ (t : SeLe4n.ThreadId) (tcbT : TCB),
      st.objects[t.toObjId]? = some (.tcb tcbT) → sc.boundThread ≠ some t) :
    ipcInvariantFull { st with objects := st.objects.insert scObj (.schedContext sc') } := by
  have hAt := insertObjects_getElem_self st scObj (.schedContext sc') hObjInv
  have hNe : ∀ oid : SeLe4n.ObjId, oid ≠ scObj →
      ({ st with objects := st.objects.insert scObj (.schedContext sc') }
        : SystemState).objects[oid]? = st.objects[oid]? :=
    fun oid h => insertObjects_getElem_ne st scObj (.schedContext sc') oid h hObjInv
  have hTcbEq : ∀ (oid : SeLe4n.ObjId) (t : TCB),
      ({ st with objects := st.objects.insert scObj (.schedContext sc') }
        : SystemState).objects[oid]? = some (.tcb t) ↔
      st.objects[oid]? = some (.tcb t) := by
    intro oid t
    by_cases h : oid = scObj
    · rw [h, hAt, hPre]
      constructor
      · intro hx; exact absurd (Option.some.inj hx) (fun hk => KernelObject.noConfusion hk)
      · intro hx; exact absurd (Option.some.inj hx) (fun hk => KernelObject.noConfusion hk)
    · rw [hNe oid h]
  have hRA : ∀ (rid : SeLe4n.ReplyId) (r : Reply),
      ({ st with objects := st.objects.insert scObj (.schedContext sc') }).objects[rid.toObjId]? = some (.reply r) ↔ st.objects[rid.toObjId]? = some (.reply r) := by
    intro rid r
    by_cases h : rid.toObjId = scObj
    · rw [h, hAt, hPre]
      constructor
      · intro hx; cases hx
      · intro hx; cases hx
    · rw [hNe _ h]
  have hAgree : donationReadAgreement st
      { st with objects := st.objects.insert scObj (.schedContext sc') } := by
    refine ⟨?_, ?_, ?_, replyCallerAgree_of_objectAgree hRA,
      replyStasherAgree_of_objectAgree hRA, ?_, ?_, ?_⟩
    · intro oid tx hx
      exact ⟨tx, (hTcbEq oid tx).mp hx, rfl, pendingMessageReadAgrees_refl _, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · intro oid ty hy
      exact ⟨ty, (hTcbEq oid ty).mpr hy, rfl, pendingMessageReadAgrees_refl _, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · intro oid k hkT hkS _
      by_cases h : oid = scObj
      · rw [h, hAt, hPre]
        constructor
        · intro hx; exact absurd (Option.some.inj hx).symm (hkS sc')
        · intro hx; exact absurd (Option.some.inj hx).symm (hkS sc)
      · rw [hNe oid h]
    · intro oid x hx
      by_cases h : oid = scObj
      · exact ⟨sc', by rw [h]; exact hAt⟩
      · exact ⟨x, by rw [hNe oid h]; exact hx⟩
    · intro oid o' _ _ _ hO hL _
      by_cases h : oid = scObj
      · rw [h, hAt] at hO; cases hO
        exact ⟨.schedContext sc, by rw [h]; exact hPre, hL⟩
      · exact ⟨o', by rw [← hNe oid h]; exact hO, hL⟩
    · intro oid
      by_cases h : oid = scObj
      · rw [h, hAt, hPre]; rfl
      · rw [hNe oid h]
  refine ipcInvariantFull_of_donationReadAgreement st _ hInv hAgree ?_ ?_ ?_ ?_
  · intro t1 t2 tcb1 tcb2 s1 s2 h1 h2 hB1 hB2
    exact hInv.donationChainAcyclic t1 t2 tcb1 tcb2 s1 s2
      ((hTcbEq _ _).mp h1) ((hTcbEq _ _).mp h2) hB1 hB2
  · intro t tcbT s0 owner hT hB
    obtain ⟨⟨scD, hScD, hBoundD⟩, oTcb, hO, hOU, hOB⟩ :=
      hInv.donationOwnerValid t tcbT s0 owner ((hTcbEq _ _).mp hT) hB
    constructor
    · by_cases hS0 : s0.toObjId = scObj
      · exfalso
        have hEq : scD = sc := by
          have := hScD
          rw [hS0, hPre] at this
          simpa only [Option.some.injEq, KernelObject.schedContext.injEq] using this.symm
        exact hNoTcbRef t tcbT ((hTcbEq _ _).mp hT) (by rw [← hEq]; exact hBoundD)
      · exact ⟨scD, by rw [hNe _ hS0]; exact hScD, hBoundD⟩
    · exact ⟨oTcb, (hTcbEq _ _).mpr hO, hOU, hOB⟩
  · intro t1 t2 tcb1 tcb2 s0 h1 h2 hNe12 hS1 hS2
    exact hInv.donationBudgetTransfer t1 t2 tcb1 tcb2 s0
      ((hTcbEq _ _).mp h1) ((hTcbEq _ _).mp h2) hNe12 hS1 hS2
  · intro t1 t2 tcb1 tcb2 s1 s2 owner h1 h2 hB1 hB2
    exact hInv.donationOwnerUnique t1 t2 tcb1 tcb2 s1 s2 owner
      ((hTcbEq _ _).mp h1) ((hTcbEq _ _).mp h2) hB1 hB2

/-- The object-writing tail of the unbind — bidirectional clear, replenish
purge, index write — over any scheduler-stage state `stA` that still holds
the pre-state objects.  The binding-rewrite lever carries the clear. -/
private theorem schedContextUnbindTail_preserves_ipcInvariantFull
    (stA : SystemState) (scObj : SeLe4n.ObjId) (tid : SeLe4n.ThreadId)
    (sc : SeLe4n.Kernel.SchedContext) (tcb : TCB)
    (h : stA.rewriteAdmissible scObj
      (.schedContext { sc with boundThreadCode := 0, isActive := false, donationOrigin := none }))
    (hObjInvA : stA.objects.invExt) (hInvA : ipcInvariantFull stA)
    (hPreS : stA.objects[scObj]? = some (.schedContext sc))
    (hPreT : stA.objects[tid.toObjId]? = some (.tcb tcb))
    (hBoundEq : sc.boundThread = some tid) :
    ipcInvariantFull ((stA.rewriteObject scObj
          (.schedContext { sc with boundThreadCode := 0, isActive := false, donationOrigin := none })
          h).updateTcb tid (fun t => { t with scBindingScCode := 0, scBindingOwnerCode := 0 })) := by
  -- `v0.35.71`: the two typed writes, reduced to the double insert the levers
  -- below are stated over.
  rw [SystemState.updateTcb_after_rewriteObject_schedContext stA scObj _ h tid tcb _ hObjInvA
    ((SystemState.getTcb?_eq_some_iff stA tid tcb).mpr hPreT)]
  have hScObjEq : (⟨scObj.toNat⟩ : SeLe4n.SchedContextId).toObjId = scObj := rfl
  have hObjInv2 := RobinHood.RHTable.insert_preserves_invExt stA.objects scObj
    (.schedContext { sc with boundThreadCode := 0, isActive := false, donationOrigin := none }) hObjInvA
  have hNeIds : tid.toObjId ≠ scObj := by
    intro h
    rw [h, hPreS] at hPreT
    exact absurd (Option.some.inj hPreT) (fun hx => KernelObject.noConfusion hx)
  have hAtS3 : (({ { stA with objects := (stA.objects.insert scObj (.schedContext { sc with boundThreadCode := 0, isActive := false, donationOrigin := none })) } with objects := ((stA.objects.insert scObj (.schedContext { sc with boundThreadCode := 0, isActive := false, donationOrigin := none }))).insert tid.toObjId (.tcb { tcb with scBindingScCode := 0, scBindingOwnerCode := 0 }) } : SystemState)).objects[scObj]? = some (.schedContext { sc with boundThreadCode := 0, isActive := false, donationOrigin := none }) := by
    simp only [RHTable_getElem?_eq_get?]
    rw [RobinHood.RHTable.getElem?_insert_ne _ tid.toObjId scObj _
      (by simp only [beq_iff_eq]; exact hNeIds) hObjInv2]
    exact RobinHood.RHTable.getElem?_insert_self stA.objects scObj _ hObjInvA
  have hAtT3 : (({ { stA with objects := (stA.objects.insert scObj (.schedContext { sc with boundThreadCode := 0, isActive := false, donationOrigin := none })) } with objects := ((stA.objects.insert scObj (.schedContext { sc with boundThreadCode := 0, isActive := false, donationOrigin := none }))).insert tid.toObjId (.tcb { tcb with scBindingScCode := 0, scBindingOwnerCode := 0 }) } : SystemState)).objects[tid.toObjId]? = some (.tcb { tcb with scBindingScCode := 0, scBindingOwnerCode := 0 }) := by
    simp only [RHTable_getElem?_eq_get?]
    exact RobinHood.RHTable.getElem?_insert_self _ _ _ hObjInv2
  have hFrame3 : ∀ oid : SeLe4n.ObjId, oid ≠ tid.toObjId → oid ≠ scObj →
      (({ { stA with objects := (stA.objects.insert scObj (.schedContext { sc with boundThreadCode := 0, isActive := false, donationOrigin := none })) } with objects := ((stA.objects.insert scObj (.schedContext { sc with boundThreadCode := 0, isActive := false, donationOrigin := none }))).insert tid.toObjId (.tcb { tcb with scBindingScCode := 0, scBindingOwnerCode := 0 }) } : SystemState)).objects[oid]? = stA.objects[oid]? := by
    intro oid hNeT hNeS
    simp only [RHTable_getElem?_eq_get?]
    rw [RobinHood.RHTable.getElem?_insert_ne _ tid.toObjId oid _
      (by simp only [beq_iff_eq]; exact fun h => hNeT h.symm) hObjInv2]
    rw [RobinHood.RHTable.getElem?_insert_ne stA.objects scObj oid _
      (by simp only [beq_iff_eq]; exact fun h => hNeS h.symm) hObjInvA]
  have hPreS' : stA.objects[(⟨scObj.toNat⟩ : SeLe4n.SchedContextId).toObjId]?
      = some (.schedContext sc) := hPreS
  have hInv3 := ipcInvariantFull_of_schedBindingRewrite stA _ tid ⟨scObj.toNat⟩ tcb
    { tcb with scBindingScCode := 0, scBindingOwnerCode := 0 }
    sc { sc with boundThreadCode := 0, isActive := false, donationOrigin := none }
    hInvA hPreT (hScObjEq ▸ hAtT3) hPreS' (hScObjEq ▸ hAtS3)
    (fun oid hT hS => hFrame3 oid hT (hScObjEq ▸ hS))
    rfl rfl rfl rfl rfl rfl rfl rfl
    (Or.inr ⟨rfl, hBoundEq, rfl⟩)
  exact ipcInvariantFull_of_objects_eq rfl hInv3

/-- The unbind's run-queue stage keeps the bundle: a re-key keeps membership, a
placement only grows it, both through the TCB run-queue links (WS-ZA ZA4.5). -/
theorem schedContextUnbindQueueStage_preserves_ipcInvariantFull (T : SystemState)
    (home : CoreId) (tid : SeLe4n.ThreadId) (prio : SeLe4n.Priority) (wasCurrent : Bool)
    (h : ipcInvariantFull T) :
    ipcInvariantFull (SchedContextOps.schedContextUnbindQueueStage T home tid prio wasCurrent) := by
  unfold SchedContextOps.schedContextUnbindQueueStage
  split
  · exact ipcInvariantFull_of_runRequeueOnCore _ _ _ _ h
  · split
    · exact markReschedulePendingOnCore_preserves_ipcInvariantFull _ _
        (ipcInvariantFull_runEnqueueOnCore _ _ _ _ h)
    · exact h

/-- `.schedContextUnbind` (core transition).

Unconditional on the bound thread's IPC state, as seL4 MCS's
`schedContext_unbindTCB` is: a thread blocked sending or calling stays blocked,
now unbound, and no conjunct of the bundle reads whether an unbound thread is
runnable (`v0.36.136` retired `passiveServerIdle`, the conjunct that did). -/
theorem schedContextUnbind_preserves_ipcInvariantFull
    (st st' : SystemState) (vScId : SeLe4n.ValidObjId)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hStep : SchedContextOps.schedContextUnbind vScId st = .ok ((), st')) :
    ipcInvariantFull st' := by
  unfold SchedContextOps.schedContextUnbind at hStep
  split at hStep
  · rename_i sc hSc _
    split at hStep
    · contradiction
    · rename_i tid hBound
      split at hStep
      · rename_i tcb hTcb
        dsimp only [] at hStep
        -- `v0.35.4`: a donated holder is refused, so a successful unbind saw a
        -- binding that is not a donation.
        have hNotDon : tcb.schedContextBinding.isDonated = false := by
          cases hD : tcb.schedContextBinding.isDonated with
          | false => rfl
          | true => rw [hD] at hStep; simp at hStep
        simp only [hNotDon, Bool.false_eq_true, if_false] at hStep
        have hScRaw := (SystemState.getSchedContext?_eq_some_iff st
          (SchedContextId.ofObjId vScId.val) sc).mp hSc
        have hTcbRaw := (SystemState.getTcb?_eq_some_iff st tid tcb).mp hTcb
        -- The current-slot stage, then the two object writes, then the
        -- run-queue stage through the TCB run-queue links (WS-ZA ZA4.5), the
        -- home-core purge, the index write and the key-change hook.
        cases hRC : runningCoreOf? st tid with
        | some rc =>
          rw [hRC] at hStep
          simp only [Option.isSome_some] at hStep
          have hStage : ipcInvariantFull { st with scheduler :=
              (st.scheduler.setCurrentOnCore rc none).markReschedulePendingOnCore rc } :=
            ipcInvariantFull_of_objects_eq (st := st) rfl hInv
          cases hStep
          exact markKeyChangeFor_preserves_ipcInvariantFull _ _ _
            (markCandidacyGainFor_preserves_ipcInvariantFull _ _ _
            (purgeReplenishment_preserves_ipcInvariantFull _ _
                (schedContextUnbindQueueStage_preserves_ipcInvariantFull _ _ _ _ _
                  (schedContextUnbindTail_preserves_ipcInvariantFull _ vScId.val tid sc tcb
                    _ hObjInv hStage hScRaw hTcbRaw hBound))))
        | none =>
          rw [hRC] at hStep
          simp only [Option.isSome_none] at hStep
          cases hStep
          exact markKeyChangeFor_preserves_ipcInvariantFull _ _ _
            (markCandidacyGainFor_preserves_ipcInvariantFull _ _ _
            (purgeReplenishment_preserves_ipcInvariantFull _ _
                (schedContextUnbindQueueStage_preserves_ipcInvariantFull _ _ _ _ _
                  (schedContextUnbindTail_preserves_ipcInvariantFull _ vScId.val tid sc tcb
                    _ hObjInv hInv hScRaw hTcbRaw hBound))))
      · rename_i hTcbNone
        dsimp only [SystemState.rewriteObject] at hStep
        cases hStep
        have hScRaw := (SystemState.getSchedContext?_eq_some_iff st
          (SchedContextId.ofObjId vScId.val) sc).mp hSc
        have hNoRef : ∀ (t : SeLe4n.ThreadId) (tcbT : TCB),
            st.objects[t.toObjId]? = some (.tcb tcbT) → sc.boundThread ≠ some t := by
          intro t tcbT hT hEq
          rw [hBound] at hEq
          obtain rfl : tid = t := Option.some.inj hEq
          rw [(SystemState.getTcb?_eq_some_iff st tid tcbT).mpr hT] at hTcbNone
          cases hTcbNone
        have hInv1 := insertObjects_schedContextClear_preserves_ipcInvariantFull st
          vScId.val sc { sc with boundThreadCode := 0, isActive := false, donationOrigin := none }
          hObjInv hInv hScRaw hNoRef
        have hInv2 := purgeReplenishment_preserves_ipcInvariantFull _ ⟨vScId.val.toNat⟩ hInv1
        refine ipcInvariantFull_of_objects_eq ?_ hInv2
        · rfl
  · contradiction

/-- `.schedContextUnbind` (dispatch arm): the per-core wrapper adds the
preemption seam, which §12 covers. -/
theorem schedContextUnbindOnCore_preserves_ipcInvariantFull
    (st st' : SystemState) (vScId : SeLe4n.ValidObjId) (ec : CoreId)
    (sgi : Option (CoreId × Concurrency.SgiKind))
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hR : st.runQueueRefined)
    (hStep : SchedContextOps.schedContextUnbindOnCore vScId ec st = .ok (st', sgi)) :
    ipcInvariantFull st' := by
  unfold SchedContextOps.schedContextUnbindOnCore at hStep
  dsimp only [] at hStep
  split at hStep
  · contradiction
  · rename_i stMid hUnbind
    have hStage := (SchedContextOps.schedContextUnbind_runQueueEntryStage vScId st stMid hUnbind).1 hObjInv hR
    exact priorityRescheduleOnCore_preserves_ipcInvariantFull stMid _ ec true st' sgi
      hStage.1
      (schedContextUnbind_preserves_ipcInvariantFull st stMid vScId hObjInv hInv hUnbind)
      hStep

-- ============================================================================
-- §13  VSpace page-table arms (`.vspaceMap`, `.vspaceUnmap`)
-- ============================================================================

/-- A single object rewrite at a slot holding a `.vspaceRoot` on both sides —
the page-table write shape shared by `.vspaceMap` and `.vspaceUnmap` — moves
nothing any conjunct reads: the store view agrees on every IPC-read kind,
CNodes are untouched, and the scheduler is framed. -/
private theorem vspaceRootWrite_preserves_ipcInvariantFull
    {st st' : SystemState} {key : SeLe4n.ObjId} {root root' : VSpaceRoot}
    (hInv : ipcInvariantFull st)
    (hPre : st.objects[key]? = some (.vspaceRoot root))
    (hAt : st'.objects[key]? = some (.vspaceRoot root'))
    (hNe : ∀ oid : SeLe4n.ObjId, oid ≠ key → st'.objects[oid]? = st.objects[oid]?) :
    ipcInvariantFull st' := by
  have hView := ipcReadViewAgreement.of_single_inert_write hNe
    (by rw [hPre]; trivial) (by rw [hAt]; trivial)
  have hCodes := sameNotificationBindings.of_single_inert_write hNe
    (by rw [hPre]; trivial) (by rw [hAt]; trivial)
  have hBack : ∀ (tid : SeLe4n.ThreadId) (tcb' : TCB),
      st'.objects[tid.toObjId]? = some (.tcb tcb') →
      ∃ tcb, st.objects[tid.toObjId]? = some (.tcb tcb) ∧
        tcb.ipcState = tcb'.ipcState ∧ tcb.schedContextBinding = tcb'.schedContextBinding := by
    intro tid tcb' h
    by_cases hK : tid.toObjId = key
    · rw [hK, hAt] at h
      exact absurd (Option.some.inj h) (fun hx => KernelObject.noConfusion hx)
    · rw [hNe _ hK] at h
      exact ⟨tcb', h, rfl, rfl⟩
  have hCap : capabilityBadgesWellFormed st' := by
    intro oid cn slot cap badge hCn hLk hB
    by_cases hK : oid = key
    · rw [hK, hAt] at hCn
      cases Option.some.inj hCn; simp [KernelObject.slotCap] at hLk
    · rw [hNe _ hK] at hCn
      exact hInv.badgeWellFormed.2 oid cn slot cap badge hCn hLk hB
  exact ipcInvariantFull_of_readViewAgreement hView hCodes
    hCap hInv

/-- `.vspaceMap` base transition: the one object write replaces a
`.vspaceRoot` with the same root plus one mapping — inert to every conjunct. -/
theorem vspaceMapPage_preserves_ipcInvariantFull
    (st st' : SystemState) (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (paddr : SeLe4n.PAddr) (perms : PagePermissions)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hStep : Architecture.vspaceMapPage asid vaddr paddr perms st = .ok ((), st')) :
    ipcInvariantFull st' := by
  unfold Architecture.vspaceMapPage at hStep
  cases hRes : Architecture.resolveAsidRoot st asid with
  | none => simp [hRes] at hStep
  | some pair =>
      obtain ⟨rootId, root⟩ := pair
      simp only [hRes] at hStep
      obtain ⟨-, hPre, -⟩ :=
        Architecture.resolveAsidRoot_some_implies_obj st asid rootId root hRes
      split at hStep
      · contradiction
      · split at hStep
        · contradiction
        · cases hMp : root.mapPage vaddr paddr perms with
          | none => simp [hMp] at hStep
          | some root' =>
              simp only [hMp] at hStep
              exact vspaceRootWrite_preserves_ipcInvariantFull hInv hPre
                (storeObject_objects_eq (Architecture.recordPhysicalWrites st _) st' rootId (.vspaceRoot root') hObjInv hStep)
                (fun oid hNe =>
                  storeObject_objects_ne (Architecture.recordPhysicalWrites st _) st' rootId oid (.vspaceRoot root') hNe hObjInv hStep)

/-- `.vspaceUnmap` base transition: same single-`.vspaceRoot`-write shape. -/
theorem vspaceUnmapPage_preserves_ipcInvariantFull
    (st st' : SystemState) (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hStep : Architecture.vspaceUnmapPage asid vaddr st = .ok ((), st')) :
    ipcInvariantFull st' := by
  unfold Architecture.vspaceUnmapPage at hStep
  cases hRes : Architecture.resolveAsidRoot st asid with
  | none => simp [hRes] at hStep
  | some pair =>
      obtain ⟨rootId, root⟩ := pair
      simp only [hRes] at hStep
      obtain ⟨-, hPre, -⟩ :=
        Architecture.resolveAsidRoot_some_implies_obj st asid rootId root hRes
      cases hMp : root.unmapPage vaddr with
      | none => simp [hMp] at hStep
      | some root' =>
          simp only [hMp] at hStep
          exact vspaceRootWrite_preserves_ipcInvariantFull hInv hPre
            (storeObject_objects_eq (Architecture.recordPhysicalWrites st _) st' rootId (.vspaceRoot root') hObjInv hStep)
            (fun oid hNe =>
              storeObject_objects_ne (Architecture.recordPhysicalWrites st _) st' rootId oid (.vspaceRoot root') hNe hObjInv hStep)

/-- The local-flush wrapper adds a `tlb`-only rewrite over the base map. -/
theorem vspaceMapPageWithFlush_preserves_ipcInvariantFull
    (st st' : SystemState) (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (paddr : SeLe4n.PAddr) (perms : PagePermissions)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hStep : Architecture.vspaceMapPageWithFlush asid vaddr paddr perms st = .ok ((), st')) :
    ipcInvariantFull st' := by
  unfold Architecture.vspaceMapPageWithFlush at hStep
  cases hBase : Architecture.vspaceMapPage asid vaddr paddr perms st with
  | error e => simp [hBase] at hStep
  | ok pair =>
      obtain ⟨u, stB⟩ := pair; cases u
      simp only [hBase] at hStep
      have hB := vspaceMapPage_preserves_ipcInvariantFull st stB asid vaddr paddr perms
        hObjInv hInv hBase
      simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
      subst hStep
      refine ipcInvariantFull_of_objects_eq ?_ hB
      · rfl

/-- The state-aware checked wrapper adds pure guards over the flush map. -/
theorem vspaceMapPageCheckedWithFlushFromState_preserves_ipcInvariantFull
    (st st' : SystemState) (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (paddr : SeLe4n.PAddr) (perms : PagePermissions)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hStep : Architecture.vspaceMapPageCheckedWithFlushFromState asid vaddr paddr perms st
      = .ok ((), st')) :
    ipcInvariantFull st' := by
  unfold Architecture.vspaceMapPageCheckedWithFlushFromState at hStep
  split at hStep
  · contradiction
  · split at hStep
    · contradiction
    · split at hStep
      · contradiction
      · exact vspaceMapPageWithFlush_preserves_ipcInvariantFull st st' asid vaddr paddr perms
          hObjInv hInv hStep

/-- The shootdown wrapper adds a `tlbShootdown`-only posting on the remap
direction and is inert on the fresh direction. -/
theorem vspaceMapPageCheckedWithShootdownFromState_preserves_ipcInvariantFull
    (st st' : SystemState) (ec : CoreId) (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (paddr : SeLe4n.PAddr) (perms : PagePermissions)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hStep : Architecture.vspaceMapPageCheckedWithShootdownFromState ec asid vaddr paddr perms st
      = .ok ((), st')) :
    ipcInvariantFull st' := by
  unfold Architecture.vspaceMapPageCheckedWithShootdownFromState at hStep
  dsimp only [] at hStep
  cases hBase : Architecture.vspaceMapPageCheckedWithFlushFromState asid vaddr paddr perms st with
  | error e => simp [hBase] at hStep
  | ok pair =>
      obtain ⟨u, stB⟩ := pair; cases u
      simp only [hBase] at hStep
      have hB := vspaceMapPageCheckedWithFlushFromState_preserves_ipcInvariantFull
        st stB asid vaddr paddr perms hObjInv hInv hBase
      split at hStep
      · rw [Architecture.withShootdownRound_total] at hStep
        simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
        subst hStep
        exact ipcInvariantFull_of_objects_eq
          (Architecture.tlbShootdownBroadcastCoalescing_frame stB ec _ _).1 hB
      · simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
        subst hStep
        exact hB

/-- The per-core TLB drain and fill are `perCoreTlb`-only. -/
private theorem tlbFillOnCore_objects_scheduler (st : SystemState) (c : CoreId)
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) :
    (Architecture.tlbFillOnCore st c asid vaddr).objects = st.objects ∧
    (Architecture.tlbFillOnCore st c asid vaddr).scheduler = st.scheduler := by
  unfold Architecture.tlbFillOnCore
  split <;> simp

/-- `.vspaceMap` (dispatch arm): the full initiator-atomic per-core wrapper —
guards, page-table write, local flush, remap shootdown, initiator drain and
fill — preserves the whole bundle. -/
theorem vspaceMapPageCheckedWithShootdownFromStatePerCore_preserves_ipcInvariantFull
    (st st' : SystemState) (ec : CoreId) (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (paddr : SeLe4n.PAddr) (perms : PagePermissions)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hStep : Architecture.vspaceMapPageCheckedWithShootdownFromStatePerCore ec asid vaddr paddr
      perms st = .ok ((), st')) :
    ipcInvariantFull st' := by
  unfold Architecture.vspaceMapPageCheckedWithShootdownFromStatePerCore at hStep
  cases hBase : Architecture.vspaceMapPageCheckedWithShootdownFromState ec asid vaddr paddr
      perms st with
  | error e => simp [hBase] at hStep
  | ok pair =>
      obtain ⟨u, stM⟩ := pair; cases u
      simp only [hBase] at hStep
      have hB := vspaceMapPageCheckedWithShootdownFromState_preserves_ipcInvariantFull
        st stM ec asid vaddr paddr perms hObjInv hInv hBase
      simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
      subst hStep
      refine ipcInvariantFull_of_objects_eq ?_ hB
      · exact (tlbFillOnCore_objects_scheduler _ _ _ _).1.trans rfl

/-- The local-flush wrapper adds a `tlb`-only rewrite over the base unmap. -/
theorem vspaceUnmapPageWithFlush_preserves_ipcInvariantFull
    (st st' : SystemState) (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hStep : Architecture.vspaceUnmapPageWithFlush asid vaddr st = .ok ((), st')) :
    ipcInvariantFull st' := by
  unfold Architecture.vspaceUnmapPageWithFlush at hStep
  cases hBase : Architecture.vspaceUnmapPage asid vaddr st with
  | error e => simp [hBase] at hStep
  | ok pair =>
      obtain ⟨u, stB⟩ := pair; cases u
      simp only [hBase] at hStep
      have hB := vspaceUnmapPage_preserves_ipcInvariantFull st stB asid vaddr hObjInv hInv hBase
      simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
      subst hStep
      refine ipcInvariantFull_of_objects_eq ?_ hB
      · rfl

/-- The shootdown wrapper adds a `tlbShootdown`-only round posting. -/
theorem vspaceUnmapPageWithShootdown_preserves_ipcInvariantFull
    (st st' : SystemState) (ec : CoreId) (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hStep : Architecture.vspaceUnmapPageWithShootdown ec asid vaddr st = .ok ((), st')) :
    ipcInvariantFull st' := by
  unfold Architecture.vspaceUnmapPageWithShootdown at hStep
  cases hBase : Architecture.vspaceUnmapPageWithFlush asid vaddr st with
  | error e => simp [hBase] at hStep
  | ok pair =>
      obtain ⟨u, stB⟩ := pair; cases u
      simp only [hBase] at hStep
      have hB := vspaceUnmapPageWithFlush_preserves_ipcInvariantFull st stB asid vaddr
        hObjInv hInv hBase
      rw [Architecture.withShootdownRound_total] at hStep
      simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
      subst hStep
      exact ipcInvariantFull_of_objects_eq
        (Architecture.tlbShootdownBroadcastCoalescing_frame stB ec _ _).1 hB

/-- The initiator-atomic wrapper adds the `perCoreTlb`-only drain. -/
theorem vspaceUnmapPageWithShootdownPerCore_preserves_ipcInvariantFull
    (st st' : SystemState) (ec : CoreId) (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hStep : Architecture.vspaceUnmapPageWithShootdownPerCore ec asid vaddr st = .ok ((), st')) :
    ipcInvariantFull st' := by
  unfold Architecture.vspaceUnmapPageWithShootdownPerCore at hStep
  cases hBase : Architecture.vspaceUnmapPageWithShootdown ec asid vaddr st with
  | error e => simp [hBase] at hStep
  | ok pair =>
      obtain ⟨u, stB⟩ := pair; cases u
      simp only [hBase] at hStep
      have hB := vspaceUnmapPageWithShootdown_preserves_ipcInvariantFull st stB ec asid vaddr
        hObjInv hInv hBase
      simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
      subst hStep
      refine ipcInvariantFull_of_objects_eq ?_ hB
      · rfl

/-- `.vspaceUnmap` (dispatch arm): the full stack — page-table erase, local
flush, shootdown round, initiator drain, instruction-cache broadcast —
preserves the whole bundle. -/
theorem vspaceUnmapPageWithShootdownAndIcacheBroadcast_preserves_ipcInvariantFull
    (st st' : SystemState) (ec : CoreId) (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hStep : Architecture.vspaceUnmapPageWithShootdownAndIcacheBroadcast ec asid vaddr st
      = .ok ((), st')) :
    ipcInvariantFull st' := by
  unfold Architecture.vspaceUnmapPageWithShootdownAndIcacheBroadcast at hStep
  cases hK : Architecture.vspaceUnmapPageWithShootdownPerCore ec asid vaddr st with
  | error e =>
      rw [(Architecture.withIcacheBroadcast_error_iff _ _ st e).mpr hK] at hStep
      contradiction
  | ok pair =>
      obtain ⟨u, stB⟩ := pair; cases u
      have hB := vspaceUnmapPageWithShootdownPerCore_preserves_ipcInvariantFull st stB ec
        asid vaddr hObjInv hInv hK
      obtain ⟨hObjs, -, hSched, -⟩ := Architecture.withIcacheBroadcast_frame hK hStep
      exact ipcInvariantFull_of_objects_eq hObjs hB

-- ============================================================================
-- §14  Untyped carve arm (`.untypedRetype`)
-- ============================================================================

/-- The carved object is pristine: every field an `ipcInvariantFull`
conjunct reads is at its inert value.  Every object a carve makes
(`CarveRequest.object`) satisfies this by construction
(`CarveRequest.object_replacementFresh`).

**WS-RR RR8.3**: `queuePPrev` joined the list when `queuePPrevAgreesWithPrev`
became `dualQueueSystemInvariant`'s fourth conjunct, and it is not derivable from
`queuePrev = none` beside it: a replacement carrying `.tcbNext p` with no
`queuePrev` *refutes* the pairing rather than satisfying it vacuously.  It sits
next to `queuePrev` because the two are one back-pointer, which is the whole
lesson of WS-OD OD1.1 and OD3.9 — each found a removal writing one of them
alone.

**WS-ZA ZA4.5**: `runCoreCode = 0` — a fresh thread's run-queue fields name no
core, so storing it keeps every run queue in agreement with the threads' links.

A fresh thread's two space slots hold no capability (`spaceSlotCaps = []`), as a
fresh CNode's slots hold none: the badge clause reads both.

A fresh Reply records no caller and no stasher (`stasherCode = 0`), so a carved
Reply names no thread it was stashed by before.

A fresh thread is bound to no notification and a fresh notification to no thread
(both binding codes `0`), so the replacement names nothing a binding could point
back at, and `notificationBindingReciprocal` reads it as an unbound slot. -/
def retypeReplacementFresh : KernelObject → Prop
  | .tcb t => t.ipcState = .ready ∧ t.pendingMessage = none ∧ t.queueNext = none ∧
      t.queuePrev = none ∧ t.queuePPrev = none ∧
      t.schedContextBinding = .unbound ∧ t.replyObject = none ∧
      t.pendingReceiveReply = none ∧ t.timeoutBudget = none ∧ t.runCoreCode = 0 ∧
      t.spaceSlotCaps = [] ∧ t.boundNotificationCode = 0
  | .endpoint ep => ep.sendQ.head = none ∧ ep.sendQ.tail = none ∧
      ep.receiveQ.head = none ∧ ep.receiveQ.tail = none
  | .notification n => n.state = .idle ∧ n.waitHead = none ∧ n.pendingBadge = none ∧
      n.boundTCBCode = 0
  | .reply r => r.caller = none ∧ r.stasherCode = 0
  | .cnode cn => ∀ slot : SeLe4n.Slot, cn.lookup slot = none
  | .schedContext _ => True
  | .vspaceRoot _ => True
  | .untyped _ => True
  | .frame _ => True
  | .pageTable _ => True

/-- The retype target is detached from every structure the IPC bundle reads:
nothing in the pre-state references `target` — no blocked thread names it as
its endpoint, no queue link, queue boundary, reply link or stash points at it,
it is not a live SchedContext, and if it holds a TCB that thread is fully
dequeued, undonated and unlinked.  These are
pre-state facts (dischargeable before the step), and together they are the
seL4 revoke-and-suspend-before-retype contract this model's cleanup guards
partially enforce at runtime; the payoff composition carries the pack as its
per-arm hypotheses. -/
structure retypeTargetDetached (st : SystemState) (target : SeLe4n.ObjId) : Prop where
  notSc : ∀ sc : SchedContext, st.objects[target]? ≠ some (.schedContext sc)
  notOwner : ∀ t : TCB, st.objects[target]? = some (.tcb t) →
    ∀ ep rt, t.ipcState ≠ .blockedOnReply ep rt
  tcbNoNext : ∀ t : TCB, st.objects[target]? = some (.tcb t) → t.queueNext = none
  tcbNoPrev : ∀ t : TCB, st.objects[target]? = some (.tcb t) → t.queuePrev = none
  tcbSelfId : ∀ t : TCB, st.objects[target]? = some (.tcb t) → t.tid.toObjId = target
  tcbNotDonated : ∀ t : TCB, st.objects[target]? = some (.tcb t) →
    ∀ scId owner, t.schedContextBinding ≠ .donated scId owner
  /-- **`v0.35.164`**: nor `.bound`.  The destroy path's reservation arm
      (`cancelDonationArmOnCore`) unbinds a bound target's context — seL4's
      `unbindFromSc` in `finaliseCap` — writing the SchedContext's `boundThread`,
      the TCB's binding and the home core's replenish queue, so under this pack
      the arm is the identity and the retype write is the pipeline's only object
      write; the runtime arm is what makes a violation safe, exactly as it is for
      `tcbNotDonated`.  Until this version a `.bound` target was admitted and the
      pipeline removed only its `scThreadIndex` entry, which left the
      SchedContext bound to a destroyed thread (`docs/REGISTERED_DEBT.md`, the
      row this version records). -/
  tcbNotBound : ∀ t : TCB, st.objects[target]? = some (.tcb t) →
    ∀ scId, t.schedContextBinding ≠ .bound scId
  tcbNotWaiter : ∀ t : TCB, st.objects[target]? = some (.tcb t) →
    ∀ oid : SeLe4n.ObjId, t.ipcState ≠ .blockedOnNotification oid
  /-- The thread is on no core: out of every core's abstract queue, its own
      run-queue links name no core (WS-ZA ZA4.5: what the destroy sweep reads),
      and no core runs it. -/
  tcbDescheduled : ∀ t : TCB, st.objects[target]? = some (.tcb t) →
    ∀ c : CoreId, (st.scheduler.runQueueOnCore c).contains t.tid = false ∧
      st.queuedOn c t.tid = false ∧ st.scheduler.currentOnCore c ≠ some t.tid
  /-- And the thread is no core's idle thread: an idle thread is the kernel's
      own scheduling reserve and no user capability names one, so this is the
      same caller obligation as the rest of the pack; destroying one would leave
      its core with nothing to run. -/
  tcbNotIdle : ∀ t : TCB, st.objects[target]? = some (.tcb t) →
    SeLe4n.Kernel.isIdleThreadId t.tid = false
  /-- **WS-BP BP7.9**: and no core's registers hold the thread's live FP/SIMD
      values.  The destroy path refuses such a target (`threadHeldOnSomeCore`),
      so under this pack the refusal is not taken — the same shape as
      `tcbDescheduled` beside it, one piece of per-core state further. -/
  tcbFpReleased : ∀ t : TCB, st.objects[target]? = some (.tcb t) →
    ∀ c : CoreId, st.machine.fpOwnerOnCore c ≠ some t.tid
  /-- **PR #904 review (`v0.36.41`)**: and no core's registers hold the thread
      as their resident EL0 context — the residency sibling of
      `tcbFpReleased`, refused by the same guard for the same reason. -/
  tcbResidencyReleased : ∀ t : TCB, st.objects[target]? = some (.tcb t) →
    ∀ c : CoreId, st.machine.residentOnCore c ≠ some t.tid
  /-- **WS-ZA ZA6.6**: and the thread has yielded to no context — its suspend
      cancelled the link (seL4-MCS's `suspend` → `schedContext_cancelYieldTo`),
      so the pre-retype cleanup's own cancel (`cancelYieldTo`) writes nothing. -/
  tcbYieldUnlinked : ∀ t : TCB, st.objects[target]? = some (.tcb t) → t.yieldToCode = 0
  blockedRefsAvoid : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB),
    st.objects[tid.toObjId]? = some (.tcb tcb) →
    tcb.ipcState ≠ .blockedOnSend target ∧ tcb.ipcState ≠ .blockedOnReceive target ∧
    tcb.ipcState ≠ .blockedOnCall target
  notQueueLinked : ∀ (a : SeLe4n.ThreadId) (tcbA : TCB) (b : SeLe4n.ThreadId),
    st.objects[a.toObjId]? = some (.tcb tcbA) → tcbA.queueNext = some b → b.toObjId ≠ target
  notPrevLinked : ∀ (b : SeLe4n.ThreadId) (tcbB : TCB) (a : SeLe4n.ThreadId),
    st.objects[b.toObjId]? = some (.tcb tcbB) → tcbB.queuePrev = some a → a.toObjId ≠ target
  notHead : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint) (hd : SeLe4n.ThreadId),
    st.objects[epId]? = some (.endpoint ep) →
    (ep.sendQ.head = some hd ∨ ep.receiveQ.head = some hd) → hd.toObjId ≠ target
  notTail : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint) (tl : SeLe4n.ThreadId),
    st.objects[epId]? = some (.endpoint ep) →
    (ep.sendQ.tail = some tl ∨ ep.receiveQ.tail = some tl) → tl.toObjId ≠ target
  noSelfLoops : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB),
    st.objects[tid.toObjId]? = some (.tcb tcb) → tcb.queueNext ≠ some tid
  notReplyLinked : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB) (rid : SeLe4n.ReplyId),
    st.objects[tid.toObjId]? = some (.tcb tcb) → tcb.replyObject = some rid →
    rid.toObjId ≠ target
  notStashed : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB) (rid : SeLe4n.ReplyId),
    st.objects[tid.toObjId]? = some (.tcb tcb) → tcb.pendingReceiveReply = some rid →
    rid.toObjId ≠ target
  /-- The object at the target holds no notification binding: a thread bound to
      no notification, a notification bound to no thread.  Under
      `notificationBindingReciprocal` this is also what makes every other slot's
      binding avoid the target, so the write leaves no binding dangling — seL4's
      `unbindNotification` / `unbindMaybeNotification` in `finaliseCap`. -/
  unbound : notificationBindingCodes st.objects[target]? = (0, 0)

/-- **The part of the detachment the bundle's erase-or-replace write reads.**
A replace (the carve) and an erase (the final-delete retire) of the object at
`target` keep `ipcInvariantFull` exactly when nothing the bundle reads names
`target`: no thread blocked on it, no queue link, queue boundary, reply link or
stash pointing at it, no thread's timeout or donation naming it as their
scheduling context, and, when it holds a thread, that thread owns no pending
reply and links to no successor.  The carve's `retypeTargetDetached` gives it
(`retypeTargetDetached.toErased`); the retire builds it from its admission scans
for a passive object, a thread and a scheduling context. -/
structure erasedTargetDetached (st : SystemState) (target : SeLe4n.ObjId) : Prop where
  scNotBudget : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB) (scId : SeLe4n.SchedContextId),
    st.objects[tid.toObjId]? = some (.tcb tcb) → tcb.timeoutBudget = some scId →
    scId.toObjId ≠ target
  scNotDonated : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB) (scId : SeLe4n.SchedContextId)
    (owner : SeLe4n.ThreadId), st.objects[tid.toObjId]? = some (.tcb tcb) →
    tcb.schedContextBinding = .donated scId owner → scId.toObjId ≠ target
  notOwner : ∀ t : TCB, st.objects[target]? = some (.tcb t) →
    ∀ ep rt, t.ipcState ≠ .blockedOnReply ep rt
  tcbNoNext : ∀ t : TCB, st.objects[target]? = some (.tcb t) → t.queueNext = none
  blockedRefsAvoid : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB),
    st.objects[tid.toObjId]? = some (.tcb tcb) →
    tcb.ipcState ≠ .blockedOnSend target ∧ tcb.ipcState ≠ .blockedOnReceive target ∧
    tcb.ipcState ≠ .blockedOnCall target
  notQueueLinked : ∀ (a : SeLe4n.ThreadId) (tcbA : TCB) (b : SeLe4n.ThreadId),
    st.objects[a.toObjId]? = some (.tcb tcbA) → tcbA.queueNext = some b → b.toObjId ≠ target
  notPrevLinked : ∀ (b : SeLe4n.ThreadId) (tcbB : TCB) (a : SeLe4n.ThreadId),
    st.objects[b.toObjId]? = some (.tcb tcbB) → tcbB.queuePrev = some a → a.toObjId ≠ target
  notHead : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint) (hd : SeLe4n.ThreadId),
    st.objects[epId]? = some (.endpoint ep) →
    (ep.sendQ.head = some hd ∨ ep.receiveQ.head = some hd) → hd.toObjId ≠ target
  notTail : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint) (tl : SeLe4n.ThreadId),
    st.objects[epId]? = some (.endpoint ep) →
    (ep.sendQ.tail = some tl ∨ ep.receiveQ.tail = some tl) → tl.toObjId ≠ target
  noSelfLoops : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB),
    st.objects[tid.toObjId]? = some (.tcb tcb) → tcb.queueNext ≠ some tid
  notReplyLinked : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB) (rid : SeLe4n.ReplyId),
    st.objects[tid.toObjId]? = some (.tcb tcb) → tcb.replyObject = some rid →
    rid.toObjId ≠ target
  notStashed : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB) (rid : SeLe4n.ReplyId),
    st.objects[tid.toObjId]? = some (.tcb tcb) → tcb.pendingReceiveReply = some rid →
    rid.toObjId ≠ target
  /-- The object at the target holds no notification binding
      (`retypeTargetDetached.unbound`). -/
  unbound : notificationBindingCodes st.objects[target]? = (0, 0)

/-- The carve's detachment gives the erase-or-replace part: its two
scheduling-context clauses follow from the target holding no scheduling context,
since a thread's timeout and donation name live ones
(`blockedThreadTimeoutConsistent`, `donationOwnerValid`). -/
theorem retypeTargetDetached.toErased {st : SystemState} {target : SeLe4n.ObjId}
    (h : retypeTargetDetached st target) (hInv : ipcInvariantFull st) :
    erasedTargetDetached st target where
  scNotBudget tid tcb scId hT hTB hEq := by
    obtain ⟨⟨sc, hSc⟩, -⟩ := hInv.blockedThreadTimeoutConsistent tid tcb scId hT hTB
    exact h.notSc sc (hEq ▸ hSc)
  scNotDonated tid tcb scId owner hT hB hEq := by
    obtain ⟨⟨sc, hSc, -⟩, -⟩ := hInv.donationOwnerValid tid tcb scId owner hT hB
    exact h.notSc sc (hEq ▸ hSc)
  notOwner := h.notOwner
  tcbNoNext := h.tcbNoNext
  blockedRefsAvoid := h.blockedRefsAvoid
  notQueueLinked := h.notQueueLinked
  notPrevLinked := h.notPrevLinked
  notHead := h.notHead
  notTail := h.notTail
  noSelfLoops := h.noSelfLoops
  notReplyLinked := h.notReplyLinked
  notStashed := h.notStashed
  unbound := h.unbound

/-- At-target lookup of a post-state kind pins the replacement object, or is
absurd where the write erased the target. -/
private theorem retypeWrite_at_target {st' : SystemState} {target : SeLe4n.ObjId}
    {newObj o : KernelObject}
    (hAt : st'.objects[target]? = some newObj ∨ st'.objects[target]? = none)
    (hT : st'.objects[target]? = some o) : newObj = o := by
  rcases hAt with hAt | hAt
  · exact Option.some.inj ((hAt.symm.trans hT))
  · rw [hAt] at hT; cases hT

private theorem retypeWrite_allPendingMessagesBounded
    {st st' : SystemState} {target : SeLe4n.ObjId} {newObj : KernelObject}
    (hAt : st'.objects[target]? = some newObj ∨ st'.objects[target]? = none)
    (hNe : ∀ oid : SeLe4n.ObjId, oid ≠ target → st'.objects[oid]? = st.objects[oid]?)
    (hFresh : retypeReplacementFresh newObj)
    (hInv : allPendingMessagesBounded st) :
    allPendingMessagesBounded st' := by
  intro tid tcb msg hT hPM
  by_cases hK : tid.toObjId = target
  · rw [hK] at hT
    obtain rfl : newObj = .tcb tcb := retypeWrite_at_target hAt hT
    obtain ⟨-, hPMn, -⟩ := hFresh
    rw [hPMn] at hPM
    cases hPM
  · rw [hNe _ hK] at hT
    exact hInv tid tcb msg hT hPM

private theorem retypeWrite_notificationBadgesWellFormed
    {st st' : SystemState} {target : SeLe4n.ObjId} {newObj : KernelObject}
    (hAt : st'.objects[target]? = some newObj ∨ st'.objects[target]? = none)
    (hNe : ∀ oid : SeLe4n.ObjId, oid ≠ target → st'.objects[oid]? = st.objects[oid]?)
    (hFresh : retypeReplacementFresh newObj)
    (hInv : notificationBadgesWellFormed st) :
    notificationBadgesWellFormed st' := by
  intro oid ntfn badge hObj hPB
  by_cases hK : oid = target
  · rw [hK] at hObj
    obtain rfl : newObj = .notification ntfn := retypeWrite_at_target hAt hObj
    obtain ⟨-, -, hPBn, -⟩ := hFresh
    rw [hPBn] at hPB
    cases hPB
  · rw [hNe _ hK] at hObj
    exact hInv oid ntfn badge hObj hPB

private theorem retypeWrite_capabilityBadgesWellFormed
    {st st' : SystemState} {target : SeLe4n.ObjId} {newObj : KernelObject}
    (hAt : st'.objects[target]? = some newObj ∨ st'.objects[target]? = none)
    (hNe : ∀ oid : SeLe4n.ObjId, oid ≠ target → st'.objects[oid]? = st.objects[oid]?)
    (hFresh : retypeReplacementFresh newObj)
    (hInv : capabilityBadgesWellFormed st) :
    capabilityBadgesWellFormed st' := by
  intro oid o slot cap badge hObj hLk hB
  by_cases hK : oid = target
  · rw [hK] at hObj
    obtain rfl : newObj = o := retypeWrite_at_target hAt hObj
    cases newObj with
    | cnode cn =>
      rw [show (KernelObject.cnode cn).slotCap slot = cn.lookup slot from rfl, hFresh slot] at hLk
      cases hLk
    | tcb t =>
      obtain ⟨_, hm⟩ := TCB.mem_spaceSlotCaps hLk
      rw [hFresh.2.2.2.2.2.2.2.2.2.2.1] at hm
      cases hm
    | _ => simp [KernelObject.slotCap] at hLk
  · rw [hNe _ hK] at hObj
    exact hInv oid o slot cap badge hObj hLk hB

private theorem retypeWrite_ipcInvariant
    {st st' : SystemState} {target : SeLe4n.ObjId} {newObj : KernelObject}
    (hAt : st'.objects[target]? = some newObj ∨ st'.objects[target]? = none)
    (hNe : ∀ oid : SeLe4n.ObjId, oid ≠ target → st'.objects[oid]? = st.objects[oid]?)
    (hFresh : retypeReplacementFresh newObj)
    (hInv : ipcInvariant st) :
    ipcInvariant st' := by
  intro oid ntfn hObj
  by_cases hK : oid = target
  · rw [hK] at hObj
    obtain rfl : newObj = .notification ntfn := retypeWrite_at_target hAt hObj
    obtain ⟨hState, hWT, hPB, -⟩ := hFresh
    show notificationQueueWellFormed ntfn
    unfold notificationQueueWellFormed
    rw [hState]
    exact ⟨hWT, hPB⟩
  · rw [hNe _ hK] at hObj
    exact hInv oid ntfn hObj

private theorem retypeWrite_blockedThreadsPendingMessageConsistent
    {st st' : SystemState} {target : SeLe4n.ObjId} {newObj : KernelObject}
    (hAt : st'.objects[target]? = some newObj ∨ st'.objects[target]? = none)
    (hNe : ∀ oid : SeLe4n.ObjId, oid ≠ target → st'.objects[oid]? = st.objects[oid]?)
    (hFresh : retypeReplacementFresh newObj)
    (hInv : blockedThreadsPendingMessageConsistent st) :
    blockedThreadsPendingMessageConsistent st' := by
  intro tid tcb hT
  by_cases hK : tid.toObjId = target
  · rw [hK] at hT
    obtain rfl : newObj = .tcb tcb := retypeWrite_at_target hAt hT
    obtain ⟨hReady, -⟩ := hFresh
    rw [hReady]
    trivial
  · rw [hNe _ hK] at hT
    exact hInv tid tcb hT

private theorem retypeWrite_blockedThreadTimeoutConsistent
    {st st' : SystemState} {target : SeLe4n.ObjId} {newObj : KernelObject}
    (hAt : st'.objects[target]? = some newObj ∨ st'.objects[target]? = none)
    (hNe : ∀ oid : SeLe4n.ObjId, oid ≠ target → st'.objects[oid]? = st.objects[oid]?)
    (hFresh : retypeReplacementFresh newObj)
    (hDet : erasedTargetDetached st target)
    (hInv : blockedThreadTimeoutConsistent st) :
    blockedThreadTimeoutConsistent st' := by
  intro tid tcb scId hT hTB
  by_cases hK : tid.toObjId = target
  · rw [hK] at hT
    obtain rfl : newObj = .tcb tcb := retypeWrite_at_target hAt hT
    obtain ⟨-, -, -, -, -, -, -, -, hTBn, -⟩ := hFresh
    rw [hTBn] at hTB
    cases hTB
  · rw [hNe _ hK] at hT
    obtain ⟨⟨sc, hSc⟩, hBlk⟩ := hInv tid tcb scId hT hTB
    refine ⟨⟨sc, ?_⟩, hBlk⟩
    have hneT : scId.toObjId ≠ target := hDet.scNotBudget tid tcb scId hT hTB
    rw [hNe _ hneT]
    exact hSc

private theorem retypeWrite_donationChainAcyclic
    {st st' : SystemState} {target : SeLe4n.ObjId} {newObj : KernelObject}
    (hAt : st'.objects[target]? = some newObj ∨ st'.objects[target]? = none)
    (hNe : ∀ oid : SeLe4n.ObjId, oid ≠ target → st'.objects[oid]? = st.objects[oid]?)
    (hFresh : retypeReplacementFresh newObj)
    (hInv : donationChainAcyclic st) :
    donationChainAcyclic st' := by
  intro tid1 tid2 tcb1 tcb2 scId1 scId2 h1 h2 hB1 hB2
  by_cases hK1 : tid1.toObjId = target
  · rw [hK1] at h1
    obtain rfl : newObj = .tcb tcb1 := retypeWrite_at_target hAt h1
    obtain ⟨-, -, -, -, -, hSB, -⟩ := hFresh
    rw [hSB] at hB1
    cases hB1
  · by_cases hK2 : tid2.toObjId = target
    · rw [hK2] at h2
      obtain rfl : newObj = .tcb tcb2 := retypeWrite_at_target hAt h2
      obtain ⟨-, -, -, -, -, hSB, -⟩ := hFresh
      rw [hSB] at hB2
      cases hB2
    · rw [hNe _ hK1] at h1
      rw [hNe _ hK2] at h2
      exact hInv tid1 tid2 tcb1 tcb2 scId1 scId2 h1 h2 hB1 hB2

private theorem retypeWrite_donationOwnerUnique
    {st st' : SystemState} {target : SeLe4n.ObjId} {newObj : KernelObject}
    (hAt : st'.objects[target]? = some newObj ∨ st'.objects[target]? = none)
    (hNe : ∀ oid : SeLe4n.ObjId, oid ≠ target → st'.objects[oid]? = st.objects[oid]?)
    (hFresh : retypeReplacementFresh newObj)
    (hInv : donationOwnerUnique st) :
    donationOwnerUnique st' := by
  intro tid1 tid2 tcb1 tcb2 scId1 scId2 owner h1 h2 hB1 hB2
  by_cases hK1 : tid1.toObjId = target
  · rw [hK1] at h1
    obtain rfl : newObj = .tcb tcb1 := retypeWrite_at_target hAt h1
    obtain ⟨-, -, -, -, -, hSB, -⟩ := hFresh
    rw [hSB] at hB1
    cases hB1
  · by_cases hK2 : tid2.toObjId = target
    · rw [hK2] at h2
      obtain rfl : newObj = .tcb tcb2 := retypeWrite_at_target hAt h2
      obtain ⟨-, -, -, -, -, hSB, -⟩ := hFresh
      rw [hSB] at hB2
      cases hB2
    · rw [hNe _ hK1] at h1
      rw [hNe _ hK2] at h2
      exact hInv tid1 tid2 tcb1 tcb2 scId1 scId2 owner h1 h2 hB1 hB2

private theorem retypeWrite_donationBudgetTransfer
    {st st' : SystemState} {target : SeLe4n.ObjId} {newObj : KernelObject}
    (hAt : st'.objects[target]? = some newObj ∨ st'.objects[target]? = none)
    (hNe : ∀ oid : SeLe4n.ObjId, oid ≠ target → st'.objects[oid]? = st.objects[oid]?)
    (hFresh : retypeReplacementFresh newObj)
    (hInv : donationBudgetTransfer st) :
    donationBudgetTransfer st' := by
  intro tid1 tid2 tcb1 tcb2 scId h1 h2 hTNe hS1 hS2
  by_cases hK1 : tid1.toObjId = target
  · rw [hK1] at h1
    obtain rfl : newObj = .tcb tcb1 := retypeWrite_at_target hAt h1
    obtain ⟨-, -, -, -, -, hSB, -⟩ := hFresh
    rw [hSB] at hS1
    simp [SchedContextBinding.scId?] at hS1
  · by_cases hK2 : tid2.toObjId = target
    · rw [hK2] at h2
      obtain rfl : newObj = .tcb tcb2 := retypeWrite_at_target hAt h2
      obtain ⟨-, -, -, -, -, hSB, -⟩ := hFresh
      rw [hSB] at hS2
      simp [SchedContextBinding.scId?] at hS2
    · rw [hNe _ hK1] at h1
      rw [hNe _ hK2] at h2
      exact hInv tid1 tid2 tcb1 tcb2 scId h1 h2 hTNe hS1 hS2

private theorem retypeWrite_blockedOnReplyHasTarget
    {st st' : SystemState} {target : SeLe4n.ObjId} {newObj : KernelObject}
    (hAt : st'.objects[target]? = some newObj ∨ st'.objects[target]? = none)
    (hNe : ∀ oid : SeLe4n.ObjId, oid ≠ target → st'.objects[oid]? = st.objects[oid]?)
    (hFresh : retypeReplacementFresh newObj)
    (hInv : blockedOnReplyHasTarget st) :
    blockedOnReplyHasTarget st' := by
  intro tid tcb epId rt hT hIpc
  by_cases hK : tid.toObjId = target
  · rw [hK] at hT
    obtain rfl : newObj = .tcb tcb := retypeWrite_at_target hAt hT
    obtain ⟨hReady, -⟩ := hFresh
    rw [hReady] at hIpc
    cases hIpc
  · rw [hNe _ hK] at hT
    exact hInv tid tcb epId rt hT hIpc

private theorem retypeWrite_blockedOnReplyHasReplyObject
    {st st' : SystemState} {target : SeLe4n.ObjId} {newObj : KernelObject}
    (hAt : st'.objects[target]? = some newObj ∨ st'.objects[target]? = none)
    (hNe : ∀ oid : SeLe4n.ObjId, oid ≠ target → st'.objects[oid]? = st.objects[oid]?)
    (hFresh : retypeReplacementFresh newObj)
    (hInv : blockedOnReplyHasReplyObject st) :
    blockedOnReplyHasReplyObject st' := by
  intro tid tcb ep rt hT hIpc
  by_cases hK : tid.toObjId = target
  · rw [hK] at hT
    obtain rfl : newObj = .tcb tcb := retypeWrite_at_target hAt hT
    obtain ⟨hReady, -⟩ := hFresh
    rw [hReady] at hIpc
    cases hIpc
  · rw [hNe _ hK] at hT
    exact hInv tid tcb ep rt hT hIpc

private theorem retypeWrite_queueNextBlockingConsistent
    {st st' : SystemState} {target : SeLe4n.ObjId} {newObj : KernelObject}
    (hAt : st'.objects[target]? = some newObj ∨ st'.objects[target]? = none)
    (hNe : ∀ oid : SeLe4n.ObjId, oid ≠ target → st'.objects[oid]? = st.objects[oid]?)
    (hFresh : retypeReplacementFresh newObj)
    (hDet : erasedTargetDetached st target)
    (hInv : queueNextBlockingConsistent st) :
    queueNextBlockingConsistent st' := by
  intro a b tcbA tcbB hA hB hN
  by_cases hKa : a.toObjId = target
  · rw [hKa] at hA
    obtain rfl : newObj = .tcb tcbA := retypeWrite_at_target hAt hA
    obtain ⟨-, -, hQN, -⟩ := hFresh
    rw [hQN] at hN
    cases hN
  · rw [hNe _ hKa] at hA
    by_cases hKb : b.toObjId = target
    · exact absurd hKb (hDet.notQueueLinked a tcbA b hA hN)
    · rw [hNe _ hKb] at hB
      exact hInv a b tcbA tcbB hA hB hN

private theorem retypeWrite_queueNextTargetBlocked
    {st st' : SystemState} {target : SeLe4n.ObjId} {newObj : KernelObject}
    (hAt : st'.objects[target]? = some newObj ∨ st'.objects[target]? = none)
    (hNe : ∀ oid : SeLe4n.ObjId, oid ≠ target → st'.objects[oid]? = st.objects[oid]?)
    (hFresh : retypeReplacementFresh newObj)
    (hDet : erasedTargetDetached st target)
    (hInv : queueNextTargetBlocked st) :
    queueNextTargetBlocked st' := by
  intro a b tcbA tcbB hA hB hN
  by_cases hKa : a.toObjId = target
  · rw [hKa] at hA
    obtain rfl : newObj = .tcb tcbA := retypeWrite_at_target hAt hA
    obtain ⟨-, -, hQN, -⟩ := hFresh
    rw [hQN] at hN
    cases hN
  · rw [hNe _ hKa] at hA
    by_cases hKb : b.toObjId = target
    · exact absurd hKb (hDet.notQueueLinked a tcbA b hA hN)
    · rw [hNe _ hKb] at hB
      exact hInv a b tcbA tcbB hA hB hN

private theorem retypeWrite_endpointQueueLinksOnlyBlocked
    {st st' : SystemState} {target : SeLe4n.ObjId} {newObj : KernelObject}
    (hAt : st'.objects[target]? = some newObj ∨ st'.objects[target]? = none)
    (hNe : ∀ oid : SeLe4n.ObjId, oid ≠ target → st'.objects[oid]? = st.objects[oid]?)
    (hFresh : retypeReplacementFresh newObj)
    (hDet : erasedTargetDetached st target)
    (hInv : endpointQueueLinksOnlyBlocked st) :
    endpointQueueLinksOnlyBlocked st' := by
  intro a tcbA hA hN
  by_cases hKa : a.toObjId = target
  · rw [hKa] at hA
    obtain rfl : newObj = .tcb tcbA := retypeWrite_at_target hAt hA
    obtain ⟨-, -, hQN, -⟩ := hFresh
    exact absurd hQN hN
  · rw [hNe _ hKa] at hA
    exact hInv a tcbA hA hN

private theorem retypeWrite_queueHeadBlockedConsistent
    {st st' : SystemState} {target : SeLe4n.ObjId} {newObj : KernelObject}
    (hAt : st'.objects[target]? = some newObj ∨ st'.objects[target]? = none)
    (hNe : ∀ oid : SeLe4n.ObjId, oid ≠ target → st'.objects[oid]? = st.objects[oid]?)
    (hFresh : retypeReplacementFresh newObj)
    (hDet : erasedTargetDetached st target)
    (hInv : queueHeadBlockedConsistent st) :
    queueHeadBlockedConsistent st' := by
  intro epId ep hd tcb hEp hT
  by_cases hKe : epId = target
  · rw [hKe] at hEp
    obtain rfl : newObj = .endpoint ep := retypeWrite_at_target hAt hEp
    obtain ⟨hSH, -, hRH, -⟩ := hFresh
    constructor
    · intro h; rw [hRH] at h; cases h
    · intro h; rw [hSH] at h; cases h
  · rw [hNe _ hKe] at hEp
    by_cases hKh : hd.toObjId = target
    · constructor
      · intro h
        exact absurd hKh (hDet.notHead epId ep hd hEp (Or.inr h))
      · intro h
        exact absurd hKh (hDet.notHead epId ep hd hEp (Or.inl h))
    · rw [hNe _ hKh] at hT
      exact hInv epId ep hd tcb hEp hT

private theorem retypeWrite_endpointQueueTailBlockedConsistent
    {st st' : SystemState} {target : SeLe4n.ObjId} {newObj : KernelObject}
    (hAt : st'.objects[target]? = some newObj ∨ st'.objects[target]? = none)
    (hNe : ∀ oid : SeLe4n.ObjId, oid ≠ target → st'.objects[oid]? = st.objects[oid]?)
    (hFresh : retypeReplacementFresh newObj)
    (hDet : erasedTargetDetached st target)
    (hInv : endpointQueueTailBlockedConsistent st) :
    endpointQueueTailBlockedConsistent st' := by
  intro epId ep tl tcb hEp hT
  by_cases hKe : epId = target
  · rw [hKe] at hEp
    obtain rfl : newObj = .endpoint ep := retypeWrite_at_target hAt hEp
    obtain ⟨-, hST, -, hRT⟩ := hFresh
    constructor
    · intro h; rw [hRT] at h; cases h
    · intro h; rw [hST] at h; cases h
  · rw [hNe _ hKe] at hEp
    by_cases hKt : tl.toObjId = target
    · constructor
      · intro h
        exact absurd hKt (hDet.notTail epId ep tl hEp (Or.inr h))
      · intro h
        exact absurd hKt (hDet.notTail epId ep tl hEp (Or.inl h))
    · rw [hNe _ hKt] at hT
      exact hInv epId ep tl tcb hEp hT

private theorem retypeWrite_endpointQueueNoDup
    {st st' : SystemState} {target : SeLe4n.ObjId} {newObj : KernelObject}
    (hAt : st'.objects[target]? = some newObj ∨ st'.objects[target]? = none)
    (hNe : ∀ oid : SeLe4n.ObjId, oid ≠ target → st'.objects[oid]? = st.objects[oid]?)
    (hFresh : retypeReplacementFresh newObj)
    (hDet : erasedTargetDetached st target)
    (hInv : endpointQueueNoDup st) :
    endpointQueueNoDup st' := by
  have hSelf : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB),
      st'.objects[tid.toObjId]? = some (.tcb tcb) → TCB.queueNext tcb ≠ some tid := by
    intro tid tcb hT
    by_cases hK : tid.toObjId = target
    · rw [hK] at hT
      obtain rfl : newObj = .tcb tcb := retypeWrite_at_target hAt hT
      obtain ⟨-, -, hQN, -⟩ := hFresh
      show tcb.queueNext ≠ some tid
      rw [hQN]
      intro h
      cases h
    · rw [hNe _ hK] at hT
      exact hDet.noSelfLoops tid tcb hT
  intro oid ep hEp
  refine ⟨hSelf, ?_⟩
  by_cases hKe : oid = target
  · rw [hKe] at hEp
    obtain rfl : newObj = .endpoint ep := retypeWrite_at_target hAt hEp
    obtain ⟨hSH, -⟩ := hFresh
    exact Or.inl hSH
  · rw [hNe _ hKe] at hEp
    exact (hInv oid ep hEp).2

private theorem retypeWrite_donationOwnerValid
    {st st' : SystemState} {target : SeLe4n.ObjId} {newObj : KernelObject}
    (hAt : st'.objects[target]? = some newObj ∨ st'.objects[target]? = none)
    (hNe : ∀ oid : SeLe4n.ObjId, oid ≠ target → st'.objects[oid]? = st.objects[oid]?)
    (hFresh : retypeReplacementFresh newObj)
    (hDet : erasedTargetDetached st target)
    (hInv : donationOwnerValid st) :
    donationOwnerValid st' := by
  intro tid tcb scId owner hT hB
  by_cases hK : tid.toObjId = target
  · rw [hK] at hT
    obtain rfl : newObj = .tcb tcb := retypeWrite_at_target hAt hT
    obtain ⟨-, -, -, -, -, hSB, -⟩ := hFresh
    rw [hSB] at hB
    cases hB
  · rw [hNe _ hK] at hT
    obtain ⟨⟨sc, hSc, hBound⟩, ⟨ownerTcb, hOT, hOUnbound, hOBlocked⟩⟩ :=
      hInv tid tcb scId owner hT hB
    have hneSc : scId.toObjId ≠ target := hDet.scNotDonated tid tcb scId owner hT hB
    have hneOwner : owner.toObjId ≠ target := by
      intro hEq
      obtain ⟨epId, rt, hIpc⟩ := hOBlocked
      exact hDet.notOwner ownerTcb (hEq ▸ hOT) epId rt hIpc
    refine ⟨⟨sc, ?_, hBound⟩, ⟨ownerTcb, ?_, hOUnbound, hOBlocked⟩⟩
    · rw [hNe _ hneSc]; exact hSc
    · rw [hNe _ hneOwner]; exact hOT

private theorem retypeWrite_ipcStateQueueMembershipConsistent
    {st st' : SystemState} {target : SeLe4n.ObjId} {newObj : KernelObject}
    (hAt : st'.objects[target]? = some newObj ∨ st'.objects[target]? = none)
    (hNe : ∀ oid : SeLe4n.ObjId, oid ≠ target → st'.objects[oid]? = st.objects[oid]?)
    (hFresh : retypeReplacementFresh newObj)
    (hDet : erasedTargetDetached st target)
    (hInv : ipcStateQueueMembershipConsistent st) :
    ipcStateQueueMembershipConsistent st' := by
  have hWitness : ∀ (epId : SeLe4n.ObjId) (tid : SeLe4n.ThreadId) (ep : Endpoint),
      epId ≠ target →
      st.objects[epId]? = some (.endpoint ep) →
      (ep.sendQ.head = some tid ∨
        ∃ (prev : SeLe4n.ThreadId) (prevTcb : TCB),
          st.objects[prev.toObjId]? = some (.tcb prevTcb) ∧
          TCB.queueNext prevTcb = some tid) →
      ∃ ep', st'.objects[epId]? = some (.endpoint ep') ∧
        (ep'.sendQ.head = some tid ∨
          ∃ (prev : SeLe4n.ThreadId) (prevTcb : TCB),
            st'.objects[prev.toObjId]? = some (.tcb prevTcb) ∧
            TCB.queueNext prevTcb = some tid) := by
    intro epId tid ep hneEp hEp hWit
    refine ⟨ep, by rw [hNe _ hneEp]; exact hEp, ?_⟩
    cases hWit with
    | inl hHead => exact Or.inl hHead
    | inr hPrev =>
        obtain ⟨prev, prevTcb, hPrevT, hPrevN⟩ := hPrev
        have hnePrev : prev.toObjId ≠ target := by
          intro hEq
          have hNone := hDet.tcbNoNext prevTcb (hEq ▸ hPrevT)
          rw [show TCB.queueNext prevTcb = prevTcb.queueNext from rfl, hNone] at hPrevN
          cases hPrevN
        exact Or.inr ⟨prev, prevTcb, by rw [hNe _ hnePrev]; exact hPrevT, hPrevN⟩
  have hWitnessR : ∀ (epId : SeLe4n.ObjId) (tid : SeLe4n.ThreadId) (ep : Endpoint),
      epId ≠ target →
      st.objects[epId]? = some (.endpoint ep) →
      (ep.receiveQ.head = some tid ∨
        ∃ (prev : SeLe4n.ThreadId) (prevTcb : TCB),
          st.objects[prev.toObjId]? = some (.tcb prevTcb) ∧
          TCB.queueNext prevTcb = some tid) →
      ∃ ep', st'.objects[epId]? = some (.endpoint ep') ∧
        (ep'.receiveQ.head = some tid ∨
          ∃ (prev : SeLe4n.ThreadId) (prevTcb : TCB),
            st'.objects[prev.toObjId]? = some (.tcb prevTcb) ∧
            TCB.queueNext prevTcb = some tid) := by
    intro epId tid ep hneEp hEp hWit
    refine ⟨ep, by rw [hNe _ hneEp]; exact hEp, ?_⟩
    cases hWit with
    | inl hHead => exact Or.inl hHead
    | inr hPrev =>
        obtain ⟨prev, prevTcb, hPrevT, hPrevN⟩ := hPrev
        have hnePrev : prev.toObjId ≠ target := by
          intro hEq
          have hNone := hDet.tcbNoNext prevTcb (hEq ▸ hPrevT)
          rw [show TCB.queueNext prevTcb = prevTcb.queueNext from rfl, hNone] at hPrevN
          cases hPrevN
        exact Or.inr ⟨prev, prevTcb, by rw [hNe _ hnePrev]; exact hPrevT, hPrevN⟩
  intro tid tcb hT
  by_cases hK : tid.toObjId = target
  · rw [hK] at hT
    obtain rfl : newObj = .tcb tcb := retypeWrite_at_target hAt hT
    obtain ⟨hReady, -⟩ := hFresh
    rw [hReady]
    trivial
  · rw [hNe _ hK] at hT
    have hPre := hInv tid tcb hT
    cases hIpc : tcb.ipcState with
    | blockedOnSend epId =>
        simp only [hIpc] at hPre
        obtain ⟨ep, hEp, hWit⟩ := hPre
        have hneEp : epId ≠ target := by
          intro hEq
          exact (hDet.blockedRefsAvoid tid tcb hT).1 (hEq ▸ hIpc)
        exact hWitness epId tid ep hneEp hEp hWit
    | blockedOnReceive epId =>
        simp only [hIpc] at hPre
        obtain ⟨ep, hEp, hWit⟩ := hPre
        have hneEp : epId ≠ target := by
          intro hEq
          exact (hDet.blockedRefsAvoid tid tcb hT).2.1 (hEq ▸ hIpc)
        exact hWitnessR epId tid ep hneEp hEp hWit
    | blockedOnCall epId =>
        simp only [hIpc] at hPre
        obtain ⟨ep, hEp, hWit⟩ := hPre
        have hneEp : epId ≠ target := by
          intro hEq
          exact (hDet.blockedRefsAvoid tid tcb hT).2.2 (hEq ▸ hIpc)
        exact hWitness epId tid ep hneEp hEp hWit
    | ready => trivial
    | blockedOnReply ep rt => trivial
    | blockedOnNotification n => trivial

private theorem retypeWrite_replyCallerLinkageReciprocal
    {st st' : SystemState} {target : SeLe4n.ObjId} {newObj : KernelObject}
    (hAt : st'.objects[target]? = some newObj ∨ st'.objects[target]? = none)
    (hNe : ∀ oid : SeLe4n.ObjId, oid ≠ target → st'.objects[oid]? = st.objects[oid]?)
    (hFresh : retypeReplacementFresh newObj)
    (hDet : erasedTargetDetached st target)
    (hInv : replyCallerLinkageReciprocal st) :
    replyCallerLinkageReciprocal st' := by
  constructor
  · intro tid tcb rid hT hRO
    by_cases hK : tid.toObjId = target
    · rw [hK] at hT
      obtain rfl : newObj = .tcb tcb := retypeWrite_at_target hAt hT
      obtain ⟨-, -, -, -, -, -, hRO0, -⟩ := hFresh
      rw [hRO0] at hRO
      cases hRO
    · rw [hNe _ hK] at hT
      obtain ⟨r, hR, hCaller⟩ := hInv.1 tid tcb rid hT hRO
      have hneR : rid.toObjId ≠ target := hDet.notReplyLinked tid tcb rid hT hRO
      exact ⟨r, by rw [hNe _ hneR]; exact hR, hCaller⟩
  · intro rid r tid hR hCaller
    by_cases hK : rid.toObjId = target
    · rw [hK] at hR
      obtain rfl : newObj = .reply r := retypeWrite_at_target hAt hR
      rw [hFresh.1] at hCaller
      cases hCaller
    · rw [hNe _ hK] at hR
      obtain ⟨tcb, hT, hRO, hBlocked⟩ := hInv.2 rid r tid hR hCaller
      have hneT : tid.toObjId ≠ target := by
        intro hEq
        obtain ⟨ep, rt, hIpc⟩ := hBlocked
        exact hDet.notOwner tcb (hEq ▸ hT) ep rt hIpc
      exact ⟨tcb, by rw [hNe _ hneT]; exact hT, hRO, hBlocked⟩

private theorem retypeWrite_pendingReceiveReplyWellFormed
    {st st' : SystemState} {target : SeLe4n.ObjId} {newObj : KernelObject}
    (hAt : st'.objects[target]? = some newObj ∨ st'.objects[target]? = none)
    (hNe : ∀ oid : SeLe4n.ObjId, oid ≠ target → st'.objects[oid]? = st.objects[oid]?)
    (hFresh : retypeReplacementFresh newObj)
    (hDet : erasedTargetDetached st target)
    (hInv : pendingReceiveReplyWellFormed st) :
    pendingReceiveReplyWellFormed st' := by
  refine ⟨?_, ?_, ?_⟩
  · intro tid tcb rid hT hPRR
    have hTobj := (SystemState.getTcb?_eq_some_iff st' tid tcb).mp hT
    by_cases hK : tid.toObjId = target
    · rw [hK] at hTobj
      obtain rfl : newObj = .tcb tcb := retypeWrite_at_target hAt hTobj
      obtain ⟨-, -, -, -, -, -, -, hPRR0, -⟩ := hFresh
      rw [hPRR0] at hPRR
      cases hPRR
    · rw [hNe _ hK] at hTobj
      have hTpre := (SystemState.getTcb?_eq_some_iff st tid tcb).mpr hTobj
      obtain ⟨hBlk, r, hR, hCnone⟩ := hInv.1 tid tcb rid hTpre hPRR
      have hRobj := (SystemState.getReply?_eq_some_iff st rid r).mp hR
      have hneR : rid.toObjId ≠ target := hDet.notStashed tid tcb rid hTobj hPRR
      refine ⟨hBlk, r, ?_, hCnone⟩
      exact (SystemState.getReply?_eq_some_iff st' rid r).mpr
        (by rw [hNe _ hneR]; exact hRobj)
  · intro tid1 tid2 tcb1 tcb2 rid hT1 hT2 hP1 hP2
    have hT1obj := (SystemState.getTcb?_eq_some_iff st' tid1 tcb1).mp hT1
    have hT2obj := (SystemState.getTcb?_eq_some_iff st' tid2 tcb2).mp hT2
    by_cases hK1 : tid1.toObjId = target
    · rw [hK1] at hT1obj
      obtain rfl : newObj = .tcb tcb1 := retypeWrite_at_target hAt hT1obj
      obtain ⟨-, -, -, -, -, -, -, hPRR0, -⟩ := hFresh
      rw [hPRR0] at hP1
      cases hP1
    · by_cases hK2 : tid2.toObjId = target
      · rw [hK2] at hT2obj
        obtain rfl : newObj = .tcb tcb2 := retypeWrite_at_target hAt hT2obj
        obtain ⟨-, -, -, -, -, -, -, hPRR0, -⟩ := hFresh
        rw [hPRR0] at hP2
        cases hP2
      · rw [hNe _ hK1] at hT1obj
        rw [hNe _ hK2] at hT2obj
        exact hInv.2.1 tid1 tid2 tcb1 tcb2 rid
          ((SystemState.getTcb?_eq_some_iff st tid1 tcb1).mpr hT1obj)
          ((SystemState.getTcb?_eq_some_iff st tid2 tcb2).mpr hT2obj) hP1 hP2
  · -- A carved TCB stashes nothing; a Reply standing elsewhere is untouched,
    -- and the stashed Reply is never the erased target.
    intro tid tcb rid hT hPRR
    have hTobj := (SystemState.getTcb?_eq_some_iff st' tid tcb).mp hT
    by_cases hK : tid.toObjId = target
    · rw [hK] at hTobj
      obtain rfl : newObj = .tcb tcb := retypeWrite_at_target hAt hTobj
      obtain ⟨-, -, -, -, -, -, -, hPRR0, -⟩ := hFresh
      rw [hPRR0] at hPRR
      cases hPRR
    · rw [hNe _ hK] at hTobj
      have hTpre := (SystemState.getTcb?_eq_some_iff st tid tcb).mpr hTobj
      obtain ⟨r, hR, hS⟩ := hInv.2.2 tid tcb rid hTpre hPRR
      have hRobj := (SystemState.getReply?_eq_some_iff st rid r).mp hR
      have hneR : rid.toObjId ≠ target := hDet.notStashed tid tcb rid hTobj hPRR
      exact ⟨r, (SystemState.getReply?_eq_some_iff st' rid r).mpr
        (by rw [hNe _ hneR]; exact hRobj), hS⟩

private theorem retypeWrite_dualQueueSystemInvariant
    {st st' : SystemState} {target : SeLe4n.ObjId} {newObj : KernelObject}
    (hAt : st'.objects[target]? = some newObj ∨ st'.objects[target]? = none)
    (hNe : ∀ oid : SeLe4n.ObjId, oid ≠ target → st'.objects[oid]? = st.objects[oid]?)
    (hFresh : retypeReplacementFresh newObj)
    (hDet : erasedTargetDetached st target)
    (hInv : dualQueueSystemInvariant st) :
    dualQueueSystemInvariant st' := by
  obtain ⟨hEpWF, ⟨hFwd, hRev⟩, hAcyclic, hPPair, hHD⟩ := hInv
  have hIQtrans : ∀ (q : IntrusiveQueue),
      intrusiveQueueWellFormed q st →
      (∀ hd, q.head = some hd → hd.toObjId ≠ target) →
      (∀ tl, q.tail = some tl → tl.toObjId ≠ target) →
      intrusiveQueueWellFormed q st' := by
    intro q ⟨hP1, hP2, hP3⟩ hHd hTl
    refine ⟨hP1, ?_, ?_⟩
    · intro hd hH
      obtain ⟨tcbH, hTH, hPnone, hPPHead⟩ := hP2 hd hH
      exact ⟨tcbH, by rw [hNe _ (hHd hd hH)]; exact hTH, hPnone, hPPHead⟩
    · intro tl hT
      obtain ⟨tcbT, hTT, hNnone⟩ := hP3 tl hT
      exact ⟨tcbT, by rw [hNe _ (hTl tl hT)]; exact hTT, hNnone⟩
  refine ⟨?_, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · -- per-endpoint dual-queue well-formedness
    intro epId ep hEp
    unfold dualQueueEndpointWellFormed
    rw [hEp]
    by_cases hKe : epId = target
    · rw [hKe] at hEp
      obtain rfl : newObj = .endpoint ep := retypeWrite_at_target hAt hEp
      obtain ⟨hSH, hST, hRH, hRT⟩ := hFresh
      have hFreshIQ : ∀ (q : IntrusiveQueue), q.head = none → q.tail = none →
          intrusiveQueueWellFormed q st' := by
        intro q hH hT
        refine ⟨by rw [hH, hT], ?_, ?_⟩
        · intro hd h; rw [hH] at h; cases h
        · intro tl h; rw [hT] at h; cases h
      exact ⟨hFreshIQ ep.sendQ hSH hST, hFreshIQ ep.receiveQ hRH hRT⟩
    · rw [hNe _ hKe] at hEp
      have hPre := hEpWF epId ep hEp
      unfold dualQueueEndpointWellFormed at hPre
      rw [hEp] at hPre
      exact ⟨hIQtrans ep.sendQ hPre.1
          (fun hd h => hDet.notHead epId ep hd hEp (Or.inl h))
          (fun tl h => hDet.notTail epId ep tl hEp (Or.inl h)),
        hIQtrans ep.receiveQ hPre.2
          (fun hd h => hDet.notHead epId ep hd hEp (Or.inr h))
          (fun tl h => hDet.notTail epId ep tl hEp (Or.inr h))⟩
  · -- forward link integrity
    intro a tcbA hA b hN
    by_cases hKa : a.toObjId = target
    · rw [hKa] at hA
      obtain rfl : newObj = .tcb tcbA := retypeWrite_at_target hAt hA
      obtain ⟨-, -, hQN, -⟩ := hFresh
      rw [hQN] at hN
      cases hN
    · rw [hNe _ hKa] at hA
      obtain ⟨tcbB, hB, hBP⟩ := hFwd a tcbA hA b hN
      have hneB : b.toObjId ≠ target := hDet.notQueueLinked a tcbA b hA hN
      exact ⟨tcbB, by rw [hNe _ hneB]; exact hB, hBP⟩
  · -- reverse link integrity
    intro b tcbB hB a hP
    by_cases hKb : b.toObjId = target
    · rw [hKb] at hB
      obtain rfl : newObj = .tcb tcbB := retypeWrite_at_target hAt hB
      obtain ⟨-, -, -, hQP, -⟩ := hFresh
      rw [hQP] at hP
      cases hP
    · rw [hNe _ hKb] at hB
      obtain ⟨tcbA, hA, hAN⟩ := hRev b tcbB hB a hP
      have hneA : a.toObjId ≠ target := hDet.notPrevLinked b tcbB a hB hP
      exact ⟨tcbA, by rw [hNe _ hneA]; exact hA, hAN⟩
  · -- chain acyclicity
    have hPath : ∀ x y, QueueNextPath st' x y → QueueNextPath st x y := by
      intro x y h
      induction h with
      | single a b tcb hObj hNext =>
          by_cases hKa : a.toObjId = target
          · rw [hKa] at hObj
            obtain rfl : newObj = .tcb tcb := retypeWrite_at_target hAt hObj
            obtain ⟨-, -, hQN, -⟩ := hFresh
            rw [show TCB.queueNext tcb = tcb.queueNext from rfl, hQN] at hNext
            cases hNext
          · rw [hNe _ hKa] at hObj
            exact .single a b tcb hObj hNext
      | cons a mid c tcb hObj hNext _ ih =>
          by_cases hKa : a.toObjId = target
          · rw [hKa] at hObj
            obtain rfl : newObj = .tcb tcb := retypeWrite_at_target hAt hObj
            obtain ⟨-, -, hQN, -⟩ := hFresh
            rw [show TCB.queueNext tcb = tcb.queueNext from rfl, hQN] at hNext
            cases hNext
          · rw [hNe _ hKa] at hObj
            exact .cons a mid c tcb hObj hNext ih
    intro tid hPathTid
    exact hAcyclic tid (hPath _ _ hPathTid)
  · -- WS-RR RR8.3: the `queuePPrev`/`queuePrev` pairing.  The replacement is
    -- pristine (`queuePPrev = none`, which constrains nothing) and every other
    -- key reads the pre-state.
    intro tid tcb hTcb
    by_cases hKt : tid.toObjId = target
    · rw [hKt] at hTcb
      obtain rfl : newObj = .tcb tcb := retypeWrite_at_target hAt hTcb
      -- `v0.35.99`: the pristine replacement is fresh in BOTH back-pointers,
      -- which `retypeReplacementFresh` has always required — the destructuring
      -- simply dropped the `queuePrev` component while the arm was vacuous.
      obtain ⟨-, -, -, hQPrev, hQPP, -⟩ := hFresh
      exact TCB.queuePPrevAgreesWithPrev_of_pprev_none hQPP hQPrev
    · rw [hNe _ hKt] at hTcb
      exact hPPair tid tcb hTcb
  · -- **PR #897 review**: the fifth conjunct.  The pristine replacement's queues
    -- are empty, so it contributes no head at all; every other key reads the
    -- pre-state, where head-disjointness already holds.
    refine endpointQueueHeadDisjoint_of_freshHeads
      (freshAt := fun _ _ _ => False) (fun _ _ _ h => h.elim)
      (fun _ _ _ _ _ h _ => h.elim) (fun k e r hd hEk hHk => ?_) hHD
    by_cases hKe : k = target
    · rw [hKe] at hEk
      obtain rfl : newObj = .endpoint e := retypeWrite_at_target hAt hEk
      obtain ⟨hSH, hST, hRH, hRT⟩ := hFresh
      cases r with
      | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at hHk
          rw [hSH] at hHk; cases hHk
      | true =>
          simp only [↓reduceIte] at hHk
          rw [hRH] at hHk; cases hHk
    · exact Or.inl ⟨e, by rw [← hNe _ hKe]; exact hEk, hHk⟩

/-- The replacement holds no binding codes, and the erased slot holds none. -/
private theorem retypeWrite_codes_at_target
    {st' : SystemState} {target : SeLe4n.ObjId} {newObj : KernelObject}
    (hAt : st'.objects[target]? = some newObj ∨ st'.objects[target]? = none)
    (hFresh : retypeReplacementFresh newObj) :
    notificationBindingCodes st'.objects[target]? = (0, 0) := by
  rcases hAt with hAt | hAt
  · rw [hAt]
    cases newObj with
    | tcb t => simp [notificationBindingCodes, KernelObject.bindingCodes, hFresh.2.2.2.2.2.2.2.2.2.2.2]
    | notification n => simp [notificationBindingCodes, KernelObject.bindingCodes, hFresh.2.2.2]
    | _ => rfl
  · rw [hAt]; rfl

/-- **The write keeps the binding reciprocity**: the target's slot holds no code
before (`erasedTargetDetached.unbound`) or after (`retypeReplacementFresh`), so no
other slot's code names it — reciprocity would have it name that slot back — and
every other slot reads the pre-state. -/
private theorem retypeWrite_notificationBindingReciprocal
    {st st' : SystemState} {target : SeLe4n.ObjId} {newObj : KernelObject}
    (hAt : st'.objects[target]? = some newObj ∨ st'.objects[target]? = none)
    (hNe : ∀ oid : SeLe4n.ObjId, oid ≠ target → st'.objects[oid]? = st.objects[oid]?)
    (hFresh : retypeReplacementFresh newObj)
    (hDet : erasedTargetDetached st target)
    (hInv : notificationBindingReciprocal st) :
    notificationBindingReciprocal st' := by
  have hPost := retypeWrite_codes_at_target hAt hFresh
  refine .of_boundCodes_agree hInv (fun k hk => ?_) (fun k hk => ?_)
  · by_cases hK : k = target
    · subst hK; exact absurd hPost hk
    · rw [hNe _ hK]
  · by_cases hK : k = target
    · subst hK; exact absurd hDet.unbound hk
    · rw [hNe _ hK]

/-- **A write that replaces the target by a pristine object or erases it**
preserves the bundle: every at-target clause reads the replacement or is
vacuous, and every other key reads the pre-state, where the detached target is
named by nothing the bundle reads. -/
private theorem retypeOrEraseWrite_preserves_ipcInvariantFull
    {st st' : SystemState} {target : SeLe4n.ObjId} {newObj : KernelObject}
    (hAt : st'.objects[target]? = some newObj ∨ st'.objects[target]? = none)
    (hNe : ∀ oid : SeLe4n.ObjId, oid ≠ target → st'.objects[oid]? = st.objects[oid]?)
    (hFresh : retypeReplacementFresh newObj)
    (hDet : erasedTargetDetached st target)
    (hInv : ipcInvariantFull st) :
    ipcInvariantFull st' :=
  ⟨retypeWrite_ipcInvariant hAt hNe hFresh hInv.ipcInvariant,
   retypeWrite_dualQueueSystemInvariant hAt hNe hFresh hDet hInv.dualQueueSystemInvariant,
   retypeWrite_allPendingMessagesBounded hAt hNe hFresh hInv.allPendingMessagesBounded,
   ⟨retypeWrite_notificationBadgesWellFormed hAt hNe hFresh hInv.badgeWellFormed.1,
    retypeWrite_capabilityBadgesWellFormed hAt hNe hFresh hInv.badgeWellFormed.2⟩,
   retypeWrite_blockedThreadsPendingMessageConsistent hAt hNe hFresh
     hInv.blockedThreadsPendingMessageConsistent,
   retypeWrite_endpointQueueNoDup hAt hNe hFresh hDet hInv.endpointQueueNoDup,
   retypeWrite_ipcStateQueueMembershipConsistent hAt hNe hFresh hDet
     hInv.ipcStateQueueMembershipConsistent,
   retypeWrite_queueNextBlockingConsistent hAt hNe hFresh hDet
     hInv.queueNextBlockingConsistent,
   retypeWrite_queueHeadBlockedConsistent hAt hNe hFresh hDet
     hInv.queueHeadBlockedConsistent,
   retypeWrite_blockedThreadTimeoutConsistent hAt hNe hFresh hDet
     hInv.blockedThreadTimeoutConsistent,
   retypeWrite_donationChainAcyclic hAt hNe hFresh hInv.donationChainAcyclic,
   retypeWrite_donationOwnerValid hAt hNe hFresh hDet hInv.donationOwnerValid,
   retypeWrite_donationBudgetTransfer hAt hNe hFresh hInv.donationBudgetTransfer,
   retypeWrite_blockedOnReplyHasTarget hAt hNe hFresh hInv.blockedOnReplyHasTarget,
   ⟨retypeWrite_replyCallerLinkageReciprocal hAt hNe hFresh hDet hInv.replyCallerLinkage.1,
    retypeWrite_blockedOnReplyHasReplyObject hAt hNe hFresh hInv.replyCallerLinkage.2⟩,
   retypeWrite_pendingReceiveReplyWellFormed hAt hNe hFresh hDet
     hInv.pendingReceiveReplyWellFormed,
   retypeWrite_donationOwnerUnique hAt hNe hFresh hInv.donationOwnerUnique,
   retypeWrite_endpointQueueTailBlockedConsistent hAt hNe hFresh hDet
     hInv.endpointQueueTailBlockedConsistent,
   retypeWrite_queueNextTargetBlocked hAt hNe hFresh hDet hInv.queueNextTargetBlocked,
   retypeWrite_notificationBindingReciprocal hAt hNe hFresh hDet
     hInv.notificationBindingReciprocal,
   retypeWrite_endpointQueueLinksOnlyBlocked hAt hNe hFresh hDet
     hInv.endpointQueueLinksOnlyBlocked⟩

/-- The retype write — one arbitrary-kind object replaced by a pristine one at
a fully detached slot — preserves the whole `ipcInvariantFull` bundle.  This is
the storeObject-shape core the carve's payoff composes
(`retypeFromUntyped_carve_preserves_ipcInvariantFull`). -/
theorem retypeWrite_preserves_ipcInvariantFull
    {st st' : SystemState} {target : SeLe4n.ObjId} {newObj : KernelObject}
    (hAt : st'.objects[target]? = some newObj)
    (hNe : ∀ oid : SeLe4n.ObjId, oid ≠ target → st'.objects[oid]? = st.objects[oid]?)
    (hFresh : retypeReplacementFresh newObj)
    (hDet : retypeTargetDetached st target)
    (hInv : ipcInvariantFull st) :
    ipcInvariantFull st' :=
  retypeOrEraseWrite_preserves_ipcInvariantFull (.inl hAt) hNe hFresh (hDet.toErased hInv) hInv

/-- **WS-ZA ZA5.4 part 14: a key that holds no object is detached from
everything the bundle reads.**  Every reference the bundle constrains names a
live object — a blocked thread its endpoint (`ipcStateQueueMembershipConsistent`),
a queue link and a queue boundary their threads (`tcbQueueLinkIntegrity`,
`intrusiveQueueWellFormed`), a reply link and a stash their replies
(`replyCallerLinkageReciprocal`, `pendingReceiveReplyWellFormed`) — so none names
an empty key, and the pack's clauses about the object at the key are vacuous.
This is what lets a carve store a fresh object of any kind at its child id. -/
theorem retypeTargetDetached_of_absent {st : SystemState} {target : SeLe4n.ObjId}
    (hAbs : st.objects[target]? = none) (hInv : ipcInvariantFull st) :
    retypeTargetDetached st target := by
  have hNo : ∀ o : KernelObject, st.objects[target]? ≠ some o := fun o h => by
    rw [hAbs] at h; cases h
  have hNe : ∀ (oid : SeLe4n.ObjId) (o : KernelObject), st.objects[oid]? = some o →
      oid ≠ target := fun oid o h hEq => hNo o (hEq ▸ h)
  refine ⟨fun sc => hNo _, fun t h => absurd h (hNo _), fun t h => absurd h (hNo _),
    fun t h => absurd h (hNo _), fun t h => absurd h (hNo _), fun t h => absurd h (hNo _),
    fun t h => absurd h (hNo _), fun t h => absurd h (hNo _), fun t h => absurd h (hNo _),
    fun t h => absurd h (hNo _),
    fun t h => absurd h (hNo _), fun t h => absurd h (hNo _), fun t h => absurd h (hNo _),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [hAbs]; rfl⟩
  · intro tid tcb hT
    have hM := hInv.ipcStateQueueMembershipConsistent tid tcb hT
    refine ⟨fun hS => ?_, fun hR => ?_, fun hC => ?_⟩
    · rw [hS] at hM; obtain ⟨ep, hEp, -⟩ := hM; exact hNo _ hEp
    · rw [hR] at hM; obtain ⟨ep, hEp, -⟩ := hM; exact hNo _ hEp
    · rw [hC] at hM; obtain ⟨ep, hEp, -⟩ := hM; exact hNo _ hEp
  · intro a tcbA b hA hN
    obtain ⟨tcbB, hB, -⟩ := hInv.dualQueueSystemInvariant.linkIntegrity.1 a tcbA hA b hN
    exact hNe _ _ hB
  · intro b tcbB a hB hP
    obtain ⟨tcbA, hA, -⟩ := hInv.dualQueueSystemInvariant.linkIntegrity.2 b tcbB hB a hP
    exact hNe _ _ hA
  · intro epId ep hd hEp hH
    have hW := hInv.dualQueueSystemInvariant.endpointsWellFormed epId ep hEp
    unfold dualQueueEndpointWellFormed at hW
    rw [hEp] at hW
    rcases hH with hH | hH
    · obtain ⟨tcb, hT, -⟩ := hW.1.2.1 hd hH; exact hNe _ _ hT
    · obtain ⟨tcb, hT, -⟩ := hW.2.2.1 hd hH; exact hNe _ _ hT
  · intro epId ep tl hEp hTl
    have hW := hInv.dualQueueSystemInvariant.endpointsWellFormed epId ep hEp
    unfold dualQueueEndpointWellFormed at hW
    rw [hEp] at hW
    rcases hTl with hTl | hTl
    · obtain ⟨tcb, hT, -⟩ := hW.1.2.2 tl hTl; exact hNe _ _ hT
    · obtain ⟨tcb, hT, -⟩ := hW.2.2.2 tl hTl; exact hNe _ _ hT
  · intro tid tcb hT
    exact tcbQueueChainAcyclic_no_self_loop hInv.dualQueueSystemInvariant.chainAcyclic tid tcb hT
  · intro tid tcb rid hT hRO
    obtain ⟨r, hR, -⟩ := hInv.replyCallerLinkage.1.1 tid tcb rid hT hRO
    exact hNe _ _ hR
  · intro tid tcb rid hT hP
    obtain ⟨-, r, hR, -⟩ := hInv.pendingReceiveReplyWellFormed.1 tid tcb rid
      ((SystemState.getTcb?_eq_some_iff st tid tcb).mpr hT) hP
    exact hNe _ _ ((SystemState.getReply?_eq_some_iff st rid r).mp hR)

/-- **An erase of a detached object preserves the bundle**: the retype write
with nothing in the target's place (`retypeOrEraseWrite_preserves_ipcInvariantFull`),
the final-delete retire of a passive object being such a write. -/
theorem eraseWrite_preserves_ipcInvariantFull
    {st st' : SystemState} {target : SeLe4n.ObjId}
    (hAt : st'.objects[target]? = none)
    (hNe : ∀ oid : SeLe4n.ObjId, oid ≠ target → st'.objects[oid]? = st.objects[oid]?)
    (hDet : erasedTargetDetached st target)
    (hInv : ipcInvariantFull st) :
    ipcInvariantFull st' :=
  retypeOrEraseWrite_preserves_ipcInvariantFull (newObj := .reply (Reply.empty ⟨0⟩))
    (.inr hAt) hNe ⟨rfl, rfl⟩ hDet hInv

/-- **A quiescent passive object holds no binding code**: a notification the
retire admits is bound to no thread (`passiveObjectQuiescent`'s own-link read of
`boundTCBCode`), and the other passive kinds hold no code. -/
theorem passiveObjectQuiescent_bindingCodes {st : SystemState} {x : SeLe4n.ObjId}
    (hP : passiveKernelObject st.objects[x]?) (hQ : passiveObjectQuiescent st x = true) :
    notificationBindingCodes st.objects[x]? = (0, 0) := by
  unfold passiveObjectQuiescent SystemState.getObject? at hQ
  cases hO : st.objects[x]? with
  | none => rfl
  | some o =>
    rw [hO] at hQ hP
    cases o with
    | notification n =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hQ
      simp [notificationBindingCodes, KernelObject.bindingCodes, hQ.2]
    | tcb _ => exact absurd hP id
    | _ => rfl

/-- **No thread is queued on a quiescent passive object**: one queued on it
names an endpoint there (`ipcStateQueueMembershipConsistent`), whose queues are
empty, so none is blocked on it (`endpointQueues_empty_noneBlocked`). -/
theorem passiveObjectQuiescent_notQueuedOn {st : SystemState} {x : SeLe4n.ObjId}
    (hQ : passiveObjectQuiescent st x = true) (hObjInv : st.objects.invExt)
    (hInv : ipcInvariantFull st) {tid : SeLe4n.ThreadId} {tcb : TCB}
    (hT : st.objects[tid.toObjId]? = some (.tcb tcb)) : ¬ ipcStateQueuedOn x tcb.ipcState := by
  intro hB
  have hM := hInv.ipcStateQueueMembershipConsistent tid tcb hT
  have hEp : ∃ ep, st.objects[x]? = some (.endpoint ep) := by
    revert hM hB
    cases tcb.ipcState <;> simp only [ipcStateQueuedOn, false_imp_iff, imp_false] <;>
      first
      | (intro hE hM; subst hE; obtain ⟨ep, hEp, -⟩ := hM; exact ⟨ep, hEp⟩)
      | trivial
  obtain ⟨ep, hEp⟩ := hEp
  obtain ⟨hS, hR⟩ := passiveObjectQuiescent_endpoint hQ hEp
  exact endpointQueues_empty_noneBlocked hInv hObjInv hEp hS hR hT hB

/-- **A quiescent passive object is detached from everything the bundle
reads**: it is no thread and no scheduling context, so every clause about the
object at the key is vacuous; queue links, boundaries and heads name threads,
so none names it; a thread blocked on it would be queued on it
(`ipcStateQueueMembershipConsistent`), and its queues are empty
(`endpointQueues_empty_noneBlocked`); a caller's reply link to it is answered by
its caller (`replyCallerLinkage`), and it has none; a receiver's stash of it is
recorded on it (`pendingReceiveReplyWellFormed`), and it records no live stash;
and as a notification it is bound to no thread.  Every fact is read off the
object's own links. -/
theorem erasedTargetDetached_of_unreferenced {st : SystemState} {x : SeLe4n.ObjId}
    (hP : passiveKernelObject st.objects[x]?) (hQ : passiveObjectQuiescent st x = true)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st) : erasedTargetDetached st x := by
  have hNo : ∀ t : TCB, st.objects[x]? ≠ some (.tcb t) := fun t h => by rw [h] at hP; exact hP
  have hNe : ∀ (oid : SeLe4n.ObjId) (t : TCB), st.objects[oid]? = some (.tcb t) → oid ≠ x :=
    fun oid t h hEq => hNo t (hEq ▸ h)
  have hNoSc : ∀ (s : SeLe4n.SchedContextId) (sc : SchedContext),
      st.objects[s.toObjId]? = some (.schedContext sc) → s.toObjId ≠ x :=
    fun s sc h hEq => by rw [hEq] at h; rw [h] at hP; exact hP
  have hQueued : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB), st.objects[tid.toObjId]? = some (.tcb tcb) →
      ¬ ipcStateQueuedOn x tcb.ipcState :=
    fun _ _ hT => passiveObjectQuiescent_notQueuedOn hQ hObjInv hInv hT
  have hReplyAt : ∀ (rid : SeLe4n.ReplyId) (r : Reply), rid.toObjId = x →
      st.objects[rid.toObjId]? = some (.reply r) →
      r.callerCode = 0 ∧ st.replyStashedAt rid r = false := by
    intro rid r hEq hR
    have hR' := hR; rw [hEq] at hR'
    obtain ⟨h1, h2, -⟩ := passiveObjectQuiescent_reply hQ hR'
    refine ⟨h1, ?_⟩
    have : rid = ⟨x.val⟩ := by rw [← hEq]; rfl
    rw [this]; exact h2
  refine ⟨fun tid tcb scId hT hTB => ?_, fun tid tcb scId owner hT hB => ?_,
    fun t h => absurd h (hNo _), fun t h => absurd h (hNo _), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    passiveObjectQuiescent_bindingCodes hP hQ⟩
  · obtain ⟨⟨sc, hSc⟩, -⟩ := hInv.blockedThreadTimeoutConsistent tid tcb scId hT hTB
    exact hNoSc _ _ hSc
  · obtain ⟨⟨sc, hSc, -⟩, -⟩ := hInv.donationOwnerValid tid tcb scId owner hT hB
    exact hNoSc _ _ hSc
  · intro tid tcb hT
    refine ⟨fun e => hQueued tid tcb hT ?_, fun e => hQueued tid tcb hT ?_,
      fun e => hQueued tid tcb hT ?_⟩ <;> rw [e] <;> rfl
  · intro a tcbA b hA hN
    obtain ⟨tcbB, hB, -⟩ := hInv.dualQueueSystemInvariant.linkIntegrity.1 a tcbA hA b hN
    exact hNe _ _ hB
  · intro b tcbB a hB hPv
    obtain ⟨tcbA, hA, -⟩ := hInv.dualQueueSystemInvariant.linkIntegrity.2 b tcbB hB a hPv
    exact hNe _ _ hA
  · intro epId ep hd hEp hH
    have hW := hInv.dualQueueSystemInvariant.endpointsWellFormed epId ep hEp
    unfold dualQueueEndpointWellFormed at hW
    rw [hEp] at hW
    rcases hH with hH | hH
    · obtain ⟨tcb, hT, -⟩ := hW.1.2.1 hd hH; exact hNe _ _ hT
    · obtain ⟨tcb, hT, -⟩ := hW.2.2.1 hd hH; exact hNe _ _ hT
  · intro epId ep tl hEp hTl
    have hW := hInv.dualQueueSystemInvariant.endpointsWellFormed epId ep hEp
    unfold dualQueueEndpointWellFormed at hW
    rw [hEp] at hW
    rcases hTl with hTl | hTl
    · obtain ⟨tcb, hT, -⟩ := hW.1.2.2 tl hTl; exact hNe _ _ hT
    · obtain ⟨tcb, hT, -⟩ := hW.2.2.2 tl hTl; exact hNe _ _ hT
  · intro tid tcb hT
    exact tcbQueueChainAcyclic_no_self_loop hInv.dualQueueSystemInvariant.chainAcyclic tid tcb hT
  · intro tid tcb rid hT hRO hEq
    obtain ⟨r, hR, hC⟩ := hInv.replyCallerLinkage.1.1 tid tcb rid hT hRO
    have h0 := (hReplyAt rid r hEq hR).1
    rw [Reply.caller, h0] at hC; cases hC
  · intro tid tcb rid hT hPR hEq
    obtain ⟨r, hR, hS⟩ := pendingReceiveReplyWellFormed.stashedAt
      hInv.pendingReceiveReplyWellFormed hT hPR
    rw [(hReplyAt rid r hEq hR).2] at hS; cases hS

/-- **A retirable thread is detached from everything the bundle reads**: it is
no endpoint, reply or scheduling context, so no blocked thread, reply link,
stash, timeout or donation names it (each names a live object of its own
kind); it is ready and links to no successor (`threadQuiescent`); and no queue
link or queue boundary names it — a neighbour's link is answered by its own
(`tcbQueueLinkIntegrity`), which it does not hold, and a queue's ends are
blocked on the queue (`queueHeadBlockedConsistent`,
`endpointQueueTailBlockedConsistent`), which it is not. -/
theorem erasedTargetDetached_of_threadRetirable {st : SystemState} {x : SeLe4n.ObjId}
    (h : threadRetirable st x = true) (hInv : ipcInvariantFull st) :
    erasedTargetDetached st x := by
  obtain ⟨t, hT, hTid, -, hQ, -⟩ := threadRetirable_parts h
  obtain ⟨-, -, -, -, hQN, hQP, -⟩ := threadQuiescent_codes hQ
  have hReady := threadQuiescent_ipcState hQ
  have hNoEp : ∀ ep : Endpoint, st.objects[x]? ≠ some (.endpoint ep) := fun ep h' => by
    rw [hT] at h'; cases h'
  have hNoR : ∀ r : Reply, st.objects[x]? ≠ some (.reply r) := fun r h' => by
    rw [hT] at h'; cases h'
  have hNoSc : ∀ sc : SchedContext, st.objects[x]? ≠ some (.schedContext sc) := fun sc h' => by
    rw [hT] at h'; cases h'
  have hVal : ∀ b : SeLe4n.ThreadId, b.toObjId = x → b.val = x.val :=
    fun b hb => congrArg SeLe4n.ObjId.val hb
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro tid tcb scId hT' hTB hEq
    obtain ⟨⟨sc, hSc⟩, -⟩ := hInv.blockedThreadTimeoutConsistent tid tcb scId hT' hTB
    exact hNoSc sc (hEq ▸ hSc)
  · intro tid tcb scId owner hT' hB hEq
    obtain ⟨⟨sc, hSc, -⟩, -⟩ := hInv.donationOwnerValid tid tcb scId owner hT' hB
    exact hNoSc sc (hEq ▸ hSc)
  · intro t' hT' ep rt hIpc
    rw [hT] at hT'; cases hT'
    rw [threadQuiescent_ipcState hQ] at hIpc; cases hIpc
  · intro t' hT'
    rw [hT] at hT'; cases hT'
    exact threadQuiescent_queueNext hQ
  · intro tid tcb hT'
    have hM := hInv.ipcStateQueueMembershipConsistent tid tcb hT'
    refine ⟨fun hS' => ?_, fun hR => ?_, fun hC => ?_⟩
    · rw [hS'] at hM; obtain ⟨ep, hEp, -⟩ := hM; exact hNoEp _ hEp
    · rw [hR] at hM; obtain ⟨ep, hEp, -⟩ := hM; exact hNoEp _ hEp
    · rw [hC] at hM; obtain ⟨ep, hEp, -⟩ := hM; exact hNoEp _ hEp
  · intro a tcbA b hA hN hEq
    obtain ⟨tcbB, hB, hBP⟩ := hInv.dualQueueSystemInvariant.linkIntegrity.1 a tcbA hA b hN
    rw [hEq, hT] at hB; cases hB
    unfold TCB.queuePrev at hBP; rw [hQP] at hBP; cases hBP
  · intro b tcbB a hB hP hEq
    obtain ⟨tcbA, hA, hAN⟩ := hInv.dualQueueSystemInvariant.linkIntegrity.2 b tcbB hB a hP
    rw [hEq, hT] at hA; cases hA
    unfold TCB.queueNext at hAN; rw [hQN] at hAN; cases hAN
  · intro epId ep hd hEp hH hEq
    have hB := hInv.queueHeadBlockedConsistent epId ep hd t hEp (hEq ▸ hT)
    rcases hH with hH | hH
    · rcases hB.2 hH with e | e <;> rw [hReady] at e <;> cases e
    · have e := hB.1 hH; rw [hReady] at e; cases e
  · intro epId ep tl hEp hTl hEq
    have hB := hInv.endpointQueueTailBlockedConsistent epId ep tl t hEp (hEq ▸ hT)
    rcases hTl with hTl | hTl
    · rcases hB.2 hTl with e | e <;> rw [hReady] at e <;> cases e
    · have e := hB.1 hTl; rw [hReady] at e; cases e
  · intro tid tcb hT'
    exact tcbQueueChainAcyclic_no_self_loop hInv.dualQueueSystemInvariant.chainAcyclic tid tcb hT'
  · intro tid tcb rid hT' hRO hEq
    obtain ⟨r, hR, -⟩ := hInv.replyCallerLinkage.1.1 tid tcb rid hT' hRO
    exact hNoR r (hEq ▸ hR)
  · intro tid tcb rid hT' hP hEq
    obtain ⟨-, r, hR, -⟩ := hInv.pendingReceiveReplyWellFormed.1 tid tcb rid
      ((SystemState.getTcb?_eq_some_iff st tid tcb).mpr hT') hP
    exact hNoR r (hEq ▸ (SystemState.getReply?_eq_some_iff st rid r).mp hR)
  · rw [hT]
    simp [notificationBindingCodes, KernelObject.bindingCodes,
      (threadQuiescent_codes hQ).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]

/-- A binding read off its codes names the context its context word names. -/
theorem TCB.scBindingScCode_of_names {t : TCB} {s : SeLe4n.SchedContextId}
    (h : t.schedContextBinding.scId? = some s) : t.scBindingScCode = s.val + 1 := by
  unfold TCB.schedContextBinding at h
  generalize t.scBindingScCode = c at h ⊢
  generalize t.scBindingOwnerCode = o at h
  cases c with
  | zero => cases h
  | succ c => cases o <;> (simp only [SchedContextBinding.ofCodes, SchedContextBinding.scId?,
      Option.some.injEq] at h; subst h; rfl)

/-- ...and a context word names the context the binding read off it names. -/
theorem TCB.schedContextBinding_scId?_of_code {t : TCB} {n : Nat}
    (h : t.scBindingScCode = n + 1) : t.schedContextBinding.scId? = some ⟨n⟩ := by
  unfold TCB.schedContextBinding
  rw [h]
  cases t.scBindingOwnerCode <;> rfl

/-- **The thread-side half of the binding pair is a consequence**: a thread's
own context names it by the binding pair, and a context lent to it names it by
the loan record (`donationOwnerValid`). -/
theorem schedContextBindingBidirectional_of_consistent {st : SystemState}
    (hC : schedContextBindingConsistent st) (hD : donationOwnerValid st) :
    schedContextBindingBidirectional st := by
  intro t tcb scId hT hs
  cases hb : tcb.schedContextBinding with
  | unbound => rw [hb] at hs; cases hs
  | bound s =>
    rw [hb] at hs; cases hs; exact hC.1 t tcb hT _ hb
  | donated s o =>
    rw [hb] at hs; cases hs; exact (hD t tcb _ o hT hb).1

/-- A context the retire guard admits is bound to no thread. -/
theorem schedContextRetirable_boundThread {st : SystemState} {x : SeLe4n.ObjId}
    {sc : SchedContext} (h : schedContextRetirable st x = true)
    (hS : st.objects[x]? = some (.schedContext sc)) : sc.boundThread = none := by
  obtain ⟨sc', hS', hB0, _⟩ := schedContextRetirable_parts h
  rw [hS] at hS'; cases hS'
  simp only [SchedContext.boundThread, hB0]; rfl

/-- **No thread names a context the retire admits** (`objectNamesSchedContext`),
though the guard reads the context's own links alone: a thread bound to it, as
its own or on loan, is named by it back (`schedContextBindingConsistent`, the
loan record `donationOwnerValid`), and it is bound to no thread; and no thread
holds a timeout budget at all (`allTimeoutBudgetsNone`). -/
theorem schedContextRetirable.tcbNamesNone {st : SystemState} {x : SeLe4n.ObjId}
    (h : schedContextRetirable st x = true) (hC : schedContextBindingConsistent st)
    (hD : donationOwnerValid st) (hB : allTimeoutBudgetsNone st)
    {k : SeLe4n.ObjId} {t : TCB} (hK : st.objects[k]? = some (.tcb t)) :
    objectNamesSchedContext (.tcb t) (x.val + 1) = false := by
  obtain ⟨sc, hS, -⟩ := schedContextRetirable_parts h
  have hT : st.objects[(SeLe4n.ThreadId.ofObjId k).toObjId]? = some (.tcb t) := hK
  simp only [objectNamesSchedContext, hB _ _ hT, Bool.or_false]
  cases hc : (t.scBindingScCode == x.val + 1) with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨sc', hS', hb⟩ := schedContextBindingBidirectional_of_consistent hC hD _ t _ hT
      (TCB.schedContextBinding_scId?_of_code (beq_iff_eq.mp hc))
    have hx : (⟨x.val⟩ : SeLe4n.SchedContextId).toObjId = x := rfl
    rw [hx, hS] at hS'; cases hS'
    rw [schedContextRetirable_boundThread h hS] at hb; cases hb

/-- **A context a thread names is not retired** (`schedContextRetirable.tcbNamesNone`
read backwards). -/
theorem schedContextRetirable_false_of_tcbNamed {st : SystemState} {x k : SeLe4n.ObjId}
    {t : TCB} (hC : schedContextBindingConsistent st) (hD : donationOwnerValid st)
    (hB : allTimeoutBudgetsNone st) (hK : st.objects[k]? = some (.tcb t))
    (hN : objectNamesSchedContext (.tcb t) (x.val + 1) = true) :
    schedContextRetirable st x = false := by
  cases hR : schedContextRetirable st x with
  | false => rfl
  | true => rw [schedContextRetirable.tcbNamesNone hR hC hD hB hK] at hN; cases hN

/-- **A retirable scheduling context is detached from everything the bundle
reads**: it is no thread, endpoint or reply, so every clause about a thread at
the key is vacuous and no blocked thread, queue link, boundary, reply link or
stash names it; no thread's timeout names it, since no thread holds a timeout
budget (`allTimeoutBudgetsNone`); and no thread's loan names it, since a lent
context names its borrower back (`donationOwnerValid`) and an admitted one is
bound to no thread. -/
theorem erasedTargetDetached_of_schedContextRetirable {st : SystemState} {x : SeLe4n.ObjId}
    (h : schedContextRetirable st x = true) (hInv : ipcInvariantFull st)
    (hBudgets : allTimeoutBudgetsNone st) :
    erasedTargetDetached st x := by
  obtain ⟨sc, hT, -⟩ := schedContextRetirable_parts h
  have hSb := schedContextRetirable_boundThread h hT
  have hNoEp : ∀ ep : Endpoint, st.objects[x]? ≠ some (.endpoint ep) := fun ep h' => by
    rw [hT] at h'; cases h'
  have hNoR : ∀ r : Reply, st.objects[x]? ≠ some (.reply r) := fun r h' => by
    rw [hT] at h'; cases h'
  have hNo : ∀ t : TCB, st.objects[x]? ≠ some (.tcb t) := fun t h' => by
    rw [hT] at h'; cases h'
  have hNe : ∀ (oid : SeLe4n.ObjId) (t : TCB), st.objects[oid]? = some (.tcb t) → oid ≠ x :=
    fun oid t h hEq => hNo t (hEq ▸ h)
  have hVal : ∀ s : SeLe4n.SchedContextId, s.toObjId = x → s.val = x.val :=
    fun s hs => congrArg SeLe4n.ObjId.val hs
  refine ⟨?_, ?_, fun t h => absurd h (hNo _), fun t h => absurd h (hNo _),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [hT]; rfl⟩
  · intro tid tcb scId hT' hTB _
    rw [hBudgets tid tcb hT'] at hTB; cases hTB
  · intro tid tcb scId owner hT' hB hEq
    obtain ⟨⟨sc', hS', hb⟩, -⟩ := hInv.donationOwnerValid tid tcb scId owner hT' hB
    rw [hEq, hT] at hS'; cases hS'
    rw [hSb] at hb; cases hb
  · intro tid tcb hT'
    have hM := hInv.ipcStateQueueMembershipConsistent tid tcb hT'
    refine ⟨fun hS' => ?_, fun hR => ?_, fun hC => ?_⟩
    · rw [hS'] at hM; obtain ⟨ep, hEp, -⟩ := hM; exact hNoEp _ hEp
    · rw [hR] at hM; obtain ⟨ep, hEp, -⟩ := hM; exact hNoEp _ hEp
    · rw [hC] at hM; obtain ⟨ep, hEp, -⟩ := hM; exact hNoEp _ hEp
  · intro a tcbA b hA hN
    obtain ⟨tcbB, hB, -⟩ := hInv.dualQueueSystemInvariant.linkIntegrity.1 a tcbA hA b hN
    exact hNe _ _ hB
  · intro b tcbB a hB hPv
    obtain ⟨tcbA, hA, -⟩ := hInv.dualQueueSystemInvariant.linkIntegrity.2 b tcbB hB a hPv
    exact hNe _ _ hA
  · intro epId ep hd hEp hH
    have hW := hInv.dualQueueSystemInvariant.endpointsWellFormed epId ep hEp
    unfold dualQueueEndpointWellFormed at hW
    rw [hEp] at hW
    rcases hH with hH | hH
    · obtain ⟨tcb, hT', -⟩ := hW.1.2.1 hd hH; exact hNe _ _ hT'
    · obtain ⟨tcb, hT', -⟩ := hW.2.2.1 hd hH; exact hNe _ _ hT'
  · intro epId ep tl hEp hTl
    have hW := hInv.dualQueueSystemInvariant.endpointsWellFormed epId ep hEp
    unfold dualQueueEndpointWellFormed at hW
    rw [hEp] at hW
    rcases hTl with hTl | hTl
    · obtain ⟨tcb, hT', -⟩ := hW.1.2.2 tl hTl; exact hNe _ _ hT'
    · obtain ⟨tcb, hT', -⟩ := hW.2.2.2 tl hTl; exact hNe _ _ hT'
  · intro tid tcb hT'
    exact tcbQueueChainAcyclic_no_self_loop hInv.dualQueueSystemInvariant.chainAcyclic tid tcb hT'
  · intro tid tcb rid hT' hRO hEq
    obtain ⟨r, hR, -⟩ := hInv.replyCallerLinkage.1.1 tid tcb rid hT' hRO
    exact hNoR r (hEq ▸ hR)
  · intro tid tcb rid hT' hP hEq
    obtain ⟨-, r, hR, -⟩ := hInv.pendingReceiveReplyWellFormed.1 tid tcb rid
      ((SystemState.getTcb?_eq_some_iff st tid tcb).mpr hT') hP
    exact hNoR r (hEq ▸ (SystemState.getReply?_eq_some_iff st rid r).mp hR)

/-- **An admitted erase is detached**: the retire admits a passive object only
quiescent and a thread or scheduling context only retirable, and each gives
the pack. -/
theorem erasedTargetDetached_of_admitted {st : SystemState} {x : SeLe4n.ObjId}
    (hAdm : finalRetireAdmitted st x = true) (hE : erasableKernelObject st.objects[x]?)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hBudgets : allTimeoutBudgetsNone st) : erasedTargetDetached st x := by
  by_cases hP : passiveKernelObject st.objects[x]?
  · have hParts := passiveObjectRetirable_parts (finalRetireAdmitted.retirable hAdm hP)
    exact erasedTargetDetached_of_unreferenced hP hParts.1 hObjInv hInv
  · have hK : schedulingKindAt st x = true := by
      rw [schedulingKindAt_iff]
      unfold erasableKernelObject at hE; unfold passiveKernelObject at hP
      unfold schedulingKernelObject
      split at hE <;> simp_all
    have hR := finalRetireAdmitted.schedulingRetirable hAdm hK
    unfold schedulingObjectRetirable at hR
    rcases Bool.or_eq_true_iff.mp hR with hR | hR
    · exact erasedTargetDetached_of_threadRetirable hR hInv
    · exact erasedTargetDetached_of_schedContextRetirable hR hInv hBudgets

/-- **The final-delete retire preserves the bundle**: the passive erase takes
out an object nothing the bundle reads names (`eraseWrite_preserves_ipcInvariantFull`,
`erasedTargetDetached_of_admitted`), and the recorded retire after it
touches only the memory kinds (`finalRetireWrite.memoryKindOrAbsent`). -/
theorem retireFinalObject_preserves_ipcInvariantFull (ec : Concurrency.CoreId)
    (target recorder : Nat) (st : SystemState) (hObjInv : st.objects.invExt)
    (hInv : ipcInvariantFull st) (hBudgets : allTimeoutBudgetsNone st) :
    ipcInvariantFull (retireFinalObject ec target recorder st) ∧
      (retireFinalObject ec target recorder st).objects.invExt := by
  rcases retireFinalObject_cases ec target recorder st with hE | ⟨hSz, hAdm, hE⟩
  · rw [hE]; exact ⟨hInv, hObjInv⟩
  rw [hE]
  generalize SeLe4n.ObjId.ofNat (target - 1) = x at hAdm ⊢
  obtain ⟨i0, room0, -, -, -, -, ne0, -⟩ := eraseRetiredObject_frame st x hObjInv hSz
  have h0 : ipcInvariantFull (eraseRetiredObject st x) := by
    by_cases hP : erasableKernelObject st.objects[x]?
    · exact eraseWrite_preserves_ipcInvariantFull (eraseRetiredObject_self hP hObjInv) ne0
        (erasedTargetDetached_of_admitted hAdm hP hObjInv hInv hBudgets) hInv
    · rw [eraseRetiredObject_of_not st x hP]; exact hInv
  obtain ⟨hExt, -, -, -, hW⟩ := retireRecordedObject_frame ec recorder x _ i0 room0
  exact ⟨ipcInvariantFull_of_memoryKindWrite
    (hW.memoryKindOrAbsent (eraseRetiredObject_not_passive st x hObjInv)) h0, hExt⟩

/-- The finalising delete keeps the object table well formed. -/
theorem cspaceDeleteSlotFinalising_preserves_objects_invExt
    (ec : Concurrency.CoreId) (addr : CSpaceAddr) (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (hStep : cspaceDeleteSlotFinalising ec addr st = .ok ((), st')) :
    st'.objects.invExt := by
  obtain ⟨st1, st2, hD, hF, rfl⟩ := cspaceDeleteSlotFinalising_ok ec addr st st' hStep
  exact (retireFinalObject_frame ec _ _ _ (finaliseReleased_frame _ st2
    (finaliseDestroyedCapabilities_ok_frame ec _ _ st1 st2
      (cspaceDeleteSlot_preserves_objects_invExt st st1 addr hObjInv hD) hF).1).invExt).1

/-- **WS-ZA ZA5.4 part 14: every object a carve makes is pristine** — a thread
unblocked, unqueued, unbound and with empty space slots, an endpoint with both
queues empty, a notification idle with no waiter and no badge, a reply with no
caller and a CNode with no capability (`retypeReplacementFresh`). -/
theorem CarveRequest.object_replacementFresh (untypedId childId : SeLe4n.ObjId)
    (ut : UntypedObject) (idx : Nat) (req : CarveRequest) :
    retypeReplacementFresh (req.object untypedId childId ut idx) := by
  cases req <;>
    simp [CarveRequest.object, retypeReplacementFresh, carvedTcb, carvedCNode, CNode.lookup,
      CNode.slots_ofSlots, UniqueSlotMap.get?_filter, UniqueSlotMap.get?_empty, Reply.empty,
      TCB.spaceSlotCaps, Endpoint.ofQueues]

/-- **WS-BP BP7.1, every kind since WS-ZA ZA5.4 part 14**: a carve out of an
untyped preserves the bundle: the child's record rewrites an untyped in place,
the fresh object — pristine whatever its kind (`CarveRequest.object_replacementFresh`)
— lands at a key that held nothing (`retypeFromUntyped`'s collision guard), so
nothing the bundle reads names it (`retypeTargetDetached_of_absent`), and the
authority's free index is rewritten in its slot, its badge kept. -/
theorem retypeFromUntyped_carve_preserves_ipcInvariantFull
    (st st' : SystemState) (authority : CSpaceAddr)
    (untypedId childId : SeLe4n.ObjId) (ut₀ : UntypedObject) (idx : Nat) (req : CarveRequest)
    (allocSize : Nat)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hStep : retypeFromUntyped authority untypedId childId (req.object untypedId childId ut₀ idx)
      allocSize st = .ok ((), st')) :
    ipcInvariantFull st' ∧ st'.objects.invExt := by
  have hFresh := retypeFromUntyped_childId_fresh authority untypedId childId
    _ _ st st' hStep
  obtain ⟨ut, ut', cap, stUt, _, stCh, cn, hUt, _, _, _, _, _, _, hLkA, _, _, hStUt, hStCh, hOCh,
    hStIdx⟩ := retypeFromUntyped_ok_stores st st' authority untypedId childId _ _ hObjInv hStep
  have hNe : childId ≠ untypedId := by
    intro h; rw [h, hUt] at hFresh; simp at hFresh
  have hInvUt := storeObject_inertNonCNode_preserves_ipcInvariantFull st stUt untypedId
    (.untyped ut') hObjInv hInv (Or.inr (by rw [hUt]; trivial)) trivial
    (fun _ h => KernelObject.noConfusion h) hStUt
  have hObjInvUt := storeObject_preserves_objects_invExt _ _ _ _ hObjInv hStUt
  have hChildNone : stUt.objects[childId]? = none := by
    rw [storeObject_objects_ne _ _ _ _ _ hNe hObjInv hStUt]
    cases h : st.objects[childId]? with
    | none => rfl
    | some _ => rw [h] at hFresh; simp at hFresh
  have hInvCh : ipcInvariantFull stCh :=
    retypeWrite_preserves_ipcInvariantFull
      (storeObject_objects_eq _ _ _ _ hObjInvUt hStCh)
      (fun oid h => storeObject_objects_ne _ _ _ _ _ h hObjInvUt hStCh)
      (CarveRequest.object_replacementFresh untypedId childId ut₀ idx req)
      (retypeTargetDetached_of_absent hChildNone hInvUt) hInvUt
  exact storeObject_capRewrite_preserves_ipcInvariantFull authority cn cap _ stCh st'
    (storeObject_preserves_objects_invExt _ _ _ _ hObjInvUt hStCh) hInvCh hOCh hLkA
    (Capability.withFreeIndex_badge _ _) hStIdx

/-- **WS-BP BP7.1 (`v0.36.5`, generalized at slice 4 and to every kind at
WS-ZA ZA5.4 part 14)**: the untyped carve preserves `ipcInvariantFull` — the
carve above, a scrub of machine memory the bundle does not read (or none), a
capability install carrying no badge, and the CDT edge. -/
theorem untypedRetypeObject_preserves_ipcInvariantFull
    (src dst : CSpaceAddr) (childId : SeLe4n.ObjId) (req : CarveRequest)
    (st st' : SystemState)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hStep : untypedRetypeObject src childId dst req st = .ok ((), st')) :
    ipcInvariantFull st' := by
  obtain ⟨utCap, untypedId, ut, st1, st2, _, _, _, hRt, hIns, rfl⟩ :=
    untypedRetypeObject_ok_decompose src dst childId req st st' hObjInv hStep
  obtain ⟨hInv1, hObjInv1⟩ := retypeFromUntyped_carve_preserves_ipcInvariantFull st st1 src
    untypedId childId ut _ req _ hObjInv hInv hRt
  have hInvZ : ipcInvariantFull (req.scrub st1 ut (req.carveIndex ut (retypeFreeIndex st src utCap))) :=
    ipcInvariantFull_of_objects_eq (CarveRequest.scrub_objects _ _ _ _) hInv1
  have hObjInvZ : (req.scrub st1 ut (req.carveIndex ut (retypeFreeIndex st src utCap))).objects.invExt := by
    rw [CarveRequest.scrub_objects]; exact hObjInv1
  exact cdtRecord_bundle_frame st2 src dst DerivationOp.retype
    (cspaceInsertSlot_preserves_objects_invExt _ st2 dst _ hObjInvZ hIns)
    (cspaceInsertSlot_preserves_ipcInvariantFull _ st2 dst _ hObjInvZ hInvZ
      (fun b hb => by
        cases req <;> simp [CarveRequest.capability, frameCapability, untypedCapability,
          vspaceRootCapability, pageTableCapability, kernelObjectCapability] at hb)
      hIns)

/-- A fully descheduled thread occupies no core, so the destroy sweep's
per-core step is the literal identity. -/
private theorem removeRunnableFromAllCores_id_of_descheduled
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hRQ : ∀ c : CoreId, st.queuedOn c tid = false)
    (hCur : ∀ c : CoreId, st.scheduler.currentOnCore c ≠ some tid) :
    removeRunnableFromAllCores st tid = st := by
  have hstep : ∀ c : CoreId, removeRunnableStepOnCore tid st c = st := by
    intro c
    unfold removeRunnableStepOnCore
    have hOcc : threadOccupiesCore st tid c = false := by
      unfold threadOccupiesCore
      rw [hRQ c, Bool.false_or, beq_eq_false_iff_ne]
      exact hCur c
    rw [hOcc]
    simp
  unfold removeRunnableFromAllCores
  generalize SeLe4n.Kernel.Concurrency.allCores = cs
  induction cs with
  | nil => rfl
  | cons c cs ih => rw [List.foldl_cons, hstep c]; exact ih

/-- A thread with no queue links needs no splice — the patch is the identity. -/
private theorem spliceOutMidQueueNode_id_of_unlinked
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hLinks : ∀ tcbX : TCB, lookupTcb st tid = some tcbX →
      tcbX.queuePrev = none ∧ tcbX.queueNext = none) :
    spliceOutMidQueueNode st tid = st := by
  unfold spliceOutMidQueueNode
  cases hLk : lookupTcb st tid with
  | none => rfl
  | some tcbX =>
      obtain ⟨hPrev, hNext⟩ := hLinks tcbX hLk
      simp only [hPrev, hNext]

/-- No endpoint boundary slot holds the victim, so the boundary sweep is the
literal identity. -/
private theorem removeFromAllEndpointQueues_id_of_unqueued
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hLinks : ∀ tcbX : TCB, lookupTcb st tid = some tcbX →
      tcbX.queuePrev = none ∧ tcbX.queueNext = none)
    (hBoundary : ∀ (oid : SeLe4n.ObjId) (ep : Endpoint),
      st.objects[oid]? = some (.endpoint ep) →
      ep.sendQ.head ≠ some tid ∧ ep.sendQ.tail ≠ some tid ∧
      ep.receiveQ.head ≠ some tid ∧ ep.receiveQ.tail ≠ some tid) :
    removeFromAllEndpointQueues st tid = st := by
  unfold removeFromAllEndpointQueues
  rw [spliceOutMidQueueNode_id_of_unlinked st tid hLinks]
  exact RobinHood.RHTable.fold_preserves_of_lookup st.objects st _ (· = st) hObjInv rfl
    (fun acc oid obj hGet hAcc => by
      rw [hAcc]
      cases obj with
      | endpoint ep =>
          have hEp : st.objects[oid]? = some (.endpoint ep) := by
            rw [RHTable_getElem?_eq_get?]; exact hGet
          obtain ⟨h1, h2, h3, h4⟩ := hBoundary oid ep hEp
          have hG : (ep.sendQ.head == some tid || ep.sendQ.tail == some tid
              || ep.receiveQ.head == some tid || ep.receiveQ.tail == some tid) = false := by
            simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne]
            exact ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
          simp only [SystemState.getEndpointWitnessed?_eq_some
            ((SystemState.getEndpoint?_eq_some_iff st oid ep).mpr hEp), hG]
          rfl
      | tcb _ | notification _ | cnode _ | vspaceRoot _ | untyped _
      | schedContext _ | reply _ | frame _ | pageTable _ => rfl)

/-- The victim waits on no notification, so the wait-list removal is the
literal identity: it reads the queue the victim's own state names, and there
is none. -/
private theorem removeFromNotificationWaitQueue_id_of_no_waits
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hNoWait : ∀ tcb : TCB, st.getTcb? tid = some tcb →
      ∀ oid : SeLe4n.ObjId, tcb.ipcState ≠ .blockedOnNotification oid) :
    removeFromNotificationWaitQueue st tid = st := by
  unfold removeFromNotificationWaitQueue
  cases hT : st.getTcb? tid with
  | none => rfl
  | some tcb =>
    simp only []
    cases hS : tcb.ipcState with
    | blockedOnNotification oid => exact absurd hS (hNoWait tcb hT oid)
    | _ => rfl

-- `v0.35.164`: `cleanupDonatedSchedContext_ok_of_not_donated` is gone — the
-- pipeline's first step is `cancelDonationArmOnCore`, which dispatches on the
-- target's own binding, so the pack's two clauses reduce it to the identity
-- directly (`cancelDonationArmOnCore_of_unbound`).

/-- Under the detachment pack the whole TCB reference sweep is the literal
identity, on any state sharing the pre-state's objects and scheduler. -/
private theorem cleanupTcbReferences_id_of_detached
    (st : SystemState) (target : SeLe4n.ObjId) (tcb : TCB)
    (hObjInv : st.objects.invExt)
    (hObj : st.objects[target]? = some (.tcb tcb))
    (hDet : retypeTargetDetached st target)
    (stX : SystemState) (hO : stX.objects = st.objects) (hS : stX.scheduler = st.scheduler) :
    cleanupTcbReferences stX tcb.tid = stX := by
  have hLkT : ∀ tcbX : TCB, lookupTcb stX tcb.tid = some tcbX → tcbX = tcb := by
    intro tcbX hLk
    unfold lookupTcb SystemState.getTcb? at hLk
    split at hLk
    · cases hLk
    · rw [hO, hDet.tcbSelfId tcb hObj, hObj] at hLk
      simp only [Option.some.injEq] at hLk
      exact hLk.symm
  unfold cleanupTcbReferences
  dsimp only []
  rw [removeRunnableFromAllCores_id_of_descheduled stX tcb.tid
    (fun c => by
      rw [(SystemState.RunCoresAgree.of_objects hO).queuedOn]
      exact (hDet.tcbDescheduled tcb hObj c).2.1)
    (fun c => by rw [hS]; exact (hDet.tcbDescheduled tcb hObj c).2.2)]
  rw [removeFromAllEndpointQueues_id_of_unqueued stX tcb.tid (hO ▸ hObjInv)
    (fun tcbX hLk => by
      obtain rfl := hLkT tcbX hLk
      exact ⟨hDet.tcbNoPrev tcbX hObj, hDet.tcbNoNext tcbX hObj⟩)
    (fun oid ep hEp => by
      rw [hO] at hEp
      have hSelf := hDet.tcbSelfId tcb hObj
      refine ⟨?_, ?_, ?_, ?_⟩ <;>
        · intro hBad
          first
            | exact hDet.notHead oid ep tcb.tid hEp (Or.inl hBad) hSelf
            | exact hDet.notHead oid ep tcb.tid hEp (Or.inr hBad) hSelf
            | exact hDet.notTail oid ep tcb.tid hEp (Or.inl hBad) hSelf
            | exact hDet.notTail oid ep tcb.tid hEp (Or.inr hBad) hSelf)]
  exact removeFromNotificationWaitQueue_id_of_no_waits stX tcb.tid
    (fun tcbX hLk => by
      have hRaw := (SystemState.getTcb?_eq_some_iff stX tcb.tid tcbX).mp hLk
      rw [hO, hDet.tcbSelfId tcb hObj, hObj] at hRaw
      cases hRaw
      exact hDet.tcbNotWaiter _ hObj)

/-- Under the detachment pack a successful pre-retype cleanup changes neither
the object store nor the scheduler, up to derivation-link words: the sweeps are
identities, the reservation arm is the identity (the pack refuses a bound or
donated target, `v0.35.164`), the CDT writes are outside the
bundle's read set, and a CNode target's slots leave the tree through a run of
link writes (`linkReach`) from a state with the pre-state's objects. -/
theorem lifecyclePreRetypeCleanup_detached_frame
    (st stClean : SystemState) (target : SeLe4n.ObjId) (currentObj newObj : KernelObject)
    (hObjInv : st.objects.invExt)
    (hObj : st.objects[target]? = some currentObj)
    (hDet : retypeTargetDetached st target)
    (hStep : lifecyclePreRetypeCleanup st target currentObj newObj = .ok stClean) :
    ∃ stM : SystemState, stM.objects = st.objects ∧ stM.scheduler = st.scheduler ∧
      stM.machine = st.machine ∧ SystemState.linkReach stM stClean := by
  unfold lifecyclePreRetypeCleanup at hStep
  cases currentObj with
  | tcb tcb =>
      have hCur : threadHeldOnSomeCore st tcb.tid = false := by
        have hC : threadCurrentOnSomeCore st tcb.tid = false := by
          unfold threadCurrentOnSomeCore
          simp only [List.any_eq_false, beq_iff_eq]
          intro c _
          exact (hDet.tcbDescheduled tcb hObj c).2.2
        have hF : st.machine.fpOwnedOnSomeCore tcb.tid = false :=
          (MachineState.fpOwnedOnSomeCore_eq_false_iff _ _).mpr (hDet.tcbFpReleased tcb hObj)
        have hR : st.machine.residentOnSomeCore tcb.tid = false :=
          (MachineState.residentOnSomeCore_eq_false_iff _ _).mpr
            (hDet.tcbResidencyReleased tcb hObj)
        simp [threadHeldOnSomeCore, hC, hF, hR]
      -- `v0.35.164`: the pack puts the target on the identity arm of the destroy
      -- path's reservation dispatcher — neither `.donated` nor `.bound`.
      have hB : tcb.schedContextBinding = .unbound := by
        cases hB' : tcb.schedContextBinding with
        | unbound => rfl
        | bound scId => exact absurd hB' (hDet.tcbNotBound tcb hObj scId)
        | donated scId owner => exact absurd hB' (hDet.tcbNotDonated tcb hObj scId owner)
      simp only [hCur, Bool.false_eq_true, if_false,
        cancelDonationArmOnCore_of_unbound st tcb.tid tcb hB] at hStep
      -- WS-ZA ZA6.6: the yield steps write nothing — the target holds no
      -- context (`hB`), so the unbind completes nothing, and has yielded to
      -- none (`tcbYieldUnlinked`), so the suspend's cancel clears nothing.
      have h0 : tcb.scBindingScCode = 0 := by
        rcases hc : tcb.scBindingScCode with _ | n
        · rfl
        · exfalso
          simp only [TCB.schedContextBinding, hc, SeLe4n.Kernel.SchedContextBinding.ofCodes] at hB
          split at hB <;> cases hB
      have hC0 : completeHeldYield st tcb.scBindingScCode = st := by rw [h0]; rfl
      rw [hC0, cleanupTcbReferences_id_of_detached st target tcb hObjInv hObj hDet
        st rfl rfl] at hStep
      have hY : cancelYieldTo st tcb.tid = st := by
        unfold cancelYieldTo
        split
        · rename_i t hT
          have hT' := (SystemState.getTcb?_eq_some_iff _ _ _).mp hT
          rw [hDet.tcbSelfId tcb hObj, hObj] at hT'
          cases hT'
          rw [hDet.tcbYieldUnlinked tcb hObj]
        · rfl
      rw [hY] at hStep
      split at hStep
      · contradiction
      · cases hStep
        obtain ⟨cdt, hReach⟩ := detachTcbSlots_shape st target
        exact ⟨{ st with cdt := cdt }, rfl, rfl, rfl, hReach⟩
  | endpoint ep =>
      cases hStep
      exact ⟨_, rfl, rfl, rfl, .refl _⟩
  | cnode cn =>
      simp only [] at hStep
      split at hStep
      · contradiction
      · cases hStep
        obtain ⟨cdt, h⟩ := detachCNodeSlots_shape st target cn
        exact ⟨{ st with cdt := cdt }, rfl, rfl, rfl, h⟩
  | reply r =>
      simp only [] at hStep
      split at hStep
      · contradiction
      · cases hStep
        exact ⟨_, rfl, rfl, rfl, .refl _⟩
  | notification n =>
      cases hStep
      exact ⟨_, rfl, rfl, rfl, .refl _⟩
  | untyped _ | vspaceRoot _ =>
      -- WS-BP BP7.1 slice 4: an untyped target is refused, as a frame is;
      -- `v0.36.35`: and so is a VSpace root.
      cases hStep
  | frame _ | pageTable _ =>
      -- WS-BP BP7.1: a frame target is refused, so there is no `.ok` step.
      cases hStep
  | schedContext sc =>
      -- `v0.35.165`: this arm is now UNREACHABLE under the pack, and that is the
      -- honest discharge rather than an accident of the arm being the identity.
      -- `notSc` says the target holds no scheduling context at all — the retype
      -- payoff's contract is that the caller revoked, suspended, cancelled and
      -- unbound first — while this arm fires exactly when it does.  Since
      -- `v0.35.165` the arm also releases the binding a context still holds, so
      -- it writes a TCB and a replenish queue and the old identity discharge
      -- would be false.
      exact absurd hObj (hDet.notSc sc)

-- ============================================================================
-- §15  TCB lifecycle arms (`.tcbResume`, `.tcbSuspend`)
-- ============================================================================

/-- The IPC-side quiescent shape a suspended thread is left in (and the shape
the resume path re-enters from): `.ready`, no intrusive queue links, no
stashed receive reply.  Pre-state facts, dischargeable before the step. -/
structure threadIpcFieldsQuiescent (st : SystemState) (tid : SeLe4n.ThreadId) : Prop where
  ready : ∀ tcb : TCB, st.getTcb? tid = some tcb → tcb.ipcState = .ready
  noNext : ∀ tcb : TCB, st.getTcb? tid = some tcb → tcb.queueNext = none
  noPrev : ∀ tcb : TCB, st.getTcb? tid = some tcb → tcb.queuePrev = none
  noPPrev : ∀ tcb : TCB, st.getTcb? tid = some tcb → tcb.queuePPrev = none
  noStash : ∀ tcb : TCB, st.getTcb? tid = some tcb → tcb.pendingReceiveReply = none
  noPendingMsg : ∀ tcb : TCB, st.getTcb? tid = some tcb → tcb.pendingMessage = none
  noBudget : ∀ tcb : TCB, st.getTcb? tid = some tcb → tcb.timeoutBudget = none

/-- Under the quiescent shape, restoring a thread to ready rewrites every
cleared field to the value it already holds — the write is pointwise inert. -/
private theorem restoreToReady_getElem_eq_of_quiescent
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hQ : threadIpcFieldsQuiescent st tid) :
    ∀ oid : SeLe4n.ObjId,
      (Lifecycle.Suspend.restoreToReady st tid).objects[oid]? = st.objects[oid]? := by
  intro oid
  unfold Lifecycle.Suspend.restoreToReady Lifecycle.Suspend.restoreToReadyStaging
  cases hLk : st.getTcb? tid with
  | none => rw [SystemState.updateTcb_eq_self_of_none hLk]
  | some tcb =>
      rw [SystemState.updateTcb_eq_of_some hLk]
      dsimp only []
      -- Stated over the shared clear (`TCB.restoredToReady`, `v0.35.134`) rather
      -- than over a copy of its field list, so a field added to the restore
      -- reaches this proof instead of leaving it quietly weaker.
      have hSame : tcb.restoredToReady = tcb := by
        have h1 := (TCB.ipcState_eq_iff_codes _ _).1 (hQ.ready tcb hLk)
        have h2 := hQ.noNext tcb hLk
        have h3 := hQ.noPrev tcb hLk
        have h4 := hQ.noPPrev tcb hLk
        have h5 := hQ.noStash tcb hLk
        cases tcb
        simp_all [ThreadIpcState.objectCode, ThreadIpcState.stateCode]
      rw [hSame]
      have hPre : st.objects[tid.toObjId]? = some (.tcb tcb) :=
        (SystemState.getTcb?_eq_some_iff st tid tcb).mp hLk
      by_cases hK : oid = tid.toObjId
      · subst hK
        simp only [RHTable_getElem?_eq_get?]
        rw [RobinHood.RHTable.getElem?_insert_self st.objects tid.toObjId _ hObjInv]
        rw [← RHTable_getElem?_eq_get?]
        exact hPre.symm
      · simp only [RHTable_getElem?_eq_get?]
        exact RobinHood.RHTable.getElem?_insert_ne st.objects tid.toObjId oid _
          (by simp; exact fun h => hK h.symm) hObjInv

private theorem restoreToReady_objects_invExt (st : SystemState) (tid : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt) :
    (Lifecycle.Suspend.restoreToReady st tid).objects.invExt := by
  unfold Lifecycle.Suspend.restoreToReady Lifecycle.Suspend.restoreToReadyStaging
  exact SystemState.updateTcb_preserves_objects_invExt _ _ _ hObjInv

/-- The resume mid-state — IPC-field restore plus the `threadState`/`pipBoost`
store, neither field bundle-read — preserves the bundle from a quiescent
victim. -/
private theorem resumeReadyMidState_preserves_ipcInvariantFull
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hQ : threadIpcFieldsQuiescent st tid)
    (hInv : ipcInvariantFull st) :
    ipcInvariantFull (Lifecycle.Suspend.resumeReadyMidState st tid) := by
  have hEq := restoreToReady_getElem_eq_of_quiescent st tid hObjInv hQ
  have hObjInv1 := restoreToReady_objects_invExt st tid hObjInv
  have hInv1 : ipcInvariantFull (Lifecycle.Suspend.restoreToReady st tid) :=
    ipcInvariantFull_of_getElem_eq hEq hInv
  unfold Lifecycle.Suspend.resumeReadyMidState
  dsimp only []
  cases hLk : (Lifecycle.Suspend.restoreToReady st tid).getTcb? tid with
  | none => rw [SystemState.updateTcb_eq_self_of_none hLk]; exact hInv1
  | some t =>
      rw [SystemState.updateTcb_eq_of_some hLk]
      exact insertObjects_tcbFieldUpdate_preserves_ipcInvariantFull
        (Lifecycle.Suspend.restoreToReady st tid) tid t
        { t with threadState := .Ready, pipBoostCode := SeLe4n.Priority.optCode (SeLe4n.Kernel.PriorityInheritance.computeMaxWaiterPriority (Lifecycle.Suspend.restoreToReady st tid) tid) }
        hObjInv1 hInv1
        ((SystemState.getTcb?_eq_some_iff _ tid t).mp hLk)
        rfl rfl rfl rfl rfl rfl rfl rfl rfl

/-- Enqueueing an already-`.ready` thread rewrites its TCB to itself and grows
one run queue — the bundle transports, since it reads no run-queue link. -/
theorem enqueueRunnableOnCore_preserves_ipcInvariantFull
    (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hReady : ∀ tcb : TCB, st.getTcb? tid = some tcb → tcb.ipcState = .ready)
    (hInv : ipcInvariantFull st) :
    ipcInvariantFull (enqueueRunnableOnCore st c tid) := by
  -- The case split precedes the unfold: the witnessed lookup's type mentions
  -- `st.getTcb? tid`, so a `cases` over the unfolded match cannot generalise it.
  cases hLk : st.getTcb? tid with
  | none =>
      unfold enqueueRunnableOnCore
      rw [SystemState.getTcbWitnessed?_eq_none hLk]
      exact hInv
  | some tcb =>
      -- The `.ready` mark re-stores the value already there, so the objects
      -- agree off run-queue fields.
      have hA := enqueueRunnableOnCore_objectsAgreeOffRunLinks_of_ready st c tid tcb hLk
        (hReady tcb hLk) hObjInv
      exact ipcInvariantFull_of_objectsAgreeOffRunLinks hA hInv

private theorem resumeReadyMidState_objects_invExt
    (st : SystemState) (tid : SeLe4n.ThreadId) (hObjInv : st.objects.invExt) :
    (Lifecycle.Suspend.resumeReadyMidState st tid).objects.invExt := by
  unfold Lifecycle.Suspend.resumeReadyMidState
  exact SystemState.updateTcb_preserves_objects_invExt _ _ _
    (restoreToReady_objects_invExt st tid hObjInv)

private theorem resumeReadyMidState_getTcb_ready
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hQ : threadIpcFieldsQuiescent st tid) :
    ∀ tcb : TCB, (Lifecycle.Suspend.resumeReadyMidState st tid).getTcb? tid = some tcb →
      tcb.ipcState = .ready := by
  intro tcb hT
  have hEq := restoreToReady_getElem_eq_of_quiescent st tid hObjInv hQ
  have hObjInv1 := restoreToReady_objects_invExt st tid hObjInv
  unfold Lifecycle.Suspend.resumeReadyMidState at hT
  dsimp only [] at hT
  cases hLk : (Lifecycle.Suspend.restoreToReady st tid).getTcb? tid with
  | none =>
      rw [SystemState.updateTcb_eq_self_of_none hLk, hLk] at hT
      cases hT
  | some t =>
      rw [SystemState.updateTcb_eq_of_some hLk] at hT
      have hTobj := (SystemState.getTcb?_eq_some_iff _ tid tcb).mp hT
      dsimp only [] at hTobj
      have hAt : ((Lifecycle.Suspend.restoreToReady st tid).objects.insert tid.toObjId (KernelObject.tcb { t with threadState := .Ready, pipBoostCode := SeLe4n.Priority.optCode (SeLe4n.Kernel.PriorityInheritance.computeMaxWaiterPriority (Lifecycle.Suspend.restoreToReady st tid) tid) }))[tid.toObjId]? = some (KernelObject.tcb { t with threadState := .Ready, pipBoostCode := SeLe4n.Priority.optCode (SeLe4n.Kernel.PriorityInheritance.computeMaxWaiterPriority (Lifecycle.Suspend.restoreToReady st tid) tid) }) := by
        simp only [RHTable_getElem?_eq_get?]
        exact RobinHood.RHTable.getElem?_insert_self _ _ _ hObjInv1
      rw [hAt] at hTobj
      obtain rfl : ({ t with threadState := .Ready, pipBoostCode := SeLe4n.Priority.optCode (SeLe4n.Kernel.PriorityInheritance.computeMaxWaiterPriority (Lifecycle.Suspend.restoreToReady st tid) tid) } : TCB) = tcb := by
        simpa using hTobj
      show t.ipcState = .ready
      have hPre1 := (SystemState.getTcb?_eq_some_iff _ tid t).mp hLk
      rw [hEq tid.toObjId] at hPre1
      exact hQ.ready t ((SystemState.getTcb?_eq_some_iff st tid t).mpr hPre1)

/-- The full per-core resume (live once the context-restore seam flips). -/
theorem resumeThreadOnCore_preserves_ipcInvariantFull
    (st st' : SystemState) (vtid : SeLe4n.ValidThreadId) (ec : CoreId)
    (sgi : Option (CoreId × Concurrency.SgiKind))
    (hObjInv : st.objects.invExt)
    (hQ : threadIpcFieldsQuiescent st vtid.val)
    (hInv : ipcInvariantFull st)
    (hStep : Lifecycle.Suspend.resumeThreadOnCore st vtid ec = .ok (st', sgi)) :
    ipcInvariantFull st' := by
  unfold Lifecycle.Suspend.resumeThreadOnCore at hStep
  dsimp only [] at hStep
  cases hLk : st.getTcb? vtid.val with
  | none => rw [hLk] at hStep; cases hStep
  | some tcb =>
      rw [hLk] at hStep
      dsimp only [] at hStep
      split at hStep
      · cases hStep
      · have hMid := markKeyChangeFrom_preserves_ipcInvariantFull st _ vtid.val
          (resumeReadyMidState_preserves_ipcInvariantFull st vtid.val hObjInv hQ hInv)
        have hMidInv : (markKeyChangeFrom st (Lifecycle.Suspend.resumeReadyMidState st vtid.val)
            vtid.val).objects.invExt := by
          rw [markKeyChangeFrom_objects]; exact resumeReadyMidState_objects_invExt st vtid.val hObjInv
        have hEnq := enqueueRunnableOnCore_preserves_ipcInvariantFull
          (markKeyChangeFrom st (Lifecycle.Suspend.resumeReadyMidState st vtid.val) vtid.val)
          (determineTargetCore st vtid.val) vtid.val hMidInv
          (by rw [markKeyChangeFrom_getTcb?]
              exact resumeReadyMidState_getTcb_ready st vtid.val hObjInv hQ) hMid
        have hEnqInv := enqueueRunnableOnCore_preserves_objects_invExt
          (markKeyChangeFrom st (Lifecycle.Suspend.resumeReadyMidState st vtid.val) vtid.val)
          (determineTargetCore st vtid.val) vtid.val hMidInv
        split at hStep
        · cases hRes : handleRescheduleSgiOnCore (enqueueRunnableOnCore
              (markKeyChangeFrom st (Lifecycle.Suspend.resumeReadyMidState st vtid.val) vtid.val)
              (determineTargetCore st vtid.val) vtid.val) ec with
          | ok st4 =>
              rw [hRes] at hStep
              cases hStep
              exact handleRescheduleSgiOnCore_preserves_ipcInvariantFull _ ec _
                hEnqInv hEnq hRes
          | error e => rw [hRes] at hStep; cases hStep
        · cases hStep
          exact hEnq

/-- Review round (PR #887): **retiring a pending fault on resume preserves
the bundle** — it is `applyFaultRestart` (a one-TCB rewrite of registers and
`pendingFault`, neither read by any conjunct) or the identity. -/
theorem retirePendingFaultForResume_preserves_ipcInvariantFull
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st) :
    ipcInvariantFull (retirePendingFaultForResume st tid) := by
  cases hT : st.getTcb? tid with
  | none => simp only [retirePendingFaultForResume, hT]; exact hInv
  | some tcb =>
      cases hF : tcb.pendingFault with
      | none => simp only [retirePendingFaultForResume, hT, hF]; exact hInv
      | some tf =>
          simp only [retirePendingFaultForResume, hT, hF, applyFaultRestart]
          rw [SystemState.updateTcb_eq_of_some hT]
          exact insertObjects_tcbFieldUpdate_preserves_ipcInvariantFull st tid tcb
            { tcb.withRestartFrame (Architecture.faultRestartFrameOfContext tf.context) with
                pendingFault := none } hObjInv hInv
            ((SystemState.getTcb?_eq_some_iff st tid tcb).mp hT)
            rfl rfl rfl rfl rfl rfl rfl rfl rfl

/-- Review round (PR #887): and the object-store invariant. -/
theorem retirePendingFaultForResume_preserves_objects_invExt
    (st : SystemState) (tid : SeLe4n.ThreadId) (hObjInv : st.objects.invExt) :
    (retirePendingFaultForResume st tid).objects.invExt := by
  cases hT : st.getTcb? tid with
  | none => simp only [retirePendingFaultForResume, hT]; exact hObjInv
  | some tcb =>
      cases hF : tcb.pendingFault with
      | none => simp only [retirePendingFaultForResume, hT, hF]; exact hObjInv
      | some tf =>
          simp only [retirePendingFaultForResume, hT, hF, applyFaultRestart]
          exact SystemState.updateTcb_preserves_objects_invExt _ _ _ hObjInv

/-- Review round (PR #887): the retire step rewrites none of the fields the
quiescence pack reads, so the pack transports to the state the resume runs
on. -/
theorem threadIpcFieldsQuiescent_retirePendingFaultForResume
    (st : SystemState) (tid : SeLe4n.ThreadId) (hObjInv : st.objects.invExt)
    (hQ : threadIpcFieldsQuiescent st tid) :
    threadIpcFieldsQuiescent (retirePendingFaultForResume st tid) tid := by
  cases hT : st.getTcb? tid with
  | none => simp only [retirePendingFaultForResume, hT]; exact hQ
  | some tcb =>
      cases hF : tcb.pendingFault with
      | none => simp only [retirePendingFaultForResume, hT, hF]; exact hQ
      | some tf =>
          simp only [retirePendingFaultForResume, hT, hF]
          have hPost := applyFaultRestart_pc st tid
            (Architecture.faultRestartFrameOfContext tf.context) tcb hT hObjInv
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro tcb' hT' <;> rw [hPost] at hT' <;>
            cases hT'
          · exact hQ.ready tcb hT
          · exact hQ.noNext tcb hT
          · exact hQ.noPrev tcb hT
          · exact hQ.noPPrev tcb hT
          · exact hQ.noStash tcb hT
          · exact hQ.noPendingMsg tcb hT
          · exact hQ.noBudget tcb hT

/-- Review round (PR #887): **configuring a fault handler preserves the
bundle** — a one-TCB rewrite of `faultHandler`, a field no conjunct reads. -/
theorem setThreadFaultHandlerOp_preserves_ipcInvariantFull
    (st st' : SystemState) (vtid : SeLe4n.ValidThreadId) (cptr : SeLe4n.CPtr)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hStep : setThreadFaultHandlerOp st vtid cptr = .ok st') :
    ipcInvariantFull st' := by
  cases hT : st.getTcb? vtid.val with
  | none => simp [setThreadFaultHandlerOp, SystemState.getTcbWitnessed?_eq_none hT] at hStep
  | some tcb =>
      cases hR : resolveFaultHandlerCPtr st tcb cptr with
      | error e =>
          simp [setThreadFaultHandlerOp, SystemState.getTcbWitnessed?_eq_some hT, hR] at hStep
      | ok tgt =>
          rw [setThreadFaultHandlerOp_ok_eq st vtid cptr tcb tgt hT hR] at hStep
          cases hStep
          unfold installFaultHandler SystemState.rewriteObject
          exact insertObjects_tcbFieldUpdate_preserves_ipcInvariantFull st vtid.val tcb
            { tcb with faultHandlerSet := true, faultHandlerWord := cptr } hObjInv hInv
            ((SystemState.getTcb?_eq_some_iff st vtid.val tcb).mp hT)
            rfl rfl rfl rfl rfl rfl rfl rfl rfl

/-- **WS-BP BP7.2**: recording physical writes touches only the ledger, which
no conjunct of the bundle reads. -/
theorem ipcInvariantFull_recordPhysicalWrites {st : SystemState}
    {ws : List Architecture.PhysicalWrite} (h : ipcInvariantFull st) :
    ipcInvariantFull (Architecture.recordPhysicalWrites st ws) :=
  ipcInvariantFull_of_vspaceRootOnlyWrite (st := st)
    (st' := Architecture.recordPhysicalWrites st ws) (fun _ => Or.inl rfl) h

/-- **WS-BP BP7.1 (`v0.36.12`)**: installing a page table preserves
`ipcInvariantFull` — two stores, a page table over a page table and a VSpace
root over a VSpace root, both kinds the bundle does not read. -/
theorem pageTableMap_preserves_ipcInvariantFull (tableId rootId : SeLe4n.ObjId)
    (vaddr : SeLe4n.VAddr) (st st' : SystemState)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hStep : Architecture.pageTableMap tableId rootId vaddr st = .ok ((), st')) :
    ipcInvariantFull st' := by
  obtain ⟨table, root, level, st1, hT, hR, -, -, -, -, hS1, hS2⟩ :=
    Architecture.pageTableMap_ok tableId rootId vaddr st st' hStep
  have hT' := (SystemState.getPageTable?_eq_some_iff st tableId table).mp hT
  have hR' := (SystemState.getVSpaceRoot?_eq_some_iff st rootId root).mp hR
  have hInv1 := storeObject_inertNonCNode_preserves_ipcInvariantFull st st1 tableId _
    hObjInv hInv (Or.inr (by rw [hT']; trivial)) (by trivial)
    (fun _ h => KernelObject.noConfusion h) hS1
  have hObjInv1 := storeObject_preserves_objects_invExt _ _ _ _ hObjInv hS1
  have hNe : rootId ≠ tableId := by
    intro hEq; subst hEq; rw [hT'] at hR'; cases hR'
  have hR1 : st1.objects[rootId]? = some (.vspaceRoot root) := by
    rw [storeObject_objects_ne _ _ _ _ _ hNe hObjInv hS1]; exact hR'
  exact storeObject_inertNonCNode_preserves_ipcInvariantFull
    (Architecture.recordPhysicalWrites st1 _) st' rootId _
    hObjInv1 (ipcInvariantFull_recordPhysicalWrites hInv1)
    (Or.inr (by simp only [Architecture.recordPhysicalWrites_objects, hR1]; trivial))
    (by trivial) (fun _ h => KernelObject.noConfusion h) hS2

/-- **WS-BP BP7.1 (`v0.36.12`)**: removing a page table preserves
`ipcInvariantFull`, for the same reason. -/
theorem pageTableUnmap_preserves_ipcInvariantFull (tableId : SeLe4n.ObjId)
    (st st' : SystemState)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hStep : Architecture.pageTableUnmap tableId st = .ok ((), st')) :
    ipcInvariantFull st' := by
  unfold Architecture.pageTableUnmap at hStep
  cases hT : st.getPageTable? tableId with
  | none => rw [hT] at hStep; cases hStep
  | some table =>
    rw [hT] at hStep
    have hT' := (SystemState.getPageTable?_eq_some_iff st tableId table).mp hT
    simp only at hStep
    cases hI : table.installedIn with
    | none => rw [hI] at hStep; cases hStep; exact hInv
    | some inst =>
      rw [hI] at hStep
      simp only at hStep
      cases hR : st.getVSpaceRoot? inst.root with
      | none =>
        rw [hR] at hStep
        exact storeObject_inertNonCNode_preserves_ipcInvariantFull st st' tableId _
          hObjInv hInv (Or.inr (by rw [hT']; trivial)) (by trivial)
          (fun _ h => KernelObject.noConfusion h) hStep
      | some root =>
        rw [hR] at hStep
        have hR' := (SystemState.getVSpaceRoot?_eq_some_iff st inst.root root).mp hR
        simp only at hStep
        split at hStep
        · split at hStep
          · cases hStep
          · cases hS1 : storeObject tableId _ st with
            | error e => rw [hS1] at hStep; cases hStep
            | ok p =>
              obtain ⟨⟨⟩, st1⟩ := p
              rw [hS1] at hStep
              have hInv1 := storeObject_inertNonCNode_preserves_ipcInvariantFull st st1 tableId _
                hObjInv hInv (Or.inr (by rw [hT']; trivial)) (by trivial)
                (fun _ h => KernelObject.noConfusion h) hS1
              have hObjInv1 := storeObject_preserves_objects_invExt _ _ _ _ hObjInv hS1
              have hNe : inst.root ≠ tableId := by
                intro hEq; rw [hEq, hT'] at hR'; cases hR'
              have hR1 : st1.objects[inst.root]? = some (.vspaceRoot root) := by
                rw [storeObject_objects_ne _ _ _ _ _ hNe hObjInv hS1]; exact hR'
              exact storeObject_inertNonCNode_preserves_ipcInvariantFull
                (Architecture.recordPhysicalWrites st1 _) st' inst.root _
                hObjInv1 (ipcInvariantFull_recordPhysicalWrites hInv1)
                (Or.inr (by simp only [Architecture.recordPhysicalWrites_objects, hR1]; trivial))
                (by trivial) (fun _ h => KernelObject.noConfusion h) hStep
        · exact storeObject_inertNonCNode_preserves_ipcInvariantFull st st' tableId _
            hObjInv hInv (Or.inr (by rw [hT']; trivial)) (by trivial)
            (fun _ h => KernelObject.noConfusion h) hStep

/-- **A thread slot's copy preserves the IPC bundle**: the delete touches no IPC
state (`cspaceDeleteSlot_preserves_ipcInvariantFull`), the insert rewrites one
thread's space slot with an unbadged capability, which no conjunct reads, and
the edge writes links alone. -/
theorem threadSlotCopied_preserves_ipcInvariantFull {st : SystemState} {tid : SeLe4n.ThreadId}
    {t : TCB} (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hT : st.getTcb? tid = some t) (slot : SeLe4n.Slot) (srcCNode : SeLe4n.ObjId)
    (srcSlot : SeLe4n.Slot) (rights : AccessRightSet) :
    ipcInvariantFull (threadSlotCopied st tid slot srcCNode srcSlot rights) := by
  have hD := cspaceDeleteSlot_preserves_ipcInvariantFull st _ _ hObjInv hInv
    (copyIntoThreadSlot_delete hT slot)
  obtain ⟨⟨t', hT', -⟩, hI⟩ := threadSlotDeleted_tcb hObjInv hT slot
  rcases threadSlotCopied_cases st tid slot srcCNode srcSlot rights with ⟨-, e⟩ | ⟨cap, -, e⟩
  · rw [e]; exact hD
  · rw [e]
    refine cdtRecord_bundle_frame _ _ _ _ (SystemState.updateTcb_preserves_objects_invExt _ _ _ hI) ?_
    rw [SystemState.updateTcb_eq_of_some hT']
    exact insertObjects_tcbFieldUpdate_preserves_ipcInvariantFull _ tid t' _ hI hD
      ((SystemState.getTcb?_eq_some_iff _ tid t').mp hT') rfl rfl rfl rfl rfl rfl rfl rfl rfl
      (fun _ c _ h hB => by
        rcases TCB.spaceSlotCap_insertSpaceCap_back h with rfl | h'
        · simp at hB
        · exact h')

/-- A slot set from a filled source keeps the thread stored: its slot then
holds a capability, so the retire after the copy cannot take the thread. -/
theorem threadSlotSet_getTcb? (ec : Concurrency.CoreId) {st : SystemState}
    {tid : SeLe4n.ThreadId} {t : TCB} (hObjInv : st.objects.invExt)
    (hT : st.getTcb? tid = some t) {slot : SeLe4n.Slot} (hs : slot.toNat < 2)
    (srcCNode : SeLe4n.ObjId) (srcSlot : SeLe4n.Slot) (rights : AccessRightSet) {cap : Capability}
    (hL : SystemState.lookupSlotCap st { cnode := srcCNode, slot := srcSlot } = some cap) :
    ((threadSlotSet ec st tid slot srcCNode srcSlot rights).getTcb? tid).isSome := by
  obtain ⟨-, hI1⟩ := threadSlotCopied_tcb hObjInv hT slot srcCNode srcSlot rights
  obtain ⟨t1, hT1, hF⟩ := threadSlotCopied_slotFilled hObjInv hT hs rights hL
  unfold threadSlotSet
  dsimp only
  rw [retireFinalObject_getTcb?_of_slotCap _ _ _ _ hI1 hT1 hF]; rfl

/-- Review round (PR #887): and the object-store invariant. -/
theorem setThreadFaultHandlerOp_preserves_objects_invExt
    (st st' : SystemState) (vtid : SeLe4n.ValidThreadId) (cptr : SeLe4n.CPtr)
    (hObjInv : st.objects.invExt)
    (hStep : setThreadFaultHandlerOp st vtid cptr = .ok st') :
    st'.objects.invExt := by
  cases hT : st.getTcb? vtid.val with
  | none => simp [setThreadFaultHandlerOp, SystemState.getTcbWitnessed?_eq_none hT] at hStep
  | some tcb =>
      cases hR : resolveFaultHandlerCPtr st tcb cptr with
      | error e =>
          simp [setThreadFaultHandlerOp, SystemState.getTcbWitnessed?_eq_some hT, hR] at hStep
      | ok tgt =>
          rw [setThreadFaultHandlerOp_ok_eq st vtid cptr tcb tgt hT hR] at hStep
          cases hStep
          unfold installFaultHandler
          exact SystemState.rewriteObject_preserves_objects_invExt _ _ _ _ hObjInv

/-- Cancelling IPC blocking on a `.ready` victim is the identity — there is
nothing to cancel. -/
private theorem cancelIpcBlocking_ready_id
    (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hReady : tcb.ipcState = .ready) :
    Lifecycle.Suspend.cancelIpcBlocking st tid tcb = st := by
  unfold Lifecycle.Suspend.cancelIpcBlocking
  rw [hReady]

/-- **WS-RR RR8.12**: and so is the teardown with its reclaim completed — the
form the suspend pipeline's G2 now reads.

A quiescent victim is not `.blockedOnReply`, so the reclaim's trigger declines
and both of its scheduler steps are the identity; the bare teardown's own
`.ready` identity then finishes it. -/
private theorem cancelIpcBlockingReclaimed_ready_id
    (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hReady : tcb.ipcState = .ready) :
    cancelIpcBlockingReclaimed tid tcb st = st := by
  rw [cancelIpcBlockingReclaimed_of_no_donation tid tcb st
        (Lifecycle.Suspend.cancelledCallerDonation?_of_ready st tid tcb hReady),
    cancelIpcBlocking_ready_id st tid tcb hReady]

/-- Descheduling a thread on one core preserves the bundle: it writes only
run-queue links, which no conjunct reads. -/
theorem removeRunnableOnCore_preserves_ipcInvariantFull
    (st : SystemState) (tid : SeLe4n.ThreadId) (c : CoreId)
    (hInv : ipcInvariantFull st) :
    ipcInvariantFull (removeRunnableOnCore st tid c) :=
  ipcInvariantFull_of_objectsAgreeOffRunLinks
    (removeRunnableOnCore_objectsAgreeOffRunLinks st tid c) hInv

/-- Under the quiescent field shape the pending-state clear rewrites every
field to the value it already holds — pointwise inert. -/
private theorem clearPendingState_getElem_eq_of_quiescent
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hFields : ∀ tcbX : TCB, st.getTcb? tid = some tcbX →
      tcbX.pendingMessage = none ∧ tcbX.timeoutBudget = none ∧
      tcbX.queuePrev = none ∧ tcbX.queueNext = none ∧ tcbX.queuePPrev = none) :
    ∀ oid : SeLe4n.ObjId,
      (Lifecycle.Suspend.clearPendingState st tid).objects[oid]? = st.objects[oid]? := by
  intro oid
  unfold Lifecycle.Suspend.clearPendingState
  cases hLk : st.getTcb? tid with
  | none => rw [SystemState.updateTcb_eq_self_of_none hLk]
  | some tcb =>
      rw [SystemState.updateTcb_eq_of_some hLk]
      dsimp only []
      obtain ⟨h1, h2, h3, h4, h5⟩ := hFields tcb hLk
      have hSame : ({ tcb with pendingMessage := none, timeoutBudget := none, queuePrevCode := 0, queueNextCode := 0, queuePPrevCode := 0 } : TCB) = tcb := by
        cases tcb
        simp_all
      rw [hSame]
      have hPre : st.objects[tid.toObjId]? = some (.tcb tcb) :=
        (SystemState.getTcb?_eq_some_iff st tid tcb).mp hLk
      by_cases hK : oid = tid.toObjId
      · subst hK
        simp only [RHTable_getElem?_eq_get?]
        rw [RobinHood.RHTable.getElem?_insert_self st.objects tid.toObjId _ hObjInv]
        rw [← RHTable_getElem?_eq_get?]
        exact hPre.symm
      · simp only [RHTable_getElem?_eq_get?]
        exact RobinHood.RHTable.getElem?_insert_ne st.objects tid.toObjId oid _
          (by simp; exact fun h => hK h.symm) hObjInv

/-- The suspend-tail scheduling point: at most one reschedule handler run. -/
private theorem suspendRescheduleOnCore_preserves_ipcInvariantFull
    (st st' : SystemState) (home ec : CoreId) (wasCur localDeboosted : Bool)
    (sgi : Option (CoreId × Concurrency.SgiKind))
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hStep : Lifecycle.Suspend.suspendRescheduleOnCore st home ec wasCur localDeboosted = .ok (st', sgi)) :
    ipcInvariantFull st' := by
  unfold Lifecycle.Suspend.suspendRescheduleOnCore at hStep
  split at hStep
  · split at hStep
    · cases hRes : handleRescheduleSgiOnCore st ec with
      | ok st4 =>
          rw [hRes] at hStep
          cases hStep
          exact handleRescheduleSgiOnCore_preserves_ipcInvariantFull st ec st' hObjInv hInv hRes
      | error e => rw [hRes] at hStep; cases hStep
    · split at hStep
      · cases hRes : handleRescheduleSgiOnCore st ec with
        | ok st4 =>
            rw [hRes] at hStep
            cases hStep
            exact handleRescheduleSgiOnCore_preserves_ipcInvariantFull st ec st' hObjInv hInv hRes
        | error e => rw [hRes] at hStep; cases hStep
      · cases hStep
        exact hInv
  · split at hStep
    · cases hRes : handleRescheduleSgiOnCore st ec with
      | ok st4 =>
          rw [hRes] at hStep
          cases hStep
          exact handleRescheduleSgiOnCore_preserves_ipcInvariantFull st ec st' hObjInv hInv hRes
      | error e => rw [hRes] at hStep; cases hStep
    · cases hStep
      exact hInv

/-- The bound-donation cancel, read through a **view** of the thread: the
binding the cancel matches on is `tcbV`'s, while the TCB it rewrites is the
stored `tcb` (the cancel writes through `updateTcb`, never the view).  The
final-delete unbind passes the stored TCB with its owner code cleared, so a
`.donated` holder is unbound by the same transition as a `.bound` one
(seL4 `schedContext_unbindTCB` on a lent context).  SC clear, replenish drop,
index drop, victim unbind — the §11 unbind-direction rewrite under a
replenish-only scheduler change. -/
theorem cancelBoundDonationOnCore_view_preserves_ipcInvariantFull
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (tcb tcbV : TCB)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hStored : st.objects[tid.toObjId]? = some (.tcb tcb))
    (hBack : ∀ scId, tcbV.schedContextBinding = .bound scId → ∃ sc : SchedContext,
      st.objects[scId.toObjId]? = some (.schedContext sc) ∧ sc.boundThread = some tid)
    (hStep : cancelBoundDonationOnCore st tid tcbV = .ok st') :
    ipcInvariantFull st' := by
  unfold cancelBoundDonationOnCore at hStep
  cases hB : tcbV.schedContextBinding with
  | unbound => rw [hB] at hStep; cases hStep
  | donated scId owner => rw [hB] at hStep; cases hStep
  | bound scId =>
      rw [hB] at hStep
      dsimp only [] at hStep
      obtain ⟨sc, hScPre, hScBack⟩ := hBack scId hB
      have hScLk : st.getSchedContext? scId = some sc :=
        (SystemState.getSchedContext?_eq_some_iff st scId sc).mpr hScPre
      rw [SystemState.updateSchedContext_eq_of_some hScLk] at hStep
      have hNeTS : tid.toObjId ≠ scId.toObjId := by
        intro hEq
        rw [hEq, hScPre] at hStored
        cases hStored
      have hObjInv1 : (st.objects.insert scId.toObjId
          (KernelObject.schedContext { sc with boundThreadCode := 0, isActive := false, donationOrigin := none })).invExt :=
        RHTable_insert_preserves_invExt _ _ _ hObjInv
      -- The purge writes release links alone: the bundle reads the store
      -- off them, so it is read on the store without the purge.
      have hT2 : ({ st with objects := st.objects.insert scId.toObjId (KernelObject.schedContext { sc with boundThreadCode := 0, isActive := false, donationOrigin := none }) } : SystemState).getTcb? tid = some tcb := by
        refine (SystemState.getTcb?_eq_some_iff _ tid tcb).mpr ?_
        show (st.objects.insert scId.toObjId (KernelObject.schedContext { sc with boundThreadCode := 0, isActive := false, donationOrigin := none }))[tid.toObjId]? = some (.tcb tcb)
        simp only [RHTable_getElem?_eq_get?]
        rw [RobinHood.RHTable.getElem?_insert_ne st.objects scId.toObjId tid.toObjId _
          (by simp; exact fun h => hNeTS h.symm) hObjInv]
        rw [← RHTable_getElem?_eq_get?]
        exact hStored
      cases hStep
      refine markKeyChangeFrom_preserves_ipcInvariantFull st _ tid ?_
      refine ipcInvariantFull_of_objectsAgreeOffSchedulerLinks (.of_releaseLinks
        ((SchedContextOps.purgeReplenishment_agree _ scId).updateTcb
          (SchedContextOps.purgeReplenishment_objects_invExt _ scId hObjInv1) hObjInv1 tid _)) ?_
      rw [SystemState.updateTcb_eq_of_some hT2]
      dsimp only []
      refine ipcInvariantFull_of_schedBindingRewrite st _ tid scId tcb
        { tcb with scBindingScCode := 0, scBindingOwnerCode := 0 } sc
        { sc with boundThreadCode := 0, isActive := false, donationOrigin := none } hInv hStored ?_ hScPre ?_ ?_
        rfl rfl rfl rfl rfl rfl rfl rfl (Or.inr ⟨rfl, hScBack, rfl⟩)
      · show ((st.objects.insert scId.toObjId (KernelObject.schedContext { sc with boundThreadCode := 0, isActive := false, donationOrigin := none })).insert tid.toObjId (KernelObject.tcb { tcb with scBindingScCode := 0, scBindingOwnerCode := 0 }))[tid.toObjId]? = some (KernelObject.tcb { tcb with scBindingScCode := 0, scBindingOwnerCode := 0 })
        simp only [RHTable_getElem?_eq_get?]
        exact RobinHood.RHTable.getElem?_insert_self _ _ _ hObjInv1
      · show ((st.objects.insert scId.toObjId (KernelObject.schedContext { sc with boundThreadCode := 0, isActive := false, donationOrigin := none })).insert tid.toObjId (KernelObject.tcb { tcb with scBindingScCode := 0, scBindingOwnerCode := 0 }))[scId.toObjId]? = some (KernelObject.schedContext { sc with boundThreadCode := 0, isActive := false, donationOrigin := none })
        simp only [RHTable_getElem?_eq_get?]
        rw [RobinHood.RHTable.getElem?_insert_ne _ tid.toObjId scId.toObjId _
          (by simp; exact fun h => hNeTS h) hObjInv1]
        exact RobinHood.RHTable.getElem?_insert_self _ _ _ hObjInv
      · intro oid hNeT hNeS
        show ((st.objects.insert scId.toObjId (KernelObject.schedContext { sc with boundThreadCode := 0, isActive := false, donationOrigin := none })).insert tid.toObjId (KernelObject.tcb { tcb with scBindingScCode := 0, scBindingOwnerCode := 0 }))[oid]? = st.objects[oid]?
        simp only [RHTable_getElem?_eq_get?]
        rw [RobinHood.RHTable.getElem?_insert_ne _ tid.toObjId oid _
          (by simp; exact fun h => hNeT h.symm) hObjInv1]
        rw [RobinHood.RHTable.getElem?_insert_ne _ scId.toObjId oid _
          (by simp; exact fun h => hNeS h.symm) hObjInv]

/-- The bound-donation cancel on the stored TCB itself
(`cancelBoundDonationOnCore_view_preserves_ipcInvariantFull` with the view the
TCB). -/
theorem cancelBoundDonationOnCore_preserves_ipcInvariantFull
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hStored : st.objects[tid.toObjId]? = some (.tcb tcb))
    (hBack : ∀ scId, tcb.schedContextBinding = .bound scId → ∃ sc : SchedContext,
      st.objects[scId.toObjId]? = some (.schedContext sc) ∧ sc.boundThread = some tid)
    (hStep : cancelBoundDonationOnCore st tid tcb = .ok st') :
    ipcInvariantFull st' :=
  cancelBoundDonationOnCore_view_preserves_ipcInvariantFull st st' tid tcb tcb hObjInv
    hInv hStored hBack hStep

/-- The donated-donation cancel: the verified donation return plus the
replenishment migration. -/
private theorem cancelDonatedDonationOnCore_preserves_ipcInvariantFull
    (st st' : SystemState) (vtid : SeLe4n.ValidThreadId) (tcb : TCB)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hStored : st.getTcb? vtid.val = some tcb)
    -- **WS-OD OD4.4**: destroying a thread that holds a donation hands the
    -- context back through the reply-stack resolver; this is the obligation that
    -- resolution carries.
    (hStackValid : ∀ scId serverTid originalOwner,
        replyStackOuterCallerValid st scId serverTid originalOwner)
    (hStep : cancelDonatedDonationOnCore st vtid.val tcb = .ok st') :
    ipcInvariantFull st' := by
  obtain ⟨tval, hprop⟩ := vtid
  dsimp only [] at hStored hStep ⊢
  have hNotRes : tval.isReserved ≠ true := by
    intro hr
    apply hprop
    have hv : tval.val = 0 := by simpa [SeLe4n.ThreadId.isReserved] using hr
    cases tval
    simp_all [SeLe4n.ThreadId.sentinel]
  have hLk : lookupTcb st tval = some tcb := by
    unfold lookupTcb SystemState.getTcb?
    rw [if_neg hNotRes, (SystemState.getTcb?_eq_some_iff st tval tcb).mp hStored]
  unfold cancelDonatedDonationOnCore at hStep
  cases hB : tcb.schedContextBinding with
  | unbound => rw [hB] at hStep; cases hStep
  | bound scId => rw [hB] at hStep; cases hStep
  | donated scId owner =>
      rw [hB] at hStep
      dsimp only [] at hStep
      cases hCl : cleanupDonatedSchedContext st tval with
      | error e => rw [hCl] at hStep; cases hStep
      | ok st1 =>
          rw [hCl] at hStep
          dsimp only [] at hStep
          cases hStep
          refine migrateSchedContextReplenishment_preserves_ipcInvariantFull st1 _ _ _ ?_
          unfold cleanupDonatedSchedContext at hCl
          simp only [hLk, hB] at hCl
          obtain ⟨n, hRes, hPop⟩ := returnDonatedSchedContextResolved_ok_decompose hCl
          exact returnDonatedSchedContext_preserves_ipcInvariantFull st st1 ⟨tval, hprop⟩
            scId owner hObjInv hInv
            (by unfold replyDonationReturn?; rw [hLk]; simp [hB])
            n (donationReturnOuterValid_of_stackValid (hStackValid scId tval owner) hRes) hPop

/-- The bound-donation cancel touches only the victim's binding — every other
bundle-read TCB field survives. -/
private theorem cancelBoundDonationOnCore_victim_shape
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hObjInv : st.objects.invExt)
    (hStored : st.objects[tid.toObjId]? = some (.tcb tcb))
    (hStep : cancelBoundDonationOnCore st tid tcb = .ok st') :
    ∀ tcbX : TCB, st'.getTcb? tid = some tcbX →
      tcbX.ipcState = tcb.ipcState ∧ tcbX.pendingMessage = tcb.pendingMessage ∧
      tcbX.timeoutBudget = tcb.timeoutBudget ∧ tcbX.queuePrev = tcb.queuePrev ∧
      tcbX.queueNext = tcb.queueNext ∧ tcbX.queuePPrev = tcb.queuePPrev := by
  unfold cancelBoundDonationOnCore at hStep
  cases hB : tcb.schedContextBinding with
  | unbound => rw [hB] at hStep; cases hStep
  | donated scId owner => rw [hB] at hStep; cases hStep
  | bound scId =>
      rw [hB] at hStep
      dsimp only [] at hStep
      cases hStep
      intro tcbX hX
      simp only [markKeyChangeFrom_getTcb?] at hX
      have hI1 := SystemState.updateSchedContext_preserves_objects_invExt st scId
        (fun sc => { sc with boundThreadCode := 0, isActive := false, donationOrigin := none }) hObjInv
      rw [SystemState.updateTcb_getTcb?_self _ _ _
          (SchedContextOps.purgeReplenishment_objects_invExt _ scId hI1),
        SchedContextOps.purgeReplenishment_getTcb?, SystemState.updateSchedContext_getTcb? _ _ _ hObjInv,
        (SystemState.getTcb?_eq_some_iff st tid tcb).mpr hStored] at hX
      cases hX
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The donation return churns only bindings — the server's other bundle-read
fields survive its three stores. -/
private theorem returnDonatedSchedContext_victim_shape
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (owner : SeLe4n.ThreadId) (tcb : TCB)
    (hObjInv : st.objects.invExt)
    (hStored : st.objects[tid.toObjId]? = some (.tcb tcb))
    (newOwner? : Option SeLe4n.ThreadId)
    (hStep : returnDonatedSchedContext st tid scId owner newOwner? = .ok st') :
    ∀ tcbX : TCB, st'.getTcb? tid = some tcbX →
      tcbX.ipcState = tcb.ipcState ∧ tcbX.pendingMessage = tcb.pendingMessage ∧
      tcbX.timeoutBudget = tcb.timeoutBudget ∧ tcbX.queuePrev = tcb.queuePrev ∧
      tcbX.queueNext = tcb.queueNext ∧ tcbX.queuePPrev = tcb.queuePPrev := by
  -- WS-OD OD3.2: the shared TCB rewrite — one field moves, the rest agree by
  -- `rfl` on the record update, so the pop's fourth store needs no new case.
  intro tcbX hX
  obtain ⟨t', hPost, _, _, hEq⟩ :=
    returnDonatedSchedContext_tcb_rewrite st st' tid scId owner hObjInv newOwner? hStep
      tid.toObjId tcb hStored
  rw [SystemState.getTcb?_eq_some_iff] at hX
  rw [hPost] at hX
  obtain rfl : t' = tcbX := KernelObject.tcb.inj (Option.some.inj hX)
  subst hEq
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem cancelDonatedDonationOnCore_victim_shape
    (st st' : SystemState) (vtid : SeLe4n.ValidThreadId) (tcb : TCB)
    (hObjInv : st.objects.invExt)
    (hStored : st.getTcb? vtid.val = some tcb)
    (hStep : cancelDonatedDonationOnCore st vtid.val tcb = .ok st') :
    ∀ tcbX : TCB, st'.getTcb? vtid.val = some tcbX →
      tcbX.ipcState = tcb.ipcState ∧ tcbX.pendingMessage = tcb.pendingMessage ∧
      tcbX.timeoutBudget = tcb.timeoutBudget ∧ tcbX.queuePrev = tcb.queuePrev ∧
      tcbX.queueNext = tcb.queueNext ∧ tcbX.queuePPrev = tcb.queuePPrev := by
  obtain ⟨tval, hprop⟩ := vtid
  dsimp only [] at hStored hStep ⊢
  have hNotRes : tval.isReserved ≠ true := by
    intro hr
    apply hprop
    have hv : tval.val = 0 := by simpa [SeLe4n.ThreadId.isReserved] using hr
    cases tval
    simp_all [SeLe4n.ThreadId.sentinel]
  have hLk : lookupTcb st tval = some tcb := by
    unfold lookupTcb SystemState.getTcb?
    rw [if_neg hNotRes, (SystemState.getTcb?_eq_some_iff st tval tcb).mp hStored]
  unfold cancelDonatedDonationOnCore at hStep
  cases hB : tcb.schedContextBinding with
  | unbound => rw [hB] at hStep; cases hStep
  | bound scId => rw [hB] at hStep; cases hStep
  | donated scId owner =>
      rw [hB] at hStep
      dsimp only [] at hStep
      cases hCl : cleanupDonatedSchedContext st tval with
      | error e => rw [hCl] at hStep; cases hStep
      | ok st1 =>
          rw [hCl] at hStep
          dsimp only [] at hStep
          cases hStep
          intro tcbX hX
          have hX1 : st1.getTcb? tval = some tcbX := by
            rw [← (migrateSchedContextReplenishment_agree _ _ _ _).getTcb?]; exact hX
          unfold cleanupDonatedSchedContext at hCl
          simp only [hLk, hB] at hCl
          obtain ⟨n, _, hPop⟩ := returnDonatedSchedContextResolved_ok_decompose hCl
          exact returnDonatedSchedContext_victim_shape st st1 tval scId owner tcb hObjInv
            ((SystemState.getTcb?_eq_some_iff st tval tcb).mp hStored) n hPop tcbX hX1

/-- The suspend tail's clear-and-deactivate stage: pending-state clear
(pointwise inert on a quiescent victim) then the `threadState := .Inactive`
store (a bundle-unread field). -/
private theorem suspendClearStore_preserves_ipcInvariantFull
    (stR2 : SystemState) (tid : SeLe4n.ThreadId)
    (hObjInvR : stR2.objects.invExt)
    (hShapeR : ∀ tcbX : TCB, stR2.getTcb? tid = some tcbX →
      tcbX.ipcState = .ready ∧ tcbX.pendingMessage = none ∧ tcbX.timeoutBudget = none ∧
      tcbX.queuePrev = none ∧ tcbX.queueNext = none ∧ tcbX.queuePPrev = none)
    (hInvR : ipcInvariantFull stR2) :
    ipcInvariantFull ((Lifecycle.Suspend.clearPendingState stR2 tid).updateTcb tid fun t => { t with threadState := .Inactive }) ∧
    ((Lifecycle.Suspend.clearPendingState stR2 tid).updateTcb tid fun t => { t with threadState := .Inactive }).objects.invExt := by
  have hFields : ∀ tcbX : TCB, stR2.getTcb? tid = some tcbX →
      tcbX.pendingMessage = none ∧ tcbX.timeoutBudget = none ∧
      tcbX.queuePrev = none ∧ tcbX.queueNext = none ∧ tcbX.queuePPrev = none :=
    fun tcbX hX => (hShapeR tcbX hX).2
  have hEq := clearPendingState_getElem_eq_of_quiescent stR2 tid hObjInvR hFields
  have hObjInvC : (Lifecycle.Suspend.clearPendingState stR2 tid).objects.invExt := by
    unfold Lifecycle.Suspend.clearPendingState
    exact SystemState.updateTcb_preserves_objects_invExt _ _ _ hObjInvR
  have hInvC : ipcInvariantFull (Lifecycle.Suspend.clearPendingState stR2 tid) :=
    ipcInvariantFull_of_getElem_eq hEq hInvR
  cases hLkC : (Lifecycle.Suspend.clearPendingState stR2 tid).getTcb? tid with
  | none => rw [SystemState.updateTcb_eq_self_of_none hLkC]; exact ⟨hInvC, hObjInvC⟩
  | some tcb2 =>
      rw [SystemState.updateTcb_eq_of_some hLkC]
      constructor
      · exact insertObjects_tcbFieldUpdate_preserves_ipcInvariantFull
          (Lifecycle.Suspend.clearPendingState stR2 tid) tid tcb2
          { tcb2 with threadState := .Inactive } hObjInvC hInvC
          ((SystemState.getTcb?_eq_some_iff _ tid tcb2).mp hLkC)
          rfl rfl rfl rfl rfl rfl rfl rfl rfl
      · exact RHTable_insert_preserves_invExt _ _ _ hObjInvC

/-- WS-RR RR8.6: descheduling a thread at a pre-resolved placement preserves
the bundle — the one-core removal at `some c`, nothing at `none`. -/
theorem descheduleAt_preserves_ipcInvariantFull
    (st : SystemState) (tid : SeLe4n.ThreadId) (placed : Option CoreId)
    (hInv : ipcInvariantFull st) :
    ipcInvariantFull (descheduleAt st tid placed) := by
  unfold descheduleAt
  cases placed with
  | none => exact hInv
  | some c => exact removeRunnableOnCore_preserves_ipcInvariantFull st tid c hInv

/-- The suspend tail's deschedule stage: the placement removal of a `.ready`
victim (WS-RR RR8.6 — one removal at the pre-resolved placement, where the
home removal and the running-core removal used to stand), then the
clear-and-deactivate stage. -/
private theorem suspendDescheduleTail_shape
    (stD : SystemState) (tid : SeLe4n.ThreadId) (placed : Option CoreId)
    (hObjInvD : stD.objects.invExt)
    (hShape : ∀ tcbX : TCB, stD.getTcb? tid = some tcbX →
      tcbX.ipcState = .ready ∧ tcbX.pendingMessage = none ∧ tcbX.timeoutBudget = none ∧
      tcbX.queuePrev = none ∧ tcbX.queueNext = none ∧ tcbX.queuePPrev = none)
    (hInvD : ipcInvariantFull stD) :
    ipcInvariantFull (descheduleAt stD tid placed) ∧
    (descheduleAt stD tid placed).objects.invExt ∧
    (∀ tcbX : TCB, (descheduleAt stD tid placed).getTcb? tid = some tcbX →
      tcbX.ipcState = .ready ∧ tcbX.pendingMessage = none ∧ tcbX.timeoutBudget = none ∧
      tcbX.queuePrev = none ∧ tcbX.queueNext = none ∧ tcbX.queuePPrev = none) := by
  refine ⟨descheduleAt_preserves_ipcInvariantFull stD tid placed hInvD, ?_, ?_⟩
  · unfold descheduleAt
    cases placed with
    | none => exact hObjInvD
    | some c => exact removeRunnableOnCore_objects_invExt stD tid c hObjInvD
  · intro tcbX hX
    unfold descheduleAt at hX
    cases placed with
    | none => exact hShape tcbX hX
    | some c =>
      have hX' := (SystemState.getTcb?_eq_some_iff _ tid tcbX).mp hX
      clear hX
      run_links_back (removeRunnableOnCore_objectsAgreeOffRunLinks stD tid c) at tcbX hX'
      exact hShape tcbX ((SystemState.getTcb?_eq_some_iff stD tid tcbX).mpr hX')

/-- WS-ZA ZA6.6: the yield-link cancel preserves the whole bundle: it rewrites a
context's yield-from code, which leaves its bound thread, and a thread's
yield-to code, which no conjunct reads. -/
theorem cancelYieldTo_preserves_ipcInvariantFull (st : SystemState) (tid : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st) :
    ipcInvariantFull (cancelYieldTo st tid) := by
  unfold cancelYieldTo
  split
  · rename_i t hT
    split
    · exact hInv
    · rename_i k _
      have hInv1 : ipcInvariantFull (st.updateSchedContext ⟨k⟩ SchedContext.yieldCleared) := by
        cases hS : st.getSchedContext? ⟨k⟩ with
        | none => rw [SystemState.updateSchedContext_eq_self_of_none hS]; exact hInv
        | some sc =>
          rw [SystemState.updateSchedContext_eq_of_some hS]
          exact insertObjects_schedContextContentUpdate_preserves_ipcInvariantFull st ⟨k⟩ sc _
            hObjInv hInv ((SystemState.getSchedContext?_eq_some_iff _ _ _).mp hS) rfl
      have hO1 := SystemState.updateSchedContext_preserves_objects_invExt st ⟨k⟩
        SchedContext.yieldCleared hObjInv
      have hT1 : (st.updateSchedContext ⟨k⟩ SchedContext.yieldCleared).getTcb? tid = some t := by
        rw [SystemState.updateSchedContext_getTcb? _ _ _ hObjInv]; exact hT
      rw [SystemState.updateTcb_eq_of_some hT1]
      exact insertObjects_tcbFieldUpdate_preserves_ipcInvariantFull _ tid t _ hO1 hInv1
        ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT1) rfl rfl rfl rfl rfl rfl rfl rfl rfl
  · exact hInv

/-- A thread rewritten in its yield-to code and registers alone keeps the bundle:
neither is a field the bundle reads. -/
theorem updateTcb_yieldWrite_preserves_ipcInvariantFull (st : SystemState)
    (tid : SeLe4n.ThreadId) (f : TCB → TCB) (hObjInv : st.objects.invExt)
    (hInv : ipcInvariantFull st)
    (hf : ∀ x,
      f x = { x with yieldToCode := (f x).yieldToCode, registerContext := (f x).registerContext }) :
    ipcInvariantFull (st.updateTcb tid f) := by
  cases hT : st.getTcb? tid with
  | none => rw [SystemState.updateTcb_eq_self_of_none hT]; exact hInv
  | some t =>
    rw [SystemState.updateTcb_eq_of_some hT]
    have e := hf t
    exact insertObjects_tcbFieldUpdate_preserves_ipcInvariantFull _ tid t _ hObjInv hInv
      ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT) (by rw [e] <;> rfl) (by rw [e] <;> rfl) (by rw [e] <;> rfl)
      (by rw [e] <;> rfl) (by rw [e] <;> rfl) (by rw [e] <;> rfl) (by rw [e] <;> rfl) (by rw [e] <;> rfl) (by rw [e] <;> rfl)
      (by intro sl c b h _; rw [e] at h; exact h) (by rw [e] <;> rfl)

/-- A context rewritten keeping its bound thread keeps the bundle. -/
theorem updateSchedContext_boundKept_preserves_ipcInvariantFull (st : SystemState)
    (s : SeLe4n.SchedContextId) (f : SchedContext → SchedContext) (hObjInv : st.objects.invExt)
    (hInv : ipcInvariantFull st) (hf : ∀ x, (f x).boundThread = x.boundThread) :
    ipcInvariantFull (st.updateSchedContext s f) := by
  cases hS : st.getSchedContext? s with
  | none => rw [SystemState.updateSchedContext_eq_self_of_none hS]; exact hInv
  | some sc =>
    rw [SystemState.updateSchedContext_eq_of_some hS]
    exact insertObjects_schedContextContentUpdate_preserves_ipcInvariantFull st s sc _
      hObjInv hInv ((SystemState.getSchedContext?_eq_some_iff _ _ _).mp hS) (hf sc)

/-- `setConsumed` keeps the bundle: a count and two registers. -/
theorem setConsumed_preserves_ipcInvariantFull (st : SystemState) (s : SeLe4n.SchedContextId)
    (t : SeLe4n.ThreadId) (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st) :
    ipcInvariantFull (setConsumed st s t) := by
  unfold setConsumed
  split
  · exact updateTcb_yieldWrite_preserves_ipcInvariantFull _ t _
      (SystemState.updateSchedContext_preserves_objects_invExt _ _ _ hObjInv)
      (updateSchedContext_boundKept_preserves_ipcInvariantFull _ _ _ hObjInv hInv
        (fun _ => rfl)) (by intro; rfl)
  · exact hInv

/-- The context's end of the cancel keeps the bundle. -/
theorem cancelYieldFrom_preserves_ipcInvariantFull (st : SystemState)
    (s : SeLe4n.SchedContextId) (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st) :
    ipcInvariantFull (cancelYieldFrom st s) := by
  unfold cancelYieldFrom
  split
  · split
    · exact hInv
    · exact updateTcb_yieldWrite_preserves_ipcInvariantFull _ _ _
        (SystemState.updateSchedContext_preserves_objects_invExt _ _ _ hObjInv)
        (updateSchedContext_boundKept_preserves_ipcInvariantFull _ _ _ hObjInv hInv
          (fun _ => rfl)) (by intro; rfl)
  · exact hInv

/-- The completion of a context's recorded yield keeps the bundle. -/
theorem completeYieldFrom_preserves_ipcInvariantFull (st : SystemState)
    (s : SeLe4n.SchedContextId) (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st) :
    ipcInvariantFull (completeYieldFrom st s) := by
  unfold completeYieldFrom
  split
  · split
    · exact hInv
    · exact cancelYieldFrom_preserves_ipcInvariantFull _ _
        (SystemState.setConsumed_preserves_objects_invExt _ _ _ hObjInv)
        (setConsumed_preserves_ipcInvariantFull _ _ _ hObjInv hInv)
  · exact hInv

/-- `.tcbSuspend` (dispatch arm): the whole per-core suspension pipeline —
cancel (inert on a quiescent victim), PIP revert (empty for a `.ready`
victim), donation cancel (all three binding arms), the placement deschedule,
pending-state clear, deactivation store, and the local scheduling point —
preserves `ipcInvariantFull`.

The victim-quiescence pack confines the bundle to victims not blocked in an
IPC queue (the post-suspend shape, and the shape the runtime cancel guards
leave every other victim in); extending the bundle over the queue-unlink
cancellation composite is registered follow-up work on the SM6.E surface. -/
theorem suspendThreadOnCore_preserves_ipcInvariantFull
    (st st' : SystemState) (vtid : SeLe4n.ValidThreadId) (ec : CoreId)
    (sgi : Option (CoreId × Concurrency.SgiKind))
    (hObjInv : st.objects.invExt)
    (hQ : threadIpcFieldsQuiescent st vtid.val)
    (hBidir : schedContextBindingBidirectional st)
    (hInv : ipcInvariantFull st)
    -- **WS-OD OD4.4**: suspending a thread that holds a donation hands the
    -- context back through the reply-stack resolver; this is the obligation that
    -- resolution carries.
    (hStackValid : ∀ scId serverTid originalOwner,
        replyStackOuterCallerValid st scId serverTid originalOwner)
    (hStep : Lifecycle.Suspend.suspendThreadOnCore st vtid ec = .ok (st', sgi)) :
    ipcInvariantFull st' := by
  unfold Lifecycle.Suspend.suspendThreadOnCore at hStep
  dsimp only [] at hStep
  cases hLk : st.getTcb? vtid.val with
  | none => rw [hLk] at hStep; cases hStep
  | some tcb =>
      rw [hLk] at hStep
      dsimp only [] at hStep
      split at hStep
      · cases hStep
      · have hReady := hQ.ready tcb hLk
        have hPre := (SystemState.getTcb?_eq_some_iff st vtid.val tcb).mp hLk
        rw [cancelIpcBlockingReclaimed_ready_id st vtid.val tcb hReady] at hStep
        have hBS : PriorityInheritance.blockingServer st vtid.val = none := by
          -- `blockingServer` reads `getTcb?`, which is what `hLk` already says;
          -- the raw restatement `hPre` is no longer the vocabulary it needs.
          unfold PriorityInheritance.blockingServer
          simp [hLk, hReady]
        rw [hBS] at hStep
        dsimp only [] at hStep
        rw [hLk] at hStep
        simp only [Option.getD_some] at hStep
        unfold Lifecycle.Suspend.clearPendingStateValid at hStep
        have hShapeOf : ∀ (stD : SystemState),
            (∀ tcbX : TCB, stD.getTcb? vtid.val = some tcbX →
              tcbX.ipcState = tcb.ipcState ∧ tcbX.pendingMessage = tcb.pendingMessage ∧
              tcbX.timeoutBudget = tcb.timeoutBudget ∧ tcbX.queuePrev = tcb.queuePrev ∧
              tcbX.queueNext = tcb.queueNext ∧ tcbX.queuePPrev = tcb.queuePPrev) →
            (∀ tcbX : TCB, stD.getTcb? vtid.val = some tcbX →
              tcbX.ipcState = .ready ∧ tcbX.pendingMessage = none ∧
              tcbX.timeoutBudget = none ∧ tcbX.queuePrev = none ∧
              tcbX.queueNext = none ∧ tcbX.queuePPrev = none) := by
          intro stD hSh tcbX hX
          obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hSh tcbX hX
          exact ⟨h1.trans hReady, h2.trans (hQ.noPendingMsg tcb hLk),
            h3.trans (hQ.noBudget tcb hLk), h4.trans (hQ.noPrev tcb hLk),
            h5.trans (hQ.noNext tcb hLk), h6.trans (hQ.noPPrev tcb hLk)⟩
        have hTail : ∀ (stD : SystemState),
            stD.objects.invExt → ipcInvariantFull stD →
            (∀ tcbX : TCB, stD.getTcb? vtid.val = some tcbX →
              tcbX.ipcState = .ready ∧ tcbX.pendingMessage = none ∧
              tcbX.timeoutBudget = none ∧ tcbX.queuePrev = none ∧
              tcbX.queueNext = none ∧ tcbX.queuePPrev = none) →
            ∀ (stR2 : SystemState), stR2.objects.invExt → ipcInvariantFull stR2 →
            (∀ tcbX : TCB, stR2.getTcb? vtid.val = some tcbX →
              tcbX.ipcState = .ready ∧ tcbX.pendingMessage = none ∧
              tcbX.timeoutBudget = none ∧ tcbX.queuePrev = none ∧
              tcbX.queueNext = none ∧ tcbX.queuePPrev = none) →
            ∀ (c2 ecX : CoreId) (wc ld : Bool) (stO : SystemState)
              (sgiO : Option (CoreId × Concurrency.SgiKind)),
            Lifecycle.Suspend.suspendRescheduleOnCore
              (cancelYieldTo ((Lifecycle.Suspend.clearPendingState stR2 vtid.val).updateTcb vtid.val
                fun t => { t with threadState := .Inactive }) vtid.val)
              c2 ecX wc ld = .ok (stO, sgiO) →
            ipcInvariantFull stO := by
          intro stD _ _ _ stR2 hObjInvR hInvR hShapeR c2 ecX wc ld stO sgiO hStepO
          obtain ⟨hInvI, hObjInvI⟩ :=
            suspendClearStore_preserves_ipcInvariantFull stR2 vtid.val hObjInvR hShapeR hInvR
          exact suspendRescheduleOnCore_preserves_ipcInvariantFull _ stO c2 ecX wc ld sgiO
            (SystemState.cancelYieldTo_preserves_objects_invExt _ _ hObjInvI)
            (cancelYieldTo_preserves_ipcInvariantFull _ _ hObjInvI hInvI) hStepO
        cases hB : tcb.schedContextBinding with
        | unbound =>
            simp only [hB] at hStep
            have hShapeD : ∀ tcbX : TCB, st.getTcb? vtid.val = some tcbX →
                tcbX.ipcState = .ready ∧ tcbX.pendingMessage = none ∧
                tcbX.timeoutBudget = none ∧ tcbX.queuePrev = none ∧
                tcbX.queueNext = none ∧ tcbX.queuePPrev = none :=
              hShapeOf st (fun tcbX hX => by
                rw [hLk] at hX
                obtain rfl : tcb = tcbX := Option.some.inj hX
                exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
            obtain ⟨hInv2, hObjInv2, hShape2⟩ := suspendDescheduleTail_shape st vtid.val
              (placedCoreOf? st vtid.val) hObjInv hShapeD hInv
            exact hTail st hObjInv hInv hShapeD _ hObjInv2 hInv2 hShape2
              _ ec _ _ st' sgi hStep
        | bound scId =>
            simp only [hB] at hStep
            cases hDon : cancelBoundDonationOnCore st vtid.val tcb
                with
            | error e => rw [hDon] at hStep; cases hStep
            | ok stD =>
                rw [hDon] at hStep
                dsimp only [] at hStep
                have hInvD := cancelBoundDonationOnCore_preserves_ipcInvariantFull st stD
                  vtid.val tcb hObjInv hInv hPre
                  (fun s hb => hBidir _ tcb s hPre (by rw [hb]; rfl)) hDon
                have hObjInvD := cancelBoundDonationOnCore_preserves_objects_invExt st stD
                  vtid.val tcb hObjInv
                  hDon
                have hShapeD := hShapeOf stD
                  (cancelBoundDonationOnCore_victim_shape st stD vtid.val tcb
                    hObjInv hPre
                    hDon)
                obtain ⟨hInv2, hObjInv2, hShape2⟩ := suspendDescheduleTail_shape stD
                  vtid.val (placedCoreOf? st vtid.val) hObjInvD hShapeD hInvD
                exact hTail stD hObjInvD hInvD hShapeD _ hObjInv2 hInv2 hShape2
                  _ ec _ _ st' sgi hStep
        | donated scId owner =>
            simp only [hB] at hStep
            cases hDon : cancelDonatedDonationOnCore st vtid.val tcb with
            | error e => rw [hDon] at hStep; cases hStep
            | ok stD =>
                rw [hDon] at hStep
                dsimp only [] at hStep
                have hInvD := cancelDonatedDonationOnCore_preserves_ipcInvariantFull st stD
                  vtid tcb hObjInv hInv hLk hStackValid hDon
                have hObjInvD := cancelDonatedDonationOnCore_preserves_objects_invExt st stD
                  vtid.val tcb hObjInv hDon
                have hShapeD := hShapeOf stD
                  (cancelDonatedDonationOnCore_victim_shape st stD vtid tcb hObjInv hLk
                    hDon)

                obtain ⟨hInv2, hObjInv2, hShape2⟩ := suspendDescheduleTail_shape stD
                  vtid.val (placedCoreOf? st vtid.val) hObjInvD hShapeD hInvD
                exact hTail stD hObjInvD hInvD hShapeD _ hObjInv2 hInv2 hShape2
                  _ ec _ _ st' sgi hStep

-- ============================================================================
-- §16  Return-frame staging composites (`Architecture.stage*`)
-- ============================================================================

/-- **WS-BP BP7.8**: and it carries no chain data. -/
theorem recordPhysicalWrites_donationChainFrame (st st' : SystemState)
    (ws : List Architecture.PhysicalWrite) (h : donationChainFrame st st') :
    donationChainFrame st (Architecture.recordPhysicalWrites st' ws) :=
  ⟨h.replyLinks, h.stackHeads, h.callerKept⟩

/-- Delivery staging is `writeReturnFrameToTcb` then a ledger record, or the identity. -/
theorem stageDeliveredMessage_preserves_ipcInvariantFull
    (st : SystemState) (tid : SeLe4n.ThreadId) (installedCaps : Nat)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st) :
    ipcInvariantFull (Architecture.stageDeliveredMessage st tid installedCaps) := by
  unfold Architecture.stageDeliveredMessage
  cases hLk : st.getTcb? tid with
  | none => exact hInv
  | some tcb =>
      dsimp only []
      split
      · rename_i hReadyT
        cases tcb.pendingMessage with
        | none => exact hInv
        | some msg =>
            exact ipcInvariantFull_recordPhysicalWrites
              (writeDeliveredFrameToTcb_preserves_ipcInvariantFull st tid _ hObjInv
                (fun t ht => by rw [hLk] at ht; cases ht; exact hReadyT) hInv)
      · exact hInv

/-- Woken-delivery staging: `stageDeliveredMessage` on the woken thread. -/
theorem stageWokenDelivery_preserves_ipcInvariantFull
    (st : SystemState) (woken? : Option SeLe4n.ThreadId) (installedCaps : Nat)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st) :
    ipcInvariantFull (Architecture.stageWokenDelivery st woken? installedCaps) := by
  cases woken? with
  | none => exact hInv
  | some tid =>
      rw [Architecture.stageWokenDelivery_some]
      exact stageDeliveredMessage_preserves_ipcInvariantFull st tid installedCaps hObjInv hInv

/-- Review round (PR #887): the delivered-message staging is a single
`writeReturnFrameToTcb` insert or the identity, so it preserves the
object-store invariant. -/
theorem stageDeliveredMessage_preserves_objects_invExt
    (st : SystemState) (tid : SeLe4n.ThreadId) (installedCaps : Nat)
    (hObjInv : st.objects.invExt) :
    (Architecture.stageDeliveredMessage st tid installedCaps).objects.invExt := by
  unfold Architecture.stageDeliveredMessage
  cases st.getTcb? tid with
  | none => exact hObjInv
  | some tcb =>
      dsimp only []
      split
      · cases tcb.pendingMessage with
        | none => exact hObjInv
        | some msg => exact writeDeliveredFrameToTcb_preserves_objects_invExt st tid _ hObjInv
      · exact hObjInv

/-- Review round (PR #887): and so does the woken-delivery wrapper. -/
theorem stageWokenDelivery_preserves_objects_invExt
    (st : SystemState) (woken? : Option SeLe4n.ThreadId) (installedCaps : Nat)
    (hObjInv : st.objects.invExt) :
    (Architecture.stageWokenDelivery st woken? installedCaps).objects.invExt := by
  cases woken? with
  | none => exact hObjInv
  | some tid =>
      rw [Architecture.stageWokenDelivery_some]
      exact stageDeliveredMessage_preserves_objects_invExt st tid installedCaps hObjInv

/-- Send-completion staging: the unit success frame or the identity. -/
theorem stageWokenSendCompletion_preserves_ipcInvariantFull
    (st : SystemState) (woken? : Option SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st) :
    ipcInvariantFull (Architecture.stageWokenSendCompletion st woken?) := by
  unfold Architecture.stageWokenSendCompletion
  cases woken? with
  | none => exact hInv
  | some tid =>
      dsimp only []
      cases st.getTcb? tid with
      | none => exact hInv
      | some tcb =>
          dsimp only []
          split
          · exact writeReturnFrameToTcb_preserves_ipcInvariantFull st tid _ hObjInv hInv
          · exact hInv

/-- Staging never disturbs the object-store invariant: every arm is one TCB
insert or the identity. -/
theorem stageDeliveredMessage_objects_invExt
    (st : SystemState) (tid : SeLe4n.ThreadId) (installedCaps : Nat)
    (hObjInv : st.objects.invExt) :
    (Architecture.stageDeliveredMessage st tid installedCaps).objects.invExt := by
  unfold Architecture.stageDeliveredMessage
  cases hLk : st.getTcb? tid with
  | none => exact hObjInv
  | some tcb =>
      dsimp only []
      split
      · cases tcb.pendingMessage with
        | none => exact hObjInv
        | some msg =>
            exact writeDeliveredFrameToTcb_preserves_objects_invExt st tid _ hObjInv
      · exact hObjInv

theorem stageWokenSendCompletion_objects_invExt
    (st : SystemState) (woken? : Option SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt) :
    (Architecture.stageWokenSendCompletion st woken?).objects.invExt := by
  unfold Architecture.stageWokenSendCompletion
  cases woken? with
  | none => exact hObjInv
  | some tid =>
      dsimp only []
      cases st.getTcb? tid with
      | none => exact hObjInv
      | some tcb =>
          dsimp only []
          split
          · exact writeReturnFrameToTcb_preserves_objects_invExt st tid _ hObjInv
          · exact hObjInv

/-- **WS-RM (`v0.35.6`)**: a return-frame writeback carries no chain data.  Its
one write is a `.tcb` at a key that already held one (`getTcb?` is what selects
the arm), so no Reply and no SchedContext is created, destroyed or rewritten. -/
theorem writeReturnFrameToTcb_donationChainFrame
    (st : SystemState) (tid : SeLe4n.ThreadId) (frame : Architecture.SyscallReturnFrame)
    (hObjInv : st.objects.invExt) :
    donationChainFrame st (Architecture.writeReturnFrameToTcb st tid frame) := by
  cases hLk : st.getTcb? tid with
  | none =>
      rw [Architecture.writeReturnFrameToTcb_id_when_not_tcb st tid frame hLk]
      exact donationChainFrame.refl st
  | some tcb =>
      unfold Architecture.writeReturnFrameToTcb
      rw [SystemState.updateTcb_eq_of_some hLk]
      exact donationChainFrame_of_objects_insert hObjInv
        (by rw [(SystemState.getTcb?_eq_some_iff st tid tcb).mp hLk]; rfl)
        (by rw [(SystemState.getTcb?_eq_some_iff st tid tcb).mp hLk]; rfl)
        (fun _ h => by cases h)

/-- **WS-ZA ZA4.7**: and so does the delivery write, a `.tcb` over a `.tcb`. -/
theorem writeDeliveredFrameToTcb_donationChainFrame
    (st : SystemState) (tid : SeLe4n.ThreadId) (frame : Architecture.SyscallReturnFrame)
    (hObjInv : st.objects.invExt) :
    donationChainFrame st (Architecture.writeDeliveredFrameToTcb st tid frame) := by
  cases hLk : st.getTcb? tid with
  | none =>
      unfold Architecture.writeDeliveredFrameToTcb
      rw [SystemState.updateTcb_eq_self_of_none hLk]
      exact donationChainFrame.refl st
  | some tcb =>
      unfold Architecture.writeDeliveredFrameToTcb
      rw [SystemState.updateTcb_eq_of_some hLk]
      exact donationChainFrame_of_objects_insert hObjInv
        (by rw [(SystemState.getTcb?_eq_some_iff st tid tcb).mp hLk]; rfl)
        (by rw [(SystemState.getTcb?_eq_some_iff st tid tcb).mp hLk]; rfl)
        (fun _ h => by cases h)

/-- **WS-RM (`v0.35.6`)**: and so does delivery staging — every arm is that
writeback or the identity. -/
theorem stageDeliveredMessage_donationChainFrame
    (st : SystemState) (tid : SeLe4n.ThreadId) (installedCaps : Nat)
    (hObjInv : st.objects.invExt) :
    donationChainFrame st (Architecture.stageDeliveredMessage st tid installedCaps) := by
  unfold Architecture.stageDeliveredMessage
  cases hLk : st.getTcb? tid with
  | none => simp only []; exact donationChainFrame.refl st
  | some tcb =>
      simp only []
      split
      · cases hPm : tcb.pendingMessage with
        | none => simp only []; exact donationChainFrame.refl st
        | some msg =>
            simp only []
            exact recordPhysicalWrites_donationChainFrame st _ _
              (writeDeliveredFrameToTcb_donationChainFrame st tid _ hObjInv)
      · exact donationChainFrame.refl st

/-- **WS-RM (`v0.35.6`)**: and so does the woken sender's completion frame. -/
theorem stageWokenSendCompletion_donationChainFrame
    (st : SystemState) (woken? : Option SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt) :
    donationChainFrame st (Architecture.stageWokenSendCompletion st woken?) := by
  unfold Architecture.stageWokenSendCompletion
  cases woken? with
  | none => exact donationChainFrame.refl st
  | some tid =>
      dsimp only []
      cases hLk : st.getTcb? tid with
      | none => simp only []; exact donationChainFrame.refl st
      | some tcb =>
          simp only []
          split
          · exact writeReturnFrameToTcb_donationChainFrame st tid _ hObjInv
          · exact donationChainFrame.refl st


end SeLe4n.Kernel
