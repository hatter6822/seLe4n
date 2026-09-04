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
import SeLe4n.Kernel.Architecture.SyscallReturn
import SeLe4n.Kernel.Architecture.PerCoreCacheModel
import SeLe4n.Kernel.Architecture.IpcBufferValidation
import SeLe4n.Kernel.IPC.Operations.NotificationBind
import SeLe4n.Kernel.SchedContext.PriorityManagementPerCore

import SeLe4n.Kernel.Capability.Operations
import SeLe4n.Kernel.SchedContext.OperationsPerCore
import SeLe4n.Kernel.Service.Registry
import SeLe4n.Kernel.IPC.CrossCore.Cancellation
import SeLe4n.Kernel.IPC.Operations.Fault

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

* `ipcInvariantFull_of_objects_scheduler_eq` (`LookupCongruence` §5) — arms
  that touch neither the object store nor the scheduler (cache maintenance,
  service-registry writes);
* `ipcInvariantFull_of_readViewAgreement` (`LookupCongruence` §5) — arms that
  rewrite only objects the bundle never reads (CNodes, VSpaceRoots, untyped
  memory), with `capabilityBadgesWellFormed` and `passiveServerIdle` supplied
  for the post-state;
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

/-- A one-TCB rewrite that keeps that TCB's `ipcState` and binding, with the
scheduler untouched, frames `passiveServerIdle`: the rewritten thread pulls
back to its pre-image with the same idle obligations, and every other thread
is untouched. -/
theorem passiveServerIdleFrame_of_tcbFieldUpdate {st st' : SystemState}
    (key : SeLe4n.ObjId) (oldTcb newTcb : TCB)
    (hPre : st.objects[key]? = some (.tcb oldTcb))
    (hAt : st'.objects[key]? = some (.tcb newTcb))
    (hFrame : ∀ oid : SeLe4n.ObjId, oid ≠ key → st'.objects[oid]? = st.objects[oid]?)
    (hIpc : newTcb.ipcState = oldTcb.ipcState)
    (hBind : newTcb.schedContextBinding = oldTcb.schedContextBinding)
    (hSched : st'.scheduler = st.scheduler) :
    passiveServerIdleFrame st st' := by
  refine ⟨fun tid tcb' hT hU hQ hC _ => ?_⟩
  rw [hSched] at hQ hC
  by_cases hK : tid.toObjId = key
  · rw [hK, hAt] at hT
    obtain rfl : newTcb = tcb' := by
      simpa only [Option.some.injEq, KernelObject.tcb.injEq] using hT
    exact ⟨oldTcb, by rw [hK]; exact hPre, hBind ▸ hU, hQ, hC, hIpc.symm⟩
  · rw [hFrame _ hK] at hT
    exact ⟨tcb', hT, hU, hQ, hC, rfl⟩

-- ============================================================================
-- §2  Service-registry arms (`.serviceRegister`, `.serviceRevoke`)
-- ============================================================================

/-- `.serviceRegister`: the registration writes the service registry only —
objects and scheduler are untouched, so the whole bundle transports. -/
theorem registerService_preserves_ipcInvariantFull
    (st st' : SystemState) (reg : ServiceRegistration)
    (hInv : ipcInvariantFull st)
    (hStep : registerService reg st = .ok ((), st')) :
    ipcInvariantFull st' :=
  ipcInvariantFull_of_objects_scheduler_eq
    (registerService_preserves_objects st st' reg hStep)
    (registerService_preserves_scheduler st st' reg hStep)
    hInv

/-- `.serviceRevoke`: revocation removes registry entries and dependency
edges — objects and scheduler are untouched, so the whole bundle transports. -/
theorem revokeService_preserves_ipcInvariantFull
    (st st' : SystemState) (sid : ServiceId)
    (hInv : ipcInvariantFull st)
    (hStep : revokeService sid st = .ok ((), st')) :
    ipcInvariantFull st' :=
  ipcInvariantFull_of_objects_scheduler_eq
    (revokeService_preserves_objects st st' sid hStep)
    (revokeService_preserves_scheduler st st' sid hStep)
    hInv

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
  exact ipcInvariantFull_of_objects_scheduler_eq hObjs hSched hInv

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
  cases hT : st.getTcb? tid with
  | none =>
      rw [Architecture.writeReturnFrameToTcb_id_when_not_tcb st tid frame hT]
      exact hObjInv
  | some tcb =>
      simp only [Architecture.writeReturnFrameToTcb, hT]
      exact RobinHood.RHTable.insert_preserves_invExt _ _ _ hObjInv

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
        rw [hT]
        exact RobinHood.RHTable.getElem?_insert_self st.objects tid.toObjId _ hObjInv
      have hFrame : ∀ oid : SeLe4n.ObjId, oid ≠ tid.toObjId →
          (Architecture.writeReturnFrameToTcb st tid frame).objects[oid]? = st.objects[oid]? :=
        fun oid hNe => Architecture.writeReturnFrameToTcb_objects_ne st tid frame oid hNe hObjInv
      have hSched := Architecture.writeReturnFrameToTcb_scheduler_eq st tid frame
      exact ipcInvariantFull_of_tcbFieldUpdate st _ tid.toObjId tcb (tcb.withReturnFrame frame)
        hInv hPre hAt hFrame rfl rfl rfl rfl rfl rfl rfl rfl rfl
        (passiveServerIdleFrame_of_tcbFieldUpdate tid.toObjId tcb (tcb.withReturnFrame frame)
          hPre hAt hFrame rfl rfl hSched)

-- ============================================================================
-- §5  One-TCB field stores (`.tcbSetIPCBuffer` and friends)
-- ============================================================================

/-- The store-level instance of the one-TCB-rewrite lever: a transition whose
success is exactly `storeObject tid.toObjId (.tcb tcb')` over a looked-up
`tcb`, with `tcb'` agreeing on every conjunct-read field, preserves the whole
bundle.  The scheduler is untouched by `storeObject`, so the passive frame is
the field-update one. -/
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
    (hBind : tcb'.schedContextBinding = tcb.schedContextBinding) :
    ipcInvariantFull st' := by
  have hAt : st'.objects[tid.toObjId]? = some (.tcb tcb') :=
    storeObject_objects_eq st st' tid.toObjId (.tcb tcb') hObjInv hStore
  have hFrame : ∀ oid : SeLe4n.ObjId, oid ≠ tid.toObjId →
      st'.objects[oid]? = st.objects[oid]? :=
    fun oid hNe => storeObject_objects_ne st st' tid.toObjId oid (.tcb tcb') hNe hObjInv hStore
  have hSched := storeObject_scheduler_eq st st' tid.toObjId (.tcb tcb') hStore
  exact ipcInvariantFull_of_tcbFieldUpdate st st' tid.toObjId tcb tcb'
    hInv hPre hAt hFrame hIpc hMsg hNext hPrev hPPrev hBudget hReply hStash hBind
    (passiveServerIdleFrame_of_tcbFieldUpdate tid.toObjId tcb tcb'
      hPre hAt hFrame hIpc hBind hSched)

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

/-- A store replacing one notification with one of identical queue content
(`state`, `waitingThreads`, `pendingBadge` — the binding and lock word are
free) preserves the whole bundle: the notification-reading conjuncts see the
same content, no other conjunct reads the key, and the scheduler is
untouched. -/
theorem storeObject_notificationContentUpdate_preserves_ipcInvariantFull
    (st st1 : SystemState) (nid : SeLe4n.ObjId) (ntfn ntfn' : Notification)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hPre : st.objects[nid]? = some (.notification ntfn))
    (hStore : storeObject nid (.notification ntfn') st = .ok ((), st1))
    (hState : ntfn'.state = ntfn.state)
    (hWaiters : ntfn'.waitingThreads = ntfn.waitingThreads)
    (hBadge : ntfn'.pendingBadge = ntfn.pendingBadge) :
    ipcInvariantFull st1 := by
  have hAt := storeObject_objects_eq st st1 nid (.notification ntfn') hObjInv hStore
  have hNe : ∀ oid : SeLe4n.ObjId, oid ≠ nid → st1.objects[oid]? = st.objects[oid]? :=
    fun oid h => storeObject_objects_ne st st1 nid oid (.notification ntfn') h hObjInv hStore
  have hSched := storeObject_scheduler_eq st st1 nid (.notification ntfn') hStore
  have hView := ipcReadViewAgreement.of_notification_content_write hPre hAt hNe
    hState hWaiters hBadge
  have hBack : ∀ (tid : SeLe4n.ThreadId) (tcb' : TCB),
      st1.objects[tid.toObjId]? = some (.tcb tcb') →
      ∃ tcb, st.objects[tid.toObjId]? = some (.tcb tcb) ∧
        tcb.ipcState = tcb'.ipcState ∧ tcb.schedContextBinding = tcb'.schedContextBinding := by
    intro tid tcb' h
    by_cases hK : tid.toObjId = nid
    · rw [hK, hAt] at h
      exact absurd (Option.some.inj h) (fun hx => KernelObject.noConfusion hx)
    · rw [hNe _ hK] at h
      exact ⟨tcb', h, rfl, rfl⟩
  have hPsi := passiveServerIdle_of_frame
    (passiveServerIdleFrame_of_backward hBack hSched) hInv.passiveServerIdle
  have hCap : capabilityBadgesWellFormed st1 := by
    intro oid cn slot cap badge hCn hLk hB
    by_cases hK : oid = nid
    · rw [hK, hAt] at hCn
      exact absurd (Option.some.inj hCn) (fun hx => KernelObject.noConfusion hx)
    · rw [hNe _ hK] at hCn
      exact hInv.badgeWellFormed.2 oid cn slot cap badge hCn hLk hB
  exact ipcInvariantFull_of_readViewAgreement hView hPsi hCap hInv

/-- `.tcbBindNotification`: the bind writes the notification's `boundTCB` and
the TCB's `boundNotification` — fields no conjunct reads — so the whole
bundle transports across both stores. -/
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
      · split at hStep
        · contradiction
        · rename_i hStore1
          split at hStep
          · contradiction
          · rename_i hStore2
            cases hStep
            have hNraw := (SystemState.getNotification?_eq_some_iff st nid ntfn).mp hN
            have hTraw := lookupTcb_some_objects st tcbId tcb hT
            have hNeIds : tcbId.toObjId ≠ nid := by
              intro hEq
              rw [hEq, hNraw] at hTraw
              exact absurd (Option.some.inj hTraw) (fun hx => KernelObject.noConfusion hx)
            have hInv1 := storeObject_notificationContentUpdate_preserves_ipcInvariantFull
              st _ nid ntfn _ hObjInv hInv hNraw hStore1 rfl rfl rfl
            have hObjInv1 := storeObject_preserves_objects_invExt st _ nid _ hObjInv hStore1
            have hPre1 := storeObject_objects_ne st _ nid tcbId.toObjId _ hNeIds hObjInv hStore1
            exact storeObject_tcbFieldUpdate_preserves_ipcInvariantFull _ _ tcbId
              tcb { tcb with boundNotification := some nid } hObjInv1 hInv1
              (hPre1.trans hTraw) hStore2 rfl rfl rfl rfl rfl rfl rfl rfl rfl
  · split at hStep <;> contradiction

/-- `.tcbUnbindNotification`: the unbind clears both directions of the
binding — again fields no conjunct reads — so the whole bundle transports
across the TCB store and the (fail-safe optional) notification store. -/
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
      · rename_i hStore1
        have hTraw := lookupTcb_some_objects st tcbId tcb hT
        have hObjInv1 := storeObject_preserves_objects_invExt st _ tcbId.toObjId _
          hObjInv hStore1
        have hInv1 := storeObject_tcbFieldUpdate_preserves_ipcInvariantFull st _ tcbId
          tcb { tcb with boundNotification := none } hObjInv hInv hTraw hStore1
          rfl rfl rfl rfl rfl rfl rfl rfl rfl
        split at hStep
        · rename_i ntfn hN1
          split at hStep
          · contradiction
          · rename_i hStore2
            cases hStep
            exact storeObject_notificationContentUpdate_preserves_ipcInvariantFull
              _ _ nid ntfn _ hObjInv1 hInv1
              ((SystemState.getNotification?_eq_some_iff _ nid ntfn).mp hN1)
              hStore2 rfl rfl rfl
        · cases hStep
          exact hInv1

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
    (hBind : tcb'.schedContextBinding = tcb.schedContextBinding) :
    ipcInvariantFull { st with objects := st.objects.insert tid.toObjId (.tcb tcb') } := by
  have hAt := insertObjects_getElem_self st tid.toObjId (.tcb tcb') hObjInv
  have hFrame : ∀ oid : SeLe4n.ObjId, oid ≠ tid.toObjId →
      ({ st with objects := st.objects.insert tid.toObjId (.tcb tcb') }
        : SystemState).objects[oid]? = st.objects[oid]? :=
    fun oid hNe => insertObjects_getElem_ne st tid.toObjId (.tcb tcb') oid hNe hObjInv
  exact ipcInvariantFull_of_tcbFieldUpdate st _ tid.toObjId tcb tcb'
    hInv hPre hAt hFrame hIpc hMsg hNext hPrev hPPrev hBudget hReply hStash hBind
    (passiveServerIdleFrame_of_tcbFieldUpdate tid.toObjId tcb tcb' hPre hAt hFrame
      hIpc hBind rfl)

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
  have hPsi := passiveServerIdle_of_frame
    (passiveServerIdleFrame_of_backward hBack rfl) hInv.passiveServerIdle
  have hCap : capabilityBadgesWellFormed
      { st with objects := st.objects.insert scId.toObjId (.schedContext sc') } := by
    intro oid cn slot cap badge hCn hLk hB
    by_cases hK : oid = scId.toObjId
    · rw [hK, hAt] at hCn
      exact absurd (Option.some.inj hCn) (fun hx => KernelObject.noConfusion hx)
    · rw [hNe _ hK] at hCn
      exact hInv.badgeWellFormed.2 oid cn slot cap badge hCn hLk hB
  exact ipcInvariantFull_of_readViewAgreement hView hPsi hCap hInv

/-- Reduction of `updatePrioritySource` at an unbound binding. -/
private theorem updatePrioritySource_unbound_eq (st : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (p : SeLe4n.Priority)
    (hB : tcb.schedContextBinding = .unbound) :
    SchedContext.PriorityManagement.updatePrioritySource st tid tcb p
      = { st with objects := st.objects.insert tid.toObjId (.tcb { tcb with priority := p }) } := by
  unfold SchedContext.PriorityManagement.updatePrioritySource
  rw [hB]

/-- Reduction of `updatePrioritySource` at a bound or donated binding, keyed on
the projected SchedContext id. -/
private theorem updatePrioritySource_sc_eq (st : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (p : SeLe4n.Priority)
    (scId : SeLe4n.SchedContextId) (sc : SeLe4n.Kernel.SchedContext)
    (hB : tcb.schedContextBinding = .bound scId ∨
          ∃ owner, tcb.schedContextBinding = .donated scId owner)
    (hSc : st.getSchedContext? scId = some sc) :
    SchedContext.PriorityManagement.updatePrioritySource st tid tcb p
      = { st with objects :=
            st.objects.insert scId.toObjId (.schedContext { sc with priority := p }) } := by
  unfold SchedContext.PriorityManagement.updatePrioritySource
  rcases hB with hB | ⟨owner, hB⟩ <;> (rw [hB]; dsimp only []; rw [hSc])

/-- Reduction of `updatePrioritySource` when the named SchedContext is absent. -/
private theorem updatePrioritySource_sc_none_eq (st : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (p : SeLe4n.Priority)
    (scId : SeLe4n.SchedContextId)
    (hB : tcb.schedContextBinding = .bound scId ∨
          ∃ owner, tcb.schedContextBinding = .donated scId owner)
    (hSc : st.getSchedContext? scId = none) :
    SchedContext.PriorityManagement.updatePrioritySource st tid tcb p = st := by
  unfold SchedContext.PriorityManagement.updatePrioritySource
  rcases hB with hB | ⟨owner, hB⟩ <;> (rw [hB]; dsimp only []; rw [hSc])

/-- `updatePrioritySource` writes a priority field — on the TCB when unbound,
on the bound SchedContext otherwise — and priority is a field no conjunct
reads. -/
theorem updatePrioritySource_preserves_ipcInvariantFull
    (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB) (p : SeLe4n.Priority)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hPre : st.objects[tid.toObjId]? = some (.tcb tcb)) :
    ipcInvariantFull (SchedContext.PriorityManagement.updatePrioritySource st tid tcb p) := by
  cases hB : tcb.schedContextBinding with
  | unbound =>
      rw [updatePrioritySource_unbound_eq st tid tcb p hB]
      exact insertObjects_tcbFieldUpdate_preserves_ipcInvariantFull st tid tcb
        { tcb with priority := p } hObjInv hInv hPre rfl rfl rfl rfl rfl rfl rfl rfl rfl
  | bound scId =>
      cases hSc : st.getSchedContext? scId with
      | some sc =>
          rw [updatePrioritySource_sc_eq st tid tcb p scId sc (Or.inl hB) hSc]
          exact insertObjects_schedContextContentUpdate_preserves_ipcInvariantFull st scId
            sc { sc with priority := p } hObjInv hInv
            ((SystemState.getSchedContext?_eq_some_iff st scId sc).mp hSc) rfl
      | none => rw [updatePrioritySource_sc_none_eq st tid tcb p scId (Or.inl hB) hSc]; exact hInv
  | donated scId owner =>
      cases hSc : st.getSchedContext? scId with
      | some sc =>
          rw [updatePrioritySource_sc_eq st tid tcb p scId sc (Or.inr ⟨owner, hB⟩) hSc]
          exact insertObjects_schedContextContentUpdate_preserves_ipcInvariantFull st scId
            sc { sc with priority := p } hObjInv hInv
            ((SystemState.getSchedContext?_eq_some_iff st scId sc).mp hSc) rfl
      | none =>
          rw [updatePrioritySource_sc_none_eq st tid tcb p scId (Or.inr ⟨owner, hB⟩) hSc]
          exact hInv

/-- `migrateRunQueueBucketOnCore` moves no object. -/
theorem migrateRunQueueBucketOnCore_objects_eq (st : SystemState)
    (tid : SeLe4n.ThreadId) (p : SeLe4n.Priority) (c : CoreId) :
    (SchedContext.PriorityManagement.migrateRunQueueBucketOnCore st tid p c).objects
      = st.objects := by
  simp only [SchedContext.PriorityManagement.migrateRunQueueBucketOnCore]
  split <;> rfl

/-- The bucket re-key changes no thread's run-queue membership on any core. -/
theorem migrateRunQueueBucketOnCore_mem_runQueueOnCore (st : SystemState)
    (tid : SeLe4n.ThreadId) (p : SeLe4n.Priority) (c c' : CoreId) (x : SeLe4n.ThreadId) :
    x ∈ (SchedContext.PriorityManagement.migrateRunQueueBucketOnCore
          st tid p c).scheduler.runQueueOnCore c'
      ↔ x ∈ st.scheduler.runQueueOnCore c' := by
  simp only [SchedContext.PriorityManagement.migrateRunQueueBucketOnCore]
  split
  · rename_i hIn
    by_cases hcc : c = c'
    · subst hcc
      rw [SchedulerState.setRunQueueOnCore_runQueueOnCore_self]
      rw [RunQueue.mem_insert, RunQueue.mem_remove]
      constructor
      · rintro (⟨hx, _⟩ | hxt)
        · exact hx
        · exact hxt ▸ hIn
      · intro hx
        by_cases hEq : x = tid
        · exact Or.inr hEq
        · exact Or.inl ⟨hx, hEq⟩
    · rw [SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ c c' _ hcc]
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
  have hObjs := migrateRunQueueBucketOnCore_objects_eq st tid p c
  refine ipcInvariantFull_of_getElem_eq (fun oid => by rw [hObjs]) ?_ hInv
  exact passiveServerIdle_of_frame
    (passiveServerIdleFrame_of_backward_monotone
      (fun t tcb' h => ⟨tcb', by rw [hObjs] at h; exact h, rfl, rfl⟩)
      (fun y hy =>
        (migrateRunQueueBucketOnCore_mem_runQueueOnCore st tid p c
          Concurrency.bootCoreId y).mpr hy)
      (migrateRunQueueBucketOnCore_currentOnCore st tid p c Concurrency.bootCoreId))
    hInv.passiveServerIdle

/-- `applyPriorityChangeOnCore` is the priority-source write followed by the
bucket re-key; the reschedule stage is state-inert (its context-restore seam
is not live — if that seam flips, this proof fails loudly at the flip, which
is the registered SM10.1 obligation surfacing where it must). -/
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
  rw [SchedContext.PriorityManagement.priorityRescheduleOnCoreLive_inert] at hStep
  have hEq := SchedContext.PriorityManagement.priorityRescheduleEnqueueOnly_state
    _ _ _ _ _ _ hStep
  subst hEq
  exact migrateRunQueueBucketOnCore_preserves_ipcInvariantFull _ _ _ _
    (updatePrioritySource_preserves_ipcInvariantFull st tid tcb p hObjInv hInv hPre)

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
      · rename_i targetTcb hTarget
        dsimp only [] at hStep
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

-- ============================================================================
-- §8  Affinity arm (`.tcbSetAffinity`)
-- ============================================================================

/-- Every unbound thread parked on any run queue is in a passive-idle-allowed
state.  A run queue holds runnable threads, so on the scheduler's queue
discipline this always holds; it enters the affinity bundle as a *pre*-state
hypothesis (dischargeable, in the RR3.1-gate sense) because the affinity
migration moves such a thread between cores' queues, turning its
`passiveServerIdle` exemption from "queued on boot" into "idle-allowed". -/
def unboundQueuedThreadsIdleAllowed (st : SystemState) : Prop :=
  ∀ (c : CoreId) (t : SeLe4n.ThreadId) (tcb : TCB),
    st.objects[t.toObjId]? = some (.tcb tcb) →
    tcb.schedContextBinding = .unbound →
    t ∈ st.scheduler.runQueueOnCore c →
    passiveServerIdleAllowed tcb.ipcState

/-- Under the queued-threads hypothesis, `passiveServerIdle` survives **any**
run-queue reshuffle that keeps objects and the boot `current` slot: a thread
off the boot queue in the post-state was either off it before (the pre-state
invariant answers) or on it before (the hypothesis answers). -/
theorem passiveServerIdle_of_objects_current_eq_of_queuedAllowed
    {st st' : SystemState}
    (hObjs : st'.objects = st.objects)
    (hCur : st'.scheduler.currentOnCore Concurrency.bootCoreId
      = st.scheduler.currentOnCore Concurrency.bootCoreId)
    (hQueued : unboundQueuedThreadsIdleAllowed st)
    (hPsi : passiveServerIdle st) : passiveServerIdle st' := by
  intro t tcb hT hUnb _ hNotCur
  rw [hObjs] at hT
  rw [hCur] at hNotCur
  by_cases hMem : t ∈ st.scheduler.runQueueOnCore Concurrency.bootCoreId
  · exact hQueued Concurrency.bootCoreId t tcb hT hUnb hMem
  · exact hPsi t tcb hT hUnb hMem hNotCur

/-- The queued-threads hypothesis transports across a one-TCB rewrite that
keeps `ipcState` and the binding, with run queues untouched. -/
theorem unboundQueuedThreadsIdleAllowed_of_tcbFieldUpdate {st st' : SystemState}
    (key : SeLe4n.ObjId) (oldTcb newTcb : TCB)
    (hPre : st.objects[key]? = some (.tcb oldTcb))
    (hAt : st'.objects[key]? = some (.tcb newTcb))
    (hFrame : ∀ oid : SeLe4n.ObjId, oid ≠ key → st'.objects[oid]? = st.objects[oid]?)
    (hIpc : newTcb.ipcState = oldTcb.ipcState)
    (hBind : newTcb.schedContextBinding = oldTcb.schedContextBinding)
    (hRq : ∀ c : CoreId, st'.scheduler.runQueueOnCore c = st.scheduler.runQueueOnCore c)
    (h : unboundQueuedThreadsIdleAllowed st) : unboundQueuedThreadsIdleAllowed st' := by
  intro c t tcb' hT hU hQ
  rw [hRq c] at hQ
  by_cases hK : t.toObjId = key
  · rw [hK, hAt] at hT
    obtain rfl : newTcb = tcb' := by
      simpa only [Option.some.injEq, KernelObject.tcb.injEq] using hT
    have := h c t oldTcb (by rw [hK]; exact hPre) (hBind ▸ hU) hQ
    rw [hIpc]
    exact this
  · rw [hFrame _ hK] at hT
    exact h c t tcb' hT hU hQ

/-- The queued-threads hypothesis transports across any step preserving
objects and every run queue. -/
theorem unboundQueuedThreadsIdleAllowed_of_objects_runQueues_eq {st st' : SystemState}
    (hObjs : st'.objects = st.objects)
    (hRq : ∀ c : CoreId, st'.scheduler.runQueueOnCore c = st.scheduler.runQueueOnCore c)
    (h : unboundQueuedThreadsIdleAllowed st) : unboundQueuedThreadsIdleAllowed st' := by
  intro c t tcb hT hU hQ
  rw [hObjs] at hT
  rw [hRq c] at hQ
  exact h c t tcb hT hU hQ

/-- The replenishment migration repoints no core's `current` slot. -/
theorem migrateSchedContextReplenishment_currentOnCore (st : SystemState)
    (scId : SeLe4n.SchedContextId) (fromCore toCore c' : CoreId) :
    (migrateSchedContextReplenishment st scId fromCore toCore).scheduler.currentOnCore c'
      = st.scheduler.currentOnCore c' := by
  unfold migrateSchedContextReplenishment
  split
  · rfl
  · simp

/-- The replenishment migration preserves the whole bundle: objects, run
queues and `current` are all untouched. -/
theorem migrateSchedContextReplenishment_preserves_ipcInvariantFull (st : SystemState)
    (scId : SeLe4n.SchedContextId) (fromCore toCore : CoreId)
    (hInv : ipcInvariantFull st) :
    ipcInvariantFull (migrateSchedContextReplenishment st scId fromCore toCore) := by
  have hObjs := migrateSchedContextReplenishment_objects st scId fromCore toCore
  refine ipcInvariantFull_of_getElem_eq (fun oid => by rw [hObjs]) ?_ hInv
  exact passiveServerIdle_of_frame
    (passiveServerIdleFrame_of_backward_monotone
      (fun t tcb' h => ⟨tcb', by rw [hObjs] at h; exact h, rfl, rfl⟩)
      (fun y hy => by
        rw [migrateSchedContextReplenishment_runQueueOnCore]
        exact hy)
      (migrateSchedContextReplenishment_currentOnCore st scId fromCore toCore
        Concurrency.bootCoreId))
    hInv.passiveServerIdle

/-- The affinity run-queue migration moves no object. -/
theorem migrateRunQueueOnAffinityChange_objects_eq (st : SystemState)
    (tid : SeLe4n.ThreadId) (fromCore toCore : CoreId) :
    (migrateRunQueueOnAffinityChange st tid fromCore toCore).objects
      = st.objects := by
  unfold migrateRunQueueOnAffinityChange
  split
  · rfl
  · split
    · rfl
    · split <;> rfl

/-- The affinity run-queue migration repoints no core's `current` slot. -/
theorem migrateRunQueueOnAffinityChange_currentOnCore (st : SystemState)
    (tid : SeLe4n.ThreadId) (fromCore toCore c' : CoreId) :
    (migrateRunQueueOnAffinityChange st tid fromCore toCore).scheduler.currentOnCore c'
      = st.scheduler.currentOnCore c' := by
  unfold migrateRunQueueOnAffinityChange
  split
  · rfl
  · split
    · rfl
    · split <;> simp

/-- The affinity run-queue migration preserves the whole bundle, given the
queued-threads hypothesis: moving the target between cores' queues transfers
its `passiveServerIdle` exemption rather than discharging it. -/
theorem migrateRunQueueOnAffinityChange_preserves_ipcInvariantFull (st : SystemState)
    (tid : SeLe4n.ThreadId) (fromCore toCore : CoreId)
    (hQueued : unboundQueuedThreadsIdleAllowed st)
    (hInv : ipcInvariantFull st) :
    ipcInvariantFull (migrateRunQueueOnAffinityChange st tid fromCore toCore) := by
  have hObjs := migrateRunQueueOnAffinityChange_objects_eq st tid fromCore toCore
  exact ipcInvariantFull_of_getElem_eq (fun oid => by rw [hObjs])
    (passiveServerIdle_of_objects_current_eq_of_queuedAllowed hObjs
      (migrateRunQueueOnAffinityChange_currentOnCore st tid fromCore toCore
        Concurrency.bootCoreId)
      hQueued hInv.passiveServerIdle)
    hInv

/-- `.tcbSetAffinity`: the affinity write is a one-TCB rewrite of a field no
conjunct reads; the replenishment and run-queue migrations that follow the
thread to its new home core move no object and repoint no `current` slot, so
under the queued-threads hypothesis the whole bundle transports. -/
theorem setThreadCpuAffinityOnCore_preserves_ipcInvariantFull
    (st st' : SystemState) (vtid : SeLe4n.ValidThreadId) (affinity : Option CoreId)
    (ec : CoreId) (sgi : Option (CoreId × Concurrency.SgiKind))
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hQueued : unboundQueuedThreadsIdleAllowed st)
    (hStep : setThreadCpuAffinityOnCore st vtid affinity ec = .ok (st', sgi)) :
    ipcInvariantFull st' := by
  unfold setThreadCpuAffinityOnCore setThreadCpuAffinityWithMigration at hStep
  split at hStep
  · rename_i tcb hT
    -- PR #889 review round 20: the declared-core refusal is a new leading
    -- branch; `hStep` says it did not fire.
    split at hStep
    · contradiction
    · split at hStep
      · contradiction
      · split at hStep
        · rename_i stSet hSet
          have hSetEq : stSet = { st with objects := st.objects.insert vtid.val.toObjId (.tcb { tcb with cpuAffinity := affinity }) } := by
            unfold setThreadCpuAffinity at hSet
            rw [hT] at hSet
            exact (Except.ok.inj hSet).symm
          subst hSetEq
          dsimp only [] at hStep
          cases hStep
          have hPreRaw := (SystemState.getTcb?_eq_some_iff st vtid.val tcb).mp hT
          have hInvSet := insertObjects_tcbFieldUpdate_preserves_ipcInvariantFull st vtid.val
            tcb { tcb with cpuAffinity := affinity } hObjInv hInv hPreRaw
            rfl rfl rfl rfl rfl rfl rfl rfl rfl
          have hAtSet := insertObjects_getElem_self st vtid.val.toObjId
            (.tcb { tcb with cpuAffinity := affinity }) hObjInv
          have hQueuedSet := unboundQueuedThreadsIdleAllowed_of_tcbFieldUpdate
            vtid.val.toObjId tcb { tcb with cpuAffinity := affinity } hPreRaw hAtSet
            (fun oid hNe => insertObjects_getElem_ne st vtid.val.toObjId
              (.tcb { tcb with cpuAffinity := affinity }) oid hNe hObjInv)
            rfl rfl (fun _ => rfl) hQueued
          cases hScid : tcb.schedContextBinding.scId? with
          | some scId =>
              exact migrateRunQueueOnAffinityChange_preserves_ipcInvariantFull _ _ _ _
                (unboundQueuedThreadsIdleAllowed_of_objects_runQueues_eq
                  (migrateSchedContextReplenishment_objects _ _ _ _)
                  (fun c => migrateSchedContextReplenishment_runQueueOnCore _ _ _ _ c)
                  hQueuedSet)
                (migrateSchedContextReplenishment_preserves_ipcInvariantFull _ _ _ _ hInvSet)
          | none =>
              exact migrateRunQueueOnAffinityChange_preserves_ipcInvariantFull _ _ _ _
                hQueuedSet hInvSet
        · contradiction
  · contradiction

-- ============================================================================
-- §9  Capability arms (`.cspaceDelete`, `.cspaceMint`, `.cspaceCopy`,
--     `.cspaceMove`, `.mintReplyCap`)
-- ============================================================================

/-- The CDT node-allocation step touches only the CDT maps. -/
theorem ensureCdtNodeForSlot_scheduler_eq (st : SystemState) (ref : SlotRef) :
    (SystemState.ensureCdtNodeForSlot st ref).snd.scheduler = st.scheduler := by
  unfold SystemState.ensureCdtNodeForSlot
  split <;> rfl

/-- The CDT attach step touches only the CDT maps. -/
theorem attachSlotToCdtNode_scheduler_eq (st : SystemState) (ref : SlotRef)
    (node : CdtNodeId) :
    (SystemState.attachSlotToCdtNode st ref node).scheduler = st.scheduler := rfl

/-- The CDT detach step touches only the CDT maps. -/
theorem detachSlotFromCdt_scheduler_eq (st : SystemState) (ref : SlotRef) :
    (SystemState.detachSlotFromCdt st ref).scheduler = st.scheduler := by
  unfold SystemState.detachSlotFromCdt
  split <;> rfl

/-- Success shape of `cspaceInsertSlot`: the target CNode existed, and the
post-state holds it with the capability inserted. -/
private theorem cspaceInsertSlot_cnode_shape
    (st st' : SystemState) (addr : CSpaceAddr) (cap : Capability)
    (hObjInv : st.objects.invExt)
    (hStep : cspaceInsertSlot addr cap st = .ok ((), st')) :
    ∃ cn : CNode, st.objects[addr.cnode]? = some (.cnode cn) ∧
      st'.objects[addr.cnode]? = some (.cnode (cn.insert addr.slot cap)) := by
  unfold cspaceInsertSlot at hStep
  cases hObj : st.objects[addr.cnode]? with
  | none => simp [hObj] at hStep
  | some obj =>
    cases obj with
    | cnode cn =>
      simp only [hObj] at hStep
      cases hLk : cn.lookup addr.slot with
      | some c => simp [hLk] at hStep
      | none =>
        simp only [hLk] at hStep
        split at hStep
        · contradiction
        · rename_i st1 hStore
          have h1 := storeObject_objects_eq st st1 addr.cnode
            (.cnode (cn.insert addr.slot cap)) hObjInv hStore
          unfold storeCapabilityRef at hStep
          cases hStep
          exact ⟨cn, rfl, h1⟩
    | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _
    | schedContext _ | reply _ => simp [hObj] at hStep

/-- `cspaceInsertSlot` preserves the whole bundle: its one object write is a
CNode, and the inserted capability's badge is valid. -/
theorem cspaceInsertSlot_preserves_ipcInvariantFull
    (st st' : SystemState) (addr : CSpaceAddr) (cap : Capability)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hCapValid : ∀ b, cap.badge = some b → b.valid)
    (hStep : cspaceInsertSlot addr cap st = .ok ((), st')) :
    ipcInvariantFull st' := by
  obtain ⟨cn, hPre, hAt⟩ := cspaceInsertSlot_cnode_shape st st' addr cap hObjInv hStep
  have hNe : ∀ oid : SeLe4n.ObjId, oid ≠ addr.cnode →
      st'.objects[oid]? = st.objects[oid]? :=
    fun oid h => cspaceInsertSlot_preserves_objects_ne st st' addr cap oid h hObjInv hStep
  have hSched := cspaceInsertSlot_preserves_scheduler st st' addr cap hStep
  have hView := ipcReadViewAgreement.of_single_inert_write hNe
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
  exact ipcInvariantFull_of_readViewAgreement hView
    (passiveServerIdle_of_frame (passiveServerIdleFrame_of_backward hBack hSched)
      hInv.passiveServerIdle)
    hBadge.2 hInv

/-- Success shape of `cspaceDeleteSlotCore`: the target CNode existed, the
post-state holds it with the slot removed, off-key objects and the scheduler
are untouched. -/
private theorem cspaceDeleteSlotCore_shape
    (st st' : SystemState) (addr : CSpaceAddr)
    (hObjInv : st.objects.invExt)
    (hStep : cspaceDeleteSlotCore addr st = .ok ((), st')) :
    ∃ cn : CNode, st.objects[addr.cnode]? = some (.cnode cn) ∧
      st'.objects[addr.cnode]? = some (.cnode (cn.remove addr.slot)) ∧
      (∀ oid : SeLe4n.ObjId, oid ≠ addr.cnode → st'.objects[oid]? = st.objects[oid]?) ∧
      st'.scheduler = st.scheduler := by
  unfold cspaceDeleteSlotCore at hStep
  cases hObj : st.objects[addr.cnode]? with
  | none => simp [hObj] at hStep
  | some obj =>
    cases obj with
    | cnode cn =>
      simp only [hObj] at hStep
      split at hStep
      · contradiction
      · rename_i st1 hStore
        unfold storeCapabilityRef at hStep
        dsimp only [] at hStep
        cases hStep
        refine ⟨cn, rfl, ?_, ?_, ?_⟩
        · rw [SystemState.detachSlotFromCdt_objects_eq]
          exact storeObject_objects_eq st st1 addr.cnode
            (.cnode (cn.remove addr.slot)) hObjInv hStore
        · intro oid hNe
          rw [SystemState.detachSlotFromCdt_objects_eq]
          exact storeObject_objects_ne st st1 addr.cnode oid
            (.cnode (cn.remove addr.slot)) hNe hObjInv hStore
        · rw [detachSlotFromCdt_scheduler_eq]
          exact storeObject_scheduler_eq st st1 addr.cnode
            (.cnode (cn.remove addr.slot)) hStore
    | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _
    | schedContext _ | reply _ => simp [hObj] at hStep

/-- `cspaceDeleteSlotCore` preserves the whole bundle: removal shrinks the
CNode's lookups, so the badge clause carries from the pre-state. -/
theorem cspaceDeleteSlotCore_preserves_ipcInvariantFull
    (st st' : SystemState) (addr : CSpaceAddr)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hStep : cspaceDeleteSlotCore addr st = .ok ((), st')) :
    ipcInvariantFull st' := by
  obtain ⟨cn, hPre, hAt, hNe, hSched⟩ := cspaceDeleteSlotCore_shape st st' addr hObjInv hStep
  have hView := ipcReadViewAgreement.of_single_inert_write hNe
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
      obtain rfl : cn.remove addr.slot = cn' := by
        simpa only [Option.some.injEq, KernelObject.cnode.injEq] using hCn
      by_cases hSlot : addr.slot = slot
      · rw [← hSlot, CNode.lookup_remove_eq_none cn addr.slot
          (CNode.slotsUnique_holds cn)] at hLk
        cases hLk
      · rw [CNode.lookup_remove_ne cn addr.slot slot hSlot
          (CNode.slotsUnique_holds cn)] at hLk
        exact hInv.badgeWellFormed.2 addr.cnode cn slot cap badge (hK ▸ hPre) hLk hB
    · rw [hNe _ hK] at hCn
      exact hInv.badgeWellFormed.2 oid cn' slot cap badge hCn hLk hB
  exact ipcInvariantFull_of_readViewAgreement hView
    (passiveServerIdle_of_frame (passiveServerIdleFrame_of_backward hBack hSched)
      hInv.passiveServerIdle)
    hCap hInv

/-- `.cspaceDelete`: the guard adds no state change on top of the core. -/
theorem cspaceDeleteSlot_preserves_ipcInvariantFull
    (st st' : SystemState) (addr : CSpaceAddr)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hStep : cspaceDeleteSlot addr st = .ok ((), st')) :
    ipcInvariantFull st' := by
  unfold cspaceDeleteSlot at hStep
  split at hStep
  · contradiction
  · exact cspaceDeleteSlotCore_preserves_ipcInvariantFull st st' addr hObjInv hInv hStep

/-- A capability read out of a CNode slot carries a valid badge, by the badge
clause of the pre-state. -/
theorem lookupSlotCap_badge_valid (st : SystemState) (addr : CSpaceAddr)
    (cap : Capability) (hCapWf : capabilityBadgesWellFormed st)
    (hLk : SystemState.lookupSlotCap st addr = some cap) :
    ∀ b, cap.badge = some b → b.valid := by
  intro b hB
  unfold SystemState.lookupSlotCap at hLk
  cases hCn : SystemState.lookupCNode st addr.cnode with
  | none => rw [hCn] at hLk; cases hLk
  | some cn =>
      rw [hCn] at hLk
      have hObj : st.objects[addr.cnode]? = some (.cnode cn) := by
        unfold SystemState.lookupCNode at hCn
        cases hO : st.objects[addr.cnode]? with
        | none => rw [hO] at hCn; cases hCn
        | some obj =>
          cases obj <;> rw [hO] at hCn <;> cases hCn
          rfl
      exact hCapWf addr.cnode cn addr.slot cap b hObj hLk hB

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
            · cases hMint; rfl
          · contradiction
        exact cspaceInsertSlot_preserves_ipcInvariantFull stMid st' dst child
          (hMid.symm ▸ hObjInv) (hMid.symm ▸ hInv)
          (fun b hb => hBadgeValid b (hChildBadge ▸ hb)) hStep

/-- The CDT-recording tail every `WithCdt` form ends in touches neither
objects nor the scheduler. -/
private theorem cdtRecord_bundle_frame (stM : SystemState) (src dst : CSpaceAddr)
    (kind : DerivationOp)
    (hInvM : ipcInvariantFull stM) :
    ipcInvariantFull
      (let p1 := SystemState.ensureCdtNodeForSlot stM src
       let p2 := SystemState.ensureCdtNodeForSlot p1.snd dst
       { p2.snd with cdt := p2.snd.cdt.addEdge p1.fst p2.fst kind }) := by
  refine ipcInvariantFull_of_objects_scheduler_eq ?_ ?_ hInvM
  · show (SystemState.ensureCdtNodeForSlot
        (SystemState.ensureCdtNodeForSlot stM src).snd dst).snd.objects = stM.objects
    rw [SystemState.ensureCdtNodeForSlot_objects_eq, SystemState.ensureCdtNodeForSlot_objects_eq]
  · show (SystemState.ensureCdtNodeForSlot
        (SystemState.ensureCdtNodeForSlot stM src).snd dst).snd.scheduler = stM.scheduler
    rw [ensureCdtNodeForSlot_scheduler_eq, ensureCdtNodeForSlot_scheduler_eq]

/-- `.cspaceMint`: the CDT-tracked form the dispatch routes through. -/
theorem cspaceMintWithCdt_preserves_ipcInvariantFull
    (st st' : SystemState) (src dst : CSpaceAddr) (rights : AccessRightSet)
    (badge : Option SeLe4n.Badge)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hBadgeValid : ∀ b, badge = some b → b.valid)
    (hStep : cspaceMintWithCdt src dst rights badge st = .ok ((), st')) :
    ipcInvariantFull st' := by
  unfold cspaceMintWithCdt at hStep
  split at hStep
  · contradiction
  · rename_i stM hMint
    dsimp only [] at hStep
    cases hStep
    exact cdtRecord_bundle_frame stM src dst DerivationOp.mint
      (cspaceMint_preserves_ipcInvariantFull st stM src dst rights badge
        hObjInv hInv hBadgeValid hMint)

/-- `.cspaceCopy`: the copied capability's badge is valid because it was
already at rest in the source slot of a state satisfying the badge clause. -/
theorem cspaceCopy_preserves_ipcInvariantFull
    (st st' : SystemState) (src dst : CSpaceAddr)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hStep : cspaceCopy src dst st = .ok ((), st')) :
    ipcInvariantFull st' := by
  unfold cspaceCopy at hStep
  split at hStep
  · contradiction
  · rename_i cap stMid hLk
    have hMid : stMid = st := cspaceLookupSlot_state_eq st stMid src cap hLk
    split at hStep
    · contradiction
    · rename_i capNN hNN
      split at hStep
      · contradiction
      · rename_i st2 hIns
        dsimp only [] at hStep
        cases hStep
        have hBadgeSrc := lookupSlotCap_badge_valid st src cap hInv.badgeWellFormed.2
          ((cspaceLookupSlot_ok_iff_lookupSlotCap st src cap).mp (hMid ▸ hLk))
        exact cdtRecord_bundle_frame st2 src dst DerivationOp.copy
          (cspaceInsertSlot_preserves_ipcInvariantFull stMid st2 dst capNN.val
            (hMid.symm ▸ hObjInv) (hMid.symm ▸ hInv)
            (fun b hb => hBadgeSrc b (toNonNull?_val_eq hNN ▸ hb)) hIns)

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
          dsimp only [] at hStep
          split at hStep
          · contradiction
          · rename_i st3 hDel
            have hInv3 := cspaceDeleteSlotCore_preserves_ipcInvariantFull st2 st3 src
              hObjInv2 hInv2 hDel
            split at hStep
            · cases hStep
              exact hInv3
            · rename_i srcNode hNode
              cases hStep
              exact ipcInvariantFull_of_objects_scheduler_eq
                (SystemState.attachSlotToCdtNode_objects_eq st3 dst srcNode)
                (attachSlotToCdtNode_scheduler_eq st3 dst srcNode)
                hInv3

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
    dsimp only [] at hStep
    cases hStep
    exact cdtRecord_bundle_frame stM src dst DerivationOp.mint
      (mintReplyCap_preserves_ipcInvariantFull st stM src dst hObjInv hInv hMint)

-- ============================================================================
-- §10  Sched-context arm (`.schedContextConfigure`)
-- ============================================================================

/-- The replenishment purge rewrites one replenish queue: objects, run queues
and `current` are untouched. -/
theorem purgeReplenishmentOnCore_preserves_ipcInvariantFull (st : SystemState)
    (c : CoreId) (scId : SeLe4n.SchedContextId)
    (hInv : ipcInvariantFull st) :
    ipcInvariantFull (SchedContextOps.purgeReplenishmentOnCore st c scId) := by
  refine ipcInvariantFull_of_getElem_eq (s1 := st) (fun oid => rfl) ?_ hInv
  refine passiveServerIdle_of_frame
    (passiveServerIdleFrame_of_backward_monotone
      (fun t tcb' h => ⟨tcb', h, rfl, rfl⟩)
      (fun y hy => hy) rfl)
    hInv.passiveServerIdle

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
  have hSched := storeObject_scheduler_eq st st1 oid (.schedContext sc') hStore
  have hView := ipcReadViewAgreement.of_schedContext_content_write hPre hAt hNe hBound
  have hBack : ∀ (tid : SeLe4n.ThreadId) (tcb' : TCB),
      st1.objects[tid.toObjId]? = some (.tcb tcb') →
      ∃ tcb, st.objects[tid.toObjId]? = some (.tcb tcb) ∧
        tcb.ipcState = tcb'.ipcState ∧ tcb.schedContextBinding = tcb'.schedContextBinding := by
    intro tid tcb' h
    by_cases hK : tid.toObjId = oid
    · rw [hK, hAt] at h
      exact absurd (Option.some.inj h) (fun hx => KernelObject.noConfusion hx)
    · rw [hNe _ hK] at h
      exact ⟨tcb', h, rfl, rfl⟩
  have hCap : capabilityBadgesWellFormed st1 := by
    intro o cn slot cap badge hCn hLk hB
    by_cases hK : o = oid
    · rw [hK, hAt] at hCn
      exact absurd (Option.some.inj hCn) (fun hx => KernelObject.noConfusion hx)
    · rw [hNe _ hK] at hCn
      exact hInv.badgeWellFormed.2 o cn slot cap badge hCn hLk hB
  exact ipcInvariantFull_of_readViewAgreement hView
    (passiveServerIdle_of_frame (passiveServerIdleFrame_of_backward hBack hSched)
      hInv.passiveServerIdle)
    hCap hInv

/-- Re-keying a queued thread's run-queue bucket in place preserves the whole
bundle: membership survives the remove/insert pair, `current` and objects are
untouched. -/
theorem ipcInvariantFull_of_runQueueReKey (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (p : SeLe4n.Priority)
    (hInv : ipcInvariantFull st)
    (hMem : tid ∈ st.scheduler.runQueueOnCore c) :
    ipcInvariantFull { st with scheduler := st.scheduler.setRunQueueOnCore c (((st.scheduler.runQueueOnCore c).remove tid).insert tid p) } := by
  refine ipcInvariantFull_of_getElem_eq (s1 := st) (fun oid => rfl) ?_ hInv
  refine passiveServerIdle_of_frame
    (passiveServerIdleFrame_of_backward_monotone (st := st)
      (fun t tcb' h => ⟨tcb', h, rfl, rfl⟩)
      (fun y hy => ?_) (by simp))
    hInv.passiveServerIdle
  show y ∈ (st.scheduler.setRunQueueOnCore c (((st.scheduler.runQueueOnCore c).remove tid).insert tid p)).runQueueOnCore Concurrency.bootCoreId
  by_cases hcc : c = Concurrency.bootCoreId
  · subst hcc
    rw [SchedulerState.setRunQueueOnCore_runQueueOnCore_self]
    rw [RunQueue.mem_insert, RunQueue.mem_remove]
    by_cases hEq : y = tid
    · exact Or.inr hEq
    · exact Or.inl ⟨hy, hEq⟩
  · rw [SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ c Concurrency.bootCoreId _ hcc]
    exact hy

/-- Domain alignment over any base state: a no-op or a one-TCB rewrite of a
field no conjunct reads. -/
private theorem domainAlignStep_preserves_ipcInvariantFull (stP : SystemState)
    (tid : SeLe4n.ThreadId) (tcbC : TCB) (domain : Nat)
    (hObjInv : stP.objects.invExt) (hInv : ipcInvariantFull stP)
    (hAt : stP.objects[tid.toObjId]? = some (.tcb tcbC)) :
    ipcInvariantFull (if tcbC.domain.val = domain then stP
      else { stP with objects := stP.objects.insert tid.toObjId (.tcb { tcbC with domain := ⟨domain⟩ }) }) := by
  by_cases h : tcbC.domain.val = domain
  · rw [if_pos h]
    exact hInv
  · rw [if_neg h]
    exact insertObjects_tcbFieldUpdate_preserves_ipcInvariantFull stP tid tcbC
      { tcbC with domain := ⟨domain⟩ } hObjInv hInv hAt rfl rfl rfl rfl rfl rfl rfl rfl rfl

/-- The factored propagation tail preserves the whole bundle: the priority
write and domain write touch fields no conjunct reads, and the re-bucket
re-keys a queued thread in place. -/
theorem schedContextConfigureBoundPropagate_preserves_ipcInvariantFull
    (stStored : SystemState) (boundTid : SeLe4n.ThreadId) (boundTcb : TCB)
    (priority domain : Nat)
    (hObjInv : stStored.objects.invExt) (hInv : ipcInvariantFull stStored)
    (hBT : stStored.getTcb? boundTid = some boundTcb) :
    ipcInvariantFull (SchedContextOps.schedContextConfigureBoundPropagate stStored boundTid
      boundTcb priority domain) := by
  have hBTRaw := (SystemState.getTcb?_eq_some_iff stStored boundTid boundTcb).mp hBT
  unfold SchedContextOps.schedContextConfigureBoundPropagate
  by_cases hPrioEq : boundTcb.priority.val = priority
  · rw [if_pos hPrioEq]
    dsimp only []
    split
    · rename_i currentTcb hCur
      have hCEq : boundTcb = currentTcb := Option.some.inj (hBT.symm.trans hCur)
      subst hCEq
      exact domainAlignStep_preserves_ipcInvariantFull stStored boundTid boundTcb domain
        hObjInv hInv hBTRaw
    · exact hInv
  · rw [if_neg hPrioEq]
    dsimp only []
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
    by_cases hMem : boundTid ∈ stStored.scheduler.runQueueOnCore
        (determineTargetCore { stStored with objects := stStored.objects.insert boundTid.toObjId (.tcb { boundTcb with priority := ⟨priority⟩ }) } boundTid)
    · rw [if_pos hMem]
      have hInvR := ipcInvariantFull_of_runQueueReKey
        { stStored with objects := stStored.objects.insert boundTid.toObjId (.tcb { boundTcb with priority := ⟨priority⟩ }) }
        (determineTargetCore { stStored with objects := stStored.objects.insert boundTid.toObjId (.tcb { boundTcb with priority := ⟨priority⟩ }) } boundTid)
        boundTid
        (match boundTcb.pipBoost with
          | none => ⟨priority⟩
          | some boostPri => ⟨Nat.max priority boostPri.val⟩)
        hInvW hMem
      split
      · rename_i currentTcb hCur
        have hCEq : { boundTcb with priority := ⟨priority⟩ } = currentTcb :=
          Option.some.inj (hSomeW.symm.trans hCur)
        subst hCEq
        exact domainAlignStep_preserves_ipcInvariantFull _ boundTid _ domain
          hObjInvW hInvR hAtW
      · exact hInvR
    · rw [if_neg hMem]
      split
      · rename_i currentTcb hCur
        have hCEq : { boundTcb with priority := ⟨priority⟩ } = currentTcb :=
          Option.some.inj (hSomeW.symm.trans hCur)
        subst hCEq
        exact domainAlignStep_preserves_ipcInvariantFull _ boundTid _ domain
          hObjInvW hInvW hAtW
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
          have hInvCleaned := purgeReplenishmentOnCore_preserves_ipcInvariantFull st
            (SchedContextOps.schedContextReplenishHome st sc) ⟨vScId.val.toNat⟩ hInv
          have hInvStored := storeObject_schedContextContentUpdate_preserves_ipcInvariantFull
            (SchedContextOps.purgeReplenishmentOnCore st
              (SchedContextOps.schedContextReplenishHome st sc) ⟨vScId.val.toNat⟩)
            stStored vScId.val sc _ hObjInv hInvCleaned hScRaw hStore rfl
          have hObjInvStored := storeObject_preserves_objects_invExt
            (SchedContextOps.purgeReplenishmentOnCore st
              (SchedContextOps.schedContextReplenishHome st sc) ⟨vScId.val.toNat⟩)
            stStored vScId.val _ hObjInv hStore
          split at hStep
          · cases hStep
            exact hInvStored
          · rename_i boundTid hBound
            split at hStep
            · rename_i boundTcb hBT
              cases hStep
              exact schedContextConfigureBoundPropagate_preserves_ipcInvariantFull stStored
                boundTid boundTcb priority domain hObjInvStored hInvStored hBT
            · cases hStep
              exact hInvStored
      · contradiction
    · contradiction

-- ============================================================================
-- §11  Sched-context binding arms (`.schedContextBind`, `.schedContextUnbind`)
-- ============================================================================

/-- Every thread on a run queue or in a `current` slot is in a
passive-idle-allowed state.  Scheduler hygiene makes this a fact of every
reachable state (a scheduled thread is `.ready`); it enters the binding arms
as a *pre*-state hypothesis because an unbind demotes the thread it
deschedules to `.unbound`, transferring its `passiveServerIdle` exemption
from "scheduled" to "idle-allowed". -/
def scheduledThreadsIdleAllowed (st : SystemState) : Prop :=
  ∀ (c : CoreId) (t : SeLe4n.ThreadId) (tcb : TCB),
    st.objects[t.toObjId]? = some (.tcb tcb) →
    (t ∈ st.scheduler.runQueueOnCore c ∨ st.scheduler.currentOnCore c = some t) →
    passiveServerIdleAllowed tcb.ipcState

/-- The scheduled form subsumes the queued form the affinity arm consumes. -/
theorem unboundQueuedThreadsIdleAllowed_of_scheduled {st : SystemState}
    (h : scheduledThreadsIdleAllowed st) : unboundQueuedThreadsIdleAllowed st :=
  fun c t tcb hT _ hQ => h c t tcb hT (Or.inl hQ)

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
    (hPassive : passiveServerIdleFrame st st') :
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
  have hAgree : donationReadAgreement st st' := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro oid tx hx
      obtain ⟨ty, hy, h1, h2, h3, h4, h5, h6, h7, h8, _⟩ := hBwd oid tx hx
      exact ⟨ty, hy, h1, h2, h3, h4, h5, h6, h7, h8⟩
    · intro oid ty hy
      by_cases hT : oid = tid.toObjId
      · rw [hT, hPreT] at hy
        obtain rfl : tcb = ty := by
          simpa only [Option.some.injEq, KernelObject.tcb.injEq] using hy
        exact ⟨tcb', by rw [hT]; exact hAtT, hIpc, hMsg, hNext, hPrev, hPPrev,
          hBudget, hReply, hStash⟩
      · by_cases hS : oid = scId.toObjId
        · rw [hS, hPreS] at hy
          exact absurd (Option.some.inj hy) (fun h => KernelObject.noConfusion h)
        · exact ⟨ty, by rw [hFrame oid hT hS]; exact hy,
            rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · intro oid k hkT hkS
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
  refine ipcInvariantFull_of_donationReadAgreement st st' hInv hAgree ?_ ?_ ?_ ?_ ?_
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
  · exact passiveServerIdle_of_frame hPassive hInv.passiveServerIdle
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
  · rename_i sc hSc
    split at hStep
    · contradiction
    · rename_i hFreeGuard
      split at hStep
      · rename_i tcb hT
        split at hStep
        · contradiction
        · split at hStep
          · rename_i hUnbound
            dsimp only [] at hStep
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
              vScId.val (.schedContext { sc with boundThread := some vThreadId.val }) hObjInv
            have hAtS2 : (( { st with objects := (st.objects.insert vScId.val (.schedContext { sc with boundThread := some vThreadId.val })).insert vThreadId.val.toObjId (.tcb { tcb with schedContextBinding := .bound ⟨vScId.val.toNat⟩, priority := sc.priority }) } : SystemState)).objects[(⟨vScId.val.toNat⟩ : SeLe4n.SchedContextId).toObjId]?
                = some (.schedContext { sc with boundThread := some vThreadId.val }) := by
              have h1 : (st.objects.insert vScId.val (.schedContext { sc with boundThread := some vThreadId.val }))[(⟨vScId.val.toNat⟩ : SeLe4n.SchedContextId).toObjId]? = some (.schedContext { sc with boundThread := some vThreadId.val }) := by
                simp only [RHTable_getElem?_eq_get?]
                exact RobinHood.RHTable.getElem?_insert_self st.objects _ _ hObjInv
              simp only [RHTable_getElem?_eq_get?] at h1 ⊢
              rw [RobinHood.RHTable.getElem?_insert_ne _ vThreadId.val.toObjId _ _
                (by simp only [beq_iff_eq]; exact hNeIds) hObjInv1]
              exact h1
            have hAtT2 : (( { st with objects := (st.objects.insert vScId.val (.schedContext { sc with boundThread := some vThreadId.val })).insert vThreadId.val.toObjId (.tcb { tcb with schedContextBinding := .bound ⟨vScId.val.toNat⟩, priority := sc.priority }) } : SystemState)).objects[vThreadId.val.toObjId]?
                = some (.tcb { tcb with schedContextBinding := .bound ⟨vScId.val.toNat⟩, priority := sc.priority }) := by
              simp only [RHTable_getElem?_eq_get?]
              exact RobinHood.RHTable.getElem?_insert_self _ _ _ hObjInv1
            have hFrame2 : ∀ oid : SeLe4n.ObjId, oid ≠ vThreadId.val.toObjId →
                oid ≠ (⟨vScId.val.toNat⟩ : SeLe4n.SchedContextId).toObjId →
                (( { st with objects := (st.objects.insert vScId.val (.schedContext { sc with boundThread := some vThreadId.val })).insert vThreadId.val.toObjId (.tcb { tcb with schedContextBinding := .bound ⟨vScId.val.toNat⟩, priority := sc.priority }) } : SystemState)).objects[oid]?
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
            have hPassive2 : passiveServerIdleFrame st
                ({ st with objects := (st.objects.insert vScId.val (.schedContext { sc with boundThread := some vThreadId.val })).insert vThreadId.val.toObjId (.tcb { tcb with schedContextBinding := .bound ⟨vScId.val.toNat⟩, priority := sc.priority }) } : SystemState) := by
              refine ⟨fun t tcb'' hT'' hU hQ hC _ => ?_⟩
              by_cases ht : t.toObjId = vThreadId.val.toObjId
              · rw [ht, hAtT2] at hT''
                obtain rfl : { tcb with schedContextBinding := SchedContextBinding.bound ⟨vScId.val.toNat⟩, priority := sc.priority } = tcb'' := by
                  simpa only [Option.some.injEq, KernelObject.tcb.injEq] using hT''
                cases hU
              · by_cases hs : t.toObjId = (⟨vScId.val.toNat⟩ : SeLe4n.SchedContextId).toObjId
                · rw [hs, hAtS2] at hT''
                  exact absurd (Option.some.inj hT'') (fun hx => KernelObject.noConfusion hx)
                · rw [hFrame2 _ ht hs] at hT''
                  exact ⟨tcb'', hT'', hU, hQ, hC, rfl⟩
            have hInv2 := ipcInvariantFull_of_schedBindingRewrite st _ vThreadId.val
              ⟨vScId.val.toNat⟩ tcb
              { tcb with schedContextBinding := .bound ⟨vScId.val.toNat⟩, priority := sc.priority }
              sc { sc with boundThread := some vThreadId.val }
              hInv hPreT hAtT2 hPreS hAtS2 hFrame2
              rfl rfl rfl rfl rfl rfl rfl rfl
              (Or.inl ⟨hUnbound, rfl, hFree, rfl, hNotOwner, hNoOther⟩)
              hPassive2
            split
            · rename_i hMem
              refine ipcInvariantFull_of_getElem_eq
                (s1 := { st with objects := (st.objects.insert vScId.val (.schedContext { sc with boundThread := some vThreadId.val })).insert vThreadId.val.toObjId (.tcb { tcb with schedContextBinding := .bound ⟨vScId.val.toNat⟩, priority := sc.priority }) })
                (fun oid => rfl) ?_ hInv2
              refine passiveServerIdle_of_frame
                (passiveServerIdleFrame_of_backward_monotone
                  (st := { st with objects := (st.objects.insert vScId.val (.schedContext { sc with boundThread := some vThreadId.val })).insert vThreadId.val.toObjId (.tcb { tcb with schedContextBinding := .bound ⟨vScId.val.toNat⟩, priority := sc.priority }) })
                  (fun t tcb'' h => ⟨tcb'', h, rfl, rfl⟩)
                  (fun y hy => ?_) (by simp))
                hInv2.passiveServerIdle
              by_cases hcc : determineTargetCore { st with objects := (st.objects.insert vScId.val (.schedContext { sc with boundThread := some vThreadId.val })).insert vThreadId.val.toObjId (.tcb { tcb with schedContextBinding := .bound ⟨vScId.val.toNat⟩, priority := sc.priority }) } vThreadId.val = Concurrency.bootCoreId
              · rw [show (Concurrency.bootCoreId : CoreId) = determineTargetCore { st with objects := (st.objects.insert vScId.val (.schedContext { sc with boundThread := some vThreadId.val })).insert vThreadId.val.toObjId (.tcb { tcb with schedContextBinding := .bound ⟨vScId.val.toNat⟩, priority := sc.priority }) } vThreadId.val from hcc.symm]
                rw [SchedulerState.setRunQueueOnCore_runQueueOnCore_self]
                rw [RunQueue.mem_insert, RunQueue.mem_remove]
                by_cases hEq : y = vThreadId.val
                · exact Or.inr hEq
                · exact Or.inl ⟨by rw [show (determineTargetCore { st with objects := (st.objects.insert vScId.val (.schedContext { sc with boundThread := some vThreadId.val })).insert vThreadId.val.toObjId (.tcb { tcb with schedContextBinding := .bound ⟨vScId.val.toNat⟩, priority := sc.priority }) } vThreadId.val : CoreId) = Concurrency.bootCoreId from hcc]; exact hy, hEq⟩
              · rw [SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ _ _ _
                  (fun h => hcc h)]
                exact hy
            · rename_i hMem
              exact ipcInvariantFull_of_getElem_eq
                (s1 := { st with objects := (st.objects.insert vScId.val (.schedContext { sc with boundThread := some vThreadId.val })).insert vThreadId.val.toObjId (.tcb { tcb with schedContextBinding := .bound ⟨vScId.val.toNat⟩, priority := sc.priority }) })
                (fun oid => rfl)
                (passiveServerIdle_of_frame
                  (passiveServerIdleFrame_of_backward_monotone
                    (st := { st with objects := (st.objects.insert vScId.val (.schedContext { sc with boundThread := some vThreadId.val })).insert vThreadId.val.toObjId (.tcb { tcb with schedContextBinding := .bound ⟨vScId.val.toNat⟩, priority := sc.priority }) })
                    (fun t tcb'' h => ⟨tcb'', h, rfl, rfl⟩)
                    (fun y hy => hy) rfl)
                  hInv2.passiveServerIdle)
                hInv2
          · contradiction
      · contradiction
  · contradiction

-- ============================================================================
-- §12  The scheduler switch chain (shared by the unbind, suspend and resume
--      arms' scheduling points)
-- ============================================================================

/-- `preemptCurrentOnCore` preserves the whole bundle: its one object write
saves the preempted thread's register context — a field no conjunct reads —
and its one queue write re-enqueues that thread (membership grows). -/
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
      · rename_i prevTcb hPrevTcb
        have hPreRaw := (SystemState.getTcb?_eq_some_iff st prevTid prevTcb).mp hPrevTcb
        have hAt := insertObjects_getElem_self st prevTid.toObjId
          (.tcb { prevTcb with registerContext := st.machine.regsOnCore c }) hObjInv
        refine ipcInvariantFull_of_tcbFieldUpdate st _ prevTid.toObjId prevTcb
          { prevTcb with registerContext := st.machine.regsOnCore c }
          hInv hPreRaw ?_ ?_ rfl rfl rfl rfl rfl rfl rfl rfl rfl ?_
        · exact hAt
        · exact fun oid hNe => insertObjects_getElem_ne st prevTid.toObjId _ oid hNe hObjInv
        · refine passiveServerIdleFrame_of_backward_monotone (st := st)
            (fun t tcb'' h => ?_) (fun y hy => ?_) (by simp)
          · by_cases ht : t.toObjId = prevTid.toObjId
            · rw [ht, hAt] at h
              obtain rfl : { prevTcb with registerContext := st.machine.regsOnCore c } = tcb'' := by
                simpa only [Option.some.injEq, KernelObject.tcb.injEq] using h
              exact ⟨prevTcb, by rw [ht]; exact hPreRaw, rfl, rfl⟩
            · rw [insertObjects_getElem_ne st prevTid.toObjId _ _ ht hObjInv] at h
              exact ⟨tcb'', h, rfl, rfl⟩
          · by_cases hcc : c = Concurrency.bootCoreId
            · subst hcc
              rw [SchedulerState.setRunQueueOnCore_runQueueOnCore_self, RunQueue.mem_insert]
              exact Or.inl hy
            · rw [SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ _ _ _ hcc]
              exact hy
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
  rw [if_neg hne, hNo]

/-- The preempted `current` thread is on the core's queue afterwards. -/
theorem preemptCurrentOnCore_prev_mem (st : SystemState) (c : CoreId)
    (incoming prev : SeLe4n.ThreadId) (ptcb : TCB)
    (hCur : st.scheduler.currentOnCore c = some prev)
    (hne : ¬(prev == incoming) = true)
    (hPT : st.getTcb? prev = some ptcb) :
    prev ∈ (preemptCurrentOnCore st c incoming).scheduler.runQueueOnCore c := by
  unfold preemptCurrentOnCore
  rw [hCur]
  dsimp only []
  rw [if_neg hne, hPT]
  dsimp only []
  rw [SchedulerState.setRunQueueOnCore_runQueueOnCore_self]
  exact (RunQueue.mem_insert _ _ _ _).mpr (Or.inr rfl)

/-- `switchToThreadOnCore` preserves the whole bundle.  Objects move only in
the preempt stage; the queue loses the switched-in thread — which becomes
`current` — and gains the preempted one; every other thread's scheduling
placement is untouched. -/
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
      refine ipcInvariantFull_of_getElem_eq
        (s1 := preemptCurrentOnCore st c tid)
        (fun oid => by
          simp only [restoreIncomingContextOnCoreUnlessCurrent_objects]) ?_ hP
      intro t tcb'' hT hU hQ hC
      simp only [restoreIncomingContextOnCoreUnlessCurrent_objects] at hT
      simp only [restoreIncomingContextOnCoreUnlessCurrent_scheduler] at hQ hC
      by_cases hcc : c = Concurrency.bootCoreId
      · subst hcc
        rw [SchedulerState.setCurrentOnCore_currentOnCore_self] at hC
        have hTne : t ≠ tid := fun h => hC (by rw [h])
        rw [SchedulerState.setCurrentOnCore_runQueueOnCore,
          SchedulerState.setRunQueueOnCore_runQueueOnCore_self,
          RunQueue.mem_remove] at hQ
        have hQpre : t ∉ (preemptCurrentOnCore st Concurrency.bootCoreId
            tid).scheduler.runQueueOnCore Concurrency.bootCoreId :=
          fun hmem => hQ ⟨hmem, hTne⟩
        have hCpre : (preemptCurrentOnCore st Concurrency.bootCoreId
            tid).scheduler.currentOnCore Concurrency.bootCoreId ≠ some t := by
          rw [preemptCurrentOnCore_currentOnCore]
          cases hCur : st.scheduler.currentOnCore Concurrency.bootCoreId with
          | none => simp
          | some prev =>
            intro hEq
            obtain rfl : prev = t := Option.some.inj hEq
            by_cases hne : (prev == tid) = true
            · exact hTne (by simpa using hne)
            · cases hPT : st.getTcb? prev with
              | some ptcb =>
                exact hQpre (preemptCurrentOnCore_prev_mem st _ tid prev ptcb hCur hne hPT)
              | none =>
                rw [preemptCurrentOnCore_noop_of_prev_no_tcb st _ tid prev hCur hne hPT] at hT
                have := (SystemState.getTcb?_eq_some_iff st prev tcb'').mpr hT
                rw [hPT] at this
                cases this
        exact hP.passiveServerIdle t tcb'' hT hU hQpre hCpre
      · rw [SchedulerState.setCurrentOnCore_runQueueOnCore,
          SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ _ _ _ hcc] at hQ
        rw [SchedulerState.setCurrentOnCore_currentOnCore_ne _ _ _ _ hcc] at hC
        exact hP.passiveServerIdle t tcb'' hT hU hQ hC
    · contradiction
  · contradiction

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
  · cases hStep
    exact hInv
  · split at hStep
    · exact switchToThreadOnCore_preserves_ipcInvariantFull st c _ st' hObjInv hInv hStep
    · cases hStep
      exact hInv

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
  have hAgree : donationReadAgreement st
      { st with objects := st.objects.insert scObj (.schedContext sc') } := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro oid tx hx
      exact ⟨tx, (hTcbEq oid tx).mp hx, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · intro oid ty hy
      exact ⟨ty, (hTcbEq oid ty).mpr hy, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · intro oid k hkT hkS
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
  refine ipcInvariantFull_of_donationReadAgreement st _ hInv hAgree ?_ ?_ ?_ ?_ ?_
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
  · refine passiveServerIdle_of_frame
      (passiveServerIdleFrame_of_backward
        (fun t tcb'' h => ⟨tcb'', (hTcbEq _ _).mp h, rfl, rfl⟩) rfl)
      hInv.passiveServerIdle
  · intro t1 t2 tcb1 tcb2 s0 h1 h2 hNe12 hS1 hS2
    exact hInv.donationBudgetTransfer t1 t2 tcb1 tcb2 s0
      ((hTcbEq _ _).mp h1) ((hTcbEq _ _).mp h2) hNe12 hS1 hS2
  · intro t1 t2 tcb1 tcb2 s1 s2 owner h1 h2 hB1 hB2
    exact hInv.donationOwnerUnique t1 t2 tcb1 tcb2 s1 s2 owner
      ((hTcbEq _ _).mp h1) ((hTcbEq _ _).mp h2) hB1 hB2

/-- The all-cores replenishment sweep preserves the whole bundle. -/
theorem purgeReplenishmentFromAllCores_preserves_ipcInvariantFull (st : SystemState)
    (scId : SeLe4n.SchedContextId)
    (hInv : ipcInvariantFull st) :
    ipcInvariantFull (SchedContextOps.purgeReplenishmentFromAllCores st scId) := by
  unfold SchedContextOps.purgeReplenishmentFromAllCores
  generalize SeLe4n.Kernel.Concurrency.allCores = l
  induction l generalizing st with
  | nil => exact hInv
  | cons c cs ih =>
      exact ih _ (purgeReplenishmentOnCore_preserves_ipcInvariantFull st c scId hInv)

/-- The object-writing tail of the unbind — bidirectional clear, replenish
purge, index write — over any scheduler-stage state `stA` that still holds
the pre-state objects.  The binding-rewrite lever carries the clear; the
demoted thread's `passiveServerIdle` exemption is the `hAllowedIpc` fact. -/
private theorem schedContextUnbindTail_preserves_ipcInvariantFull
    (stA : SystemState) (scObj : SeLe4n.ObjId) (tid : SeLe4n.ThreadId)
    (sc : SeLe4n.Kernel.SchedContext) (tcb : TCB)
    (c : CoreId) (scIdT : SeLe4n.SchedContextId)
    (idx : RobinHood.RHTable SeLe4n.SchedContextId (List SeLe4n.ThreadId))
    (hObjInvA : stA.objects.invExt) (hInvA : ipcInvariantFull stA)
    (hPreS : stA.objects[scObj]? = some (.schedContext sc))
    (hPreT : stA.objects[tid.toObjId]? = some (.tcb tcb))
    (hBoundEq : sc.boundThread = some tid)
    (hAllowedIpc : passiveServerIdleAllowed tcb.ipcState) :
    ipcInvariantFull { SchedContextOps.purgeReplenishmentOnCore { { stA with objects := (stA.objects.insert scObj (.schedContext { sc with boundThread := none, isActive := false })) } with objects := ((stA.objects.insert scObj (.schedContext { sc with boundThread := none, isActive := false }))).insert tid.toObjId (.tcb { tcb with schedContextBinding := .unbound }) } c scIdT with scThreadIndex := idx } := by
  have hScObjEq : (⟨scObj.toNat⟩ : SeLe4n.SchedContextId).toObjId = scObj := rfl
  have hObjInv2 := RobinHood.RHTable.insert_preserves_invExt stA.objects scObj
    (.schedContext { sc with boundThread := none, isActive := false }) hObjInvA
  have hNeIds : tid.toObjId ≠ scObj := by
    intro h
    rw [h, hPreS] at hPreT
    exact absurd (Option.some.inj hPreT) (fun hx => KernelObject.noConfusion hx)
  have hAtS3 : (({ { stA with objects := (stA.objects.insert scObj (.schedContext { sc with boundThread := none, isActive := false })) } with objects := ((stA.objects.insert scObj (.schedContext { sc with boundThread := none, isActive := false }))).insert tid.toObjId (.tcb { tcb with schedContextBinding := .unbound }) } : SystemState)).objects[scObj]? = some (.schedContext { sc with boundThread := none, isActive := false }) := by
    simp only [RHTable_getElem?_eq_get?]
    rw [RobinHood.RHTable.getElem?_insert_ne _ tid.toObjId scObj _
      (by simp only [beq_iff_eq]; exact hNeIds) hObjInv2]
    exact RobinHood.RHTable.getElem?_insert_self stA.objects scObj _ hObjInvA
  have hAtT3 : (({ { stA with objects := (stA.objects.insert scObj (.schedContext { sc with boundThread := none, isActive := false })) } with objects := ((stA.objects.insert scObj (.schedContext { sc with boundThread := none, isActive := false }))).insert tid.toObjId (.tcb { tcb with schedContextBinding := .unbound }) } : SystemState)).objects[tid.toObjId]? = some (.tcb { tcb with schedContextBinding := .unbound }) := by
    simp only [RHTable_getElem?_eq_get?]
    exact RobinHood.RHTable.getElem?_insert_self _ _ _ hObjInv2
  have hFrame3 : ∀ oid : SeLe4n.ObjId, oid ≠ tid.toObjId → oid ≠ scObj →
      (({ { stA with objects := (stA.objects.insert scObj (.schedContext { sc with boundThread := none, isActive := false })) } with objects := ((stA.objects.insert scObj (.schedContext { sc with boundThread := none, isActive := false }))).insert tid.toObjId (.tcb { tcb with schedContextBinding := .unbound }) } : SystemState)).objects[oid]? = stA.objects[oid]? := by
    intro oid hNeT hNeS
    simp only [RHTable_getElem?_eq_get?]
    rw [RobinHood.RHTable.getElem?_insert_ne _ tid.toObjId oid _
      (by simp only [beq_iff_eq]; exact fun h => hNeT h.symm) hObjInv2]
    rw [RobinHood.RHTable.getElem?_insert_ne stA.objects scObj oid _
      (by simp only [beq_iff_eq]; exact fun h => hNeS h.symm) hObjInvA]
  have hPassive3 : passiveServerIdleFrame stA
      ({ { stA with objects := (stA.objects.insert scObj (.schedContext { sc with boundThread := none, isActive := false })) } with objects := ((stA.objects.insert scObj (.schedContext { sc with boundThread := none, isActive := false }))).insert tid.toObjId (.tcb { tcb with schedContextBinding := .unbound }) } : SystemState) := by
    refine ⟨fun t tcb'' hT'' hU hQ hC hNA => ?_⟩
    by_cases ht : t.toObjId = tid.toObjId
    · rw [ht, hAtT3] at hT''
      obtain rfl : { tcb with schedContextBinding := SchedContextBinding.unbound } = tcb'' := by
        simpa only [Option.some.injEq, KernelObject.tcb.injEq] using hT''
      exact absurd hAllowedIpc hNA
    · by_cases hs : t.toObjId = scObj
      · rw [hs, hAtS3] at hT''
        exact absurd (Option.some.inj hT'') (fun hx => KernelObject.noConfusion hx)
      · rw [hFrame3 _ ht hs] at hT''
        exact ⟨tcb'', hT'', hU, hQ, hC, rfl⟩
  have hPreS' : stA.objects[(⟨scObj.toNat⟩ : SeLe4n.SchedContextId).toObjId]?
      = some (.schedContext sc) := hPreS
  have hInv3 := ipcInvariantFull_of_schedBindingRewrite stA _ tid ⟨scObj.toNat⟩ tcb
    { tcb with schedContextBinding := .unbound }
    sc { sc with boundThread := none, isActive := false }
    hInvA hPreT (hScObjEq ▸ hAtT3) hPreS' (hScObjEq ▸ hAtS3)
    (fun oid hT hS => hFrame3 oid hT (hScObjEq ▸ hS))
    rfl rfl rfl rfl rfl rfl rfl rfl
    (Or.inr ⟨rfl, hBoundEq, rfl⟩)
    hPassive3
  have hInv4 := purgeReplenishmentOnCore_preserves_ipcInvariantFull _ c scIdT hInv3
  refine ipcInvariantFull_of_objects_scheduler_eq ?_ ?_ hInv4
  · rfl
  · rfl

/-- The scheduler stage of the unbind — current-clear plus optional re-bucket
— preserves the bundle: the demoted thread's exemption is the `hAllowedIpc`
fact, every other thread's boot-core placement is monotone. -/
private theorem unbindSchedulerStage_preserves_ipcInvariantFull
    (st stA : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hInv : ipcInvariantFull st)
    (hObjs : stA.objects = st.objects)
    (hTcbRaw : st.objects[tid.toObjId]? = some (.tcb tcb))
    (hAllowedIpc : passiveServerIdleAllowed tcb.ipcState)
    (hQmono : ∀ t : SeLe4n.ThreadId, t ≠ tid →
      t ∈ st.scheduler.runQueueOnCore Concurrency.bootCoreId →
      t ∈ stA.scheduler.runQueueOnCore Concurrency.bootCoreId)
    (hCimp : ∀ t : SeLe4n.ThreadId, t ≠ tid →
      stA.scheduler.currentOnCore Concurrency.bootCoreId ≠ some t →
      st.scheduler.currentOnCore Concurrency.bootCoreId ≠ some t) :
    ipcInvariantFull stA := by
  refine ipcInvariantFull_of_getElem_eq (s1 := st) (fun oid => by rw [hObjs]) ?_ hInv
  intro t tcb'' hT hU hQ hC
  rw [hObjs] at hT
  by_cases ht : t = tid
  · subst ht
    obtain rfl : tcb = tcb'' := by
      have := hTcbRaw.symm.trans hT
      simpa only [Option.some.injEq, KernelObject.tcb.injEq] using this
    exact hAllowedIpc
  · exact hInv.passiveServerIdle t tcb'' hT hU
      (fun hm => hQ (hQmono t ht hm)) (hCimp t ht hC)

/-- `.schedContextUnbind` (core transition).

`hBoundAllowed` is a genuine pre-state obligation, not bookkeeping: unbinding
a thread blocked on a send or call leaves it `.unbound` in a state
`passiveServerIdle` forbids — an unbound thread cannot hold the timeout its
blocked IPC requires.  The discipline that discharges it is "unbind only
scheduled or descheduled-idle threads"; hardening the operation itself to
refuse the remaining case is registered follow-up work, deliberately not
absorbed into this bundle. -/
theorem schedContextUnbind_preserves_ipcInvariantFull
    (st st' : SystemState) (vScId : SeLe4n.ValidObjId)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hBoundAllowed : ∀ (scX : SeLe4n.Kernel.SchedContext) (t : SeLe4n.ThreadId) (tcbX : TCB),
      st.objects[(SchedContextId.ofObjId vScId.val).toObjId]? = some (.schedContext scX) →
      scX.boundThread = some t →
      st.objects[t.toObjId]? = some (.tcb tcbX) →
      passiveServerIdleAllowed tcbX.ipcState)
    (hStep : SchedContextOps.schedContextUnbind vScId st = .ok ((), st')) :
    ipcInvariantFull st' := by
  unfold SchedContextOps.schedContextUnbind at hStep
  split at hStep
  · rename_i sc hSc
    split at hStep
    · contradiction
    · rename_i tid hBound
      split at hStep
      · rename_i tcb hTcb
        dsimp only [] at hStep
        have hScRaw := (SystemState.getSchedContext?_eq_some_iff st
          (SchedContextId.ofObjId vScId.val) sc).mp hSc
        have hTcbRaw := (SystemState.getTcb?_eq_some_iff st tid tcb).mp hTcb
        have hAllowedIpc := hBoundAllowed sc tid tcb hScRaw hBound hTcbRaw
        cases hRC : runningCoreOf? st tid with
        | some rc =>
          have hCurRC : st.scheduler.currentOnCore rc = some tid := by
            have := List.find?_some hRC
            simpa using this
          rw [hRC] at hStep
          simp only [Option.isSome_some] at hStep
          have hStage : ipcInvariantFull { st with scheduler := (st.scheduler.setCurrentOnCore rc none).setRunQueueOnCore (determineTargetCore st tid) ((((st.scheduler.setCurrentOnCore rc none).runQueueOnCore (determineTargetCore st tid)).remove tid).insert tid (effectiveRunQueuePriority { tcb with schedContextBinding := .unbound })) } := by
            refine unbindSchedulerStage_preserves_ipcInvariantFull st _ tid tcb hInv rfl
              hTcbRaw hAllowedIpc ?_ ?_
            · intro t htne hm
              by_cases hcc : determineTargetCore st tid = Concurrency.bootCoreId
              · rw [show (Concurrency.bootCoreId : CoreId) = determineTargetCore st tid
                  from hcc.symm]
                rw [SchedulerState.setRunQueueOnCore_runQueueOnCore_self,
                  RunQueue.mem_insert, RunQueue.mem_remove,
                  SchedulerState.setCurrentOnCore_runQueueOnCore]
                exact Or.inl ⟨by rw [hcc]; exact hm, htne⟩
              · rw [SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ _ _ _ hcc,
                  SchedulerState.setCurrentOnCore_runQueueOnCore]
                exact hm
            · intro t htne _
              by_cases hrb : rc = Concurrency.bootCoreId
              · rw [← hrb, hCurRC]
                exact fun h => htne (Option.some.inj h).symm
              · intro hpre
                have hA : ((st.scheduler.setCurrentOnCore rc none).setRunQueueOnCore (determineTargetCore st tid) ((((st.scheduler.setCurrentOnCore rc none).runQueueOnCore (determineTargetCore st tid)).remove tid).insert tid (effectiveRunQueuePriority { tcb with schedContextBinding := .unbound }))).currentOnCore Concurrency.bootCoreId = some t := by
                  rw [SchedulerState.setRunQueueOnCore_currentOnCore,
                    SchedulerState.setCurrentOnCore_currentOnCore_ne _ _ _ _ hrb]
                  exact hpre
                rename_i hcur
                exact hcur hA
          split at hStep
          all_goals
            cases hStep
          all_goals
            exact schedContextUnbindTail_preserves_ipcInvariantFull _ vScId.val tid sc tcb
              _ _ _ hObjInv hStage hScRaw hTcbRaw hBound hAllowedIpc
        | none =>
          rw [hRC] at hStep
          simp only [Option.isSome_none] at hStep
          split at hStep
          · rename_i hMem
            cases hStep
            have hStage : ipcInvariantFull { st with scheduler := st.scheduler.setRunQueueOnCore (determineTargetCore st tid) (((st.scheduler.runQueueOnCore (determineTargetCore st tid)).remove tid).insert tid (effectiveRunQueuePriority { tcb with schedContextBinding := .unbound })) } := by
              refine unbindSchedulerStage_preserves_ipcInvariantFull st _ tid tcb hInv rfl
                hTcbRaw hAllowedIpc ?_ ?_
              · intro t htne hm
                by_cases hcc : determineTargetCore st tid = Concurrency.bootCoreId
                · rw [show (Concurrency.bootCoreId : CoreId) = determineTargetCore st tid
                    from hcc.symm]
                  rw [SchedulerState.setRunQueueOnCore_runQueueOnCore_self,
                    RunQueue.mem_insert, RunQueue.mem_remove]
                  exact Or.inl ⟨by rw [hcc]; exact hm, htne⟩
                · rw [SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ _ _ _ hcc]
                  exact hm
              · intro t _ hcur
                intro hpre
                exact hcur (by rw [SchedulerState.setRunQueueOnCore_currentOnCore]; exact hpre)
            exact schedContextUnbindTail_preserves_ipcInvariantFull _ vScId.val tid sc tcb
              _ _ _ hObjInv hStage hScRaw hTcbRaw hBound hAllowedIpc
          · split at hStep
            · simp at *
            · cases hStep
              exact schedContextUnbindTail_preserves_ipcInvariantFull _ vScId.val tid sc tcb
                _ _ _ hObjInv
                (unbindSchedulerStage_preserves_ipcInvariantFull st st tid tcb hInv rfl
                  hTcbRaw hAllowedIpc (fun t _ hm => hm) (fun t _ hcur => hcur))
                hScRaw hTcbRaw hBound hAllowedIpc
      · rename_i hTcbNone
        dsimp only [] at hStep
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
          vScId.val sc { sc with boundThread := none, isActive := false }
          hObjInv hInv hScRaw hNoRef
        have hInv2 := purgeReplenishmentFromAllCores_preserves_ipcInvariantFull _ ⟨vScId.val.toNat⟩ hInv1
        refine ipcInvariantFull_of_objects_scheduler_eq ?_ ?_ hInv2
        · rfl
        · rfl
  · contradiction

/-- `.schedContextUnbind` (dispatch arm): the per-core wrapper adds the
preemption seam, which §12 covers. -/
theorem schedContextUnbindOnCore_preserves_ipcInvariantFull
    (st st' : SystemState) (vScId : SeLe4n.ValidObjId) (ec : CoreId)
    (sgi : Option (CoreId × Concurrency.SgiKind))
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hBoundAllowed : ∀ (scX : SeLe4n.Kernel.SchedContext) (t : SeLe4n.ThreadId) (tcbX : TCB),
      st.objects[(SchedContextId.ofObjId vScId.val).toObjId]? = some (.schedContext scX) →
      scX.boundThread = some t →
      st.objects[t.toObjId]? = some (.tcb tcbX) →
      passiveServerIdleAllowed tcbX.ipcState)
    (hObjInvPreserved : ∀ stMid, SchedContextOps.schedContextUnbind vScId st = .ok ((), stMid) →
      stMid.objects.invExt)
    (hStep : SchedContextOps.schedContextUnbindOnCore vScId ec st = .ok (st', sgi)) :
    ipcInvariantFull st' := by
  unfold SchedContextOps.schedContextUnbindOnCore at hStep
  dsimp only [] at hStep
  split at hStep
  · contradiction
  · rename_i stMid hUnbind
    exact priorityRescheduleOnCore_preserves_ipcInvariantFull stMid _ ec true st' sgi
      (hObjInvPreserved stMid hUnbind)
      (schedContextUnbind_preserves_ipcInvariantFull st stMid vScId hObjInv hInv
        hBoundAllowed hUnbind)
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
    (hNe : ∀ oid : SeLe4n.ObjId, oid ≠ key → st'.objects[oid]? = st.objects[oid]?)
    (hSched : st'.scheduler = st.scheduler) :
    ipcInvariantFull st' := by
  have hView := ipcReadViewAgreement.of_single_inert_write hNe
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
      exact absurd (Option.some.inj hCn) (fun hx => KernelObject.noConfusion hx)
    · rw [hNe _ hK] at hCn
      exact hInv.badgeWellFormed.2 oid cn slot cap badge hCn hLk hB
  exact ipcInvariantFull_of_readViewAgreement hView
    (passiveServerIdle_of_frame (passiveServerIdleFrame_of_backward hBack hSched)
      hInv.passiveServerIdle)
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
                (storeObject_objects_eq st st' rootId (.vspaceRoot root') hObjInv hStep)
                (fun oid hNe =>
                  storeObject_objects_ne st st' rootId oid (.vspaceRoot root') hNe hObjInv hStep)
                (storeObject_scheduler_eq st st' rootId (.vspaceRoot root') hStep)

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
            (storeObject_objects_eq st st' rootId (.vspaceRoot root') hObjInv hStep)
            (fun oid hNe =>
              storeObject_objects_ne st st' rootId oid (.vspaceRoot root') hNe hObjInv hStep)
            (storeObject_scheduler_eq st st' rootId (.vspaceRoot root') hStep)

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
      refine ipcInvariantFull_of_objects_scheduler_eq ?_ ?_ hB
      · rfl
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
        exact ipcInvariantFull_of_objects_scheduler_eq
          (Architecture.tlbShootdownBroadcastCoalescing_frame stB ec _ _).1
          (Architecture.tlbShootdownBroadcastCoalescing_frame stB ec _ _).2.1 hB
      · simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
        subst hStep
        exact hB

/-- The per-core TLB drain and fill are `perCoreTlb`-only. -/
private theorem tlbFillOnCore_objects_scheduler (st : SystemState) (c : CoreId)
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) :
    (Architecture.tlbFillOnCore st c asid vaddr).objects = st.objects ∧
    (Architecture.tlbFillOnCore st c asid vaddr).scheduler = st.scheduler := by
  unfold Architecture.tlbFillOnCore
  split <;> exact ⟨rfl, rfl⟩

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
      refine ipcInvariantFull_of_objects_scheduler_eq ?_ ?_ hB
      · exact (tlbFillOnCore_objects_scheduler _ _ _ _).1.trans rfl
      · exact (tlbFillOnCore_objects_scheduler _ _ _ _).2.trans rfl

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
      refine ipcInvariantFull_of_objects_scheduler_eq ?_ ?_ hB
      · rfl
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
      exact ipcInvariantFull_of_objects_scheduler_eq
        (Architecture.tlbShootdownBroadcastCoalescing_frame stB ec _ _).1
        (Architecture.tlbShootdownBroadcastCoalescing_frame stB ec _ _).2.1 hB

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
      refine ipcInvariantFull_of_objects_scheduler_eq ?_ ?_ hB
      · rfl
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
      exact ipcInvariantFull_of_objects_scheduler_eq hObjs hSched hB

-- ============================================================================
-- §14  Lifecycle retype arm (`.lifecycleRetype`)
-- ============================================================================

/-- The retype replacement object is pristine: every field an `ipcInvariantFull`
conjunct reads is at its inert value.  `objectOfKernelType` — the only
replacement builder the live `.lifecycleRetype` dispatch uses — satisfies this
by construction (`objectOfKernelType_replacementFresh`). -/
def retypeReplacementFresh : KernelObject → Prop
  | .tcb t => t.ipcState = .ready ∧ t.pendingMessage = none ∧ t.queueNext = none ∧
      t.queuePrev = none ∧ t.schedContextBinding = .unbound ∧ t.replyObject = none ∧
      t.pendingReceiveReply = none ∧ t.timeoutBudget = none
  | .endpoint ep => ep.sendQ.head = none ∧ ep.sendQ.tail = none ∧
      ep.receiveQ.head = none ∧ ep.receiveQ.tail = none
  | .notification n => n.state = .idle ∧ n.waitingThreads.val = [] ∧ n.pendingBadge = none
  | .reply r => r.caller = none
  | .cnode cn => ∀ slot : SeLe4n.Slot, cn.lookup slot = none
  | .schedContext _ => True
  | .vspaceRoot _ => True
  | .untyped _ => True

/-- The live dispatch arm's replacement builder is pristine per
`retypeReplacementFresh`, for every object kind and size hint. -/
theorem objectOfKernelType_replacementFresh (k : KernelObjectType) (n : Nat) :
    retypeReplacementFresh (objectOfKernelType k n) := by
  cases k <;>
    simp [objectOfKernelType, retypeReplacementFresh, CNode.lookup,
      UniqueSlotMap.get?, RobinHood.RHTable.getElem?_empty, Reply.empty]

/-- The retype target is detached from every structure the IPC bundle reads:
nothing in the pre-state references `target` — no blocked thread names it as
its endpoint, no queue link, queue boundary, reply link or stash points at it,
it is not a live SchedContext, and if it holds a TCB that thread is fully
dequeued, undonated, unlinked and in an allowed passive state.  These are
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
  tcbAllowedState : ∀ t : TCB, st.objects[target]? = some (.tcb t) →
    passiveServerIdleAllowed t.ipcState
  tcbNotDonated : ∀ t : TCB, st.objects[target]? = some (.tcb t) →
    ∀ scId owner, t.schedContextBinding ≠ .donated scId owner
  tcbNotWaiter : ∀ t : TCB, st.objects[target]? = some (.tcb t) →
    ∀ (oid : SeLe4n.ObjId) (n : Notification), st.objects[oid]? = some (.notification n) →
    t.tid ∉ n.waitingThreads.val
  tcbDescheduled : ∀ t : TCB, st.objects[target]? = some (.tcb t) →
    ∀ c : CoreId, (st.scheduler.runQueueOnCore c).contains t.tid = false ∧
      st.scheduler.currentOnCore c ≠ some t.tid
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

/-- At-target lookup of a post-state kind pins the replacement object. -/
private theorem retypeWrite_at_target {st' : SystemState} {target : SeLe4n.ObjId}
    {newObj o : KernelObject}
    (hAt : st'.objects[target]? = some newObj)
    (hT : st'.objects[target]? = some o) : newObj = o :=
  Option.some.inj ((hAt.symm.trans hT))

private theorem retypeWrite_allPendingMessagesBounded
    {st st' : SystemState} {target : SeLe4n.ObjId} {newObj : KernelObject}
    (hAt : st'.objects[target]? = some newObj)
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
    (hAt : st'.objects[target]? = some newObj)
    (hNe : ∀ oid : SeLe4n.ObjId, oid ≠ target → st'.objects[oid]? = st.objects[oid]?)
    (hFresh : retypeReplacementFresh newObj)
    (hInv : notificationBadgesWellFormed st) :
    notificationBadgesWellFormed st' := by
  intro oid ntfn badge hObj hPB
  by_cases hK : oid = target
  · rw [hK] at hObj
    obtain rfl : newObj = .notification ntfn := retypeWrite_at_target hAt hObj
    obtain ⟨-, -, hPBn⟩ := hFresh
    rw [hPBn] at hPB
    cases hPB
  · rw [hNe _ hK] at hObj
    exact hInv oid ntfn badge hObj hPB

private theorem retypeWrite_capabilityBadgesWellFormed
    {st st' : SystemState} {target : SeLe4n.ObjId} {newObj : KernelObject}
    (hAt : st'.objects[target]? = some newObj)
    (hNe : ∀ oid : SeLe4n.ObjId, oid ≠ target → st'.objects[oid]? = st.objects[oid]?)
    (hFresh : retypeReplacementFresh newObj)
    (hInv : capabilityBadgesWellFormed st) :
    capabilityBadgesWellFormed st' := by
  intro oid cn slot cap badge hObj hLk hB
  by_cases hK : oid = target
  · rw [hK] at hObj
    obtain rfl : newObj = .cnode cn := retypeWrite_at_target hAt hObj
    rw [hFresh slot] at hLk
    cases hLk
  · rw [hNe _ hK] at hObj
    exact hInv oid cn slot cap badge hObj hLk hB

private theorem retypeWrite_ipcInvariant
    {st st' : SystemState} {target : SeLe4n.ObjId} {newObj : KernelObject}
    (hAt : st'.objects[target]? = some newObj)
    (hNe : ∀ oid : SeLe4n.ObjId, oid ≠ target → st'.objects[oid]? = st.objects[oid]?)
    (hFresh : retypeReplacementFresh newObj)
    (hInv : ipcInvariant st) :
    ipcInvariant st' := by
  intro oid ntfn hObj
  by_cases hK : oid = target
  · rw [hK] at hObj
    obtain rfl : newObj = .notification ntfn := retypeWrite_at_target hAt hObj
    obtain ⟨hState, hWT, hPB⟩ := hFresh
    show notificationQueueWellFormed ntfn
    unfold notificationQueueWellFormed
    rw [hState]
    exact ⟨hWT, hPB⟩
  · rw [hNe _ hK] at hObj
    exact hInv oid ntfn hObj

private theorem retypeWrite_blockedThreadsPendingMessageConsistent
    {st st' : SystemState} {target : SeLe4n.ObjId} {newObj : KernelObject}
    (hAt : st'.objects[target]? = some newObj)
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
    (hAt : st'.objects[target]? = some newObj)
    (hNe : ∀ oid : SeLe4n.ObjId, oid ≠ target → st'.objects[oid]? = st.objects[oid]?)
    (hFresh : retypeReplacementFresh newObj)
    (hDet : retypeTargetDetached st target)
    (hInv : blockedThreadTimeoutConsistent st) :
    blockedThreadTimeoutConsistent st' := by
  intro tid tcb scId hT hTB
  by_cases hK : tid.toObjId = target
  · rw [hK] at hT
    obtain rfl : newObj = .tcb tcb := retypeWrite_at_target hAt hT
    obtain ⟨-, -, -, -, -, -, -, hTBn⟩ := hFresh
    rw [hTBn] at hTB
    cases hTB
  · rw [hNe _ hK] at hT
    obtain ⟨⟨sc, hSc⟩, hBlk⟩ := hInv tid tcb scId hT hTB
    refine ⟨⟨sc, ?_⟩, hBlk⟩
    have hneT : scId.toObjId ≠ target := fun hEq => hDet.notSc sc (hEq ▸ hSc)
    rw [hNe _ hneT]
    exact hSc

private theorem retypeWrite_donationChainAcyclic
    {st st' : SystemState} {target : SeLe4n.ObjId} {newObj : KernelObject}
    (hAt : st'.objects[target]? = some newObj)
    (hNe : ∀ oid : SeLe4n.ObjId, oid ≠ target → st'.objects[oid]? = st.objects[oid]?)
    (hFresh : retypeReplacementFresh newObj)
    (hInv : donationChainAcyclic st) :
    donationChainAcyclic st' := by
  intro tid1 tid2 tcb1 tcb2 scId1 scId2 h1 h2 hB1 hB2
  by_cases hK1 : tid1.toObjId = target
  · rw [hK1] at h1
    obtain rfl : newObj = .tcb tcb1 := retypeWrite_at_target hAt h1
    obtain ⟨-, -, -, -, hSB, -⟩ := hFresh
    rw [hSB] at hB1
    cases hB1
  · by_cases hK2 : tid2.toObjId = target
    · rw [hK2] at h2
      obtain rfl : newObj = .tcb tcb2 := retypeWrite_at_target hAt h2
      obtain ⟨-, -, -, -, hSB, -⟩ := hFresh
      rw [hSB] at hB2
      cases hB2
    · rw [hNe _ hK1] at h1
      rw [hNe _ hK2] at h2
      exact hInv tid1 tid2 tcb1 tcb2 scId1 scId2 h1 h2 hB1 hB2

private theorem retypeWrite_donationOwnerUnique
    {st st' : SystemState} {target : SeLe4n.ObjId} {newObj : KernelObject}
    (hAt : st'.objects[target]? = some newObj)
    (hNe : ∀ oid : SeLe4n.ObjId, oid ≠ target → st'.objects[oid]? = st.objects[oid]?)
    (hFresh : retypeReplacementFresh newObj)
    (hInv : donationOwnerUnique st) :
    donationOwnerUnique st' := by
  intro tid1 tid2 tcb1 tcb2 scId1 scId2 owner h1 h2 hB1 hB2
  by_cases hK1 : tid1.toObjId = target
  · rw [hK1] at h1
    obtain rfl : newObj = .tcb tcb1 := retypeWrite_at_target hAt h1
    obtain ⟨-, -, -, -, hSB, -⟩ := hFresh
    rw [hSB] at hB1
    cases hB1
  · by_cases hK2 : tid2.toObjId = target
    · rw [hK2] at h2
      obtain rfl : newObj = .tcb tcb2 := retypeWrite_at_target hAt h2
      obtain ⟨-, -, -, -, hSB, -⟩ := hFresh
      rw [hSB] at hB2
      cases hB2
    · rw [hNe _ hK1] at h1
      rw [hNe _ hK2] at h2
      exact hInv tid1 tid2 tcb1 tcb2 scId1 scId2 owner h1 h2 hB1 hB2

private theorem retypeWrite_donationBudgetTransfer
    {st st' : SystemState} {target : SeLe4n.ObjId} {newObj : KernelObject}
    (hAt : st'.objects[target]? = some newObj)
    (hNe : ∀ oid : SeLe4n.ObjId, oid ≠ target → st'.objects[oid]? = st.objects[oid]?)
    (hFresh : retypeReplacementFresh newObj)
    (hInv : donationBudgetTransfer st) :
    donationBudgetTransfer st' := by
  intro tid1 tid2 tcb1 tcb2 scId h1 h2 hTNe hS1 hS2
  by_cases hK1 : tid1.toObjId = target
  · rw [hK1] at h1
    obtain rfl : newObj = .tcb tcb1 := retypeWrite_at_target hAt h1
    obtain ⟨-, -, -, -, hSB, -⟩ := hFresh
    rw [hSB] at hS1
    simp [SchedContextBinding.scId?] at hS1
  · by_cases hK2 : tid2.toObjId = target
    · rw [hK2] at h2
      obtain rfl : newObj = .tcb tcb2 := retypeWrite_at_target hAt h2
      obtain ⟨-, -, -, -, hSB, -⟩ := hFresh
      rw [hSB] at hS2
      simp [SchedContextBinding.scId?] at hS2
    · rw [hNe _ hK1] at h1
      rw [hNe _ hK2] at h2
      exact hInv tid1 tid2 tcb1 tcb2 scId h1 h2 hTNe hS1 hS2

private theorem retypeWrite_blockedOnReplyHasTarget
    {st st' : SystemState} {target : SeLe4n.ObjId} {newObj : KernelObject}
    (hAt : st'.objects[target]? = some newObj)
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
    (hAt : st'.objects[target]? = some newObj)
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
    (hAt : st'.objects[target]? = some newObj)
    (hNe : ∀ oid : SeLe4n.ObjId, oid ≠ target → st'.objects[oid]? = st.objects[oid]?)
    (hFresh : retypeReplacementFresh newObj)
    (hDet : retypeTargetDetached st target)
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
    (hAt : st'.objects[target]? = some newObj)
    (hNe : ∀ oid : SeLe4n.ObjId, oid ≠ target → st'.objects[oid]? = st.objects[oid]?)
    (hFresh : retypeReplacementFresh newObj)
    (hDet : retypeTargetDetached st target)
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

private theorem retypeWrite_queueHeadBlockedConsistent
    {st st' : SystemState} {target : SeLe4n.ObjId} {newObj : KernelObject}
    (hAt : st'.objects[target]? = some newObj)
    (hNe : ∀ oid : SeLe4n.ObjId, oid ≠ target → st'.objects[oid]? = st.objects[oid]?)
    (hFresh : retypeReplacementFresh newObj)
    (hDet : retypeTargetDetached st target)
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
    (hAt : st'.objects[target]? = some newObj)
    (hNe : ∀ oid : SeLe4n.ObjId, oid ≠ target → st'.objects[oid]? = st.objects[oid]?)
    (hFresh : retypeReplacementFresh newObj)
    (hDet : retypeTargetDetached st target)
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
    (hAt : st'.objects[target]? = some newObj)
    (hNe : ∀ oid : SeLe4n.ObjId, oid ≠ target → st'.objects[oid]? = st.objects[oid]?)
    (hFresh : retypeReplacementFresh newObj)
    (hDet : retypeTargetDetached st target)
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
    (hAt : st'.objects[target]? = some newObj)
    (hNe : ∀ oid : SeLe4n.ObjId, oid ≠ target → st'.objects[oid]? = st.objects[oid]?)
    (hFresh : retypeReplacementFresh newObj)
    (hDet : retypeTargetDetached st target)
    (hInv : donationOwnerValid st) :
    donationOwnerValid st' := by
  intro tid tcb scId owner hT hB
  by_cases hK : tid.toObjId = target
  · rw [hK] at hT
    obtain rfl : newObj = .tcb tcb := retypeWrite_at_target hAt hT
    obtain ⟨-, -, -, -, hSB, -⟩ := hFresh
    rw [hSB] at hB
    cases hB
  · rw [hNe _ hK] at hT
    obtain ⟨⟨sc, hSc, hBound⟩, ⟨ownerTcb, hOT, hOUnbound, hOBlocked⟩⟩ :=
      hInv tid tcb scId owner hT hB
    have hneSc : scId.toObjId ≠ target := fun hEq => hDet.notSc sc (hEq ▸ hSc)
    have hneOwner : owner.toObjId ≠ target := by
      intro hEq
      obtain ⟨epId, rt, hIpc⟩ := hOBlocked
      exact hDet.notOwner ownerTcb (hEq ▸ hOT) epId rt hIpc
    refine ⟨⟨sc, ?_, hBound⟩, ⟨ownerTcb, ?_, hOUnbound, hOBlocked⟩⟩
    · rw [hNe _ hneSc]; exact hSc
    · rw [hNe _ hneOwner]; exact hOT

private theorem retypeWrite_ipcStateQueueMembershipConsistent
    {st st' : SystemState} {target : SeLe4n.ObjId} {newObj : KernelObject}
    (hAt : st'.objects[target]? = some newObj)
    (hNe : ∀ oid : SeLe4n.ObjId, oid ≠ target → st'.objects[oid]? = st.objects[oid]?)
    (hFresh : retypeReplacementFresh newObj)
    (hDet : retypeTargetDetached st target)
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
    (hAt : st'.objects[target]? = some newObj)
    (hNe : ∀ oid : SeLe4n.ObjId, oid ≠ target → st'.objects[oid]? = st.objects[oid]?)
    (hFresh : retypeReplacementFresh newObj)
    (hDet : retypeTargetDetached st target)
    (hInv : replyCallerLinkageReciprocal st) :
    replyCallerLinkageReciprocal st' := by
  constructor
  · intro tid tcb rid hT hRO
    by_cases hK : tid.toObjId = target
    · rw [hK] at hT
      obtain rfl : newObj = .tcb tcb := retypeWrite_at_target hAt hT
      obtain ⟨-, -, -, -, -, hRO0, -⟩ := hFresh
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
      rw [hFresh] at hCaller
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
    (hAt : st'.objects[target]? = some newObj)
    (hNe : ∀ oid : SeLe4n.ObjId, oid ≠ target → st'.objects[oid]? = st.objects[oid]?)
    (hFresh : retypeReplacementFresh newObj)
    (hDet : retypeTargetDetached st target)
    (hInv : pendingReceiveReplyWellFormed st) :
    pendingReceiveReplyWellFormed st' := by
  constructor
  · intro tid tcb rid hT hPRR
    have hTobj := (SystemState.getTcb?_eq_some_iff st' tid tcb).mp hT
    by_cases hK : tid.toObjId = target
    · rw [hK] at hTobj
      obtain rfl : newObj = .tcb tcb := retypeWrite_at_target hAt hTobj
      obtain ⟨-, -, -, -, -, -, hPRR0, -⟩ := hFresh
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
      obtain ⟨-, -, -, -, -, -, hPRR0, -⟩ := hFresh
      rw [hPRR0] at hP1
      cases hP1
    · by_cases hK2 : tid2.toObjId = target
      · rw [hK2] at hT2obj
        obtain rfl : newObj = .tcb tcb2 := retypeWrite_at_target hAt hT2obj
        obtain ⟨-, -, -, -, -, -, hPRR0, -⟩ := hFresh
        rw [hPRR0] at hP2
        cases hP2
      · rw [hNe _ hK1] at hT1obj
        rw [hNe _ hK2] at hT2obj
        exact hInv.2 tid1 tid2 tcb1 tcb2 rid
          ((SystemState.getTcb?_eq_some_iff st tid1 tcb1).mpr hT1obj)
          ((SystemState.getTcb?_eq_some_iff st tid2 tcb2).mpr hT2obj) hP1 hP2

private theorem retypeWrite_passiveServerIdle
    {st st' : SystemState} {target : SeLe4n.ObjId} {newObj : KernelObject}
    (hAt : st'.objects[target]? = some newObj)
    (hNe : ∀ oid : SeLe4n.ObjId, oid ≠ target → st'.objects[oid]? = st.objects[oid]?)
    (hSched : st'.scheduler = st.scheduler)
    (hFresh : retypeReplacementFresh newObj)
    (hInv : passiveServerIdle st) :
    passiveServerIdle st' := by
  intro tid tcb hT hUnbound hNQ hNC
  by_cases hK : tid.toObjId = target
  · rw [hK] at hT
    obtain rfl : newObj = .tcb tcb := retypeWrite_at_target hAt hT
    obtain ⟨hReady, -⟩ := hFresh
    exact Or.inl hReady
  · rw [hNe _ hK] at hT
    rw [hSched] at hNQ hNC
    exact hInv tid tcb hT hUnbound hNQ hNC

private theorem retypeWrite_dualQueueSystemInvariant
    {st st' : SystemState} {target : SeLe4n.ObjId} {newObj : KernelObject}
    (hAt : st'.objects[target]? = some newObj)
    (hNe : ∀ oid : SeLe4n.ObjId, oid ≠ target → st'.objects[oid]? = st.objects[oid]?)
    (hFresh : retypeReplacementFresh newObj)
    (hDet : retypeTargetDetached st target)
    (hInv : dualQueueSystemInvariant st) :
    dualQueueSystemInvariant st' := by
  obtain ⟨hEpWF, ⟨hFwd, hRev⟩, hAcyclic⟩ := hInv
  have hIQtrans : ∀ (q : IntrusiveQueue),
      intrusiveQueueWellFormed q st →
      (∀ hd, q.head = some hd → hd.toObjId ≠ target) →
      (∀ tl, q.tail = some tl → tl.toObjId ≠ target) →
      intrusiveQueueWellFormed q st' := by
    intro q ⟨hP1, hP2, hP3⟩ hHd hTl
    refine ⟨hP1, ?_, ?_⟩
    · intro hd hH
      obtain ⟨tcbH, hTH, hPnone⟩ := hP2 hd hH
      exact ⟨tcbH, by rw [hNe _ (hHd hd hH)]; exact hTH, hPnone⟩
    · intro tl hT
      obtain ⟨tcbT, hTT, hNnone⟩ := hP3 tl hT
      exact ⟨tcbT, by rw [hNe _ (hTl tl hT)]; exact hTT, hNnone⟩
  refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
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

/-- The retype write — one arbitrary-kind object replaced by a pristine one at
a fully detached slot — preserves the whole `ipcInvariantFull` bundle.  This is
the storeObject-shape core shared by every retype entry point; the
`lifecycleRetypeObject_preserves_*` family proves the same conjuncts one at a
time for the CSpaceAddr-authorized variant. -/
theorem retypeWrite_preserves_ipcInvariantFull
    {st st' : SystemState} {target : SeLe4n.ObjId} {newObj : KernelObject}
    (hAt : st'.objects[target]? = some newObj)
    (hNe : ∀ oid : SeLe4n.ObjId, oid ≠ target → st'.objects[oid]? = st.objects[oid]?)
    (hSched : st'.scheduler = st.scheduler)
    (hFresh : retypeReplacementFresh newObj)
    (hDet : retypeTargetDetached st target)
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
   retypeWrite_passiveServerIdle hAt hNe hSched hFresh hInv.passiveServerIdle,
   retypeWrite_donationBudgetTransfer hAt hNe hFresh hInv.donationBudgetTransfer,
   retypeWrite_blockedOnReplyHasTarget hAt hNe hFresh hInv.blockedOnReplyHasTarget,
   ⟨retypeWrite_replyCallerLinkageReciprocal hAt hNe hFresh hDet hInv.replyCallerLinkage.1,
    retypeWrite_blockedOnReplyHasReplyObject hAt hNe hFresh hInv.replyCallerLinkage.2⟩,
   retypeWrite_pendingReceiveReplyWellFormed hAt hNe hFresh hDet
     hInv.pendingReceiveReplyWellFormed,
   retypeWrite_donationOwnerUnique hAt hNe hFresh hInv.donationOwnerUnique,
   retypeWrite_endpointQueueTailBlockedConsistent hAt hNe hFresh hDet
     hInv.endpointQueueTailBlockedConsistent,
   retypeWrite_queueNextTargetBlocked hAt hNe hFresh hDet hInv.queueNextTargetBlocked⟩

/-- A fully descheduled thread occupies no core, so the destroy sweep's
per-core step is the literal identity. -/
private theorem removeRunnableFromAllCores_id_of_descheduled
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hRQ : ∀ c : CoreId, (st.scheduler.runQueueOnCore c).contains tid = false)
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
          simp only [hG]
          rfl
      | tcb _ | notification _ | cnode _ | vspaceRoot _ | untyped _
      | schedContext _ | reply _ => rfl)

/-- The victim waits on no notification, so the wait-list sweep is the
literal identity. -/
private theorem removeFromAllNotificationWaitLists_id_of_no_waits
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hNoWait : ∀ (oid : SeLe4n.ObjId) (n : Notification),
      st.objects[oid]? = some (.notification n) → tid ∉ n.waitingThreads.val) :
    removeFromAllNotificationWaitLists st tid = st := by
  unfold removeFromAllNotificationWaitLists
  exact RobinHood.RHTable.fold_preserves_of_lookup st.objects st _ (· = st) hObjInv rfl
    (fun acc oid obj hGet hAcc => by
      rw [hAcc]
      cases obj with
      | notification n =>
          have hN : st.objects[oid]? = some (.notification n) := by
            rw [RHTable_getElem?_eq_get?]; exact hGet
          have hC : n.waitingThreads.val.contains tid = false := by
            simp [hNoWait oid n hN]
          simp only [hC]
          rfl
      | tcb _ | endpoint _ | cnode _ | vspaceRoot _ | untyped _
      | schedContext _ | reply _ => rfl)

/-- An unbound-or-bound (never donated) thread returns no SchedContext at
cleanup — the donation return is the identity success. -/
private theorem cleanupDonatedSchedContext_ok_of_not_donated
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hNotDonated : ∀ tcbX : TCB, lookupTcb st tid = some tcbX →
      ∀ scId owner, tcbX.schedContextBinding ≠ .donated scId owner) :
    cleanupDonatedSchedContext st tid = .ok st := by
  unfold cleanupDonatedSchedContext
  cases hLk : lookupTcb st tid with
  | none => rfl
  | some tcbX =>
      cases hB : tcbX.schedContextBinding with
      | donated scId owner => exact absurd hB (hNotDonated tcbX hLk scId owner)
      | unbound => simp only [hB]
      | bound scId => simp only [hB]

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
    unfold lookupTcb at hLk
    split at hLk
    · cases hLk
    · rw [hO, hDet.tcbSelfId tcb hObj, hObj] at hLk
      simp only [Option.some.injEq] at hLk
      exact hLk.symm
  unfold cleanupTcbReferences
  dsimp only []
  rw [removeRunnableFromAllCores_id_of_descheduled stX tcb.tid
    (fun c => by rw [hS]; exact (hDet.tcbDescheduled tcb hObj c).1)
    (fun c => by rw [hS]; exact (hDet.tcbDescheduled tcb hObj c).2)]
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
  exact removeFromAllNotificationWaitLists_id_of_no_waits stX tcb.tid (hO ▸ hObjInv)
    (fun oid n hN => by
      rw [hO] at hN
      exact hDet.tcbNotWaiter tcb hObj oid n hN)

/-- Under the detachment pack a successful pre-retype cleanup changes neither
the object store nor the scheduler — the sweeps are identities, the donation
return is trivial, and the CDT/serviceRegistry/scThreadIndex writes are outside
the bundle's read set. -/
private theorem lifecyclePreRetypeCleanup_detached_frame
    (st stClean : SystemState) (target : SeLe4n.ObjId) (currentObj newObj : KernelObject)
    (hObjInv : st.objects.invExt)
    (hObj : st.objects[target]? = some currentObj)
    (hDet : retypeTargetDetached st target)
    (hStep : lifecyclePreRetypeCleanup st target currentObj newObj = .ok stClean) :
    stClean.objects = st.objects ∧ stClean.scheduler = st.scheduler := by
  unfold lifecyclePreRetypeCleanup at hStep
  cases currentObj with
  | tcb tcb =>
      have hCur : threadCurrentOnSomeCore st tcb.tid = false := by
        unfold threadCurrentOnSomeCore
        simp only [List.any_eq_false, beq_iff_eq]
        intro c _
        exact (hDet.tcbDescheduled tcb hObj c).2
      have hND : ∀ tcbX : TCB, lookupTcb st tcb.tid = some tcbX →
          ∀ scId owner, tcbX.schedContextBinding ≠ .donated scId owner := by
        intro tcbX hLk scId owner
        unfold lookupTcb at hLk
        split at hLk
        · cases hLk
        · rw [hDet.tcbSelfId tcb hObj, hObj] at hLk
          simp only [Option.some.injEq] at hLk
          rw [← hLk]
          exact hDet.tcbNotDonated tcb hObj scId owner
      simp only [hCur, Bool.false_eq_true, if_false,
        cleanupDonatedSchedContext_ok_of_not_donated st tcb.tid hND] at hStep
      cases hB : tcb.schedContextBinding with
      | donated scId owner => exact absurd hB (hDet.tcbNotDonated tcb hObj scId owner)
      | unbound =>
          simp only [hB] at hStep
          rw [cleanupTcbReferences_id_of_detached st target tcb hObjInv hObj hDet
            st rfl rfl] at hStep
          split at hStep
          · contradiction
          · cases hStep
            exact ⟨rfl, rfl⟩
      | bound scId =>
          simp only [hB] at hStep
          rw [cleanupTcbReferences_id_of_detached st target tcb hObjInv hObj hDet
            { st with scThreadIndex := scThreadIndexRemove st.scThreadIndex scId tcb.tid }
            rfl rfl] at hStep
          split at hStep
          · contradiction
          · cases hStep
            exact ⟨rfl, rfl⟩
  | endpoint ep =>
      simp only [] at hStep
      cases hStep
      exact ⟨cleanupEndpointServiceRegistrations_objects_eq st target,
        cleanupEndpointServiceRegistrations_scheduler_eq st target⟩
  | cnode cn =>
      simp only [] at hStep
      split at hStep
      · contradiction
      · cases hStep
        exact ⟨detachCNodeSlots_objects_eq st target cn,
          detachCNodeSlots_scheduler_eq st target cn⟩
  | reply r =>
      simp only [] at hStep
      split at hStep
      · contradiction
      · cases hStep
        exact ⟨rfl, rfl⟩
  | notification n =>
      cases hStep
      exact ⟨rfl, rfl⟩
  | vspaceRoot v =>
      cases hStep
      exact ⟨rfl, rfl⟩
  | untyped u =>
      cases hStep
      exact ⟨rfl, rfl⟩
  | schedContext sc =>
      cases hStep
      exact ⟨rfl, rfl⟩

/-- The detachment pack transports across any objects- and scheduler-preserving
step (the cleanup and scrub stages). -/
private theorem retypeTargetDetached_of_objects_scheduler_eq
    {st st2 : SystemState} {target : SeLe4n.ObjId}
    (hObjs : st2.objects = st.objects) (hSched : st2.scheduler = st.scheduler)
    (hDet : retypeTargetDetached st target) : retypeTargetDetached st2 target := by
  constructor
  · intro sc; rw [hObjs]; exact hDet.notSc sc
  · intro t hT; rw [hObjs] at hT; exact hDet.notOwner t hT
  · intro t hT; rw [hObjs] at hT; exact hDet.tcbNoNext t hT
  · intro t hT; rw [hObjs] at hT; exact hDet.tcbNoPrev t hT
  · intro t hT; rw [hObjs] at hT; exact hDet.tcbSelfId t hT
  · intro t hT; rw [hObjs] at hT; exact hDet.tcbAllowedState t hT
  · intro t hT; rw [hObjs] at hT; exact hDet.tcbNotDonated t hT
  · intro t hT oid n hN; rw [hObjs] at hT hN; exact hDet.tcbNotWaiter t hT oid n hN
  · intro t hT c; rw [hObjs] at hT; rw [hSched]; exact hDet.tcbDescheduled t hT c
  · intro tid tcb hT; rw [hObjs] at hT; exact hDet.blockedRefsAvoid tid tcb hT
  · intro a tcbA b hA hN; rw [hObjs] at hA; exact hDet.notQueueLinked a tcbA b hA hN
  · intro b tcbB a hB hP; rw [hObjs] at hB; exact hDet.notPrevLinked b tcbB a hB hP
  · intro epId ep hd hEp hH; rw [hObjs] at hEp; exact hDet.notHead epId ep hd hEp hH
  · intro epId ep tl hEp hT; rw [hObjs] at hEp; exact hDet.notTail epId ep tl hEp hT
  · intro tid tcb hT; rw [hObjs] at hT; exact hDet.noSelfLoops tid tcb hT
  · intro tid tcb rid hT hRO; rw [hObjs] at hT; exact hDet.notReplyLinked tid tcb rid hT hRO
  · intro tid tcb rid hT hP; rw [hObjs] at hT; exact hDet.notStashed tid tcb rid hT hP

/-- The pre-resolved-authority retype base: guards then one pristine write. -/
theorem lifecycleRetypeDirect_preserves_ipcInvariantFull
    (st st' : SystemState) (authCap : Capability) (target : SeLe4n.ObjId)
    (newObj : KernelObject)
    (hObjInv : st.objects.invExt)
    (hFresh : retypeReplacementFresh newObj)
    (hDet : retypeTargetDetached st target)
    (hInv : ipcInvariantFull st)
    (hStep : lifecycleRetypeDirect authCap target newObj st = .ok ((), st')) :
    ipcInvariantFull st' := by
  unfold lifecycleRetypeDirect at hStep
  cases hObj : st.objects[target]? with
  | none => simp [hObj] at hStep
  | some currentObj =>
      simp only [hObj] at hStep
      split at hStep
      · split at hStep
        · exact retypeWrite_preserves_ipcInvariantFull
            (storeObject_objects_eq st st' target newObj hObjInv hStep)
            (fun oid hNeO =>
              storeObject_objects_ne st st' target oid newObj hNeO hObjInv hStep)
            (storeObject_scheduler_eq st st' target newObj hStep)
            hFresh hDet hInv
        · contradiction
      · contradiction

/-- **`.lifecycleRetype`'s cleanup composite**: well-formedness guard,
per-kind cleanup, memory scrub, then the pristine write. -/
theorem lifecycleRetypeDirectWithCleanup_preserves_ipcInvariantFull
    (st st' : SystemState) (authCap : Capability) (target : SeLe4n.ObjId)
    (newObj : KernelObject)
    (hObjInv : st.objects.invExt)
    (hFresh : retypeReplacementFresh newObj)
    (hDet : retypeTargetDetached st target)
    (hInv : ipcInvariantFull st)
    (hStep : lifecycleRetypeDirectWithCleanup authCap target newObj st = .ok ((), st')) :
    ipcInvariantFull st' := by
  unfold lifecycleRetypeDirectWithCleanup at hStep
  split at hStep
  · contradiction
  · cases hObj : st.objects[target]? with
    | none =>
        simp only [hObj] at hStep
        exact lifecycleRetypeDirect_preserves_ipcInvariantFull st st' authCap target newObj
          hObjInv hFresh hDet hInv hStep
    | some currentObj =>
        simp only [hObj] at hStep
        cases hClean : lifecyclePreRetypeCleanup st target currentObj newObj with
        | error e => rw [hClean] at hStep; cases hStep
        | ok stClean =>
            rw [hClean] at hStep
            dsimp only [] at hStep
            obtain ⟨hCO, hCS⟩ := lifecyclePreRetypeCleanup_detached_frame st stClean target
              currentObj newObj hObjInv hObj hDet hClean
            have hSO : (scrubObjectMemory stClean target currentObj.objectType).objects
                = st.objects :=
              (scrubObjectMemory_objects_eq stClean target currentObj.objectType).trans hCO
            have hSS : (scrubObjectMemory stClean target currentObj.objectType).scheduler
                = st.scheduler :=
              (scrubObjectMemory_scheduler_eq stClean target currentObj.objectType).trans hCS
            exact lifecycleRetypeDirect_preserves_ipcInvariantFull _ st' authCap target newObj
              (hSO ▸ hObjInv)
              hFresh
              (retypeTargetDetached_of_objects_scheduler_eq hSO hSS hDet)
              (ipcInvariantFull_of_objects_scheduler_eq hSO hSS hInv)
              hStep

/-- The ASID shootdown stage is `tlb`/`tlbShootdown`-only. -/
theorem lifecycleRetypeDirectWithCleanupShootdown_preserves_ipcInvariantFull
    (st st' : SystemState) (ec : CoreId) (authCap : Capability) (target : SeLe4n.ObjId)
    (newObj : KernelObject)
    (hObjInv : st.objects.invExt)
    (hFresh : retypeReplacementFresh newObj)
    (hDet : retypeTargetDetached st target)
    (hInv : ipcInvariantFull st)
    (hStep : lifecycleRetypeDirectWithCleanupShootdown ec authCap target newObj st
      = .ok ((), st')) :
    ipcInvariantFull st' := by
  unfold lifecycleRetypeDirectWithCleanupShootdown at hStep
  cases hBase : lifecycleRetypeDirectWithCleanup authCap target newObj st with
  | error e => simp [hBase] at hStep
  | ok pair =>
      obtain ⟨u, stB⟩ := pair; cases u
      simp only [hBase] at hStep
      have hB := lifecycleRetypeDirectWithCleanup_preserves_ipcInvariantFull st stB authCap
        target newObj hObjInv hFresh hDet hInv hBase
      rw [retypeShootdownAsids_eq] at hStep
      simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
      subst hStep
      exact ipcInvariantFull_of_objects_scheduler_eq
        (retypeAsidRoundFold_objects ec _ stB)
        (retypeAsidRoundFold_scheduler ec _ stB) hB

/-- The initiator drain is `perCoreTlb`-only. -/
private theorem retypeInitiatorDrain_objects_scheduler
    (ec : CoreId) (asids : List SeLe4n.ASID) (stX : SystemState) :
    (retypeInitiatorDrain ec asids stX).objects = stX.objects ∧
    (retypeInitiatorDrain ec asids stX).scheduler = stX.scheduler := by
  unfold retypeInitiatorDrain
  cases asids with
  | nil => exact ⟨rfl, rfl⟩
  | cons a rest => exact ⟨rfl, rfl⟩

/-- The initiator-atomic per-core retype wrapper. -/
theorem lifecycleRetypeDirectWithCleanupShootdownPerCore_preserves_ipcInvariantFull
    (st st' : SystemState) (ec : CoreId) (authCap : Capability) (target : SeLe4n.ObjId)
    (newObj : KernelObject)
    (hObjInv : st.objects.invExt)
    (hFresh : retypeReplacementFresh newObj)
    (hDet : retypeTargetDetached st target)
    (hInv : ipcInvariantFull st)
    (hStep : lifecycleRetypeDirectWithCleanupShootdownPerCore ec authCap target newObj st
      = .ok ((), st')) :
    ipcInvariantFull st' := by
  unfold lifecycleRetypeDirectWithCleanupShootdownPerCore at hStep
  cases hBase : lifecycleRetypeDirectWithCleanupShootdown ec authCap target newObj st with
  | error e => simp [hBase] at hStep
  | ok pair =>
      obtain ⟨u, stB⟩ := pair; cases u
      simp only [hBase] at hStep
      have hB := lifecycleRetypeDirectWithCleanupShootdown_preserves_ipcInvariantFull st stB
        ec authCap target newObj hObjInv hFresh hDet hInv hBase
      simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
      subst hStep
      exact ipcInvariantFull_of_objects_scheduler_eq
        (retypeInitiatorDrain_objects_scheduler ec _ stB).1
        (retypeInitiatorDrain_objects_scheduler ec _ stB).2 hB

/-- `.lifecycleRetype` (dispatch arm): the full stack — well-formedness guard,
per-kind cleanup, scrub, pristine write, ASID shootdown rounds, initiator
drain, instruction-cache broadcast — preserves the whole bundle. -/
theorem lifecycleRetypeDirectWithCleanupShootdownPerCoreIcache_preserves_ipcInvariantFull
    (st st' : SystemState) (ec : CoreId) (authCap : Capability) (target : SeLe4n.ObjId)
    (newObj : KernelObject)
    (hObjInv : st.objects.invExt)
    (hFresh : retypeReplacementFresh newObj)
    (hDet : retypeTargetDetached st target)
    (hInv : ipcInvariantFull st)
    (hStep : lifecycleRetypeDirectWithCleanupShootdownPerCoreIcache ec authCap target newObj st
      = .ok ((), st')) :
    ipcInvariantFull st' := by
  unfold lifecycleRetypeDirectWithCleanupShootdownPerCoreIcache at hStep
  cases hK : lifecycleRetypeDirectWithCleanupShootdownPerCore ec authCap target newObj st with
  | error e =>
      rw [(Architecture.withIcacheBroadcast_error_iff _ _ st e).mpr hK] at hStep
      contradiction
  | ok pair =>
      obtain ⟨u, stB⟩ := pair; cases u
      have hB := lifecycleRetypeDirectWithCleanupShootdownPerCore_preserves_ipcInvariantFull
        st stB ec authCap target newObj hObjInv hFresh hDet hInv hK
      obtain ⟨hObjs, -, hSched, -⟩ := Architecture.withIcacheBroadcast_frame hK hStep
      exact ipcInvariantFull_of_objects_scheduler_eq hObjs hSched hB

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
  unfold Lifecycle.Suspend.restoreToReady
  cases hLk : st.getTcb? tid with
  | none => rfl
  | some tcb =>
      dsimp only []
      have hSame : ({ tcb with ipcState := .ready, queuePrev := none, queueNext := none, queuePPrev := none, pendingReceiveReply := none } : TCB) = tcb := by
        have h1 := hQ.ready tcb hLk
        have h2 := hQ.noNext tcb hLk
        have h3 := hQ.noPrev tcb hLk
        have h4 := hQ.noPPrev tcb hLk
        have h5 := hQ.noStash tcb hLk
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

private theorem restoreToReady_objects_invExt (st : SystemState) (tid : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt) :
    (Lifecycle.Suspend.restoreToReady st tid).objects.invExt := by
  unfold Lifecycle.Suspend.restoreToReady
  split
  · exact RHTable_insert_preserves_invExt st.objects tid.toObjId _ hObjInv
  · exact hObjInv

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
  have hSched := Lifecycle.Suspend.restoreToReady_scheduler_eq st tid
  have hObjInv1 := restoreToReady_objects_invExt st tid hObjInv
  have hInv1 : ipcInvariantFull (Lifecycle.Suspend.restoreToReady st tid) := by
    refine ipcInvariantFull_of_getElem_eq hEq ?_ hInv
    intro t tcbT hT hUnb hNQ hNC
    rw [hEq] at hT
    rw [hSched] at hNQ hNC
    exact hInv.passiveServerIdle t tcbT hT hUnb hNQ hNC
  unfold Lifecycle.Suspend.resumeReadyMidState
  dsimp only []
  cases hLk : (Lifecycle.Suspend.restoreToReady st tid).getTcb? tid with
  | none => exact hInv1
  | some t =>
      exact insertObjects_tcbFieldUpdate_preserves_ipcInvariantFull
        (Lifecycle.Suspend.restoreToReady st tid) tid t
        { t with threadState := .Ready, pipBoost := SeLe4n.Kernel.PriorityInheritance.computeMaxWaiterPriority (Lifecycle.Suspend.restoreToReady st tid) tid }
        hObjInv1 hInv1
        ((SystemState.getTcb?_eq_some_iff _ tid t).mp hLk)
        rfl rfl rfl rfl rfl rfl rfl rfl rfl

/-- Enqueueing an already-`.ready` thread rewrites its TCB to itself and grows
one run queue — the bundle transports, with `passiveServerIdle` covered by the
queue-growth direction. -/
private theorem enqueueRunnableOnCore_preserves_ipcInvariantFull
    (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hReady : ∀ tcb : TCB, st.getTcb? tid = some tcb → tcb.ipcState = .ready)
    (hInv : ipcInvariantFull st) :
    ipcInvariantFull (enqueueRunnableOnCore st c tid) := by
  unfold enqueueRunnableOnCore
  cases hLk : st.getTcb? tid with
  | none => exact hInv
  | some tcb =>
      dsimp only []
      split
      · exact hInv
      · have hSame : ({ tcb with ipcState := .ready } : TCB) = tcb := by
          have h1 := hReady tcb hLk
          cases tcb
          simp_all
        rw [hSame]
        have hPre : st.objects[tid.toObjId]? = some (.tcb tcb) :=
          (SystemState.getTcb?_eq_some_iff st tid tcb).mp hLk
        have hEq : ∀ oid : SeLe4n.ObjId,
            ({ st with objects := st.objects.insert tid.toObjId (.tcb tcb), scheduler := st.scheduler.setRunQueueOnCore c ((st.scheduler.runQueueOnCore c).insert tid (effectiveRunQueuePriority tcb)) } : SystemState).objects[oid]? = st.objects[oid]? := by
          intro oid
          show (st.objects.insert tid.toObjId (.tcb tcb))[oid]? = st.objects[oid]?
          by_cases hK : oid = tid.toObjId
          · subst hK
            simp only [RHTable_getElem?_eq_get?]
            rw [RobinHood.RHTable.getElem?_insert_self st.objects tid.toObjId _ hObjInv]
            rw [← RHTable_getElem?_eq_get?]
            exact hPre.symm
          · simp only [RHTable_getElem?_eq_get?]
            exact RobinHood.RHTable.getElem?_insert_ne st.objects tid.toObjId oid _
              (by simp; exact fun h => hK h.symm) hObjInv
        refine ipcInvariantFull_of_getElem_eq hEq ?_ hInv
        intro t tcbT hT hUnb hNQ hNC
        rw [hEq] at hT
        rw [show ({ st with objects := st.objects.insert tid.toObjId (.tcb tcb), scheduler := st.scheduler.setRunQueueOnCore c ((st.scheduler.runQueueOnCore c).insert tid (effectiveRunQueuePriority tcb)) } : SystemState).scheduler.currentOnCore Concurrency.bootCoreId = st.scheduler.currentOnCore Concurrency.bootCoreId from by simp] at hNC
        have hNQ' : t ∉ st.scheduler.runQueueOnCore Concurrency.bootCoreId := by
          intro hMem
          apply hNQ
          show t ∈ ({ st with objects := st.objects.insert tid.toObjId (.tcb tcb), scheduler := st.scheduler.setRunQueueOnCore c ((st.scheduler.runQueueOnCore c).insert tid (effectiveRunQueuePriority tcb)) } : SystemState).scheduler.runQueueOnCore Concurrency.bootCoreId
          by_cases hc : c = Concurrency.bootCoreId
          · subst hc
            show t ∈ (st.scheduler.setRunQueueOnCore Concurrency.bootCoreId ((st.scheduler.runQueueOnCore Concurrency.bootCoreId).insert tid (effectiveRunQueuePriority tcb))).runQueueOnCore Concurrency.bootCoreId
            rw [SchedulerState.setRunQueueOnCore_runQueueOnCore_self]
            exact (RunQueue.mem_insert _ _ _ _).mpr (Or.inl hMem)
          · show t ∈ (st.scheduler.setRunQueueOnCore c ((st.scheduler.runQueueOnCore c).insert tid (effectiveRunQueuePriority tcb))).runQueueOnCore Concurrency.bootCoreId
            rw [SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ _ _ _ hc]
            exact hMem
        exact hInv.passiveServerIdle t tcbT hT hUnb hNQ' hNC

private theorem resumeReadyMidState_objects_invExt
    (st : SystemState) (tid : SeLe4n.ThreadId) (hObjInv : st.objects.invExt) :
    (Lifecycle.Suspend.resumeReadyMidState st tid).objects.invExt := by
  unfold Lifecycle.Suspend.resumeReadyMidState
  dsimp only []
  split
  · exact RHTable_insert_preserves_invExt _ _ _ (restoreToReady_objects_invExt st tid hObjInv)
  · exact restoreToReady_objects_invExt st tid hObjInv

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
  | none => simp only [hLk] at hT; cases hT
  | some t =>
      simp only [hLk] at hT
      have hTobj := (SystemState.getTcb?_eq_some_iff _ tid tcb).mp hT
      dsimp only [] at hTobj
      have hAt : ((Lifecycle.Suspend.restoreToReady st tid).objects.insert tid.toObjId (KernelObject.tcb { t with threadState := .Ready, pipBoost := SeLe4n.Kernel.PriorityInheritance.computeMaxWaiterPriority (Lifecycle.Suspend.restoreToReady st tid) tid }))[tid.toObjId]? = some (KernelObject.tcb { t with threadState := .Ready, pipBoost := SeLe4n.Kernel.PriorityInheritance.computeMaxWaiterPriority (Lifecycle.Suspend.restoreToReady st tid) tid }) := by
        simp only [RHTable_getElem?_eq_get?]
        exact RobinHood.RHTable.getElem?_insert_self _ _ _ hObjInv1
      rw [hAt] at hTobj
      obtain rfl : ({ t with threadState := .Ready, pipBoost := SeLe4n.Kernel.PriorityInheritance.computeMaxWaiterPriority (Lifecycle.Suspend.restoreToReady st tid) tid } : TCB) = tcb := by
        simpa using hTobj
      show t.ipcState = .ready
      have hPre1 := (SystemState.getTcb?_eq_some_iff _ tid t).mp hLk
      rw [hEq tid.toObjId] at hPre1
      exact hQ.ready t ((SystemState.getTcb?_eq_some_iff st tid t).mpr hPre1)

private theorem enqueueRunnableOnCore_objects_invExt
    (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt) :
    (enqueueRunnableOnCore st c tid).objects.invExt := by
  unfold enqueueRunnableOnCore
  dsimp only []
  split
  · split
    · exact hObjInv
    · exact RHTable_insert_preserves_invExt _ _ _ hObjInv
  · exact hObjInv

/-- The enqueue-only resume — the branch the live `.tcbResume` arm runs while
the context-restore seam is dark. -/
theorem resumeThreadEnqueueOnly_preserves_ipcInvariantFull
    (st st' : SystemState) (vtid : SeLe4n.ValidThreadId) (ec : CoreId)
    (sgi : Option (CoreId × Concurrency.SgiKind))
    (hObjInv : st.objects.invExt)
    (hQ : threadIpcFieldsQuiescent st vtid.val)
    (hInv : ipcInvariantFull st)
    (hStep : Lifecycle.Suspend.resumeThreadEnqueueOnly st vtid ec = .ok (st', sgi)) :
    ipcInvariantFull st' := by
  unfold Lifecycle.Suspend.resumeThreadEnqueueOnly at hStep
  dsimp only [] at hStep
  cases hLk : st.getTcb? vtid.val with
  | none => rw [hLk] at hStep; cases hStep
  | some tcb =>
      rw [hLk] at hStep
      dsimp only [] at hStep
      split at hStep
      · cases hStep
      · have hMid := resumeReadyMidState_preserves_ipcInvariantFull st vtid.val hObjInv hQ hInv
        have hEnq := enqueueRunnableOnCore_preserves_ipcInvariantFull
          (Lifecycle.Suspend.resumeReadyMidState st vtid.val)
          (determineTargetCore st vtid.val) vtid.val
          (resumeReadyMidState_objects_invExt st vtid.val hObjInv)
          (resumeReadyMidState_getTcb_ready st vtid.val hObjInv hQ) hMid
        split at hStep <;> · cases hStep; exact hEnq

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
      · have hMid := resumeReadyMidState_preserves_ipcInvariantFull st vtid.val hObjInv hQ hInv
        have hEnq := enqueueRunnableOnCore_preserves_ipcInvariantFull
          (Lifecycle.Suspend.resumeReadyMidState st vtid.val)
          (determineTargetCore st vtid.val) vtid.val
          (resumeReadyMidState_objects_invExt st vtid.val hObjInv)
          (resumeReadyMidState_getTcb_ready st vtid.val hObjInv hQ) hMid
        have hEnqInv := enqueueRunnableOnCore_objects_invExt
          (Lifecycle.Suspend.resumeReadyMidState st vtid.val)
          (determineTargetCore st vtid.val) vtid.val
          (resumeReadyMidState_objects_invExt st vtid.val hObjInv)
        split at hStep
        · cases hRes : handleRescheduleSgiOnCore (enqueueRunnableOnCore
              (Lifecycle.Suspend.resumeReadyMidState st vtid.val)
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
          exact RobinHood.RHTable.insert_preserves_invExt _ _ _ hObjInv

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
  | none => simp [setThreadFaultHandlerOp, hT] at hStep
  | some tcb =>
      cases hR : resolveFaultHandlerCPtr st tcb cptr with
      | error e => simp [setThreadFaultHandlerOp, hT, hR] at hStep
      | ok tgt =>
          rw [setThreadFaultHandlerOp_ok_eq st vtid cptr tcb tgt hT hR] at hStep
          cases hStep
          simp only [installFaultHandler]
          exact insertObjects_tcbFieldUpdate_preserves_ipcInvariantFull st vtid.val tcb
            { tcb with faultHandler := some cptr } hObjInv hInv
            ((SystemState.getTcb?_eq_some_iff st vtid.val tcb).mp hT)
            rfl rfl rfl rfl rfl rfl rfl rfl rfl

/-- Review round (PR #887): and the object-store invariant. -/
theorem setThreadFaultHandlerOp_preserves_objects_invExt
    (st st' : SystemState) (vtid : SeLe4n.ValidThreadId) (cptr : SeLe4n.CPtr)
    (hObjInv : st.objects.invExt)
    (hStep : setThreadFaultHandlerOp st vtid cptr = .ok st') :
    st'.objects.invExt := by
  cases hT : st.getTcb? vtid.val with
  | none => simp [setThreadFaultHandlerOp, hT] at hStep
  | some tcb =>
      cases hR : resolveFaultHandlerCPtr st tcb cptr with
      | error e => simp [setThreadFaultHandlerOp, hT, hR] at hStep
      | ok tgt =>
          rw [setThreadFaultHandlerOp_ok_eq st vtid cptr tcb tgt hT hR] at hStep
          cases hStep
          simp only [installFaultHandler]
          exact RobinHood.RHTable.insert_preserves_invExt _ _ _ hObjInv

/-- `.tcbResume` (dispatch arm): the seam-gated wrapper, both branches. -/
theorem resumeThreadOnCoreLive_preserves_ipcInvariantFull
    (st st' : SystemState) (vtid : SeLe4n.ValidThreadId) (ec : CoreId)
    (sgi : Option (CoreId × Concurrency.SgiKind))
    (hObjInv : st.objects.invExt)
    (hQ : threadIpcFieldsQuiescent st vtid.val)
    (hInv : ipcInvariantFull st)
    (hStep : Lifecycle.Suspend.resumeThreadOnCoreLive st vtid ec = .ok (st', sgi)) :
    ipcInvariantFull st' := by
  unfold Lifecycle.Suspend.resumeThreadOnCoreLive at hStep
  split at hStep
  · exact resumeThreadOnCore_preserves_ipcInvariantFull st st' vtid ec sgi
      hObjInv hQ hInv hStep
  · exact resumeThreadEnqueueOnly_preserves_ipcInvariantFull st st' vtid ec sgi
      hObjInv hQ hInv hStep

/-- Cancelling IPC blocking on a `.ready` victim is the identity — there is
nothing to cancel. -/
private theorem cancelIpcBlocking_ready_id
    (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hReady : tcb.ipcState = .ready) :
    Lifecycle.Suspend.cancelIpcBlocking st tid tcb = st := by
  unfold Lifecycle.Suspend.cancelIpcBlocking
  rw [hReady]

/-- Descheduling a `.ready` thread on one core preserves the bundle: objects
are untouched, and `passiveServerIdle` closes over the removed thread because
`.ready` is an allowed passive state. -/
private theorem removeRunnableOnCore_preserves_ipcInvariantFull
    (st : SystemState) (tid : SeLe4n.ThreadId) (c : CoreId)
    (hReady : ∀ tcbX : TCB, st.getTcb? tid = some tcbX → tcbX.ipcState = .ready)
    (hInv : ipcInvariantFull st) :
    ipcInvariantFull (removeRunnableOnCore st tid c) := by
  refine ipcInvariantFull_of_getElem_eq (s1 := st) (fun oid => rfl) ?_ hInv
  intro t tcbT hT hUnb hNQ hNC
  by_cases hTv : t = tid
  · subst hTv
    have := hReady tcbT ((SystemState.getTcb?_eq_some_iff st t tcbT).mpr hT)
    exact Or.inl this
  · have hNQ' : t ∉ st.scheduler.runQueueOnCore Concurrency.bootCoreId := by
      intro hMem
      apply hNQ
      show t ∈ ((st.scheduler.setRunQueueOnCore c ((st.scheduler.runQueueOnCore c).remove tid)).setCurrentOnCore c (if (st.scheduler.currentOnCore c) = some tid then none else (st.scheduler.currentOnCore c))).runQueueOnCore Concurrency.bootCoreId
      rw [SchedulerState.setCurrentOnCore_runQueueOnCore]
      by_cases hc : c = Concurrency.bootCoreId
      · subst hc
        rw [SchedulerState.setRunQueueOnCore_runQueueOnCore_self]
        exact (RunQueue.mem_remove _ _ _).mpr ⟨hMem, hTv⟩
      · rw [SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ _ _ _ hc]
        exact hMem
    have hNC' : st.scheduler.currentOnCore Concurrency.bootCoreId ≠ some t := by
      intro hCur
      by_cases hc : c = Concurrency.bootCoreId
      · subst hc
        by_cases hEq : st.scheduler.currentOnCore Concurrency.bootCoreId = some tid
        · rw [hEq] at hCur
          exact hTv (Option.some.inj hCur).symm
        · apply hNC
          show ((st.scheduler.setRunQueueOnCore Concurrency.bootCoreId ((st.scheduler.runQueueOnCore Concurrency.bootCoreId).remove tid)).setCurrentOnCore Concurrency.bootCoreId (if (st.scheduler.currentOnCore Concurrency.bootCoreId) = some tid then none else (st.scheduler.currentOnCore Concurrency.bootCoreId))).currentOnCore Concurrency.bootCoreId = some t
          rw [SchedulerState.setCurrentOnCore_currentOnCore_self, if_neg hEq]
          exact hCur
      · apply hNC
        show ((st.scheduler.setRunQueueOnCore c ((st.scheduler.runQueueOnCore c).remove tid)).setCurrentOnCore c (if (st.scheduler.currentOnCore c) = some tid then none else (st.scheduler.currentOnCore c))).currentOnCore Concurrency.bootCoreId = some t
        rw [SchedulerState.setCurrentOnCore_currentOnCore_ne _ _ _ _ hc,
          SchedulerState.setRunQueueOnCore_currentOnCore]
        exact hCur
    exact hInv.passiveServerIdle t tcbT hT hUnb hNQ' hNC'

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
  | none => rfl
  | some tcb =>
      dsimp only []
      obtain ⟨h1, h2, h3, h4, h5⟩ := hFields tcb hLk
      have hSame : ({ tcb with pendingMessage := none, timeoutBudget := none, queuePrev := none, queueNext := none, queuePPrev := none } : TCB) = tcb := by
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

/-- The bound-donation cancel: SC clear, replenish drop, index drop, victim
unbind — the §11 unbind-direction rewrite under a replenish-only scheduler
change. -/
private theorem cancelBoundDonationOnCore_preserves_ipcInvariantFull
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB) (rqCore : CoreId)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hStored : st.objects[tid.toObjId]? = some (.tcb tcb))
    (hAllowed : passiveServerIdleAllowed tcb.ipcState)
    (hBidir : schedContextBindingBidirectional st)
    (hStep : cancelBoundDonationOnCore st tid tcb rqCore = .ok st') :
    ipcInvariantFull st' := by
  unfold cancelBoundDonationOnCore at hStep
  cases hB : tcb.schedContextBinding with
  | unbound => rw [hB] at hStep; cases hStep
  | donated scId owner => rw [hB] at hStep; cases hStep
  | bound scId =>
      rw [hB] at hStep
      dsimp only [] at hStep
      obtain ⟨sc, hScPre, hScBack⟩ := hBidir tid tcb scId hStored
        (by rw [hB]; rfl)
      have hScLk : st.getSchedContext? scId = some sc :=
        (SystemState.getSchedContext?_eq_some_iff st scId sc).mpr hScPre
      rw [hScLk] at hStep
      dsimp only [] at hStep
      have hNeTS : tid.toObjId ≠ scId.toObjId := by
        intro hEq
        rw [hEq, hScPre] at hStored
        cases hStored
      have hObjInv1 : (st.objects.insert scId.toObjId
          (KernelObject.schedContext { sc with boundThread := none, isActive := false })).invExt :=
        RHTable_insert_preserves_invExt _ _ _ hObjInv
      have hT2 : ({ { { st with objects := st.objects.insert scId.toObjId (KernelObject.schedContext { sc with boundThread := none, isActive := false }) } with scheduler := ({ st with objects := st.objects.insert scId.toObjId (KernelObject.schedContext { sc with boundThread := none, isActive := false }) } : SystemState).scheduler.setReplenishQueueOnCore rqCore (ReplenishQueue.remove (({ st with objects := st.objects.insert scId.toObjId (KernelObject.schedContext { sc with boundThread := none, isActive := false }) } : SystemState).scheduler.replenishQueueOnCore rqCore) scId) } with scThreadIndex := scThreadIndexRemove ({ { st with objects := st.objects.insert scId.toObjId (KernelObject.schedContext { sc with boundThread := none, isActive := false }) } with scheduler := ({ st with objects := st.objects.insert scId.toObjId (KernelObject.schedContext { sc with boundThread := none, isActive := false }) } : SystemState).scheduler.setReplenishQueueOnCore rqCore (ReplenishQueue.remove (({ st with objects := st.objects.insert scId.toObjId (KernelObject.schedContext { sc with boundThread := none, isActive := false }) } : SystemState).scheduler.replenishQueueOnCore rqCore) scId) } : SystemState).scThreadIndex scId tid } : SystemState).getTcb? tid = some tcb := by
        refine (SystemState.getTcb?_eq_some_iff _ tid tcb).mpr ?_
        show (st.objects.insert scId.toObjId (KernelObject.schedContext { sc with boundThread := none, isActive := false }))[tid.toObjId]? = some (.tcb tcb)
        simp only [RHTable_getElem?_eq_get?]
        rw [RobinHood.RHTable.getElem?_insert_ne st.objects scId.toObjId tid.toObjId _
          (by simp; exact fun h => hNeTS h.symm) hObjInv]
        rw [← RHTable_getElem?_eq_get?]
        exact hStored
      rw [hT2] at hStep
      dsimp only [] at hStep
      cases hStep
      refine ipcInvariantFull_of_schedBindingRewrite st _ tid scId tcb
        { tcb with schedContextBinding := .unbound } sc
        { sc with boundThread := none, isActive := false } hInv hStored ?_ hScPre ?_ ?_
        rfl rfl rfl rfl rfl rfl rfl rfl (Or.inr ⟨rfl, hScBack, rfl⟩) ?_
      · show ((st.objects.insert scId.toObjId (KernelObject.schedContext { sc with boundThread := none, isActive := false })).insert tid.toObjId (KernelObject.tcb { tcb with schedContextBinding := .unbound }))[tid.toObjId]? = some (KernelObject.tcb { tcb with schedContextBinding := .unbound })
        simp only [RHTable_getElem?_eq_get?]
        exact RobinHood.RHTable.getElem?_insert_self _ _ _ hObjInv1
      · show ((st.objects.insert scId.toObjId (KernelObject.schedContext { sc with boundThread := none, isActive := false })).insert tid.toObjId (KernelObject.tcb { tcb with schedContextBinding := .unbound }))[scId.toObjId]? = some (KernelObject.schedContext { sc with boundThread := none, isActive := false })
        simp only [RHTable_getElem?_eq_get?]
        rw [RobinHood.RHTable.getElem?_insert_ne _ tid.toObjId scId.toObjId _
          (by simp; exact fun h => hNeTS h) hObjInv1]
        exact RobinHood.RHTable.getElem?_insert_self _ _ _ hObjInv
      · intro oid hNeT hNeS
        show ((st.objects.insert scId.toObjId (KernelObject.schedContext { sc with boundThread := none, isActive := false })).insert tid.toObjId (KernelObject.tcb { tcb with schedContextBinding := .unbound }))[oid]? = st.objects[oid]?
        simp only [RHTable_getElem?_eq_get?]
        rw [RobinHood.RHTable.getElem?_insert_ne _ tid.toObjId oid _
          (by simp; exact fun h => hNeT h.symm) hObjInv1]
        rw [RobinHood.RHTable.getElem?_insert_ne _ scId.toObjId oid _
          (by simp; exact fun h => hNeS h.symm) hObjInv]
      · constructor
        intro t tcb' hT hUnb hNQ hNC hNotAllowed
        dsimp only [] at hT hNQ hNC
        simp only [SchedulerState.setReplenishQueueOnCore_runQueueOnCore] at hNQ
        simp only [SchedulerState.setReplenishQueueOnCore_currentOnCore] at hNC
        by_cases hTv : t = tid
        · subst hTv
          rw [show ((st.objects.insert scId.toObjId (KernelObject.schedContext { sc with boundThread := none, isActive := false })).insert t.toObjId (KernelObject.tcb { tcb with schedContextBinding := .unbound }))[t.toObjId]? = some (KernelObject.tcb { tcb with schedContextBinding := .unbound }) from by simp only [RHTable_getElem?_eq_get?]; exact RobinHood.RHTable.getElem?_insert_self _ _ _ hObjInv1] at hT
          obtain rfl : ({ tcb with schedContextBinding := .unbound } : TCB) = tcb' := by
            simpa using hT
          exact absurd hAllowed hNotAllowed
        · by_cases hTs : t.toObjId = scId.toObjId
          · rw [show ((st.objects.insert scId.toObjId (KernelObject.schedContext { sc with boundThread := none, isActive := false })).insert tid.toObjId (KernelObject.tcb { tcb with schedContextBinding := .unbound }))[t.toObjId]? = some (KernelObject.schedContext { sc with boundThread := none, isActive := false }) from by rw [hTs]; simp only [RHTable_getElem?_eq_get?]; rw [RobinHood.RHTable.getElem?_insert_ne _ tid.toObjId scId.toObjId _ (by simp; exact fun h => hNeTS h) hObjInv1]; exact RobinHood.RHTable.getElem?_insert_self _ _ _ hObjInv] at hT
            cases hT
          · rw [show ((st.objects.insert scId.toObjId (KernelObject.schedContext { sc with boundThread := none, isActive := false })).insert tid.toObjId (KernelObject.tcb { tcb with schedContextBinding := .unbound }))[t.toObjId]? = st.objects[t.toObjId]? from by simp only [RHTable_getElem?_eq_get?]; rw [RobinHood.RHTable.getElem?_insert_ne _ tid.toObjId t.toObjId _ (by simp; exact fun h => hTv (SeLe4n.ThreadId.toObjId_injective t tid h.symm)) hObjInv1]; rw [RobinHood.RHTable.getElem?_insert_ne _ scId.toObjId t.toObjId _ (by simp; exact fun h => hTs h.symm) hObjInv]] at hT
            exact ⟨tcb', hT, hUnb, hNQ, hNC, rfl⟩

/-- The donated-donation cancel: the verified donation return plus the
replenishment migration. -/
private theorem cancelDonatedDonationOnCore_preserves_ipcInvariantFull
    (st st' : SystemState) (vtid : SeLe4n.ValidThreadId) (tcb : TCB)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st)
    (hStored : st.getTcb? vtid.val = some tcb)
    (hAllowed : passiveServerIdleAllowed tcb.ipcState)
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
    unfold lookupTcb
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
          exact returnDonatedSchedContext_preserves_ipcInvariantFull st st1 ⟨tval, hprop⟩
            scId owner hObjInv hInv
            (by unfold replyDonationReturn?; rw [hLk]; simp [hB])
            (fun tcbX hX => by
              rw [hStored] at hX
              obtain rfl : tcb = tcbX := Option.some.inj hX
              exact hAllowed)
            hCl

/-- The bound-donation cancel touches only the victim's binding — every other
bundle-read TCB field survives. -/
private theorem cancelBoundDonationOnCore_victim_shape
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB) (rqCore : CoreId)
    (hObjInv : st.objects.invExt)
    (hStored : st.objects[tid.toObjId]? = some (.tcb tcb))
    (hStep : cancelBoundDonationOnCore st tid tcb rqCore = .ok st') :
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
      cases hScLk : st.getSchedContext? scId with
      | some sc =>
          rw [hScLk] at hStep
          dsimp only [] at hStep
          have hScPre := (SystemState.getSchedContext?_eq_some_iff st scId sc).mp hScLk
          have hNeTS : tid.toObjId ≠ scId.toObjId := by
            intro hEq
            rw [hEq, hScPre] at hStored
            cases hStored
          have hObjInv1 : (st.objects.insert scId.toObjId
              (KernelObject.schedContext { sc with boundThread := none, isActive := false })).invExt :=
            RHTable_insert_preserves_invExt _ _ _ hObjInv
          have hT2 : ({ { { st with objects := st.objects.insert scId.toObjId (KernelObject.schedContext { sc with boundThread := none, isActive := false }) } with scheduler := ({ st with objects := st.objects.insert scId.toObjId (KernelObject.schedContext { sc with boundThread := none, isActive := false }) } : SystemState).scheduler.setReplenishQueueOnCore rqCore (ReplenishQueue.remove (({ st with objects := st.objects.insert scId.toObjId (KernelObject.schedContext { sc with boundThread := none, isActive := false }) } : SystemState).scheduler.replenishQueueOnCore rqCore) scId) } with scThreadIndex := scThreadIndexRemove ({ { st with objects := st.objects.insert scId.toObjId (KernelObject.schedContext { sc with boundThread := none, isActive := false }) } with scheduler := ({ st with objects := st.objects.insert scId.toObjId (KernelObject.schedContext { sc with boundThread := none, isActive := false }) } : SystemState).scheduler.setReplenishQueueOnCore rqCore (ReplenishQueue.remove (({ st with objects := st.objects.insert scId.toObjId (KernelObject.schedContext { sc with boundThread := none, isActive := false }) } : SystemState).scheduler.replenishQueueOnCore rqCore) scId) } : SystemState).scThreadIndex scId tid } : SystemState).getTcb? tid = some tcb := by
            refine (SystemState.getTcb?_eq_some_iff _ tid tcb).mpr ?_
            show (st.objects.insert scId.toObjId (KernelObject.schedContext { sc with boundThread := none, isActive := false }))[tid.toObjId]? = some (.tcb tcb)
            simp only [RHTable_getElem?_eq_get?]
            rw [RobinHood.RHTable.getElem?_insert_ne st.objects scId.toObjId tid.toObjId _
              (by simp; exact fun h => hNeTS h.symm) hObjInv]
            rw [← RHTable_getElem?_eq_get?]
            exact hStored
          rw [hT2] at hStep
          dsimp only [] at hStep
          cases hStep
          intro tcbX hX
          have hXobj := (SystemState.getTcb?_eq_some_iff _ tid tcbX).mp hX
          rw [show ((st.objects.insert scId.toObjId (KernelObject.schedContext { sc with boundThread := none, isActive := false })).insert tid.toObjId (KernelObject.tcb { tcb with schedContextBinding := .unbound }))[tid.toObjId]? = some (KernelObject.tcb { tcb with schedContextBinding := .unbound }) from by simp only [RHTable_getElem?_eq_get?]; exact RobinHood.RHTable.getElem?_insert_self _ _ _ hObjInv1] at hXobj
          obtain rfl : ({ tcb with schedContextBinding := .unbound } : TCB) = tcbX := by
            simpa using hXobj
          exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      | none =>
          rw [hScLk] at hStep
          dsimp only [] at hStep
          have hT2 : ({ { st with scheduler := st.scheduler.setReplenishQueueOnCore rqCore (ReplenishQueue.remove (st.scheduler.replenishQueueOnCore rqCore) scId) } with scThreadIndex := scThreadIndexRemove ({ st with scheduler := st.scheduler.setReplenishQueueOnCore rqCore (ReplenishQueue.remove (st.scheduler.replenishQueueOnCore rqCore) scId) } : SystemState).scThreadIndex scId tid } : SystemState).getTcb? tid = some tcb := by
            refine (SystemState.getTcb?_eq_some_iff _ tid tcb).mpr ?_
            exact hStored
          rw [hT2] at hStep
          dsimp only [] at hStep
          cases hStep
          intro tcbX hX
          have hXobj := (SystemState.getTcb?_eq_some_iff _ tid tcbX).mp hX
          rw [show (st.objects.insert tid.toObjId (KernelObject.tcb { tcb with schedContextBinding := .unbound }))[tid.toObjId]? = some (KernelObject.tcb { tcb with schedContextBinding := .unbound }) from by simp only [RHTable_getElem?_eq_get?]; exact RobinHood.RHTable.getElem?_insert_self _ _ _ hObjInv] at hXobj
          obtain rfl : ({ tcb with schedContextBinding := .unbound } : TCB) = tcbX := by
            simpa using hXobj
          exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The donation return churns only bindings — the server's other bundle-read
fields survive its three stores. -/
private theorem returnDonatedSchedContext_victim_shape
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (owner : SeLe4n.ThreadId) (tcb : TCB)
    (hObjInv : st.objects.invExt)
    (hStored : st.objects[tid.toObjId]? = some (.tcb tcb))
    (hStep : returnDonatedSchedContext st tid scId owner = .ok st') :
    ∀ tcbX : TCB, st'.getTcb? tid = some tcbX →
      tcbX.ipcState = tcb.ipcState ∧ tcbX.pendingMessage = tcb.pendingMessage ∧
      tcbX.timeoutBudget = tcb.timeoutBudget ∧ tcbX.queuePrev = tcb.queuePrev ∧
      tcbX.queueNext = tcb.queueNext ∧ tcbX.queuePPrev = tcb.queuePPrev := by
  unfold returnDonatedSchedContext at hStep
  cases hScLk : st.objects[scId.toObjId]? with
  | none => rw [hScLk] at hStep; cases hStep
  | some obj =>
      cases obj with
      | schedContext sc =>
          rw [hScLk] at hStep
          dsimp only [] at hStep
          split at hStep
          · cases hStep
          · cases hS1 : storeObject scId.toObjId (.schedContext { sc with boundThread := some owner }) st with
            | error e => rw [hS1] at hStep; cases hStep
            | ok p1 =>
                obtain ⟨u1, st1⟩ := p1; cases u1
                rw [hS1] at hStep
                dsimp only [] at hStep
                have hObjInv1 : st1.objects.invExt := by
                  unfold storeObject at hS1
                  cases hS1
                  exact RHTable_insert_preserves_invExt _ _ _ hObjInv
                have hNeTS : tid.toObjId ≠ scId.toObjId := by
                  intro hEq
                  rw [hEq, hScLk] at hStored
                  cases hStored
                have hT1 : st1.objects[tid.toObjId]? = some (.tcb tcb) := by
                  rw [storeObject_objects_ne st st1 scId.toObjId tid.toObjId _ hNeTS hObjInv hS1]
                  exact hStored
                cases hL1 : lookupTcb st1 owner with
                | none => rw [hL1] at hStep; cases hStep
                | some clientTcb =>
                    rw [hL1] at hStep
                    dsimp only [] at hStep
                    cases hS2 : storeObject owner.toObjId (.tcb { clientTcb with schedContextBinding := .bound scId }) st1 with
                    | error e => rw [hS2] at hStep; cases hStep
                    | ok p2 =>
                        obtain ⟨u2, st2⟩ := p2; cases u2
                        rw [hS2] at hStep
                        dsimp only [] at hStep
                        have hObjInv2 : st2.objects.invExt := by
                          unfold storeObject at hS2
                          cases hS2
                          exact RHTable_insert_preserves_invExt _ _ _ hObjInv1
                        have hT2 : ∃ tcbM : TCB, st2.objects[tid.toObjId]? = some (.tcb tcbM) ∧
                            tcbM.ipcState = tcb.ipcState ∧ tcbM.pendingMessage = tcb.pendingMessage ∧
                            tcbM.timeoutBudget = tcb.timeoutBudget ∧ tcbM.queuePrev = tcb.queuePrev ∧
                            tcbM.queueNext = tcb.queueNext ∧ tcbM.queuePPrev = tcb.queuePPrev := by
                          by_cases hOw : owner.toObjId = tid.toObjId
                          · refine ⟨{ clientTcb with schedContextBinding := .bound scId }, ?_, ?_⟩
                            · rw [← hOw]
                              exact storeObject_objects_eq st1 st2 owner.toObjId _ hObjInv1 hS2
                            · have hCl : clientTcb = tcb := by
                                unfold lookupTcb at hL1
                                split at hL1
                                · cases hL1
                                · rw [hOw, hT1] at hL1
                                  simp only [Option.some.injEq] at hL1
                                  exact hL1.symm
                              rw [hCl]
                              exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
                          · refine ⟨tcb, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
                            rw [storeObject_objects_ne st1 st2 owner.toObjId tid.toObjId _
                              (fun h => hOw h.symm) hObjInv1 hS2]
                            exact hT1
                        obtain ⟨tcbM, hTM, hFlds⟩ := hT2
                        cases hL2 : lookupTcb st2 tid with
                        | none => rw [hL2] at hStep; cases hStep
                        | some serverTcb =>
                            rw [hL2] at hStep
                            dsimp only [] at hStep
                            have hSrv : serverTcb = tcbM := by
                              unfold lookupTcb at hL2
                              split at hL2
                              · cases hL2
                              · rw [hTM] at hL2
                                simp only [Option.some.injEq] at hL2
                                exact hL2.symm
                            cases hS3 : storeObject tid.toObjId (.tcb { serverTcb with schedContextBinding := .unbound }) st2 with
                            | error e => rw [hS3] at hStep; cases hStep
                            | ok p3 =>
                                obtain ⟨u3, st3⟩ := p3; cases u3
                                rw [hS3] at hStep
                                dsimp only [] at hStep
                                cases hStep
                                intro tcbX hX
                                have hXobj := (SystemState.getTcb?_eq_some_iff _ tid tcbX).mp hX
                                dsimp only [] at hXobj
                                rw [storeObject_objects_eq st2 st3 tid.toObjId _ hObjInv2 hS3] at hXobj
                                obtain rfl : ({ serverTcb with schedContextBinding := .unbound } : TCB) = tcbX := by
                                  simpa using hXobj
                                rw [hSrv]
                                exact hFlds
      | tcb _ | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _
      | reply _ => rw [hScLk] at hStep; cases hStep

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
    unfold lookupTcb
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
          have hXobj := (SystemState.getTcb?_eq_some_iff _ tval tcbX).mp hX
          rw [migrateSchedContextReplenishment_objects] at hXobj
          have hX1 : st1.getTcb? tval = some tcbX :=
            (SystemState.getTcb?_eq_some_iff st1 tval tcbX).mpr hXobj
          unfold cleanupDonatedSchedContext at hCl
          simp only [hLk, hB] at hCl
          exact returnDonatedSchedContext_victim_shape st st1 tval scId owner tcb hObjInv
            ((SystemState.getTcb?_eq_some_iff st tval tcb).mp hStored) hCl tcbX hX1

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
    ipcInvariantFull (match (Lifecycle.Suspend.clearPendingState stR2 tid).getTcb? tid with | some tcb'' => { Lifecycle.Suspend.clearPendingState stR2 tid with objects := (Lifecycle.Suspend.clearPendingState stR2 tid).objects.insert tid.toObjId (.tcb { tcb'' with threadState := .Inactive }) } | none => Lifecycle.Suspend.clearPendingState stR2 tid) ∧
    (match (Lifecycle.Suspend.clearPendingState stR2 tid).getTcb? tid with | some tcb'' => { Lifecycle.Suspend.clearPendingState stR2 tid with objects := (Lifecycle.Suspend.clearPendingState stR2 tid).objects.insert tid.toObjId (.tcb { tcb'' with threadState := .Inactive }) } | none => Lifecycle.Suspend.clearPendingState stR2 tid).objects.invExt := by
  have hFields : ∀ tcbX : TCB, stR2.getTcb? tid = some tcbX →
      tcbX.pendingMessage = none ∧ tcbX.timeoutBudget = none ∧
      tcbX.queuePrev = none ∧ tcbX.queueNext = none ∧ tcbX.queuePPrev = none :=
    fun tcbX hX => (hShapeR tcbX hX).2
  have hEq := clearPendingState_getElem_eq_of_quiescent stR2 tid hObjInvR hFields
  have hObjInvC : (Lifecycle.Suspend.clearPendingState stR2 tid).objects.invExt := by
    unfold Lifecycle.Suspend.clearPendingState
    split
    · exact RHTable_insert_preserves_invExt _ _ _ hObjInvR
    · exact hObjInvR
  have hInvC : ipcInvariantFull (Lifecycle.Suspend.clearPendingState stR2 tid) := by
    refine ipcInvariantFull_of_getElem_eq hEq ?_ hInvR
    intro t tcbT hT hUnb hNQ hNC
    rw [hEq] at hT
    have hSchedC : (Lifecycle.Suspend.clearPendingState stR2 tid).scheduler = stR2.scheduler := by
      unfold Lifecycle.Suspend.clearPendingState
      split <;> rfl
    rw [hSchedC] at hNQ hNC
    exact hInvR.passiveServerIdle t tcbT hT hUnb hNQ hNC
  cases hLkC : (Lifecycle.Suspend.clearPendingState stR2 tid).getTcb? tid with
  | none => exact ⟨hInvC, hObjInvC⟩
  | some tcb2 =>
      constructor
      · exact insertObjects_tcbFieldUpdate_preserves_ipcInvariantFull
          (Lifecycle.Suspend.clearPendingState stR2 tid) tid tcb2
          { tcb2 with threadState := .Inactive } hObjInvC hInvC
          ((SystemState.getTcb?_eq_some_iff _ tid tcb2).mp hLkC)
          rfl rfl rfl rfl rfl rfl rfl rfl rfl
      · exact RHTable_insert_preserves_invExt _ _ _ hObjInvC

/-- The suspend tail's deschedule stage: one or two run-queue removals of a
`.ready` victim, then the clear-and-deactivate stage. -/
private theorem suspendDescheduleTail_shape
    (stD : SystemState) (tid : SeLe4n.ThreadId) (c1 c2 : CoreId)
    (hObjInvD : stD.objects.invExt)
    (hShape : ∀ tcbX : TCB, stD.getTcb? tid = some tcbX →
      tcbX.ipcState = .ready ∧ tcbX.pendingMessage = none ∧ tcbX.timeoutBudget = none ∧
      tcbX.queuePrev = none ∧ tcbX.queueNext = none ∧ tcbX.queuePPrev = none)
    (hInvD : ipcInvariantFull stD) :
    ipcInvariantFull (removeRunnableOnCore (removeRunnableOnCore stD tid c1) tid c2) ∧
    (removeRunnableOnCore (removeRunnableOnCore stD tid c1) tid c2).objects.invExt ∧
    (∀ tcbX : TCB,
      (removeRunnableOnCore (removeRunnableOnCore stD tid c1) tid c2).getTcb? tid
        = some tcbX →
      tcbX.ipcState = .ready ∧ tcbX.pendingMessage = none ∧ tcbX.timeoutBudget = none ∧
      tcbX.queuePrev = none ∧ tcbX.queueNext = none ∧ tcbX.queuePPrev = none) := by
  have hReadyD : ∀ tcbX : TCB, stD.getTcb? tid = some tcbX → tcbX.ipcState = .ready :=
    fun tcbX hX => (hShape tcbX hX).1
  have hInv1 := removeRunnableOnCore_preserves_ipcInvariantFull stD tid c1 hReadyD hInvD
  have hInv2 := removeRunnableOnCore_preserves_ipcInvariantFull
    (removeRunnableOnCore stD tid c1) tid c2 (fun tcbX hX => hReadyD tcbX hX) hInv1
  exact ⟨hInv2, hObjInvD, fun tcbX hX => hShape tcbX hX⟩

/-- `.tcbSuspend` (dispatch arm): the whole per-core suspension pipeline —
cancel (inert on a quiescent victim), PIP revert (empty for a `.ready`
victim), donation cancel (all three binding arms), home/running deschedule,
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
        rw [Lifecycle.Suspend.cancelIpcBlockingValid_eq,
          cancelIpcBlocking_ready_id st vtid.val tcb hReady] at hStep
        have hBS : PriorityInheritance.blockingServer st vtid.val = none := by
          unfold PriorityInheritance.blockingServer
          simp [hPre, hReady]
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
              (match (Lifecycle.Suspend.clearPendingState stR2 vtid.val).getTcb? vtid.val with | some tcb'' => { Lifecycle.Suspend.clearPendingState stR2 vtid.val with objects := (Lifecycle.Suspend.clearPendingState stR2 vtid.val).objects.insert vtid.val.toObjId (.tcb { tcb'' with threadState := .Inactive }) } | none => Lifecycle.Suspend.clearPendingState stR2 vtid.val)
              c2 ecX wc ld = .ok (stO, sgiO) →
            ipcInvariantFull stO := by
          intro stD _ _ _ stR2 hObjInvR hInvR hShapeR c2 ecX wc ld stO sgiO hStepO
          obtain ⟨hInvI, hObjInvI⟩ :=
            suspendClearStore_preserves_ipcInvariantFull stR2 vtid.val hObjInvR hShapeR hInvR
          exact suspendRescheduleOnCore_preserves_ipcInvariantFull _ stO c2 ecX wc ld sgiO
            hObjInvI hInvI hStepO
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
            cases hRC : runningCoreOf? st vtid.val with
            | none =>
                simp only [hRC] at hStep
                exact hTail st hObjInv hInv hShapeD
                  (removeRunnableOnCore st vtid.val (determineTargetCore st vtid.val))
                  hObjInv
                  (removeRunnableOnCore_preserves_ipcInvariantFull st vtid.val
                    (determineTargetCore st vtid.val)
                    (fun tcbX hX => (hShapeD tcbX hX).1) hInv)
                  (fun tcbX hX => hShapeD tcbX hX)
                  _ ec _ _ st' sgi hStep
            | some rc =>
                simp only [hRC] at hStep
                by_cases hEqC : (rc == determineTargetCore st vtid.val) = true
                · simp only [hEqC] at hStep
                  exact hTail st hObjInv hInv hShapeD
                    (removeRunnableOnCore st vtid.val (determineTargetCore st vtid.val))
                    hObjInv
                    (removeRunnableOnCore_preserves_ipcInvariantFull st vtid.val
                      (determineTargetCore st vtid.val)
                      (fun tcbX hX => (hShapeD tcbX hX).1) hInv)
                    (fun tcbX hX => hShapeD tcbX hX)
                    _ ec _ _ st' sgi hStep
                · simp only [hEqC] at hStep
                  obtain ⟨hInv2, hObjInv2, hShape2⟩ := suspendDescheduleTail_shape st vtid.val
                    (determineTargetCore st vtid.val) rc hObjInv hShapeD hInv
                  exact hTail st hObjInv hInv hShapeD _ hObjInv2 hInv2 hShape2
                    _ ec _ _ st' sgi hStep
        | bound scId =>
            simp only [hB] at hStep
            cases hDon : cancelBoundDonationOnCore st vtid.val tcb
                (determineTargetCore st vtid.val) with
            | error e => rw [hDon] at hStep; cases hStep
            | ok stD =>
                rw [hDon] at hStep
                dsimp only [] at hStep
                have hInvD := cancelBoundDonationOnCore_preserves_ipcInvariantFull st stD
                  vtid.val tcb (determineTargetCore st vtid.val) hObjInv hInv hPre
                  (Or.inl hReady) hBidir hDon
                have hObjInvD := cancelBoundDonationOnCore_preserves_objects_invExt st stD
                  vtid.val tcb (determineTargetCore st vtid.val) hObjInv
                  hDon
                have hShapeD := hShapeOf stD
                  (cancelBoundDonationOnCore_victim_shape st stD vtid.val tcb
                    (determineTargetCore st vtid.val) hObjInv hPre
                    hDon)
                cases hRC : runningCoreOf? st vtid.val with
                | none =>
                    simp only [hRC] at hStep
                    exact hTail stD hObjInvD hInvD hShapeD
                      (removeRunnableOnCore stD vtid.val (determineTargetCore st vtid.val))
                      hObjInvD
                      (removeRunnableOnCore_preserves_ipcInvariantFull stD vtid.val
                        (determineTargetCore st vtid.val)
                        (fun tcbX hX => (hShapeD tcbX hX).1) hInvD)
                      (fun tcbX hX => hShapeD tcbX hX)
                      _ ec _ _ st' sgi hStep
                | some rc =>
                    simp only [hRC] at hStep
                    by_cases hEqC : (rc == determineTargetCore st vtid.val) = true
                    · simp only [hEqC] at hStep
                      exact hTail stD hObjInvD hInvD hShapeD
                        (removeRunnableOnCore stD vtid.val (determineTargetCore st vtid.val))
                        hObjInvD
                        (removeRunnableOnCore_preserves_ipcInvariantFull stD vtid.val
                          (determineTargetCore st vtid.val)
                          (fun tcbX hX => (hShapeD tcbX hX).1) hInvD)
                        (fun tcbX hX => hShapeD tcbX hX)
                        _ ec _ _ st' sgi hStep
                    · simp only [hEqC] at hStep
                      obtain ⟨hInv2, hObjInv2, hShape2⟩ := suspendDescheduleTail_shape stD
                        vtid.val (determineTargetCore st vtid.val) rc hObjInvD hShapeD hInvD
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
                  vtid tcb hObjInv hInv hLk (Or.inl hReady)
                  hDon
                have hObjInvD := cancelDonatedDonationOnCore_preserves_objects_invExt st stD
                  vtid.val tcb hObjInv hDon
                have hShapeD := hShapeOf stD
                  (cancelDonatedDonationOnCore_victim_shape st stD vtid tcb hObjInv hLk
                    hDon)
                cases hRC : runningCoreOf? st vtid.val with
                | none =>
                    simp only [hRC] at hStep
                    exact hTail stD hObjInvD hInvD hShapeD
                      (removeRunnableOnCore stD vtid.val (determineTargetCore st vtid.val))
                      hObjInvD
                      (removeRunnableOnCore_preserves_ipcInvariantFull stD vtid.val
                        (determineTargetCore st vtid.val)
                        (fun tcbX hX => (hShapeD tcbX hX).1) hInvD)
                      (fun tcbX hX => hShapeD tcbX hX)
                      _ ec _ _ st' sgi hStep
                | some rc =>
                    simp only [hRC] at hStep
                    by_cases hEqC : (rc == determineTargetCore st vtid.val) = true
                    · simp only [hEqC] at hStep
                      exact hTail stD hObjInvD hInvD hShapeD
                        (removeRunnableOnCore stD vtid.val (determineTargetCore st vtid.val))
                        hObjInvD
                        (removeRunnableOnCore_preserves_ipcInvariantFull stD vtid.val
                          (determineTargetCore st vtid.val)
                          (fun tcbX hX => (hShapeD tcbX hX).1) hInvD)
                        (fun tcbX hX => hShapeD tcbX hX)
                        _ ec _ _ st' sgi hStep
                    · simp only [hEqC] at hStep
                      obtain ⟨hInv2, hObjInv2, hShape2⟩ := suspendDescheduleTail_shape stD
                        vtid.val (determineTargetCore st vtid.val) rc hObjInvD hShapeD hInvD
                      exact hTail stD hObjInvD hInvD hShapeD _ hObjInv2 hInv2 hShape2
                        _ ec _ _ st' sgi hStep

-- ============================================================================
-- §16  Return-frame staging composites (`Architecture.stage*`)
-- ============================================================================

/-- Delivery staging is `writeReturnFrameToTcb` or the identity. -/
theorem stageDeliveredMessage_preserves_ipcInvariantFull
    (st : SystemState) (tid : SeLe4n.ThreadId) (installedCaps : Nat)
    (hObjInv : st.objects.invExt) (hInv : ipcInvariantFull st) :
    ipcInvariantFull (Architecture.stageDeliveredMessage st tid installedCaps) := by
  unfold Architecture.stageDeliveredMessage
  cases st.getTcb? tid with
  | none => exact hInv
  | some tcb =>
      dsimp only []
      split
      · cases tcb.pendingMessage with
        | none => exact hInv
        | some msg =>
            exact writeReturnFrameToTcb_preserves_ipcInvariantFull st tid _ hObjInv hInv
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
        | some msg => exact writeReturnFrameToTcb_preserves_objects_invExt st tid _ hObjInv
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
            unfold Architecture.writeReturnFrameToTcb
            cases hLk2 : st.getTcb? tid with
            | none => exact hObjInv
            | some tcb2 =>
                exact RHTable_insert_preserves_invExt _ _ _ hObjInv
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
          · unfold Architecture.writeReturnFrameToTcb
            cases st.getTcb? tid with
            | none => exact hObjInv
            | some tcb2 => exact RHTable_insert_preserves_invExt _ _ _ hObjInv
          · exact hObjInv

end SeLe4n.Kernel
