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
import SeLe4n.Kernel.Scheduler.Operations.PerCoreCbs
import SeLe4n.Kernel.Capability.Operations
import SeLe4n.Kernel.SchedContext.OperationsPerCore
import SeLe4n.Kernel.Service.Registry

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
    split at hStep
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
private theorem lookupSlotCap_badge_valid (st : SystemState) (addr : CSpaceAddr)
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

end SeLe4n.Kernel
