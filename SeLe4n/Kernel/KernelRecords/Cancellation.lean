-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.KernelRecords.Fault
import SeLe4n.Kernel.IPC.Invariant.FinaliseThreadFrames
import SeLe4n.Kernel.Lifecycle.Invariant.CancellationQueueShape

/-!
# The cancellations keep the records

WS-ZA ZA6.37.  A cancellation takes a thread off the queue or the reply it waits
on and restores it `.ready`; the restore retires the thread's fault record
(`TCB.restoredToReady`), so the restored thread carries none.  Every other write
of a cancellation rewrites queue links, reply links, bindings or objects other
than threads, and keeps every thread's fault flag, thread state and IPC state
(`tcbProjKept faultFields`).  None of them writes a VSpace root.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- What a fault record's parking reads of a thread. -/
def faultFields (x : TCB) : Bool × ThreadState × ThreadIpcState :=
  (x.pendingFault.isSome, x.threadState, x.ipcState)

/-- A step keeping every thread's fault fields leaves every fault record parked. -/
theorem FaultsStayParked.of_kept {st st' : SystemState} (h : tcbProjKept faultFields st' st) :
    FaultsStayParked st st' :=
  of_fields fun t tcb' hT _ => by
    have e := h t
    rw [hT] at e
    cases hs : st.getTcb? t with
    | none => rw [hs] at e; cases e
    | some x =>
      rw [hs] at e
      simp only [Option.map_some, Option.some.injEq, faultFields, Prod.mk.injEq] at e
      exact ⟨x, rfl, e.1.symm, e.2.1.symm, e.2.2.symm⟩

/-- A step that keeps every VSpace root keeps every root's address-space view. -/
theorem rootViews_of_roots_iff {st st' : SystemState}
    (h : ∀ (k : SeLe4n.ObjId) (r : VSpaceRoot), st'.objects[k]? = some (.vspaceRoot r) ↔
      st.objects[k]? = some (.vspaceRoot r)) :
    ∀ k : SeLe4n.ObjId, rootViewOf st'.objects[k]? = rootViewOf st.objects[k]? := fun k => by
  cases h1 : rootViewOf st.objects[k]? with
  | some v =>
    obtain ⟨r, hr, -⟩ := root_of_rootViewOf h1
    rw [(h k r).2 hr, ← h1, hr]
  | none =>
    cases h2 : rootViewOf st'.objects[k]? with
    | none => rfl
    | some v =>
      obtain ⟨r, hr, -⟩ := root_of_rootViewOf h2
      rw [(h k r).1 hr] at h1
      simp [rootViewOf, KernelObject.mappingView] at h1

/-- The restore's field clear retires the fault record. -/
theorem TCB.restoredToReady_pendingFault (x : TCB) : x.restoredToReady.pendingFault = none := by
  unfold TCB.restoredToReady
  rw [TCB.setIpcState_pendingFault, TCB.pendingFault_setPendingFault]

namespace RecordsStep

/-- **A step keeping every root, the ASID table and every thread's fault fields.** -/
theorem of_kept {st st' : SystemState}
    (hR : ∀ (k : SeLe4n.ObjId) (r : VSpaceRoot), st'.objects[k]? = some (.vspaceRoot r) ↔
      st.objects[k]? = some (.vspaceRoot r))
    (hA : st'.asidTable = st.asidTable) (hI : st'.objects.invExt)
    (hK : tcbProjKept faultFields st' st) : RecordsStep st st' :=
  ⟨rootViews_of_roots_iff hR, hA, hI, FaultsStayParked.of_kept hK⟩

/-- **A finalisation-shaped write keeping every thread's fault fields.** -/
theorem of_finaliseKept {st st' : SystemState} (F : FinaliseFrameAny st st')
    (hK : tcbProjKept faultFields st' st) : RecordsStep st st' :=
  of_kept F.write.roots_iff F.asidTable F.invExt hK

/-- **The restore** retires the restored thread's fault record. -/
theorem restoreToReadyStaging (st : SystemState) (t : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) (hInv : st.objects.invExt) :
    RecordsStep st (Lifecycle.Suspend.restoreToReadyStaging st t frame) := by
  unfold Lifecycle.Suspend.restoreToReadyStaging
  exact updateTcb st t hInv fun x _ => TcbStaysParked.of_noFault (by
    cases frame with
    | none => exact TCB.restoredToReady_pendingFault x
    | some f => exact TCB.restoredToReady_pendingFault x)

theorem restoreToReadyCancelled (st : SystemState) (t : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) :
    RecordsStep st (Lifecycle.Suspend.restoreToReadyCancelled st t) :=
  restoreToReadyStaging st t _ hInv

end RecordsStep

-- ============================================================================
-- §2  A frame read off the threads and the roots
-- ============================================================================

/-- The thread a slot holds. -/
def tcbAt : Option KernelObject → Option TCB
  | some (.tcb t) => some t
  | _ => none

theorem getTcb?_eq_tcbAt (st : SystemState) (k : SeLe4n.ObjId) :
    st.getTcb? ⟨k.val⟩ = tcbAt st.objects[k]? := rfl

/-- A slot's record view is read off its thread's and its root's. -/
theorem recordViewOf_congr {o o' : Option KernelObject}
    (hT : (tcbAt o').map TCB.recordView = (tcbAt o).map TCB.recordView)
    (hR : rootViewOf o' = rootViewOf o) : recordViewOf o' = recordViewOf o := by
  rcases o with _ | x <;> rcases o' with _ | y
  · rfl
  · cases y <;> simp_all [tcbAt, rootViewOf, recordViewOf, KernelObject.mappingView]
  · cases x <;> simp_all [tcbAt, rootViewOf, recordViewOf, KernelObject.mappingView]
  · cases x <;> cases y <;> simp_all [tcbAt, rootViewOf, recordViewOf, KernelObject.mappingView]

/-- **A step keeping every root's view, the ASID table and every thread's record
view is a frame.** -/
theorem RecordsFrame.of_kept {st st' : SystemState}
    (hR : ∀ k : SeLe4n.ObjId, rootViewOf st'.objects[k]? = rootViewOf st.objects[k]?)
    (hA : st'.asidTable = st.asidTable) (hI : st'.objects.invExt)
    (hK : tcbProjKept TCB.recordView st' st) : RecordsFrame st st' :=
  ⟨fun k => recordViewOf_congr (by
      have := hK ⟨k.val⟩
      rwa [getTcb?_eq_tcbAt, getTcb?_eq_tcbAt] at this) (hR k), hA, hI⟩

-- ============================================================================
-- §1  The cancellation's writes
-- ============================================================================

namespace tcbProjKept

theorem removeFromBlockingEndpoint (st : SystemState) (t : SeLe4n.ThreadId) (e : SeLe4n.ObjId)
    (hInv : st.objects.invExt) :
    tcbProjKept faultFields (SeLe4n.Kernel.removeFromBlockingEndpoint st t e) st := fun x => by
  rw [removeFromBlockingEndpoint_getTcb?_eq_splice st t e hInv x]
  exact spliceOutMidQueueNode_tcbField_frame faultFields (fun _ _ _ _ _ _ => rfl) st t hInv x

theorem removeFromNotificationWaitQueue (st : SystemState) (t : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) :
    tcbProjKept faultFields (SeLe4n.Kernel.removeFromNotificationWaitQueue st t) st :=
  removeFromNotificationWaitQueue_tcbField_frame faultFields (fun _ _ _ _ _ _ => rfl) st t hInv

theorem cutThreadReplyFrameOut (st : SystemState) (t : TCB) (hInv : st.objects.invExt) :
    tcbProjKept faultFields (SeLe4n.Kernel.cutThreadReplyFrameOut st t) st :=
  of_fwd_bwd (fun k t0 hk => ⟨t0, cutThreadReplyFrameOut_tcb_eq st t hInv k t0 hk, rfl⟩)
    (fun k t' hk => ⟨t', cutThreadReplyFrameOut_tcb_backward st t hInv k t' hk⟩)

end tcbProjKept

theorem spliceOutMidQueueNode_asidTable (st : SystemState) (t : SeLe4n.ThreadId) :
    (spliceOutMidQueueNode st t).asidTable = st.asidTable := by
  unfold spliceOutMidQueueNode; split <;> rfl

theorem removeFromBlockingEndpoint_asidTable (st : SystemState) (t : SeLe4n.ThreadId)
    (e : SeLe4n.ObjId) : (removeFromBlockingEndpoint st t e).asidTable = st.asidTable := by
  rcases removeFromBlockingEndpoint_cases st t e with hc | ⟨ep, hA, hE, hc⟩ <;> rw [hc]
  · exact spliceOutMidQueueNode_asidTable st t
  · exact (SystemState.rewriteObject_asidTable _ _ _ _).trans (spliceOutMidQueueNode_asidTable st t)

namespace RecordsStep

/-- The targeted dequeue writes queue links and an endpoint. -/
theorem removeFromBlockingEndpoint (st : SystemState) (t : SeLe4n.ThreadId) (e : SeLe4n.ObjId)
    (hInv : st.objects.invExt) :
    RecordsStep st (SeLe4n.Kernel.removeFromBlockingEndpoint st t e) :=
  of_kept (fun k r =>
      (removeFromBlockingEndpoint_nonEndpoint st t e
        (spliceOutMidQueueNode_preserves_objects_invExt st t hInv) k _ (fun _ h => by cases h)).trans
      (spliceOutMidQueueNode_nonTcb st t hInv k _ (fun _ h => by cases h)))
    (removeFromBlockingEndpoint_asidTable st t e)
    (removeFromBlockingEndpoint_preserves_objects_invExt st t e hInv)
    (tcbProjKept.removeFromBlockingEndpoint st t e hInv)

/-- **The IPC teardown keeps the records**: every arm restores the cancelled
thread with its fault record retired, and its other writes keep every thread's
fault fields and every root. -/
theorem cancelIpcBlocking (st : SystemState) (t : SeLe4n.ThreadId) (tcb : TCB)
    (hInv : st.objects.invExt) : RecordsStep st (Lifecycle.Suspend.cancelIpcBlocking st t tcb) := by
  cases hB : tcb.ipcState with
  | ready => unfold Lifecycle.Suspend.cancelIpcBlocking; rw [hB]; exact refl hInv
  | blockedOnSend e | blockedOnReceive e | blockedOnCall e =>
    unfold Lifecycle.Suspend.cancelIpcBlocking; rw [hB]
    have S := removeFromBlockingEndpoint st t e hInv
    exact S.trans (restoreToReadyCancelled _ t S.invExt)
  | blockedOnReply ep rt =>
    rw [cancelIpcBlocking_replyArm_unfold st t tcb hB]
    have F0 := FinaliseFrameAny.returnDonationToCancelledCaller st t tcb hInv
    have S0 := of_finaliseKept F0
      (tcbProjKept.returnDonationToCancelledCaller st t tcb hInv fun _ _ _ => rfl)
    have F1 := FinaliseFrameAny.cutThreadReplyFrameOut _ tcb S0.invExt
    have S1 := S0.trans (of_finaliseKept F1 (tcbProjKept.cutThreadReplyFrameOut _ tcb S0.invExt))
    have S2 := S1.trans (restoreToReadyCancelled _ t S1.invExt)
    have F3 := FinaliseFrameAny.consumeReplyLink _ t tcb S2.invExt
    have S3 := S2.trans (of_finaliseKept F3
      (tcbProjKept.consumeReplyLink _ t tcb S2.invExt fun _ => rfl))
    exact S3.trans (unlinkReplyWaiterOpt _ t _ S3.invExt)
  | blockedOnNotification n =>
    have F := FinaliseFrame.notificationCancel st t tcb n hInv hB
    have hEq : Lifecycle.Suspend.cancelIpcBlocking st t tcb =
        Lifecycle.Suspend.restoreToReadyCancelled (SeLe4n.Kernel.removeFromNotificationWaitQueue st t) t := by
      unfold Lifecycle.Suspend.cancelIpcBlocking; rw [hB]
    have hI1 := removeFromNotificationWaitQueue_preserves_objects_invExt st t hInv
    refine ⟨(rootViews_of_roots_iff F.any.write.roots_iff), F.asidTable, F.invExt, ?_⟩
    rw [hEq]
    exact (FaultsStayParked.of_kept (tcbProjKept.removeFromNotificationWaitQueue st t hInv)).trans
      (restoreToReadyCancelled _ t hI1).faults

end RecordsStep

end SeLe4n.Kernel
