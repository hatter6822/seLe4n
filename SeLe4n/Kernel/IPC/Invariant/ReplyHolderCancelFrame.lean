-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.Invariant.CancelAllFrame
import SeLe4n.Kernel.IPC.CrossCore.ReplyHolderCancel

/-!
# What a reply holder's cancel writes

`cancelReplyHolder` (seL4-MCS `receiveIPC`'s `cancelIPC(replyTCB)`) is the
suspend's IPC teardown on the busy reply's holder, the boost it lent reverted,
and the `Inactive` write.  Its write frame is a finalisation's
(`FinaliseFrameAny`): every key keeps its object or holds a thread, an endpoint,
a notification, a scheduling context or a reply before and after, of the same
kind and with the same capability slots.  So it writes no CNode
(`cancelReplyHolder_getCNode?`), and the receive that runs on the cancelled
state resolves every capability as it resolved on the state it was handed.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

namespace finaliseWriteAny

/-- A finalisation write writes no CNode. -/
theorem getCNode? {st st' : SystemState} (h : finaliseWriteAny st st') (id : SeLe4n.ObjId) :
    st'.getCNode? id = st.getCNode? id := by
  have hN : ∀ cn : CNode, ¬ finaliseWritableAny (.cnode cn) := fun cn hw => hw.not_cnode rfl
  cases hS : st.getCNode? id with
  | some cn =>
    exact (SystemState.getCNode?_eq_some_iff _ _ _).mpr
      (h.keeps ((SystemState.getCNode?_eq_some_iff _ _ _).mp hS) (hN cn))
  | none =>
    cases hS' : st'.getCNode? id with
    | none => rfl
    | some cn =>
      have := h.keeps' ((SystemState.getCNode?_eq_some_iff _ _ _).mp hS') (hN cn)
      rw [← (SystemState.getCNode?_eq_some_iff _ _ _).mpr this, hS]

end finaliseWriteAny

namespace FinaliseFrame

/-- One queue neighbour's links patched in its slot. -/
theorem queueNeighbourPatch (st : SystemState) (nid? : Option SeLe4n.ThreadId)
    (upd : TCB → TCB) (hInv : st.objects.invExt)
    (hU : ∀ t, (upd t).spaceCells = t.spaceCells ∧ (upd t).spaceLinks = t.spaceLinks)
    (hL : ∀ t, TCB.loanKept (upd t) t) :
    FinaliseFrame st { st with objects := SeLe4n.Kernel.queueNeighbourPatch st.objects nid? upd } := by
  cases nid? with
  | none => exact .refl hInv
  | some nid =>
    have hKeep : SeLe4n.Kernel.queueNeighbourPatch st.objects (some nid) upd = st.objects →
        FinaliseFrame st
          { st with objects := SeLe4n.Kernel.queueNeighbourPatch st.objects (some nid) upd } :=
      fun e => by rw [e]; exact .refl hInv
    cases h : st.objects[nid.toObjId]? with
    | none => exact hKeep (by simp only [SeLe4n.Kernel.queueNeighbourPatch, h])
    | some o =>
      cases o
      case tcb t =>
        have hG : st.getTcb? nid = some t := (SystemState.getTcb?_eq_some_iff st nid t).mpr h
        have e : { st with objects := SeLe4n.Kernel.queueNeighbourPatch st.objects (some nid) upd }
            = st.updateTcb nid upd := by
          rw [SystemState.updateTcb_eq_of_some hG]
          simp only [SeLe4n.Kernel.queueNeighbourPatch, h]
        rw [e]
        exact updateTcb st nid upd hInv hU hL
      all_goals exact hKeep (by simp only [SeLe4n.Kernel.queueNeighbourPatch, h])

/-- The mid-queue splice: the removed thread's two neighbours' links patched. -/
theorem spliceOutMidQueueNode (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) :
    FinaliseFrame st (SeLe4n.Kernel.spliceOutMidQueueNode st tid) := by
  rw [spliceOutMidQueueNode_eq_patches]
  split
  · exact .refl hInv
  · rename_i tcb _
    have h1 := queueNeighbourPatch st tcb.queuePrev (queueUnlinkPredecessor tcb) hInv
      (fun _ => ⟨rfl, rfl⟩) (fun _ => ⟨rfl, fun _ _ h => h⟩)
    exact h1.trans (queueNeighbourPatch _ tcb.queueNext (queueUnlinkSuccessor tcb) h1.invExt
      (fun _ => ⟨rfl, rfl⟩) (fun _ => ⟨rfl, fun _ _ h => h⟩))

/-- An endpoint rewritten in its slot. -/
theorem rewriteEndpoint (s : SystemState) (e : SeLe4n.ObjId) (ep ep' : Endpoint)
    (hInv : s.objects.invExt) (hE : s.objects[e]? = some (.endpoint ep))
    (hA : s.rewriteAdmissible e (.endpoint ep')) :
    FinaliseFrame s (s.rewriteObject e (.endpoint ep') hA) := by
  have hEq : s.rewriteObject e (.endpoint ep') hA
      = s.modifyObject e (fun o => match o with | .endpoint _ => .endpoint ep' | o => o) := by
    unfold SystemState.rewriteObject SystemState.modifyObject
    rw [RobinHood.RHTable.modify_of_get? (by rw [← RHTable_getElem?_eq_get?]; exact hE)]
  rw [hEq]
  exact modifyObject s e _ hInv (fun o => by
    cases o with
    | endpoint _ =>
      exact Or.inr ⟨rfl, rfl, rfl, Or.inr (Or.inl rfl), by simp [KernelObject.objectType]⟩
    | _ => exact Or.inl rfl)

/-- The targeted dequeue (seL4's `tcbEPDequeue`): the splice, then the one
endpoint whose queue ends name the thread rewritten in its slot. -/
theorem removeFromBlockingEndpoint (st : SystemState) (tid : SeLe4n.ThreadId)
    (e : SeLe4n.ObjId) (hInv : st.objects.invExt) :
    FinaliseFrame st (SeLe4n.Kernel.removeFromBlockingEndpoint st tid e) := by
  have h1 := spliceOutMidQueueNode st tid hInv
  rcases removeFromBlockingEndpoint_cases st tid e with hc | ⟨ep, hA, hE, hc⟩ <;> rw [hc]
  · exact h1
  · exact h1.trans (rewriteEndpoint _ e ep _ h1.invExt hE hA)

end FinaliseFrame

namespace FinaliseFrameAny

/-- **seL4-MCS `cancelIPC`'s teardown on any thread state** (`cancelIpcBlocking`):
nothing on a thread that is not blocked, the targeted dequeue and the restore on
an endpoint wait, the reply arm on a reply wait, the notification's on a
notification wait. -/
theorem cancelIpcBlocking (st : SystemState) (c : SeLe4n.ThreadId) (t : TCB)
    (hInv : st.objects.invExt) :
    FinaliseFrameAny st (Lifecycle.Suspend.cancelIpcBlocking st c t) := by
  have hEp : ∀ ep, FinaliseFrameAny st
      (Lifecycle.Suspend.restoreToReadyCancelled (removeFromBlockingEndpoint st c ep) c) := by
    intro ep
    have h1 := FinaliseFrame.removeFromBlockingEndpoint st c ep hInv
    unfold Lifecycle.Suspend.restoreToReadyCancelled Lifecycle.Suspend.restoreToReadyStaging
    exact (h1.trans (FinaliseFrame.updateTcb _ c _ h1.invExt)).any
  cases hB : t.ipcState with
  | ready =>
    have e : Lifecycle.Suspend.cancelIpcBlocking st c t = st := by
      unfold Lifecycle.Suspend.cancelIpcBlocking; rw [hB]
    rw [e]; exact .refl hInv
  | blockedOnSend ep =>
    have e : Lifecycle.Suspend.cancelIpcBlocking st c t =
        Lifecycle.Suspend.restoreToReadyCancelled (removeFromBlockingEndpoint st c ep) c := by
      unfold Lifecycle.Suspend.cancelIpcBlocking; rw [hB]
    rw [e]; exact hEp ep
  | blockedOnReceive ep =>
    have e : Lifecycle.Suspend.cancelIpcBlocking st c t =
        Lifecycle.Suspend.restoreToReadyCancelled (removeFromBlockingEndpoint st c ep) c := by
      unfold Lifecycle.Suspend.cancelIpcBlocking; rw [hB]
    rw [e]; exact hEp ep
  | blockedOnCall ep =>
    have e : Lifecycle.Suspend.cancelIpcBlocking st c t =
        Lifecycle.Suspend.restoreToReadyCancelled (removeFromBlockingEndpoint st c ep) c := by
      unfold Lifecycle.Suspend.cancelIpcBlocking; rw [hB]
    rw [e]; exact hEp ep
  | blockedOnReply ep rt => exact replyCancel st c t hInv hB
  | blockedOnNotification n => exact (FinaliseFrame.notificationCancel st c t n hInv hB).any

/-- The suspend's IPC cancel (seL4-MCS `cancelIPC`): the cut, then the
teardown. -/
theorem cancelIpcKeepingContexts (st : SystemState) (c : SeLe4n.ThreadId) (t : TCB)
    (hInv : st.objects.invExt) :
    FinaliseFrameAny st (Lifecycle.Suspend.cancelIpcKeepingContexts st c t) := by
  unfold Lifecycle.Suspend.cancelIpcKeepingContexts
  have h1 := cutCancelledCallerHead t (.refl hInv)
  exact h1.trans (cancelIpcBlocking _ c t h1.invExt)

end FinaliseFrameAny

/-- **A reply holder's cancel is a finalisation write**: the IPC cancel, the
chain revert and the `Inactive` write. -/
theorem cancelReplyHolder_finaliseFrameAny (st : SystemState) (holder : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (hInv : st.objects.invExt) :
    FinaliseFrameAny st (cancelReplyHolder st holder executingCore) := by
  unfold cancelReplyHolder
  split
  · exact .refl hInv
  · rename_i tcb _
    have h1 : FinaliseFrameAny st
        (Lifecycle.Suspend.suspendCancelRevert st holder tcb executingCore) := by
      unfold Lifecycle.Suspend.suspendCancelRevert
      have h0 := FinaliseFrameAny.cancelIpcKeepingContexts st holder tcb hInv
      dsimp only
      split
      · exact h0.trans (FinaliseFrame.propagatePip _ _ _ _ h0.invExt).any
      · exact h0
    exact h1.trans (FinaliseFrame.updateTcb _ holder _ h1.invExt).any

/-- A reply holder's cancel keeps the object table well formed. -/
theorem cancelReplyHolder_objects_invExt (st : SystemState) (holder : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (hInv : st.objects.invExt) :
    (cancelReplyHolder st holder executingCore).objects.invExt :=
  (cancelReplyHolder_finaliseFrameAny st holder executingCore hInv).invExt

/-- **A reply holder's cancel writes no CNode**, so every capability resolves on
the cancelled state as it resolved on the state it was handed. -/
theorem cancelReplyHolder_getCNode? (st : SystemState) (holder : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (hInv : st.objects.invExt) (id : SeLe4n.ObjId) :
    (cancelReplyHolder st holder executingCore).getCNode? id = st.getCNode? id :=
  (cancelReplyHolder_finaliseFrameAny st holder executingCore hInv).write.getCNode? id

end SeLe4n.Kernel
