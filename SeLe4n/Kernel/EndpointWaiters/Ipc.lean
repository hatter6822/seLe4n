-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.EndpointWaiters.Stage
import SeLe4n.Kernel.KernelRecords.IpcCall

/-! # The blocking IPC arms: the creators

WS-SX SX11.2.  The send, the call and the receive each block at most their
invoking thread on the endpoint they name (`EndpointWaitersGrowAt`); every other write
they make keeps a thread's IPC state or writes one waiting on no endpoint (the
woken partner made `.ready`, a caller blocked on its reply).  The checked
dispatch that runs the arm checks `endpointFlowGate` on that thread and that
endpoint, two-way, so the new waiter has the endpoint's label and the arm is a
waiters' stage (`endpointFlowGate_implies_eq`).  Each proof follows the records'
own (`KernelRecords/IpcSend.lean`, `IpcReceive.lean`, `IpcCall.lean`), whose
frames it reuses.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

namespace EndpointWaitersGrowFrame

/-- **The per-core send blocks at most its sender, on its endpoint.** -/
theorem endpointSendDualOnCore {endpointId : SeLe4n.ObjId} {sender : SeLe4n.ThreadId}
    {payload : SendPayload} {c : CoreId} {st : SystemState} (hInv : st.objects.invExt) :
    EndpointWaitersGrowFrame sender endpointId st
      (_root_.SeLe4n.Kernel.endpointSendDualOnCore endpointId sender payload c st).1 := by
  unfold _root_.SeLe4n.Kernel.endpointSendDualOnCore
  split
  · split
    · split
      · exact refl hInv
      · split
        · exact refl hInv
        · rename_i receiver _tcb st1 hPop
          split
          · exact refl hInv
          · rename_i st2 hRecv
            have F1 := RecordsFrame.endpointQueuePopHead hInv hPop
            have S2 := EndpointWaitersFrame.storeTcbReceiveComplete F1.invExt hRecv
            obtain ⟨x, -, hx⟩ := modifyTcb_getTcb?_self F1.invExt hRecv
            have F3 := RecordsFrame.wakeThread st2 receiver c S2.invExt (fun y hy => by
              rw [hx] at hy; cases hy; simp)
            exact (((EndpointWaitersFrame.of_frame F1).trans S2).trans (.of_frame F3)).growAt _ _
    · split
      · exact refl hInv
      · rename_i st1 hEnq
        split
        · exact refl hInv
        · rename_i st2 hBlk
          have F1 := RecordsFrame.endpointQueueEnqueue hInv hEnq
          have G2 := storeTcbIpcStateAndMessage (e0 := endpointId) F1.invExt hBlk
            (fun _ h => ipcWaitsOnEndpoint_blockedOnSend h)
          have F3 := RecordsFrame.removeRunnableOnCore st2 sender c G2.invExt
          have F4 := RecordsFrame.recordSendCap _ sender payload.badge payload.grant
            payload.grantReply F3.invExt
          exact ((EndpointWaitersFrame.of_frame F1).thenGrow G2).thenFrame
            ((EndpointWaitersFrame.of_frame F3).trans (.of_frame F4))
  · split <;> exact refl hInv

/-- The send with capability transfer. -/
theorem endpointSendDualWithCapsOnCore {endpointId : SeLe4n.ObjId} {sender : SeLe4n.ThreadId}
    {payload : SendPayload} {c : CoreId} {st : SystemState} (hInv : st.objects.invExt) :
    EndpointWaitersGrowFrame sender endpointId st
      (_root_.SeLe4n.Kernel.endpointSendDualWithCapsOnCore endpointId sender payload c st).1 := by
  unfold _root_.SeLe4n.Kernel.endpointSendDualWithCapsOnCore
  have S := endpointSendDualOnCore (endpointId := endpointId) (sender := sender)
    (payload := payload) (c := c) hInv
  generalize _root_.SeLe4n.Kernel.endpointSendDualOnCore endpointId sender payload c st = r at S
  obtain ⟨st1, res⟩ := r
  dsimp only at S ⊢
  cases res with
  | error _ => exact S
  | ok sgi =>
    dsimp only
    repeat' split
    all_goals first
      | exact S
      | (rename_i hU
         exact S.thenFrame (.of_frame (RecordsFrame.receiveTransferCaps S.invExt hU)))

/-- **The per-core call blocks at most its caller, on its endpoint**: a caller
that meets a receiver blocks on its reply, which waits on no endpoint. -/
theorem endpointCallOnCore {endpointId : SeLe4n.ObjId} {caller : SeLe4n.ThreadId}
    {payload : SendPayload} {c : CoreId} {st : SystemState} (hInv : st.objects.invExt) :
    EndpointWaitersGrowFrame caller endpointId st
      (_root_.SeLe4n.Kernel.endpointCallOnCore endpointId caller payload c st).1 := by
  unfold _root_.SeLe4n.Kernel.endpointCallOnCore
  split
  · split
    · split
      · split
        · exact refl hInv
        · rename_i receiver _tcb st1 hPop
          have F1 := RecordsFrame.endpointQueuePopHead hInv hPop
          split
          · exact refl hInv
          · rename_i st2 hRdy
            have S2 := EndpointWaitersFrame.storeTcbIpcStateAndMessage F1.invExt hRdy
            obtain ⟨x, -, hx⟩ := modifyTcb_getTcb?_self F1.invExt hRdy
            have F3 := RecordsFrame.wakeThread st2 receiver c S2.invExt (fun y hy => by
              rw [hx] at hy; cases hy; simp)
            split
            · exact refl hInv
            · rename_i st4 hBlk
              have S4 := EndpointWaitersFrame.storeTcbIpcStateAndMessage F3.invExt hBlk
              split
              · exact refl hInv
              · rename_i st5 hLink
                have F5 := RecordsFrame.linkServerStashedReply S4.invExt hLink
                have F6 := RecordsFrame.removeRunnableOnCore st5 caller c F5.invExt
                have W7 := EndpointWaitersFrame.linkReplyWaiter _ caller receiver F6.invExt
                exact (((((EndpointWaitersFrame.of_frame F1).trans S2).trans (.of_frame F3)).trans
                  S4).trans ((EndpointWaitersFrame.of_frame F5).trans ((EndpointWaitersFrame.of_frame F6).trans
                  W7))).growAt _ _
      · split
        · exact refl hInv
        · rename_i receiver _tcb st1 hPop
          have F1 := RecordsFrame.endpointQueuePopHead hInv hPop
          split
          · exact refl hInv
          · rename_i st2 hRC
            split
            · exact refl hInv
            have S2 := EndpointWaitersFrame.storeTcbReceiveComplete F1.invExt hRC
            obtain ⟨x, -, hx⟩ := modifyTcb_getTcb?_self F1.invExt hRC
            have F3 := RecordsFrame.wakeThread st2 receiver c S2.invExt (fun y hy => by
              rw [hx] at hy; cases hy; simp)
            have F4 := RecordsFrame.removeRunnableOnCore _ caller c F3.invExt
            exact (((((EndpointWaitersFrame.of_frame F1).trans S2).trans (.of_frame F3)).trans
              (.of_frame F4)).trans (EndpointWaitersFrame.updateTcb _ caller F4.invExt
                (f := fun t => { t with threadState := .Inactive })
                fun _ => TcbWaitsKept.of_ipc rfl)).growAt _ _
    · split
      · exact refl hInv
      · rename_i st1 hEnq
        split
        · exact refl hInv
        · rename_i st2 hBlk
          have F1 := RecordsFrame.endpointQueueEnqueue hInv hEnq
          have G2 := storeTcbIpcStateAndMessage (e0 := endpointId) F1.invExt hBlk
            (fun _ h => ipcWaitsOnEndpoint_blockedOnCall h)
          have F3 := RecordsFrame.removeRunnableOnCore st2 caller c G2.invExt
          have F4 := RecordsFrame.recordSendCap _ caller payload.badge payload.grant
            payload.grantReply F3.invExt
          exact ((EndpointWaitersFrame.of_frame F1).thenGrow G2).thenFrame
            ((EndpointWaitersFrame.of_frame F3).trans (.of_frame F4))
  · split <;> exact refl hInv

theorem endpointCallWithCapsOnCore {endpointId : SeLe4n.ObjId} {caller : SeLe4n.ThreadId}
    {payload : SendPayload} {c : CoreId} {st : SystemState} (hInv : st.objects.invExt) :
    EndpointWaitersGrowFrame caller endpointId st
      (_root_.SeLe4n.Kernel.endpointCallWithCapsOnCore endpointId caller payload c st).1 := by
  unfold _root_.SeLe4n.Kernel.endpointCallWithCapsOnCore
  have S := endpointCallOnCore (endpointId := endpointId) (caller := caller) (payload := payload)
    (c := c) hInv
  generalize _root_.SeLe4n.Kernel.endpointCallOnCore endpointId caller payload c st = r at S
  obtain ⟨st1, res⟩ := r
  dsimp only at S ⊢
  cases res with
  | error _ => exact S
  | ok sgi =>
    dsimp only
    repeat' split
    all_goals first
      | exact S
      | (rename_i hU
         exact S.thenFrame (.of_frame (RecordsFrame.receiveTransferCaps S.invExt hU)))

theorem endpointCallCrossCoreDispatch {endpointId : SeLe4n.ObjId} {caller : SeLe4n.ThreadId}
    {payload : SendPayload} {c : CoreId} {st : SystemState}
    (hInv : st.objects.invExt) :
    EndpointWaitersGrowFrame caller endpointId st
      (_root_.SeLe4n.Kernel.endpointCallCrossCoreDispatch endpointId caller payload c st).1 := by
  unfold _root_.SeLe4n.Kernel.endpointCallCrossCoreDispatch
  have S := endpointCallWithCapsOnCore (endpointId := endpointId) (caller := caller)
    (payload := payload) (c := c) hInv
  generalize _root_.SeLe4n.Kernel.endpointCallWithCapsOnCore endpointId caller payload
    c st = r at S
  obtain ⟨st1, res⟩ := r
  dsimp only at S ⊢
  cases res with
  | error _ => exact S
  | ok p =>
    obtain ⟨summary, sgi⟩ := p
    dsimp only
    repeat' split
    all_goals first
      | exact S
      | (rename_i hD
         have F := ((RecordsFrame.applyCallDonationOnCore S.invExt) hD)
         exact S.thenFrame (.of_frame (F.trans
           (RecordsFrame.propagatePipChainCrossCore _ _ _ _ F.invExt))))

/-- **The per-core receive blocks at most its receiver, on its endpoint**: the
sender it meets is made `.ready` or blocked on its reply. -/
theorem endpointReceiveDualOnCore {endpointId : SeLe4n.ObjId} {receiver : SeLe4n.ThreadId}
    {replyId : Option SeLe4n.ReplyId} {c : CoreId} {st : SystemState} (hInv : st.objects.invExt) :
    EndpointWaitersGrowFrame receiver endpointId st
      (_root_.SeLe4n.Kernel.endpointReceiveDualOnCore endpointId receiver replyId c st).1 := by
  unfold _root_.SeLe4n.Kernel.endpointReceiveDualOnCore
  split
  · split
    · split
      · exact refl hInv
      · rename_i sender senderTcb st1 hPop
        have F1 := EndpointWaitersFrame.of_frame (RecordsFrame.endpointQueuePopHead hInv hPop)
        dsimp only
        split
        · simp only [↓reduceIte]
          split
          · split
            · exact refl hInv
            · rename_i st2 hBlk
              have S2 := F1.trans (EndpointWaitersFrame.storeTcbIpcStateAndMessage F1.invExt hBlk)
              split
              · exact refl hInv
              · split
                · exact refl hInv
                · rename_i stL hL
                  have F3 := S2.trans (.of_frame (RecordsFrame.linkCallerReply S2.invExt hL))
                  split
                  · rename_i st4 hRdy
                    have S4 := F3.trans (EndpointWaitersFrame.storeTcbIpcStateAndMessage F3.invExt hRdy)
                    exact (S4.trans (EndpointWaitersFrame.linkReplyWaiter _ _ _ S4.invExt)).growAt _ _
                  · exact refl hInv
          · split
            · exact refl hInv
            · rename_i st2 hRdy
              have S2 := F1.trans (EndpointWaitersFrame.storeTcbIpcStateAndMessage F1.invExt hRdy)
              have S3 := S2.trans (EndpointWaitersFrame.updateTcb _ sender S2.invExt
                (f := fun t => { t with threadState := .Inactive })
                fun _ => TcbWaitsKept.of_ipc rfl)
              split
              · rename_i st4 hRcvd
                exact (S3.trans (EndpointWaitersFrame.storeTcbIpcStateAndMessage S3.invExt hRcvd)).growAt _ _
              · exact refl hInv
        · simp only [Bool.false_eq_true, ↓reduceIte]
          split
          · exact refl hInv
          · rename_i st2 hRdy
            have S2 := F1.trans (EndpointWaitersFrame.storeTcbIpcStateAndMessage F1.invExt hRdy)
            obtain ⟨x, -, hx⟩ := modifyTcb_getTcb?_self F1.invExt hRdy
            have F3 := S2.trans (.of_frame (RecordsFrame.wakeThread st2 sender c S2.invExt
              (fun y hy => by rw [hx] at hy; cases hy; simp)))
            split
            · rename_i st4 hRcvd
              exact (F3.trans (EndpointWaitersFrame.storeTcbIpcStateAndMessage F3.invExt hRcvd)).growAt _ _
            · exact refl hInv
    · split
      · exact refl hInv
      · rename_i stClean hClean
        have F0 := RecordsFrame.cleanupPreReceiveDonationMigrated hInv hClean
        split
        · exact refl hInv
        · rename_i st1 hEnq
          have F1 := EndpointWaitersFrame.of_frame (F0.trans (RecordsFrame.endpointQueueEnqueue F0.invExt hEnq))
          split
          · exact refl hInv
          · rename_i st2 hBlk
            have G2 := F1.thenGrow (storeTcbIpcStateAndMessage (e0 := endpointId) F1.invExt hBlk
              (fun _ h => ipcWaitsOnEndpoint_blockedOnReceive h))
            split
            · exact G2.thenFrame (.of_frame (RecordsFrame.removeRunnableOnCore _ _ _ G2.invExt))
            · rename_i rTcb hT
              split
              · split
                · exact refl hInv
                · rename_i stS hS
                  have FR := RecordsFrame.recordReplyStasher _ (SeLe4n.ReplyId.optCode replyId)
                    receiver G2.invExt
                  have hTR : (st2.recordReplyStasher (SeLe4n.ReplyId.optCode replyId) receiver).objects[receiver.toObjId]?
                      = some (.tcb rTcb) := (SystemState.getTcb?_eq_some_iff _ _ _).mp
                    (by rw [SystemState.recordReplyStasher_getTcb? _ _ _ G2.invExt]; exact hT)
                  have F3 := FR.trans (RecordsFrame.storeObject FR.invExt hS (by rw [hTR]; rfl)
                    (fun _ h => by cases h))
                  exact G2.thenFrame ((EndpointWaitersFrame.of_frame F3).trans
                    (.of_frame (RecordsFrame.removeRunnableOnCore _ _ _ F3.invExt)))
              · exact refl hInv
  · split <;> exact refl hInv

theorem endpointReceiveDualWithCapsOnCore {endpointId : SeLe4n.ObjId} {receiver : SeLe4n.ThreadId}
    {replyId : Option SeLe4n.ReplyId} {c : CoreId} {st : SystemState} (hInv : st.objects.invExt) :
    EndpointWaitersGrowFrame receiver endpointId st
      (_root_.SeLe4n.Kernel.endpointReceiveDualWithCapsOnCore endpointId receiver replyId c st).1 := by
  unfold _root_.SeLe4n.Kernel.endpointReceiveDualWithCapsOnCore
  have S := endpointReceiveDualOnCore (endpointId := endpointId) (receiver := receiver)
    (replyId := replyId) (c := c) hInv
  generalize _root_.SeLe4n.Kernel.endpointReceiveDualOnCore endpointId receiver replyId c st = r at S
  obtain ⟨st1, res⟩ := r
  dsimp only at S ⊢
  cases res with
  | error _ => exact S
  | ok p =>
    obtain ⟨senderId, sgi⟩ := p
    dsimp only
    repeat' split
    all_goals first
      | exact S
      | (rename_i hU
         exact S.thenFrame (.of_frame (RecordsFrame.receiveTransferCaps S.invExt hU)))

end EndpointWaitersGrowFrame


namespace EndpointWaitersStage

variable {ctx : LabelingContext}

/-- **The checked send carries the waiters' labels**: its gate, two-way, gives
the sender the endpoint's label before the send can block it. -/
theorem endpointSendCrossCoreDispatchChecked {endpointId : SeLe4n.ObjId}
    {sender : SeLe4n.ThreadId} {payload : SendPayload} {c : CoreId} {st : SystemState}
    (hInv : st.objects.invExt) :
    EndpointWaitersStage ctx st (_root_.SeLe4n.Kernel.endpointSendCrossCoreDispatchChecked ctx endpointId
      sender payload c st).1 := by
  unfold _root_.SeLe4n.Kernel.endpointSendCrossCoreDispatchChecked
  split
  · rename_i hGate
    exact (EndpointWaitersGrowFrame.endpointSendDualWithCapsOnCore hInv).stage
      (endpointFlowGate_implies_eq ctx endpointId _ _ hGate)
  · exact refl _

/-- **The checked call carries the waiters' labels**, from its gate. -/
theorem endpointCallCrossCoreDispatchChecked {endpointId : SeLe4n.ObjId}
    {caller : SeLe4n.ThreadId} {payload : SendPayload} {c : CoreId} {st : SystemState}
    (hInv : st.objects.invExt) :
    EndpointWaitersStage ctx st (_root_.SeLe4n.Kernel.endpointCallCrossCoreDispatchChecked ctx endpointId
      caller payload c st).1 := by
  unfold _root_.SeLe4n.Kernel.endpointCallCrossCoreDispatchChecked
  split
  · rename_i hGate
    exact (EndpointWaitersGrowFrame.endpointCallCrossCoreDispatch hInv).stage
      (endpointFlowGate_implies_eq ctx endpointId _ _ hGate)
  · exact refl _

/-- **A receive admitted by its gate carries the waiters' labels**: the gate,
two-way, gives the receiver the endpoint's label. -/
theorem endpointReceiveDualWithCapsOnCore {endpointId : SeLe4n.ObjId}
    {receiver : SeLe4n.ThreadId} {replyId : Option SeLe4n.ReplyId} {c : CoreId} {st : SystemState}
    (hInv : st.objects.invExt)
    (hGate : endpointFlowGate ctx endpointId (ctx.endpointLabelOf endpointId)
      (ctx.threadLabelOf receiver) = true) :
    EndpointWaitersStage ctx st (_root_.SeLe4n.Kernel.endpointReceiveDualWithCapsOnCore endpointId receiver
      replyId c st).1 :=
  (EndpointWaitersGrowFrame.endpointReceiveDualWithCapsOnCore hInv).stage
    (endpointFlowGate_implies_eq ctx endpointId _ _ hGate).symm

end EndpointWaitersStage

end SeLe4n.Kernel
