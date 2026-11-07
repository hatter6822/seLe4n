-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.KernelRecords.IpcSend
import SeLe4n.Kernel.KernelRecords.Donation
import SeLe4n.Kernel.KernelRecords.CapabilityPrimitives

/-!
# The receive keeps the records

WS-ZA ZA6.37.  A receive meeting a caller parks the caller on the reply
(`.blockedOnReply`, a parked state) and makes the receiver `.ready`; one meeting
a sender makes the sender, which the queue holds blocked on the send
(`queueHeadBlockedConsistent`), `.ready`; one meeting nobody blocks the receiver
on the receive.  The receiver runs, so it is parked on nothing; it is not the
caller it meets, which is parked.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

/-- A thread parked on nothing, read on a state. -/
def NotParkedAt (st : SystemState) (t : SeLe4n.ThreadId) : Prop :=
  ∀ x, st.getTcb? t = some x → ¬ ipcParked x.ipcState

/-- A checked TCB write of another thread leaves the thread unparked. -/
theorem NotParkedAt.modifyTcb_ne {st st' : SystemState} {t u : SeLe4n.ThreadId} {f : TCB → TCB}
    (hInv : st.objects.invExt) (h : _root_.SeLe4n.Kernel.modifyTcb st t f = .ok st')
    (hne : t.toObjId ≠ u.toObjId) (hN : NotParkedAt st u) : NotParkedAt st' u := fun x hx =>
  hN x (by rw [← modifyTcb_getTcb?_ne hInv h hne]; exact hx)

/-- A checked TCB write that parks no unparked thread leaves every thread
unparked that was. -/
theorem NotParkedAt.modifyTcb {st st' : SystemState} {t u : SeLe4n.ThreadId} {f : TCB → TCB}
    (hInv : st.objects.invExt) (h : _root_.SeLe4n.Kernel.modifyTcb st t f = .ok st')
    (hf : ∀ x, ¬ ipcParked x.ipcState → ¬ ipcParked (f x).ipcState)
    (hN : NotParkedAt st u) : NotParkedAt st' u := by
  by_cases hne : t.toObjId = u.toObjId
  · intro y hy
    obtain ⟨x, hx, hx'⟩ := modifyTcb_getTcb?_self hInv h
    have hu : u = t := by
      cases u; cases t; simp only [SeLe4n.ThreadId.toObjId] at hne
      cases hne; rfl
    subst hu
    rw [hx'] at hy; cases hy
    exact hf x (hN x hx)
  · exact modifyTcb_ne hInv h hne hN

/-- A frame keeps a thread unparked. -/
theorem NotParkedAt.frame {st st' : SystemState} (F : RecordsFrame st st') {t : SeLe4n.ThreadId}
    (h : NotParkedAt st t) : NotParkedAt st' t := F.notParked h

namespace RecordsStep

/-- **The per-core receive keeps the address-space records and every fault
record parked**, from a receiver parked on nothing. -/
theorem endpointReceiveDualOnCore {endpointId : SeLe4n.ObjId} {receiver : SeLe4n.ThreadId}
    {replyId : Option SeLe4n.ReplyId} {c : CoreId} {st : SystemState} (hInv : st.objects.invExt)
    (hQ : queueHeadBlockedConsistent st) (hRcv : NotParkedAt st receiver) :
    RecordsStep st (_root_.SeLe4n.Kernel.endpointReceiveDualOnCore endpointId receiver replyId c st).1 := by
  unfold _root_.SeLe4n.Kernel.endpointReceiveDualOnCore
  split
  · rename_i ep hEp
    have hEpO := (SystemState.getEndpoint?_eq_some_iff _ _ _).mp hEp
    split
    · rename_i hd hHead
      split
      · exact refl hInv
      · rename_i sender senderTcb st1 hPop
        have hSh : sender = hd := endpointQueuePopHead_popped_eq_head _ false _ _ ep _ _ _
          hEpO (by simpa using hHead) hPop
        subst hSh
        have hSO := endpointQueuePopHead_returns_pre_tcb _ false _ ep _ _ _ hEpO hPop
        have hSQ := (hQ endpointId ep sender senderTcb hEpO hSO).2 hHead
        have F1 := RecordsFrame.endpointQueuePopHead hInv hPop
        dsimp only
        split
        · -- the sender called
          rename_i e hCall
          simp only [↓reduceIte]
          have hne : sender.toObjId ≠ receiver.toObjId := fun hk => by
            have hT : st.getTcb? receiver = some senderTcb :=
              (SystemState.getTcb?_eq_some_iff _ _ _).mpr (hk ▸ hSO)
            exact hRcv _ hT (by rw [hCall]; simp)
          split
          · exact refl hInv
          · rename_i st2 hBlk
            have S2 := storeTcbIpcStateAndMessage F1.invExt hBlk (fun _ _ => .inr (by simp))
            have N2 := NotParkedAt.modifyTcb_ne F1.invExt hBlk hne (hRcv.frame F1)
            split
            · exact refl hInv
            · split
              · exact refl hInv
              · rename_i stL hL
                have F3 := RecordsFrame.linkCallerReply S2.invExt hL
                split
                · rename_i st4 hRdy
                  have S4 := storeTcbIpcStateAndMessage F3.invExt hRdy
                    (fun x hx => .inl (N2.frame F3 x hx))
                  exact (of_frame F1).trans (S2.trans ((of_frame F3).trans (S4.trans
                    (linkReplyWaiter _ _ _ S4.invExt))))
                · exact refl hInv
        · -- the sender sent
          rename_i hNotCall
          simp only [Bool.false_eq_true, ↓reduceIte]
          have hSend : senderTcb.ipcState = .blockedOnSend endpointId := by
            rcases hSQ with h | h
            · exact h
            · exact absurd h (hNotCall _)
          split
          · exact refl hInv
          · rename_i st2 hRdy
            have S2 := storeTcbIpcStateAndMessage F1.invExt hRdy (fun x hx => .inl (by
              obtain ⟨y, hy, hv⟩ := F1.getTcb?_view hx
              have : y.ipcState = x.ipcState := congrArg TcbRecordView.ipc hv
              rw [(SystemState.getTcb?_eq_some_iff _ _ _).mp hy] at hSO
              cases hSO
              rw [← this, hSend]; simp))
            have N2 := NotParkedAt.modifyTcb F1.invExt hRdy (fun x _ => by simp) (hRcv.frame F1)
            obtain ⟨x, -, hx⟩ := modifyTcb_getTcb?_self F1.invExt hRdy
            have F3 := RecordsFrame.wakeThread st2 sender c S2.invExt (fun y hy => by
              rw [hx] at hy; cases hy; simp)
            split
            · rename_i st4 hRcvd
              have S4 := storeTcbIpcStateAndMessage F3.invExt hRcvd
                (fun x hx => .inl (N2.frame F3 x hx))
              exact (of_frame F1).trans (S2.trans ((of_frame F3).trans S4))
            · exact refl hInv
    · -- no sender: block
      split
      · exact refl hInv
      · rename_i stClean hClean
        have F0 := RecordsFrame.cleanupPreReceiveDonationMigrated hInv hClean
        split
        · exact refl hInv
        · rename_i st1 hEnq
          have F1 := F0.trans (RecordsFrame.endpointQueueEnqueue F0.invExt hEnq)
          split
          · exact refl hInv
          · rename_i st2 hBlk
            have S2 := storeTcbIpcStateAndMessage F1.invExt hBlk
              (fun x hx => .inl (hRcv.frame F1 x hx))
            have P := (of_frame F1).trans S2
            split
            · exact P.trans (of_frame (RecordsFrame.removeRunnableOnCore _ _ _ S2.invExt))
            · rename_i rTcb hT
              split
              · split
                · exact refl hInv
                · rename_i stS hS
                  have FR := RecordsFrame.recordReplyStasher _ (SeLe4n.ReplyId.optCode replyId)
                    receiver S2.invExt
                  have hTR : (st2.recordReplyStasher (SeLe4n.ReplyId.optCode replyId) receiver).objects[receiver.toObjId]?
                      = some (.tcb rTcb) := (SystemState.getTcb?_eq_some_iff _ _ _).mp
                    (by rw [SystemState.recordReplyStasher_getTcb? _ _ _ S2.invExt]; exact hT)
                  have F3 := FR.trans (RecordsFrame.storeObject FR.invExt hS (by rw [hTR]; rfl)
                    (fun _ h => by cases h))
                  exact P.trans ((of_frame F3).trans
                    (of_frame (RecordsFrame.removeRunnableOnCore _ _ _ F3.invExt)))
              · exact refl hInv
  · split <;> exact refl hInv

/-- The send with capability transfer. -/
theorem endpointSendDualWithCapsOnCore {endpointId : SeLe4n.ObjId} {sender : SeLe4n.ThreadId}
    {payload : SendPayload} {receiverSlotBase : SeLe4n.Slot} {c : CoreId} {st : SystemState}
    (hInv : st.objects.invExt) (hQ : queueHeadBlockedConsistent st)
    (hSnd : NotParkedAt st sender) :
    RecordsStep st (_root_.SeLe4n.Kernel.endpointSendDualWithCapsOnCore endpointId sender payload
      receiverSlotBase c st).1 := by
  unfold _root_.SeLe4n.Kernel.endpointSendDualWithCapsOnCore
  have S := endpointSendDualOnCore (endpointId := endpointId) (payload := payload) (c := c)
    hInv hQ hSnd
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
      | (rename_i hU; exact S.trans (of_frame (RecordsFrame.receiveTransferCaps S.invExt hU)))

/-- The live checked send. -/
theorem endpointSendCrossCoreDispatchChecked {ctx : LabelingContext} {endpointId : SeLe4n.ObjId}
    {sender : SeLe4n.ThreadId} {payload : SendPayload} {receiverSlotBase : SeLe4n.Slot}
    {c : CoreId} {st : SystemState} (hInv : st.objects.invExt) (hQ : queueHeadBlockedConsistent st)
    (hSnd : NotParkedAt st sender) :
    RecordsStep st (_root_.SeLe4n.Kernel.endpointSendCrossCoreDispatchChecked ctx endpointId sender
      payload receiverSlotBase c st).1 := by
  unfold _root_.SeLe4n.Kernel.endpointSendCrossCoreDispatchChecked
  split
  · exact endpointSendDualWithCapsOnCore hInv hQ hSnd
  · exact refl hInv

/-- The receive with capability transfer. -/
theorem endpointReceiveDualWithCapsOnCore {endpointId : SeLe4n.ObjId} {receiver : SeLe4n.ThreadId}
    {replyId : Option SeLe4n.ReplyId} {receiverCspaceRoot : SeLe4n.ObjId}
    {receiverSlotBase : SeLe4n.Slot} {c : CoreId} {st : SystemState} (hInv : st.objects.invExt)
    (hQ : queueHeadBlockedConsistent st) (hRcv : NotParkedAt st receiver) :
    RecordsStep st (_root_.SeLe4n.Kernel.endpointReceiveDualWithCapsOnCore endpointId receiver
      replyId receiverCspaceRoot receiverSlotBase c st).1 := by
  unfold _root_.SeLe4n.Kernel.endpointReceiveDualWithCapsOnCore
  have S := endpointReceiveDualOnCore (endpointId := endpointId) (replyId := replyId) (c := c)
    hInv hQ hRcv
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
      | (rename_i hU; exact S.trans (of_frame (RecordsFrame.receiveTransferCaps S.invExt hU)))

end RecordsStep

end SeLe4n.Kernel
