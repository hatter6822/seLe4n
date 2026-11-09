-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.KernelRecords.IpcReceive

/-!
# The call keeps the records

WS-ZA ZA6.37.  A call meeting a receiver makes the receiver, which the queue
holds blocked on the receive, `.ready`, and parks the caller on the reply; a call
meeting nobody parks the caller on the call.  Every thread the call moves goes
from an unparked state or into a parked one, so every fault record stays parked
whatever the caller held.  The lend and the chain walk keep every record view.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

namespace RecordsFrame

/-- The server's stashed reply handed to the caller. -/
theorem linkServerStashedReply {caller server : SeLe4n.ThreadId} {st st' : SystemState}
    (hInv : st.objects.invExt)
    (h : SystemState.linkServerStashedReply caller server st = .ok ((), st')) :
    RecordsFrame st st' := by
  unfold SystemState.linkServerStashedReply at h
  split at h
  · cases h
  · rename_i rid _
    cases hL : SystemState.linkCallerReply caller rid st with
    | error e => simp [hL] at h
    | ok p1 =>
      obtain ⟨⟨⟩, st1⟩ := p1
      simp only [hL] at h
      have F1 := linkCallerReply hInv hL
      cases hT : st1.getTcb? server with
      | none => simp only [hT] at h; cases h; exact F1
      | some sTcb =>
        simp only [hT] at h
        exact F1.trans (storeObject F1.invExt h
          (by rw [(SystemState.getTcb?_eq_some_iff st1 server sTcb).mp hT]; rfl)
          (fun _ h => by cases h))

end RecordsFrame

namespace RecordsStep

/-- **The per-core call keeps the address-space records and every fault record
parked.** -/
theorem endpointCallOnCore {endpointId : SeLe4n.ObjId} {caller : SeLe4n.ThreadId}
    {payload : SendPayload} {c : CoreId} {st : SystemState} (hInv : st.objects.invExt)
    (hQ : queueHeadBlockedConsistent st) :
    RecordsStep st (_root_.SeLe4n.Kernel.endpointCallOnCore endpointId caller payload c st).1 := by
  unfold _root_.SeLe4n.Kernel.endpointCallOnCore
  split
  · rename_i ep hEp
    have hEpO := (SystemState.getEndpoint?_eq_some_iff _ _ _).mp hEp
    split
    · rename_i hd hHead
      split
      · exact refl hInv
      · rename_i receiver _tcb st1 hPop
        have hRh : receiver = hd := endpointQueuePopHead_popped_eq_head _ true _ _ ep _ _ _
          hEpO (by simpa using hHead) hPop
        subst hRh
        have F1 := RecordsFrame.endpointQueuePopHead hInv hPop
        split
        · exact refl hInv
        · rename_i st2 hRdy
          have S2 := storeTcbIpcStateAndMessage F1.invExt hRdy
            (fun x hx => .inl (F1.notParked (receiveHead_notParked hQ hEpO hHead) x hx))
          obtain ⟨x, -, hx⟩ := modifyTcb_getTcb?_self F1.invExt hRdy
          have F3 := RecordsFrame.wakeThread st2 receiver c S2.invExt (fun y hy => by
            rw [hx] at hy; cases hy; simp)
          split
          · exact refl hInv
          · rename_i st4 hBlk
            have S4 := storeTcbIpcStateAndMessage F3.invExt hBlk (fun _ _ => .inr (by simp))
            split
            · exact refl hInv
            · rename_i st5 hLink
              have F5 := RecordsFrame.linkServerStashedReply S4.invExt hLink
              have F6 := RecordsFrame.removeRunnableOnCore st5 caller c F5.invExt
              exact (of_frame F1).trans (S2.trans ((of_frame F3).trans (S4.trans
                ((of_frame F5).trans ((of_frame F6).trans (linkReplyWaiter _ _ _ F6.invExt))))))
    · split
      · exact refl hInv
      · rename_i st1 hEnq
        split
        · exact refl hInv
        · rename_i st2 hBlk
          have F1 := RecordsFrame.endpointQueueEnqueue hInv hEnq
          have S2 := storeTcbIpcStateAndMessage F1.invExt hBlk (fun _ _ => .inr (by simp))
          have F3 := RecordsFrame.removeRunnableOnCore st2 caller c S2.invExt
          have F4 := RecordsFrame.recordSendCap _ caller payload.badge payload.grant F3.invExt
          exact (of_frame F1).trans (S2.trans ((of_frame F3).trans (of_frame F4)))
  · split <;> exact refl hInv

theorem endpointCallWithCapsOnCore {endpointId : SeLe4n.ObjId} {caller : SeLe4n.ThreadId}
    {payload : SendPayload} {c : CoreId} {st : SystemState}
    (hInv : st.objects.invExt) (hQ : queueHeadBlockedConsistent st) :
    RecordsStep st (_root_.SeLe4n.Kernel.endpointCallWithCapsOnCore endpointId caller payload
      c st).1 := by
  unfold _root_.SeLe4n.Kernel.endpointCallWithCapsOnCore
  have S := endpointCallOnCore (endpointId := endpointId) (caller := caller) (payload := payload)
    (c := c) hInv hQ
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
      | (rename_i hU; exact S.trans (of_frame (RecordsFrame.receiveTransferCaps S.invExt hU)))

theorem endpointCallCrossCoreDispatch {endpointId : SeLe4n.ObjId} {caller : SeLe4n.ThreadId}
    {payload : SendPayload} {c : CoreId} {st : SystemState}
    (hInv : st.objects.invExt) (hQ : queueHeadBlockedConsistent st) :
    RecordsStep st (_root_.SeLe4n.Kernel.endpointCallCrossCoreDispatch endpointId caller payload
      c st).1 := by
  unfold _root_.SeLe4n.Kernel.endpointCallCrossCoreDispatch
  have S := endpointCallWithCapsOnCore (endpointId := endpointId) (caller := caller)
    (payload := payload) (c := c) hInv hQ
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
         have F := RecordsFrame.applyCallDonationOnCore S.invExt hD
         exact S.trans (of_frame (F.trans (RecordsFrame.propagatePipChainCrossCore _ _ _ _ F.invExt))))

theorem endpointCallCrossCoreDispatchChecked {ctx : LabelingContext} {endpointId : SeLe4n.ObjId}
    {caller : SeLe4n.ThreadId} {payload : SendPayload}
    {c : CoreId} {st : SystemState} (hInv : st.objects.invExt) (hQ : queueHeadBlockedConsistent st) :
    RecordsStep st (_root_.SeLe4n.Kernel.endpointCallCrossCoreDispatchChecked ctx endpointId caller
      payload c st).1 := by
  unfold _root_.SeLe4n.Kernel.endpointCallCrossCoreDispatchChecked
  split
  · exact endpointCallCrossCoreDispatch hInv hQ
  · exact refl hInv

end RecordsStep

end SeLe4n.Kernel
