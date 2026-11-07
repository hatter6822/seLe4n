-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.KernelRecords.IpcPrimitives
import SeLe4n.Kernel.IPC.CrossCore.ReplyWaitersDispatch

/-!
# The send keeps the records

WS-ZA ZA6.37.  A send to a waiting receiver pops the receiver, which the queue
holds blocked on the receive (`queueHeadBlockedConsistent`), and makes it
`.ready`; a send with no receiver blocks the sender, which runs and so is
blocked on nothing.  Neither thread is fault-blocked before its write, so every
fault record stays parked; the address-space records are never written.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

/-- A checked TCB write's thread after it is the write of the thread before. -/
theorem modifyTcb_getTcb?_self {st st' : SystemState} {t : SeLe4n.ThreadId} {f : TCB → TCB}
    (hInv : st.objects.invExt) (h : modifyTcb st t f = .ok st') :
    ∃ x, st.getTcb? t = some x ∧ st'.getTcb? t = some (f x) := by
  obtain ⟨tcb, hL, hS⟩ := modifyTcb_ok_decompose h
  refine ⟨tcb, (SystemState.getTcb?_eq_some_iff _ _ _).mpr (lookupTcb_some_objects st t tcb hL),
    (SystemState.getTcb?_eq_some_iff _ _ _).mpr ?_⟩
  exact storeObject_objects_eq st st' _ _ hInv hS

/-- The head of a receive queue is not fault-blocked. -/
theorem receiveHead_notParked {st : SystemState} (hQ : queueHeadBlockedConsistent st)
    {eid : SeLe4n.ObjId} {ep : Endpoint} {r : SeLe4n.ThreadId}
    (hE : st.objects[eid]? = some (.endpoint ep)) (hH : ep.receiveQ.head = some r) :
    ∀ x, st.getTcb? r = some x → ¬ ipcParked x.ipcState := fun x hx => by
  rw [(hQ eid ep r x hE ((SystemState.getTcb?_eq_some_iff _ _ _).mp hx)).1 hH]; simp

/-- A thread's fault-parking reads carried across a frame. -/
theorem RecordsFrame.notParked {st st' : SystemState} (F : RecordsFrame st st')
    {t : SeLe4n.ThreadId} (h : ∀ x, st.getTcb? t = some x → ¬ ipcParked x.ipcState) :
    ∀ x, st'.getTcb? t = some x → ¬ ipcParked x.ipcState := fun x hx => by
  obtain ⟨y, hy, hv⟩ := F.getTcb?_view hx
  have : y.ipcState = x.ipcState := congrArg TcbRecordView.ipc hv
  rw [← this]; exact h y hy

namespace RecordsStep

/-- **The per-core send keeps the address-space records and every fault record
parked.** -/
theorem endpointSendDualOnCore {endpointId : SeLe4n.ObjId} {sender : SeLe4n.ThreadId}
    {payload : SendPayload} {c : CoreId} {st : SystemState} (hInv : st.objects.invExt)
    (hQ : queueHeadBlockedConsistent st)
    (hSnd : ∀ x, st.getTcb? sender = some x → ¬ ipcParked x.ipcState) :
    RecordsStep st (_root_.SeLe4n.Kernel.endpointSendDualOnCore endpointId sender payload c st).1 := by
  unfold _root_.SeLe4n.Kernel.endpointSendDualOnCore
  split
  · rename_i ep hEp
    have hEpO := (SystemState.getEndpoint?_eq_some_iff _ _ _).mp hEp
    split
    · rename_i hd hHead
      split
      · exact refl hInv
      · split
        · exact refl hInv
        · rename_i receiver _tcb st1 hPop
          split
          · exact refl hInv
          · rename_i st2 hRecv
            have hRh : receiver = hd := endpointQueuePopHead_popped_eq_head _ true _ _ ep _ _ _
              hEpO (by simpa using hHead) hPop
            subst hRh
            have F1 := RecordsFrame.endpointQueuePopHead hInv hPop
            have S2 := storeTcbReceiveComplete F1.invExt hRecv
              (F1.notParked (receiveHead_notParked hQ hEpO hHead))
            obtain ⟨x, -, hx⟩ := modifyTcb_getTcb?_self F1.invExt hRecv
            have F3 := RecordsFrame.wakeThread st2 receiver c S2.invExt (fun y hy => by
              rw [hx] at hy; cases hy; simp)
            exact (of_frame F1).trans (S2.trans (of_frame F3))
    · split
      · exact refl hInv
      · rename_i st1 hEnq
        split
        · exact refl hInv
        · rename_i st2 hBlk
          have F1 := RecordsFrame.endpointQueueEnqueue hInv hEnq
          have S2 := storeTcbIpcStateAndMessage F1.invExt hBlk
            (fun x hx => .inl (F1.notParked hSnd x hx))
          have F3 := RecordsFrame.removeRunnableOnCore st2 sender c S2.invExt
          have F4 := RecordsFrame.recordSendCap _ sender payload.badge payload.grant F3.invExt
          exact (of_frame F1).trans (S2.trans ((of_frame F3).trans (of_frame F4)))
  · split <;> exact refl hInv

end RecordsStep

end SeLe4n.Kernel
