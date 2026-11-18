-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n - A Lean Microkernel
  Copyright (C) 2026 Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.CrossCore.DeliveredInPlace
import SeLe4n.Kernel.IPC.CrossCore.NotificationBind
import SeLe4n.Kernel.IPC.DualQueue.RemoveInPlace

/-!
# A signal delivered to its notification's bound receiver, in place

WS-ZA ZA6.35.  A signal to a notification no thread waits on, whose bound
thread is blocked receiving on an endpoint, hands the badge to that thread
(seL4's `sendSignal`, the `ThreadState_BlockedOnReceive` case of a bound
TCB: `cancelIPC`, then `setThreadState Running` with the badge in its
`badgeRegister`).  The specification's form (`notificationSignalBoundOnCore`)
takes the thread off the endpoint's receive queue (`endpointQueueRemoveDual`),
makes it ready with the badge in its badge register and no message held
(`storeTcbSignalBoundWoken`), and wakes it.  Here the removal is the in-place
removal (`storeQueueRemove`, `queueRemove_inPlace`) and the wake a write of the
thread where it stands (`notificationSignalBoundOnCore_bound_eq`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model SeLe4n.Kernel.RobinHood SeLe4n.Kernel.Concurrency

/-- An in-place removal leaves the object table without a resize due. -/
theorem storeQueueRemove_noResizeDue (st : SystemState) (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (tid : SeLe4n.ThreadId) (ep : Endpoint) (tcb : TCB)
    (hNo : st.objects.noResizeDue) :
    (storeQueueRemove st endpointId isReceiveQ tid ep tcb).objects.noResizeDue := by
  unfold storeQueueRemove
  dsimp only
  apply updateTcb_noResizeDue
  apply modifyObject_noResizeDue
  split
  · apply updateTcb_noResizeDue
    split
    · exact modifyObject_noResizeDue _ _ _ hNo
    · exact updateTcb_noResizeDue _ _ _ hNo
    · exact hNo
  · split
    · exact modifyObject_noResizeDue _ _ _ hNo
    · exact updateTcb_noResizeDue _ _ _ hNo
    · exact hNo

/-- **A bound delivery's writes, each in its slot**: the bound thread `t`, blocked
receiving on `epId`, taken off that endpoint's receive queue where every write
stays in its slot (`queueRemoveInPlace`), made ready with the badge in its
badge register (`TCB.signalBoundWoken`) as a write of the thread in its slot,
then the wake. -/
theorem notificationSignalBoundOnCore_bound_eq (nid : SeLe4n.ObjId) (badge : SeLe4n.Badge)
    (c : CoreId) (st : SystemState) (t : SeLe4n.ThreadId) (epId : SeLe4n.ObjId)
    (ep : Endpoint) (tcb : TCB)
    (hTarget : boundDeliveryTarget? st nid = some (t, epId))
    (hE : st.objects[epId]? = some (.endpoint ep))
    (hT : st.objects[t.toObjId]? = some (.tcb tcb))
    (hG : queueRemoveInPlace st epId true t ep tcb = true) :
    notificationSignalBoundOnCore nid badge c st =
      ((wakeThread ((storeQueueRemove st epId true t ep tcb).updateTcb t
          (TCB.signalBoundWoken badge)) t c).1,
        .ok (wakeThread ((storeQueueRemove st epId true t ep tcb).updateTcb t
          (TCB.signalBoundWoken badge)) t c).2) := by
  obtain ⟨hRm, hFr⟩ := queueRemove_inPlace st epId true t ep tcb hE hT hG
  have hG' := hG
  unfold queueRemoveInPlace at hG'
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hG'
  obtain ⟨⟨⟨⟨⟨⟨hR, _⟩, _⟩, hLT⟩, _⟩, _⟩, _⟩ := hG'
  have hStore : storeTcbSignalBoundWoken (storeQueueRemove st epId true t ep tcb) t badge =
      .ok ((storeQueueRemove st epId true t ep tcb).updateTcb t
        (TCB.signalBoundWoken badge)) :=
    modifyTcb_eq_updateTcb _ hR hFr.removed_tcb (hFr.leaves hLT)
  unfold notificationSignalBoundOnCore
  rw [hTarget]
  simp only [hRm, hStore]

end SeLe4n.Kernel
