-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.EndpointWaiters.ThreadLifecycle

/-! # The notification arms: frames

WS-SX SX11.2.  A signal makes the thread it wakes `.ready` (a bound receiver
taken off its endpoint's queue, so a waiter removed); a wait blocks its waiter
on the notification, not on an endpoint.  So neither moves a thread onto an
endpoint.  The proofs follow the records' own
(`KernelRecords/IpcNotification.lean`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

namespace EndpointWaitersFrame

theorem storeTcbSignalWoken {st st' : SystemState} {t : SeLe4n.ThreadId} {b : SeLe4n.Badge}
    (hInv : st.objects.invExt) (h : _root_.SeLe4n.Kernel.storeTcbSignalWoken st t b = .ok st') :
    EndpointWaitersFrame st st' :=
  modifyTcb hInv h fun _ => TcbWaitsKept.of_noWait (by simp [TCB.signalWoken])

theorem storeTcbSignalBoundWoken {st st' : SystemState} {t : SeLe4n.ThreadId} {b : SeLe4n.Badge}
    (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.storeTcbSignalBoundWoken st t b = .ok st') :
    EndpointWaitersFrame st st' :=
  modifyTcb hInv h fun _ => TcbWaitsKept.of_noWait (by simp [TCB.signalBoundWoken])

theorem notificationSignalOnCore {nid : SeLe4n.ObjId} {badge : SeLe4n.Badge} {c : CoreId}
    {st : SystemState} (hInv : st.objects.invExt) :
    EndpointWaitersFrame st (_root_.SeLe4n.Kernel.notificationSignalOnCore nid badge c st).1 := by
  unfold _root_.SeLe4n.Kernel.notificationSignalOnCore
  split
  · rename_i ntfn hG
    split
    · rename_i w hH
      dsimp only
      cases hS : SeLe4n.Model.storeObject nid _ st with
      | error _ => exact refl hInv
      | ok p =>
        obtain ⟨⟨⟩, st1⟩ := p
        have F1 := RecordsFrame.storeNotificationAt hInv hG hS
        dsimp only
        split
        · exact refl hInv
        · rename_i st2 hT
          have S2 := storeTcbSignalWoken F1.invExt hT
          obtain ⟨x, -, hx⟩ := modifyTcb_getTcb?_self F1.invExt hT
          have F3 := RecordsFrame.detachNtfnHead st2 w (ntfnSuccessor? st w) S2.invExt
          have F4 := RecordsFrame.wakeThread _ w c F3.invExt (F3.ready (fun y hy => by
            rw [hx] at hy; cases hy; simp [TCB.signalWoken]))
          exact (of_frame F1).trans (S2.trans ((of_frame F3).trans (of_frame F4)))
    · dsimp only
      cases hS : SeLe4n.Model.storeObject nid _ st with
      | error _ => exact refl hInv
      | ok p =>
        obtain ⟨⟨⟩, st1⟩ := p
        exact of_frame (RecordsFrame.storeNotificationAt hInv hG hS)
  · split <;> exact refl hInv

theorem notificationSignalBoundOnCore {nid : SeLe4n.ObjId} {badge : SeLe4n.Badge} {c : CoreId}
    {st : SystemState} (hInv : st.objects.invExt) :
    EndpointWaitersFrame st (_root_.SeLe4n.Kernel.notificationSignalBoundOnCore nid badge c st).1 := by
  unfold _root_.SeLe4n.Kernel.notificationSignalBoundOnCore
  split
  · rename_i t epId hB
    split
    · exact refl hInv
    · rename_i st1 hRm
      have F1 := RecordsFrame.endpointQueueRemoveDual hInv hRm
      split
      · exact refl hInv
      · rename_i st2 hC
        have S2 := storeTcbSignalBoundWoken F1.invExt hC
        obtain ⟨x, -, hx⟩ := modifyTcb_getTcb?_self F1.invExt hC
        have F3 := RecordsFrame.wakeThread st2 t c S2.invExt (fun y hy => by
          rw [hx] at hy; cases hy; simp [TCB.signalBoundWoken])
        exact (of_frame F1).trans (S2.trans (of_frame F3))
  · exact notificationSignalOnCore hInv

theorem notificationSignalDeclassifiedOnCore {ctx : GenericLabelingContext}
    {declPolicy : DeclassificationPolicy} {nid : SeLe4n.ObjId} {badge : SeLe4n.Badge} {c : CoreId}
    {st : SystemState} (hInv : st.objects.invExt) :
    EndpointWaitersFrame st (_root_.SeLe4n.Kernel.notificationSignalDeclassifiedOnCore ctx declPolicy
      nid badge c st).1 := by
  unfold _root_.SeLe4n.Kernel.notificationSignalDeclassifiedOnCore
  have S := notificationSignalBoundOnCore (badge := badge) (c := c) hInv (nid := nid)
  generalize _root_.SeLe4n.Kernel.notificationSignalBoundOnCore nid badge c st = r at S
  obtain ⟨st1, res⟩ := r
  cases res <;> dsimp only at S ⊢ <;> repeat' split
  all_goals first
    | exact refl hInv
    | (rename_i hRec
       have hEq := recordDeclassifiedHops_frame _ _ _ _ _ hRec
       exact S.trans (of_frame (RecordsFrame.of_objects_eq S.invExt (by rw [hEq]) (by rw [hEq])
         (by rw [hEq]))))

/-- **The wait** blocks its waiter on the notification, not on an endpoint. -/
theorem notificationWaitOnCore {nid : SeLe4n.ObjId} {waiter : SeLe4n.ThreadId} {c : CoreId}
    {st : SystemState} (hInv : st.objects.invExt) :
    EndpointWaitersFrame st (_root_.SeLe4n.Kernel.notificationWaitOnCore nid waiter c st).1 := by
  unfold _root_.SeLe4n.Kernel.notificationWaitOnCore
  split
  · rename_i ntfn hG
    split
    · dsimp only
      split
      · exact refl hInv
      · rename_i st1 hS
        have F1 := RecordsFrame.storeNotificationAt hInv hG hS
        split
        · exact refl hInv
        · rename_i st2 hT
          exact (of_frame F1).trans (storeTcbIpcState F1.invExt hT)
    · split
      · exact refl hInv
      · rename_i tcb hL
        split
        · exact refl hInv
        · dsimp only
          split
          · exact refl hInv
          · rename_i st1 hS
            have F1 := RecordsFrame.storeNotificationAt hInv hG hS
            split
            · exact refl hInv
            · rename_i st2 hT
              unfold storeTcbIpcStateAndMessage_fromTcb at hT
              revert hT
              cases hSt : SeLe4n.Model.storeObject waiter.toObjId _ st1 with
              | error _ => intro h; cases h
              | ok p =>
                obtain ⟨⟨⟩, s⟩ := p
                intro h
                have he := Except.ok.inj h
                subst he
                have hO := lookupTcb_some_objects _ _ _ hL
                have hO1 : st1.objects[waiter.toObjId]? = some (.tcb tcb) := by
                  have := (SeLe4n.Model.storeObject_objects_ne st st1 nid waiter.toObjId _
                    (fun e => by rw [e, (SystemState.getNotification?_eq_some_iff _ _ _).mp hG] at hO
                                 cases hO) hInv hS)
                  rw [this]; exact hO
                have S2 := storeObject_tcb F1.invExt hO1 hSt (TcbWaitsKept.of_noWait (by simp))
                split
                · exact refl hInv
                · rename_i st4 hLink
                  have F3 := RecordsFrame.linkNtfnWaiter S2.invExt hLink
                  have F4 := RecordsFrame.removeRunnableOnCore _ waiter c F3.invExt
                  exact (of_frame F1).trans (S2.trans ((of_frame F3).trans (of_frame F4)))
  · split <;> exact refl hInv

theorem notificationWaitCrossCoreDispatchChecked {ctx : LabelingContext} {nid : SeLe4n.ObjId}
    {waiter : SeLe4n.ThreadId} {c : CoreId} {st : SystemState} (hInv : st.objects.invExt) :
    EndpointWaitersFrame st (_root_.SeLe4n.Kernel.notificationWaitCrossCoreDispatchChecked ctx nid
      waiter c st).1 := by
  unfold _root_.SeLe4n.Kernel.notificationWaitCrossCoreDispatchChecked
  split
  · split
    · exact refl hInv
    · exact notificationWaitOnCore hInv
  · exact refl hInv

end EndpointWaitersFrame

end SeLe4n.Kernel
