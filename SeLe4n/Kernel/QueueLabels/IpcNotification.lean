-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.QueueLabels.ThreadLifecycle

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

/-- **The woken head's notification store**: its successor heads the queue,
carrying the head's label, which is the notification's. -/
theorem NtfnLabelsKept.storeHeadPopped {st st1 : SystemState} {nid : SeLe4n.ObjId} {ntfn : Notification}
    {w : SeLe4n.ThreadId} (hInv : st.objects.invExt) (hG : st.getNotification? nid = some ntfn)
    (hH : ntfn.waitHead = some w)
    (hS : SeLe4n.Model.storeObject nid (.notification (ntfn.withHeadPopped (ntfnSuccessor? st w))) st =
      .ok ((), st1)) : NtfnLabelsKept st st1 := fun ctx H => by
  obtain ⟨hB, hHd, hTl⟩ := notificationLabelsAgree_notification H hG
  refine notificationLabelsAgree.storeObject hInv hS H
    (notificationLabelsAgree.ntfn_entry (fun u hu => hB u (by simpa using hu)) (fun u hu => ?_)
      (fun u hu => ?_))
  · simp only [Notification.withHeadPopped_waitHead] at hu
    unfold ntfnSuccessor? at hu
    split at hu
    · rename_i tcb hL
      exact notificationLabelsAgree.gate_of_label (hHd w hH)
        ((H _ _ (lookupTcb_some_objects _ _ _ hL)).2.2 u hu)
    · cases hu
  · simp only [Notification.waitTail, Notification.withHeadPopped] at hu
    split at hu
    · exact hTl u hu
    · simp at hu

/-- A store of a notification whose queue is empty and whose binding is kept. -/
theorem NtfnLabelsKept.storeQueueEmptied {st st1 : SystemState} {nid : SeLe4n.ObjId}
    {ntfn n' : Notification} (hInv : st.objects.invExt) (hG : st.getNotification? nid = some ntfn)
    (hS : SeLe4n.Model.storeObject nid (.notification n') st = .ok ((), st1))
    (hB : n'.boundTCBCode = ntfn.boundTCBCode) (hHd : n'.waitHeadCode = 0) (hTl : n'.waitTailCode = 0) :
    NtfnLabelsKept st st1 := fun ctx H => by
  obtain ⟨hB0, -, -⟩ := notificationLabelsAgree_notification H hG
  exact notificationLabelsAgree.storeObject hInv hS H (notificationLabelsAgree.ntfn_entry
    (fun u hu => hB0 u (by simpa [Notification.boundTCB, hB] using hu))
    (fun u hu => by simp [Notification.waitHead, hHd] at hu)
    (fun u hu => by simp [Notification.waitTail, hTl] at hu))

namespace QueueLabelsFrame

theorem storeTcbSignalWoken {st st' : SystemState} {t : SeLe4n.ThreadId} {b : SeLe4n.Badge}
    (hInv : st.objects.invExt) (h : _root_.SeLe4n.Kernel.storeTcbSignalWoken st t b = .ok st') :
    QueueLabelsFrame st st' :=
  modifyTcb hInv h fun _ => TcbWaitsKept.of_noWait (by simp [TCB.signalWoken])

theorem storeTcbSignalBoundWoken {st st' : SystemState} {t : SeLe4n.ThreadId} {b : SeLe4n.Badge}
    (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.storeTcbSignalBoundWoken st t b = .ok st') :
    QueueLabelsFrame st st' :=
  modifyTcb hInv h fun _ => TcbWaitsKept.of_noWait (by simp [TCB.signalBoundWoken])

theorem notificationSignalOnCore {nid : SeLe4n.ObjId} {badge : SeLe4n.Badge} {c : CoreId}
    {st : SystemState} (hInv : st.objects.invExt) :
    QueueLabelsFrame st (_root_.SeLe4n.Kernel.notificationSignalOnCore nid badge c st).1 := by
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
        have F1 := RecordsCoreFrame.storeNotificationAt hInv hG hS
        dsimp only
        split
        · exact refl hInv
        · rename_i st2 hT
          have S2 := storeTcbSignalWoken F1.invExt hT
          obtain ⟨x, -, hx⟩ := modifyTcb_getTcb?_self F1.invExt hT
          have F3 := RecordsCoreFrame.detachNtfnHead st2 w (ntfnSuccessor? st w) S2.invExt
          have F4 := RecordsFrame.wakeThread _ w c F3.invExt (F3.ready (fun y hy => by
            rw [hx] at hy; cases hy; simp [TCB.signalWoken]))
          exact (of_coreFrame F1 (NtfnLabelsKept.storeHeadPopped hInv hG hH hS)).trans
            (S2.trans ((of_coreFrame F3 (NtfnLabelsKept.detachNtfnHead _ _ _ S2.invExt)).trans
              (of_frame F4)))
    · dsimp only
      cases hS : SeLe4n.Model.storeObject nid _ st with
      | error _ => exact refl hInv
      | ok p =>
        obtain ⟨⟨⟩, st1⟩ := p
        exact of_coreFrame (RecordsCoreFrame.storeNotificationAt hInv hG hS)
          (NtfnLabelsKept.storeQueueEmptied hInv hG hS rfl rfl rfl)
  · split <;> exact refl hInv

theorem notificationSignalBoundOnCore {nid : SeLe4n.ObjId} {badge : SeLe4n.Badge} {c : CoreId}
    {st : SystemState} (hInv : st.objects.invExt) :
    QueueLabelsFrame st (_root_.SeLe4n.Kernel.notificationSignalBoundOnCore nid badge c st).1 := by
  unfold _root_.SeLe4n.Kernel.notificationSignalBoundOnCore
  split
  · rename_i t epId hB
    split
    · exact refl hInv
    · rename_i st1 hRm
      have F1 := RecordsEndpointFrame.endpointQueueRemoveDual hInv hRm
      split
      · exact refl hInv
      · rename_i st2 hC
        have S2 := storeTcbSignalBoundWoken F1.invExt hC
        obtain ⟨x, -, hx⟩ := modifyTcb_getTcb?_self F1.invExt hC
        have F3 := RecordsFrame.wakeThread st2 t c S2.invExt (fun y hy => by
          rw [hx] at hy; cases hy; simp [TCB.signalBoundWoken])
        exact (of_endpointFrame F1).trans (S2.trans (of_frame F3))
  · exact notificationSignalOnCore hInv

theorem notificationSignalDeclassifiedOnCore {ctx : GenericLabelingContext}
    {declPolicy : DeclassificationPolicy} {nid : SeLe4n.ObjId} {badge : SeLe4n.Badge} {c : CoreId}
    {st : SystemState} (hInv : st.objects.invExt) :
    QueueLabelsFrame st (_root_.SeLe4n.Kernel.notificationSignalDeclassifiedOnCore ctx declPolicy
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

end QueueLabelsFrame

namespace QueueLabelsNtfnGrowFrame

open notificationLabelsAgree in
/-- **The wait** blocks its waiter on the notification, not on an endpoint, and
adds at most the waiter to the notification's queue: the waiter heads it or
follows the old tail, which carries the notification's label. -/
theorem notificationWaitOnCore {nid : SeLe4n.ObjId} {waiter : SeLe4n.ThreadId} {c : CoreId}
    {st : SystemState} (hInv : st.objects.invExt) :
    QueueLabelsNtfnGrowFrame waiter nid st
      (_root_.SeLe4n.Kernel.notificationWaitOnCore nid waiter c st).1 := by
  unfold _root_.SeLe4n.Kernel.notificationWaitOnCore
  split
  · rename_i ntfn hG
    split
    · dsimp only
      split
      · exact refl hInv
      · rename_i st1 hS
        have F1 := RecordsCoreFrame.storeNotificationAt hInv hG hS
        split
        · exact refl hInv
        · rename_i st2 hT
          exact ((QueueLabelsFrame.of_coreFrame F1
            (NtfnLabelsKept.storeQueueEmptied hInv hG hS rfl rfl rfl)).trans
            (QueueLabelsFrame.storeTcbIpcState F1.invExt hT)).ntfnGrowAt _ _
    · split
      · exact refl hInv
      · rename_i tcb hL
        split
        · exact refl hInv
        · dsimp only
          split
          · exact refl hInv
          · rename_i st1 hS
            have F1 := RecordsCoreFrame.storeNotificationAt hInv hG hS
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
                have I2 := storeObject_preserves_objects_invExt _ _ _ _ F1.invExt hSt
                split
                · exact refl hInv
                · rename_i st4 hLink
                  have F3 := RecordsCoreFrame.linkNtfnWaiter I2 hLink
                  have F4 := RecordsFrame.removeRunnableOnCore _ waiter c F3.invExt
                  refine ⟨?_, fun ctx hGate H => ?_, F4.invExt⟩
                  · exact ((EndpointWaitersShrink.of_coreFrame F1).trans
                      (EndpointWaitersShrink.storeObject_tcb F1.invExt hO1 hSt
                        (TcbWaitsKept.of_noWait (by simp)))).trans
                      ((EndpointWaitersShrink.of_coreFrame F3).trans (EndpointWaitersShrink.of_frame F4))
                  · obtain ⟨hB, hHd, hTl⟩ := notificationLabelsAgree_notification H hG
                    have H1 : notificationLabelsAgree ctx st1 := notificationLabelsAgree.storeObject hInv hS H
                      (notificationLabelsAgree.ntfn_entry
                      (fun u hu => hB u (by simpa [Notification.withWaiterAppended] using hu))
                      (fun u hu => by
                        simp only [Notification.waitHead, Notification.withWaiterAppended] at hu
                        split at hu
                        · simp only [SeLe4n.ThreadId.ofOptCode_optCode, Option.some.injEq] at hu
                          subst hu; exact hGate
                        · exact hHd u hu)
                      (fun u hu => by
                        simp only [Notification.waitTail, Notification.withWaiterAppended,
                          SeLe4n.ThreadId.ofOptCode_optCode, Option.some.injEq] at hu
                        subst hu; exact hGate))
                    have H2 : notificationLabelsAgree ctx s := notificationLabelsAgree.storeObject F1.invExt hSt H1
                      ⟨fun n hn => by
                        simp only [TCB.ipcState_setIpcState, ThreadIpcState.blockedOnNotification.injEq] at hn
                        subst hn; exact hGate,
                       (H1 _ _ hO1).2.1, (H1 _ _ hO1).2.2⟩
                    have H3 := notificationLabelsAgree.linkNtfnWaiter I2 hLink H2 fun u hu =>
                      notificationLabelsAgree.label_of_gates hGate (hTl u hu)
                    exact NtfnLabelsKept.of_frame F4 ctx H3
  · split <;> exact refl hInv

end QueueLabelsNtfnGrowFrame

namespace QueueLabelsGatedFrame

/-- **The checked wait**: its gate admits the waiter under the labelling it checks. -/
theorem notificationWaitCrossCoreDispatchChecked {ctx : LabelingContext} {nid : SeLe4n.ObjId}
    {waiter : SeLe4n.ThreadId} {c : CoreId} {st : SystemState} (hInv : st.objects.invExt) :
    QueueLabelsGatedFrame ctx st (_root_.SeLe4n.Kernel.notificationWaitCrossCoreDispatchChecked ctx nid
      waiter c st).1 := by
  unfold _root_.SeLe4n.Kernel.notificationWaitCrossCoreDispatchChecked
  split
  · rename_i hGate
    split
    · exact refl hInv
    · exact (QueueLabelsNtfnGrowFrame.notificationWaitOnCore hInv).gated (by simpa using hGate)
  · exact refl hInv

end QueueLabelsGatedFrame


end SeLe4n.Kernel
