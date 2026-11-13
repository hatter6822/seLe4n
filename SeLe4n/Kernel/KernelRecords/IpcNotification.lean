-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.KernelRecords.IpcReply
import SeLe4n.Kernel.InformationFlow.DeclassifiedSignal

/-!
# The notifications keep the records

WS-ZA ZA6.37.  A signal wakes the notification's head waiter, which the queue
holds blocked on the notification (`notificationWaiterConsistent`), or a bound
thread blocked on a receive; a wait consumes a badge or blocks the waiter, which
runs and so is parked on nothing.  No thread leaves a parked state, so every
fault record stays parked.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

namespace RecordsFrame

/-- An endpoint stored over a slot that held an endpoint when the frame began. -/
theorem storeEndpointOver {st s : SystemState} {oid : SeLe4n.ObjId} {ep ep' : Endpoint}
    {pair : Unit × SystemState} (hObj : st.objects[oid]? = some (.endpoint ep))
    (F : RecordsFrame st s) (h : SeLe4n.Model.storeObject oid (.endpoint ep') s = .ok pair) :
    RecordsFrame st pair.2 := by
  obtain ⟨⟨⟩, s'⟩ := pair
  exact F.trans (storeObject_noView F.invExt h rfl (by rw [F.views, hObj]; rfl))

/-- **The endpoint-queue removal keeps every record view**: endpoint stores and
queue-link writes. -/
theorem endpointQueueRemoveDual {st st' : SystemState} {endpointId : SeLe4n.ObjId}
    {isReceiveQ : Bool} {tid : SeLe4n.ThreadId} (hInv : st.objects.invExt)
    (hStep : _root_.SeLe4n.Kernel.endpointQueueRemoveDual endpointId isReceiveQ tid st = .ok ((), st')) :
    RecordsFrame st st' := by
  unfold _root_.SeLe4n.Kernel.endpointQueueRemoveDual dualQueueRemovalEnabled dualQueueRemovalGuard SystemState.getObject? at hStep; revert hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ | frame _ | pageTable _ => simp
    | endpoint ep =>
      simp only []
      cases hLookup : lookupTcb st tid with
      | none => simp
      | some tcb =>
        simp only []
        cases hPPrev : tcb.queuePPrev with
        | none => simp
        | some pprev =>
          simp only []
          generalize (if isReceiveQ then ep.receiveQ else ep.sendQ) = q
          -- `v0.35.59`: `cases pprev` precedes the `split`.  With the two
          -- preconditions collapsed into `dualQueueRemovalEnabled`, unfolding the
          -- guard exposes the guard's own `match pprev` *inside* the `if`
          -- condition, and `split` takes that before the `if` -- so the
          -- constructor split has to come first.
          cases pprev with
            | endpointHead =>
              simp only []
              split
              · simp
              · cases hStore1 : SeLe4n.Model.storeObject endpointId _ st with
                | error e => simp
                | ok pair1 =>
                simp only []; cases hNext : tcb.queueNext with
                | none =>
                  simp only []
                  cases hStore2 : SeLe4n.Model.storeObject endpointId _ pair1.2 with
                  | error e => simp
                  | ok pair2 =>
                  simp only []; cases hFinal : _root_.SeLe4n.Kernel.storeTcbQueueLinks pair2.2 tid none none none with
                  | error e => simp
                  | ok st4 =>
                    simp only [Except.ok.injEq, Prod.mk.injEq]
                    intro ⟨_, hEq⟩; subst hEq
                    have f1 := storeEndpointOver hObj (refl hInv) hStore1
                    have f2 := storeEndpointOver hObj f1 hStore2
                    exact f2.trans (storeTcbQueueLinks f2.invExt hFinal)
                | some nextTid =>
                  simp only []
                  cases hLookupN : lookupTcb pair1.2 nextTid with
                  | none => simp
                  | some nextTcb =>
                  simp only []; cases hLink : _root_.SeLe4n.Kernel.storeTcbQueueLinks pair1.2 nextTid _ _ nextTcb.queueNext with
                  | error e => simp
                  | ok st2 =>
                  simp only []; cases hStore2 : SeLe4n.Model.storeObject endpointId _ st2 with
                  | error e => simp
                  | ok pair2 =>
                  simp only []; cases hFinal : _root_.SeLe4n.Kernel.storeTcbQueueLinks pair2.2 tid none none none with
                  | error e => simp
                  | ok st4 =>
                    simp only [Except.ok.injEq, Prod.mk.injEq]
                    intro ⟨_, hEq⟩; subst hEq
                    have f1 := storeEndpointOver hObj (refl hInv) hStore1
                    have f2 := f1.trans (storeTcbQueueLinks f1.invExt hLink)
                    have f3 := storeEndpointOver hObj f2 hStore2
                    exact f3.trans (storeTcbQueueLinks f3.invExt hFinal)
            | tcbNext prevTid =>
              dsimp only
              split
              · simp
              · cases hLookupP : lookupTcb st prevTid with
                | none => simp
                | some prevTcb =>
                dsimp only [hLookupP]; split
                · simp
                · -- split introduced heq✝ : (if ... then .error else match storeTcbQueueLinks ... with ...) = .ok st''✝
                  -- and the goal uses st''✝. Resolve heq✝ to extract the actual state.
                  rename_i _ _ stAp heqAp
                  split at heqAp
                  · simp at heqAp
                  · cases hLink0 : _root_.SeLe4n.Kernel.storeTcbQueueLinks st prevTid prevTcb.queuePrev prevTcb.queuePPrev tcb.queueNext with
                    | error e => simp [hLink0] at heqAp
                    | ok stPrev =>
                    simp [hLink0] at heqAp; subst heqAp
                    -- Now stAp = stPrev, goal uses stPrev
                    cases hNext : tcb.queueNext with
                    | none =>
                      dsimp only [hNext]
                      cases hStore2 : SeLe4n.Model.storeObject endpointId _ stPrev with
                      | error e => simp
                      | ok pair2 =>
                      dsimp only [hStore2]; cases hFinal : _root_.SeLe4n.Kernel.storeTcbQueueLinks pair2.2 tid none none none with
                      | error e => simp
                      | ok st4 =>
                        simp only [Except.ok.injEq, Prod.mk.injEq]
                        intro ⟨_, hEq⟩; subst hEq
                        have f1 := storeTcbQueueLinks hInv hLink0
                        have f2 := storeEndpointOver hObj f1 hStore2
                        exact f2.trans (storeTcbQueueLinks f2.invExt hFinal)
                    | some nextTid =>
                      dsimp only [hNext]
                      cases hLookupN : lookupTcb stPrev nextTid with
                      | none => simp
                      | some nextTcb =>
                      dsimp only [hLookupN]; cases hLink1 : _root_.SeLe4n.Kernel.storeTcbQueueLinks stPrev nextTid _ _ nextTcb.queueNext with
                      | error e => simp
                      | ok st2 =>
                      dsimp only [hLink1]; cases hStore2 : SeLe4n.Model.storeObject endpointId _ st2 with
                      | error e => simp
                      | ok pair2 =>
                      dsimp only [hStore2]; cases hFinal : _root_.SeLe4n.Kernel.storeTcbQueueLinks pair2.2 tid none none none with
                      | error e => simp
                      | ok st4 =>
                        simp only [Except.ok.injEq, Prod.mk.injEq]
                        intro ⟨_, hEq⟩; subst hEq
                        have f1 := storeTcbQueueLinks hInv hLink0
                        have f2 := f1.trans (storeTcbQueueLinks f1.invExt hLink1)
                        have f3 := storeEndpointOver hObj f2 hStore2
                        exact f3.trans (storeTcbQueueLinks f3.invExt hFinal)

/-- A step that rewrites notification-queue links only. -/
theorem of_ntfnLinksRewritten {st s : SystemState} (h : ntfnLinksRewritten st s) :
    RecordsFrame st s := by
  obtain ⟨hEq, hInv, hK⟩ := h
  refine ⟨fun k => ?_, by rw [hEq], hInv, by rw [hEq]⟩
  rcases hK k with e | ⟨t, t', ht, ht', np, nn, rfl⟩
  · rw [e]
  · rw [ht, ht']; rfl

theorem detachNtfnHead (st : SystemState) (head : SeLe4n.ThreadId) (next : Option SeLe4n.ThreadId)
    (hInv : st.objects.invExt) : RecordsFrame st (_root_.SeLe4n.Kernel.detachNtfnHead st head next) :=
  of_ntfnLinksRewritten (ntfnLinksRewritten_unlinkNtfnNeighbours
    (ntfnLinksRewritten_clearNtfnLinks (ntfnLinksRewritten.refl hInv) head) none next)

theorem linkNtfnWaiter {st st' : SystemState} {w : SeLe4n.ThreadId} {tail : Option SeLe4n.ThreadId}
    (hInv : st.objects.invExt) (h : _root_.SeLe4n.Kernel.linkNtfnWaiter st w tail = .ok st') :
    RecordsFrame st st' := by
  unfold _root_.SeLe4n.Kernel.linkNtfnWaiter at h
  split at h
  · cases h
  · rename_i st3 h3
    have F1 := modifyTcb (f := fun tcb => { tcb with
      ntfnPrevCode := SeLe4n.ThreadId.optCode tail, ntfnNextCode := SeLe4n.ThreadId.optCode none })
      hInv (fun _ => rfl) h3
    unfold relinkNtfnNext modifyTcbOpt at h
    split at h
    · cases h; exact F1
    · exact F1.trans (modifyTcb (f := fun tcb => { tcb with
        ntfnNextCode := SeLe4n.ThreadId.optCode (some w) }) F1.invExt (fun _ => rfl) h)

/-- A notification stored over a notification. -/
theorem storeNotificationAt {st st' : SystemState} {nid : SeLe4n.ObjId} {n n' : Notification}
    (hInv : st.objects.invExt) (hN : st.getNotification? nid = some n)
    (h : SeLe4n.Model.storeObject nid (.notification n') st = .ok ((), st')) : RecordsFrame st st' :=
  storeNotification hInv ((SystemState.getNotification?_eq_some_iff _ _ _).mp hN) h

end RecordsFrame

/-- A frame keeps a thread ready. -/
theorem RecordsFrame.ready {st st' : SystemState} (F : RecordsFrame st st') {t : SeLe4n.ThreadId}
    (h : ∀ x, st.getTcb? t = some x → x.ipcState = .ready) :
    ∀ x, st'.getTcb? t = some x → x.ipcState = .ready := fun x hx => by
  obtain ⟨y, hy, hv⟩ := F.getTcb?_view hx
  have : y.ipcState = x.ipcState := congrArg TcbRecordView.ipc hv
  rw [← this]; exact h y hy

/-- The head of a notification queue is not parked. -/
theorem notificationHead_notParked {st : SystemState} (hN : notificationWaiterConsistent st)
    {nid : SeLe4n.ObjId} {n : Notification} {w : SeLe4n.ThreadId}
    (hG : st.getNotification? nid = some n) (hH : n.waitHead = some w) : NotParkedAt st w :=
  fun x hx => by
    obtain ⟨t, hT, hB⟩ := (hN.1 nid n ((SystemState.getNotification?_eq_some_iff st nid n).1 hG)).2.1 w hH
    rw [(SystemState.getTcb?_eq_some_iff _ _ _).mp hx] at hT
    cases hT; rw [hB]; simp

namespace RecordsStep

theorem notificationSignalOnCore {nid : SeLe4n.ObjId} {badge : SeLe4n.Badge} {c : CoreId}
    {st : SystemState} (hInv : st.objects.invExt) (hN : notificationWaiterConsistent st) :
    RecordsStep st (_root_.SeLe4n.Kernel.notificationSignalOnCore nid badge c st).1 := by
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
          have S2 := storeTcbIpcStateAndMessage F1.invExt hT
            (fun x hx => .inl ((notificationHead_notParked hN hG hH).frame F1 x hx))
          obtain ⟨x, -, hx⟩ := modifyTcb_getTcb?_self F1.invExt hT
          have F3 := RecordsFrame.detachNtfnHead st2 w (ntfnSuccessor? st w) S2.invExt
          have F4 := RecordsFrame.wakeThread _ w c F3.invExt (F3.ready (fun y hy => by
            rw [hx] at hy; cases hy; simp))
          exact (of_frame F1).trans (S2.trans ((of_frame F3).trans (of_frame F4)))
    · dsimp only
      cases hS : SeLe4n.Model.storeObject nid _ st with
      | error _ => exact refl hInv
      | ok p =>
        obtain ⟨⟨⟩, st1⟩ := p
        exact of_frame (RecordsFrame.storeNotificationAt hInv hG hS)
  · split <;> exact refl hInv

theorem notificationSignalBoundOnCore {nid : SeLe4n.ObjId} {badge : SeLe4n.Badge} {c : CoreId}
    {st : SystemState} (hInv : st.objects.invExt) (hN : notificationWaiterConsistent st) :
    RecordsStep st (_root_.SeLe4n.Kernel.notificationSignalBoundOnCore nid badge c st).1 := by
  unfold _root_.SeLe4n.Kernel.notificationSignalBoundOnCore
  split
  · rename_i t epId hB
    obtain ⟨tcb, hT, hR⟩ := boundDeliveryTarget?_some st nid t epId hB
    dsimp only
    split
    · exact refl hInv
    · rename_i st1 hRm
      have F1 := RecordsFrame.endpointQueueRemoveDual hInv hRm
      split
      · exact refl hInv
      · rename_i st2 hC
        have hNP : NotParkedAt st t := fun x hx => by
          rw [hT] at hx; cases hx; rw [hR]; simp
        have S2 := storeTcbReceiveComplete F1.invExt hC (hNP.frame F1)
        obtain ⟨x, -, hx⟩ := modifyTcb_getTcb?_self F1.invExt hC
        have F3 := RecordsFrame.wakeThread st2 t c S2.invExt (fun y hy => by
          rw [hx] at hy; cases hy; simp)
        exact (of_frame F1).trans (S2.trans (of_frame F3))
  · exact notificationSignalOnCore hInv hN

theorem notificationSignalBoundCrossCoreDispatchChecked {ctx : LabelingContext} {nid : SeLe4n.ObjId}
    {signaler : SeLe4n.ThreadId} {badge : SeLe4n.Badge} {c : CoreId} {st : SystemState}
    (hInv : st.objects.invExt) (hN : notificationWaiterConsistent st) :
    RecordsStep st (_root_.SeLe4n.Kernel.notificationSignalBoundCrossCoreDispatchChecked ctx nid
      signaler badge c st).1 := by
  unfold _root_.SeLe4n.Kernel.notificationSignalBoundCrossCoreDispatchChecked
  split
  · split
    · split
      · exact notificationSignalBoundOnCore hInv hN
      · exact refl hInv
    · exact notificationSignalBoundOnCore hInv hN
  · exact refl hInv

theorem notificationSignalDeclassifiedOnCore {ctx : GenericLabelingContext}
    {declPolicy : DeclassificationPolicy} {nid : SeLe4n.ObjId} {badge : SeLe4n.Badge} {c : CoreId}
    {st : SystemState} (hInv : st.objects.invExt) (hN : notificationWaiterConsistent st) :
    RecordsStep st (_root_.SeLe4n.Kernel.notificationSignalDeclassifiedOnCore ctx declPolicy nid
      badge c st).1 := by
  unfold _root_.SeLe4n.Kernel.notificationSignalDeclassifiedOnCore
  have S := notificationSignalBoundOnCore (badge := badge) (c := c) hInv hN (nid := nid)
  generalize _root_.SeLe4n.Kernel.notificationSignalBoundOnCore nid badge c st = r at S
  obtain ⟨st1, res⟩ := r
  cases res <;> dsimp only at S ⊢ <;> repeat' split
  all_goals first
    | exact refl hInv
    | (rename_i hRec
       have hEq := recordDeclassifiedHops_frame _ _ _ _ _ hRec
       exact S.trans (of_frame (RecordsFrame.of_objects_eq S.invExt (by rw [hEq]) (by rw [hEq])
         (by rw [hEq]))))

/-- The wait, from a waiter parked on nothing. -/
theorem notificationWaitOnCore {nid : SeLe4n.ObjId} {waiter : SeLe4n.ThreadId} {c : CoreId}
    {st : SystemState} (hInv : st.objects.invExt) (hW : NotParkedAt st waiter) :
    RecordsStep st (_root_.SeLe4n.Kernel.notificationWaitOnCore nid waiter c st).1 := by
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
          exact (of_frame F1).trans (storeTcbIpcState F1.invExt hT
            (fun x hx => .inl (hW.frame F1 x hx)))
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
                have S2 := storeObject_tcb F1.invExt hO1 hSt (TcbStaysParked.of_ipc (by simp) (by simp)
                  (by
                    have := hW tcb ((SystemState.getTcb?_eq_some_iff _ _ _).mpr hO)
                    simpa using this))
                split
                · exact refl hInv
                · rename_i st4 hLink
                  have F3 := RecordsFrame.linkNtfnWaiter S2.invExt hLink
                  have F4 := RecordsFrame.removeRunnableOnCore _ waiter c F3.invExt
                  exact (of_frame F1).trans (S2.trans ((of_frame F3).trans (of_frame F4)))
  · split <;> exact refl hInv

theorem notificationWaitCrossCoreDispatchChecked {ctx : LabelingContext} {nid : SeLe4n.ObjId}
    {waiter : SeLe4n.ThreadId} {c : CoreId} {st : SystemState} (hInv : st.objects.invExt)
    (hW : NotParkedAt st waiter) :
    RecordsStep st (_root_.SeLe4n.Kernel.notificationWaitCrossCoreDispatchChecked ctx nid waiter
      c st).1 := by
  unfold _root_.SeLe4n.Kernel.notificationWaitCrossCoreDispatchChecked
  split
  · split
    · exact refl hInv
    · exact notificationWaitOnCore hInv hW
  · exact refl hInv

end RecordsStep

end SeLe4n.Kernel
