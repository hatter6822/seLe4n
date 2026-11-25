-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.Invariant.SchedLinkFrame
import SeLe4n.Kernel.IPC.CrossCore.SignalDonation

/-!
# A signal's wake writes no scheduling link

seL4-MCS `sendSignal` donates the notification's context to the thread it wakes
after the wake (`sendSignalOnCore`).  The wake stores the notification, writes
the woken thread's IPC state, badge register and queue links, unlinks it from
its endpoint or its notification's queue, and places it on its home core's run
queue: no thread's binding codes, budget or affinity, no context's bound thread
or release fields, and no release-queue slot.  So the donation finds the binding
pair, the guard and the home core as the signal was handed them.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency

/-- A head leaving its notification queue keeps the object store's integrity. -/
theorem detachNtfnHead_preserves_objects_invExt (st : SystemState) (head : SeLe4n.ThreadId)
    (next : Option SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    (detachNtfnHead st head next).objects.invExt := by
  unfold detachNtfnHead unlinkNtfnNeighbours clearNtfnLinks
  have i1 := SystemState.updateTcb_preserves_objects_invExt st head (fun t => { t with
    ntfnPrevCode := SeLe4n.ThreadId.optCode none,
    ntfnNextCode := SeLe4n.ThreadId.optCode none }) hInv
  dsimp only
  cases next with
  | none => exact i1
  | some n => exact SystemState.updateTcb_preserves_objects_invExt _ n _ i1

namespace SchedLinkFrame

/-- A thread rewritten through `modifyTcb` keeping its binding codes, budget and
affinity. -/
theorem modifyTcb {st st' : SystemState} {tid : SeLe4n.ThreadId} {f : TCB → TCB}
    (hInv : st.objects.invExt) (h : SeLe4n.Kernel.modifyTcb st tid f = .ok st')
    (hf : ∀ x, (f x).scBindingScCode = x.scBindingScCode ∧
      (f x).scBindingOwnerCode = x.scBindingOwnerCode ∧ (f x).timeoutBudget = x.timeoutBudget ∧
      (f x).cpuAffinity = x.cpuAffinity := by intro _; exact ⟨rfl, rfl, rfl, rfl⟩) :
    SchedLinkFrame st st' := by
  obtain ⟨tcb, hL, hS⟩ := modifyTcb_ok_decompose h
  have hPre := lookupTcb_some_objects st tid tcb hL
  obtain ⟨h1, h2, h3, h4⟩ := hf tcb
  exact SchedLinkFrame.storeObject hInv hS (by rw [hPre]; simp [tcbSchedAuxOf, h3, h4])
    (by rw [hPre]; simp [schedBindingLinksOf, h1, h2]) (by rw [hPre]; rfl)

/-- A thread's endpoint-queue links written. -/
theorem storeTcbQueueLinks {st st' : SystemState} {tid : SeLe4n.ThreadId}
    {prev : Option SeLe4n.ThreadId} {pprev : Option QueuePPrev} {next : Option SeLe4n.ThreadId}
    (hInv : st.objects.invExt) (h : SeLe4n.Kernel.storeTcbQueueLinks st tid prev pprev next = .ok st') :
    SchedLinkFrame st st' :=
  modifyTcb hInv h

/-- An endpoint stored over an endpoint. -/
theorem storeObject_endpoint {st st' : SystemState} {k : SeLe4n.ObjId} {ep ep' : Endpoint}
    (hInv : st.objects.invExt) (hPre : st.objects[k]? = some (.endpoint ep))
    (hS : SeLe4n.Model.storeObject k (.endpoint ep') st = .ok ((), st')) : SchedLinkFrame st st' :=
  SchedLinkFrame.storeObject hInv hS (by rw [hPre]; rfl) (by rw [hPre]; rfl) (by rw [hPre]; rfl)

/-- A notification stored over a notification. -/
theorem storeObject_notification {st st' : SystemState} {k : SeLe4n.ObjId} {n n' : Notification}
    (hInv : st.objects.invExt) (hPre : st.objects[k]? = some (.notification n))
    (hS : SeLe4n.Model.storeObject k (.notification n') st = .ok ((), st')) : SchedLinkFrame st st' :=
  SchedLinkFrame.storeObject hInv hS (by rw [hPre]; rfl) (by rw [hPre]; rfl) (by rw [hPre]; rfl)

/-- A head leaving its notification queue: its links and its successor's
predecessor link cleared. -/
theorem detachNtfnHead (st : SystemState) (head : SeLe4n.ThreadId)
    (next : Option SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    SchedLinkFrame st (SeLe4n.Kernel.detachNtfnHead st head next) := by
  unfold SeLe4n.Kernel.detachNtfnHead unlinkNtfnNeighbours clearNtfnLinks
  have h1 := updateTcb st head (fun t => { t with
    ntfnPrevCode := SeLe4n.ThreadId.optCode none,
    ntfnNextCode := SeLe4n.ThreadId.optCode none }) hInv
  have i1 := SystemState.updateTcb_preserves_objects_invExt st head (fun t => { t with
    ntfnPrevCode := SeLe4n.ThreadId.optCode none,
    ntfnNextCode := SeLe4n.ThreadId.optCode none }) hInv
  dsimp only
  cases next with
  | none => exact h1
  | some n => exact h1.trans (updateTcb _ n _ i1)

/-- The wake: the thread placed on its home core's run queue. -/
theorem wakeThread (st : SystemState) (t : SeLe4n.ThreadId) (c : CoreId)
    (hInv : st.objects.invExt) : SchedLinkFrame st (SeLe4n.Kernel.wakeThread st t c).1 :=
  enqueueRunnableOnCore st _ t hInv

/-- An endpoint-queue removal: endpoint stores and queue-link writes. -/
theorem endpointQueueRemoveDual {st st' : SystemState} {endpointId : SeLe4n.ObjId}
    {isReceiveQ : Bool} {tid : SeLe4n.ThreadId} (hInv : st.objects.invExt)
    (h : SeLe4n.Kernel.endpointQueueRemoveDual endpointId isReceiveQ tid st = .ok ((), st')) :
    SchedLinkFrame st st' :=
  endpointQueueRemoveDual_carry (P := fun s => SchedLinkFrame st s) endpointId isReceiveQ tid st st'
    (fun _ _ _ _ hE hI hS _ hP => hP.trans (storeObject_endpoint hI hE hS))
    (fun _ _ _ _ _ _ hI hS hP => hP.trans (storeTcbQueueLinks hI hS)) hInv h (.refl st)

end SchedLinkFrame

/-- **A signal's wake of its notification's head or its word's accumulation
writes no scheduling link.** -/
theorem notificationSignalOnCore_schedLinkFrame (n : SeLe4n.ObjId) (badge : SeLe4n.Badge)
    (c : CoreId) (st : SystemState) (hInv : st.objects.invExt) :
    SchedLinkFrame st (notificationSignalOnCore n badge c st).1 := by
  unfold notificationSignalOnCore
  split
  · rename_i ntfn hN
    have hPre := (SystemState.getNotification?_eq_some_iff st n ntfn).mp hN
    split
    · dsimp only
      cases hS : storeObject n _ st with
      | error _ => exact .refl st
      | ok p =>
        obtain ⟨⟨⟩, st1⟩ := p
        have F1 := SchedLinkFrame.storeObject_notification hInv hPre hS
        have I1 := storeObject_preserves_objects_invExt st st1 _ _ hInv hS
        dsimp only
        split
        · exact .refl st
        · rename_i st2 hT
          rename_i waiter _ _
          have F2 := F1.trans (SchedLinkFrame.modifyTcb I1 hT)
          have I2 := storeTcbSignalWoken_preserves_objects_invExt _ _ _ _ I1 hT
          have F3 := F2.trans (SchedLinkFrame.detachNtfnHead st2 waiter (ntfnSuccessor? st waiter) I2)
          exact F3.trans (SchedLinkFrame.wakeThread _ _ c
            (detachNtfnHead_preserves_objects_invExt _ _ _ I2))
    · dsimp only
      cases hS : storeObject n _ st with
      | error _ => exact .refl st
      | ok p =>
        obtain ⟨⟨⟩, st1⟩ := p
        exact SchedLinkFrame.storeObject_notification hInv hPre hS
  · split <;> exact .refl st

/-- **A signal's wake writes no scheduling link**: the bound thread taken off
its endpoint and woken, or the notification's own signal. -/
theorem notificationSignalBoundOnCore_schedLinkFrame (n : SeLe4n.ObjId) (badge : SeLe4n.Badge)
    (c : CoreId) (st : SystemState) (hInv : st.objects.invExt) :
    SchedLinkFrame st (notificationSignalBoundOnCore n badge c st).1 := by
  unfold notificationSignalBoundOnCore
  split
  · split
    · exact .refl st
    · rename_i st1 hR
      have F1 := SchedLinkFrame.endpointQueueRemoveDual hInv hR
      have I1 := endpointQueueRemoveDual_preserves_objects_invExt _ _ _ _ _ hInv hR
      split
      · exact .refl st
      · rename_i st2 hT
        have F2 := F1.trans (SchedLinkFrame.modifyTcb I1 hT)
        have I2 := storeTcbSignalBoundWoken_preserves_objects_invExt _ _ _ _ I1 hT
        exact F2.trans (SchedLinkFrame.wakeThread _ _ c I2)
  · exact notificationSignalOnCore_schedLinkFrame n badge c st hInv

/-- **The bind's writes keep the object store's integrity**: the context and the
thread rewritten in their slots, the run-queue links and the release links. -/
theorem schedContextBindPerform_preserves_objects_invExt (st : SystemState)
    (vS : SeLe4n.ValidObjId) (vT : SeLe4n.ValidThreadId) (hInv : st.objects.invExt) :
    (SchedContextOps.schedContextBindPerform st vS vT).objects.invExt := by
  unfold SchedContextOps.schedContextBindPerform
  split
  · exact hInv
  split
  · exact hInv
  dsimp only
  apply SystemState.releasePlace_objects_invExt
  split
  · rw [SystemState.markReschedulePendingOnCore_objects]
    exact SystemState.runEnqueueOnCore_objects_invExt _ _ _ _
      (SystemState.updateTcb_preserves_objects_invExt _ _ _
        (SystemState.rewriteObject_preserves_objects_invExt _ _ _ _ hInv))
  · exact SystemState.updateTcb_preserves_objects_invExt _ _ _
      (SystemState.rewriteObject_preserves_objects_invExt _ _ _ _ hInv)

/-- **The donation keeps the object store's integrity.** -/
theorem maybeDonateSchedContext_preserves_objects_invExt (st : SystemState) (n : SeLe4n.ObjId)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    (maybeDonateSchedContext st n tid).objects.invExt :=
  maybeDonateSchedContext_induct (fun _ b => b.objects.invExt) st n tid hInv
    (fun vS vT _ _ => schedContextBindPerform_preserves_objects_invExt st vS vT hInv)

/-- …and so does seL4's `sendSignal`. -/
theorem sendSignalOnCore_preserves_objects_invExt
    (n : SeLe4n.ObjId) (badge : SeLe4n.Badge) (c : CoreId) (st : SystemState)
    (hInv : st.objects.invExt) : (sendSignalOnCore n badge c st).1.objects.invExt :=
  sendSignalOnCore_induct (fun s => s.objects.invExt) n badge c st
    (notificationSignalBoundOnCore_preserves_objects_invExt n badge c st hInv)
    (fun t _ _ _ => maybeDonateSchedContext_preserves_objects_invExt _ n t
      (notificationSignalBoundOnCore_preserves_objects_invExt n badge c st hInv))

/-- **The thread a signal wakes is blocked on a receive or on the notification**,
never on a reply, so it owns no donation. -/
theorem signalWokenThread?_not_blockedOnReply {st : SystemState} {n : SeLe4n.ObjId}
    {t : SeLe4n.ThreadId} (hNWC : notificationWaiterConsistent st)
    (h : signalWokenThread? st n = some t) :
    ∀ tcb, st.objects[t.toObjId]? = some (.tcb tcb) → ∀ ep rt,
      tcb.ipcState ≠ .blockedOnReply ep rt := by
  intro tcb hT ep rt hR
  unfold signalWokenThread? at h
  cases hB : boundDeliveryTarget? st n with
  | some p =>
    obtain ⟨t', e⟩ := p
    rw [hB] at h
    cases h
    obtain ⟨tcb', hT', hI⟩ := boundDeliveryTarget?_some st n t e hB
    rw [(SystemState.getTcb?_eq_some_iff _ _ _).mp hT'] at hT
    cases hT
    rw [hI] at hR; cases hR
  | none =>
    rw [hB] at h
    cases hN : st.getNotification? n with
    | none => rw [hN] at h; cases h
    | some ntfn =>
      rw [hN] at h
      obtain ⟨tcb', hT', hI⟩ := (hNWC.1 n ntfn
        ((SystemState.getNotification?_eq_some_iff _ _ _).mp hN)).2.1 t h
      rw [hT'] at hT
      cases hT
      rw [hI] at hR; cases hR

end SeLe4n.Kernel
