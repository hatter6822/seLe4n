-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/
import SeLe4n.Kernel.IPC.Invariant.SignalWakeLinkFrame
import SeLe4n.Kernel.SchedContext.NotificationDonationLenderFlow
import SeLe4n.Kernel.IPC.Invariant.ReplyBindingPairFrame
import SeLe4n.Kernel.Concurrency.Locks.LockSetForSyscall

/-!
# The head reply a signal's donation reads is the entry state's

The checked notification donation (`maybeDonateSchedContextFlowing`) asks its
lender question on the state the wake (a signal) or the consumption (a wait)
leaves: it reads the notification's context word, that context's stack head
(`SchedContext.scReply`) and the head reply's caller
(`notificationContextHeadReply?`, `notificationContextHeadLender?`).  A
footprint is resolved on the entry state, so the reply it names read-only
(`signalDonationHeadReply?`, `waitDonationHeadReply?`) is the reply the check
reads only if the step before the check moves none of the three.

Neither step does: the wake stores the notification over itself with its
context word kept, writes the woken thread and its queue neighbours, the
endpoint it leaves and the run queue; the consumption stores the notification
and writes the waiter.  No context and no reply is written.  This module states
that as a frame over the three fields (`DonationHeadFrame`) and carries it
through both steps.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency

/-- **What the donation's lender check reads of an object**: a notification's
context word, a context's stack head, a reply's caller. -/
inductive DonationHeadView where
  | notification (sc : Option SeLe4n.SchedContextId)
  | context (head : Option SeLe4n.ReplyId)
  | reply (caller : Option SeLe4n.ThreadId)

/-- The lender check's view of an object; none for any other kind. -/
def donationHeadViewOf : Option KernelObject → Option DonationHeadView
  | some (.notification n) => some (.notification n.schedContext)
  | some (.schedContext sc) => some (.context sc.scReply)
  | some (.reply r) => some (.reply r.caller)
  | _ => none

/-- **A step that moves nothing the lender check reads.** -/
def DonationHeadFrame (st st' : SystemState) : Prop :=
  ∀ oid : SeLe4n.ObjId, donationHeadViewOf st'.objects[oid]? = donationHeadViewOf st.objects[oid]?

namespace DonationHeadFrame

theorem refl (st : SystemState) : DonationHeadFrame st st := fun _ => rfl

theorem trans {a b c : SystemState} (h₁ : DonationHeadFrame a b) (h₂ : DonationHeadFrame b c) :
    DonationHeadFrame a c := fun o => (h₂ o).trans (h₁ o)

theorem of_objects_eq {st st' : SystemState} (h : st'.objects = st.objects) :
    DonationHeadFrame st st' := fun _ => by rw [h]

theorem view_withoutRunLinks (o : KernelObject) :
    donationHeadViewOf (some o.withoutRunLinks) = donationHeadViewOf (some o) := by
  cases o <;> rfl

/-- A step that writes run-queue links alone. -/
theorem of_agreeOffRunLinks {st st' : SystemState} (hA : st'.objectsAgreeOffRunLinks st) :
    DonationHeadFrame st st' :=
  fun o => proj_eq_of_map_eq _ _ view_withoutRunLinks (hA o)

/-- An insert keeping its key's view. -/
theorem of_insert {st : SystemState} {k : SeLe4n.ObjId} {o : KernelObject}
    (hInv : st.objects.invExt) (hk : donationHeadViewOf (some o) = donationHeadViewOf st.objects[k]?) :
    DonationHeadFrame st { st with objects := st.objects.insert k o } :=
  proj_insert_eq _ hInv hk

/-- A store keeping its key's view. -/
theorem storeObject {st st' : SystemState} {k : SeLe4n.ObjId} {o : KernelObject}
    (hInv : st.objects.invExt) (hS : SeLe4n.Model.storeObject k o st = .ok ((), st'))
    (hk : donationHeadViewOf (some o) = donationHeadViewOf st.objects[k]?) :
    DonationHeadFrame st st' := fun oid => by
  by_cases h : oid = k
  · subst h; rw [storeObject_objects_eq st st' oid o hInv hS]; exact hk
  · rw [storeObject_objects_ne st st' k oid o h hInv hS]

/-- A thread rewritten in its slot. -/
theorem updateTcb (st : SystemState) (t : SeLe4n.ThreadId) (f : TCB → TCB)
    (hInv : st.objects.invExt) : DonationHeadFrame st (st.updateTcb t f) := by
  cases hG : st.getTcb? t with
  | none => rw [SystemState.updateTcb_eq_self_of_none hG]; exact refl st
  | some x =>
    rw [SystemState.updateTcb_eq_of_some hG]
    have hPre := (SystemState.getTcb?_eq_some_iff st t x).mp hG
    exact of_insert hInv (by rw [hPre]; rfl)

/-- A thread rewritten through `modifyTcb`. -/
theorem modifyTcb {st st' : SystemState} {tid : SeLe4n.ThreadId} {f : TCB → TCB}
    (hInv : st.objects.invExt) (h : SeLe4n.Kernel.modifyTcb st tid f = .ok st') :
    DonationHeadFrame st st' := by
  obtain ⟨tcb, hL, hS⟩ := modifyTcb_ok_decompose h
  have hPre := lookupTcb_some_objects st tid tcb hL
  exact storeObject hInv hS (by rw [hPre]; rfl)

/-- An endpoint stored over an endpoint. -/
theorem storeObject_endpoint {st st' : SystemState} {k : SeLe4n.ObjId} {ep ep' : Endpoint}
    (hInv : st.objects.invExt) (hPre : st.objects[k]? = some (.endpoint ep))
    (hS : SeLe4n.Model.storeObject k (.endpoint ep') st = .ok ((), st')) :
    DonationHeadFrame st st' :=
  storeObject hInv hS (by rw [hPre]; rfl)

/-- A notification stored over a notification, its context word kept. -/
theorem storeObject_notification {st st' : SystemState} {k : SeLe4n.ObjId} {n n' : Notification}
    (hInv : st.objects.invExt) (hPre : st.objects[k]? = some (.notification n))
    (hS : SeLe4n.Model.storeObject k (.notification n') st = .ok ((), st'))
    (hC : n'.schedContextCode = n.schedContextCode) : DonationHeadFrame st st' :=
  storeObject hInv hS (by rw [hPre]; simp only [donationHeadViewOf, Notification.schedContext, hC])

/-- A head leaving its notification queue. -/
theorem detachNtfnHead (st : SystemState) (head : SeLe4n.ThreadId)
    (next : Option SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    DonationHeadFrame st (SeLe4n.Kernel.detachNtfnHead st head next) := by
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

/-- The wake: a run-queue insert and the `.ready` mark. -/
theorem enqueueRunnableOnCore (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) :
    DonationHeadFrame st (SeLe4n.Kernel.enqueueRunnableOnCore st c t) := by
  cases hT : st.getTcb? t with
  | none =>
    simp only [SeLe4n.Kernel.enqueueRunnableOnCore, SystemState.getTcbWitnessed?_eq_none hT]
    exact refl st
  | some tcb =>
    cases hD : wakeDeclines st c t with
    | true =>
      simp only [SeLe4n.Kernel.enqueueRunnableOnCore, SystemState.getTcbWitnessed?_eq_some hT, hD,
        if_true]
      exact refl st
    | false =>
      have hPre := (SystemState.getTcb?_eq_some_iff st t tcb).mp hT
      have h1 := of_insert (st := st) (k := t.toObjId) (o := .tcb (tcb.setIpcState .ready)) hInv
        (by rw [hPre]; rfl)
      exact h1.trans (of_agreeOffRunLinks (enqueueRunnableOnCore_objectsAgree_marked st c t tcb hT hD))

theorem wakeThread (st : SystemState) (t : SeLe4n.ThreadId) (c : CoreId)
    (hInv : st.objects.invExt) : DonationHeadFrame st (SeLe4n.Kernel.wakeThread st t c).1 :=
  enqueueRunnableOnCore st _ t hInv

/-- An endpoint-queue removal: endpoint stores and queue-link writes. -/
theorem endpointQueueRemoveDual {st st' : SystemState} {endpointId : SeLe4n.ObjId}
    {isReceiveQ : Bool} {tid : SeLe4n.ThreadId} (hInv : st.objects.invExt)
    (h : SeLe4n.Kernel.endpointQueueRemoveDual endpointId isReceiveQ tid st = .ok ((), st')) :
    DonationHeadFrame st st' :=
  endpointQueueRemoveDual_carry (P := fun s => DonationHeadFrame st s) endpointId isReceiveQ tid st st'
    (fun _ _ _ _ hE hI hS _ hP => hP.trans (storeObject_endpoint hI hE hS))
    (fun _ _ _ _ _ _ hI hS hP => hP.trans (modifyTcb hI hS)) hInv h (refl st)

end DonationHeadFrame

/-- **A signal's wake of its notification's head or its word's accumulation
moves nothing the lender check reads.** -/
theorem notificationSignalOnCore_donationHeadFrame (n : SeLe4n.ObjId) (badge : SeLe4n.Badge)
    (c : CoreId) (st : SystemState) (hInv : st.objects.invExt) :
    DonationHeadFrame st (notificationSignalOnCore n badge c st).1 := by
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
        have F1 := DonationHeadFrame.storeObject hInv hS (by rw [hPre]; rfl)
        have I1 := storeObject_preserves_objects_invExt st st1 _ _ hInv hS
        dsimp only
        split
        · exact .refl st
        · rename_i st2 hT
          rename_i waiter _ _
          have F2 := F1.trans (DonationHeadFrame.modifyTcb I1 hT)
          have I2 := storeTcbSignalWoken_preserves_objects_invExt _ _ _ _ I1 hT
          have I3 := detachNtfnHead_preserves_objects_invExt st2 waiter (ntfnSuccessor? st waiter) I2
          have F3 := DonationHeadFrame.detachNtfnHead st2 waiter (ntfnSuccessor? st waiter) I2
          exact (F2.trans F3).trans (DonationHeadFrame.enqueueRunnableOnCore _ _ _ I3)
    · dsimp only
      cases hS : storeObject n _ st with
      | error _ => exact .refl st
      | ok p =>
        obtain ⟨⟨⟩, st1⟩ := p
        exact DonationHeadFrame.storeObject hInv hS (by rw [hPre]; rfl)
  · split <;> exact .refl st

/-- **A signal's wake moves nothing the lender check reads**: the bound thread
taken off its endpoint and woken, or the notification's own signal. -/
theorem notificationSignalBoundOnCore_donationHeadFrame (n : SeLe4n.ObjId) (badge : SeLe4n.Badge)
    (c : CoreId) (st : SystemState) (hInv : st.objects.invExt) :
    DonationHeadFrame st (notificationSignalBoundOnCore n badge c st).1 := by
  unfold notificationSignalBoundOnCore
  split
  · split
    · exact .refl st
    · rename_i st1 hR
      have F1 := DonationHeadFrame.endpointQueueRemoveDual hInv hR
      have I1 := endpointQueueRemoveDual_preserves_objects_invExt _ _ _ _ _ hInv hR
      split
      · exact .refl st
      · rename_i st2 hT
        have F2 := F1.trans (DonationHeadFrame.modifyTcb I1 hT)
        have I2 := storeTcbSignalBoundWoken_preserves_objects_invExt _ _ _ _ I1 hT
        exact F2.trans (DonationHeadFrame.wakeThread _ _ c I2)
  · exact notificationSignalOnCore_donationHeadFrame n badge c st hInv

/-- **A wait that consumes its notification's word moves nothing the lender
check reads**: the notification stored with its context word kept, the waiter
marked ready. -/
theorem notificationWaitOnCore_consumed_donationHeadFrame {n : SeLe4n.ObjId}
    {w : SeLe4n.ThreadId} {c : CoreId} {st st' : SystemState} {badge : SeLe4n.Badge}
    (hInv : st.objects.invExt) (h : notificationWaitOnCore n w c st = (st', .ok (some badge))) :
    DonationHeadFrame st st' := by
  unfold notificationWaitOnCore at h
  cases hN : st.getNotification? n with
  | none =>
    rw [hN] at h
    by_cases hO : (st.getObject? n).isSome = true
    · simp only [hO, ↓reduceIte] at h; cases h
    · simp only [hO, Bool.false_eq_true, ↓reduceIte] at h; cases h
  | some ntfn =>
    rw [hN] at h
    have hPre := (SystemState.getNotification?_eq_some_iff st n ntfn).mp hN
    cases hB : ntfn.pendingBadge with
    | none =>
      simp only [hB] at h
      split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · cases h
          · split at h
            · cases h
            · split at h <;> cases h
    | some b =>
      simp only [hB] at h
      generalize hS : storeObject n _ st = rS at h
      cases rS with
      | error _ => cases h
      | ok p =>
        obtain ⟨⟨⟩, st1⟩ := p
        have F1 := DonationHeadFrame.storeObject hInv hS (by rw [hPre]; rfl)
        have I1 := storeObject_preserves_objects_invExt st st1 _ _ hInv hS
        dsimp only at h
        cases hT : storeTcbIpcState st1 w .ready with
        | error _ => rw [hT] at h; cases h
        | ok st2 =>
          rw [hT] at h
          cases h
          exact F1.trans (DonationHeadFrame.modifyTcb I1 hT)

/-! ### The check reads the entry state's head reply -/

/-- The notification context word a view carries. -/
def DonationHeadView.ntfnContext? : Option DonationHeadView → Option (Option SeLe4n.SchedContextId)
  | some (.notification s) => some s
  | _ => none

/-- The stack head a view carries. -/
def DonationHeadView.contextHead? : Option DonationHeadView → Option (Option SeLe4n.ReplyId)
  | some (.context r) => some r
  | _ => none

/-- The caller a view carries. -/
def DonationHeadView.replyCaller? : Option DonationHeadView → Option (Option SeLe4n.ThreadId)
  | some (.reply c) => some c
  | _ => none

theorem getNotification?_schedContext_view (st : SystemState) (n : SeLe4n.ObjId) :
    (st.getNotification? n).map (·.schedContext) =
      DonationHeadView.ntfnContext? (donationHeadViewOf st.objects[n]?) := by
  unfold SystemState.getNotification?
  cases st.objects[n]? with
  | none => rfl
  | some o => cases o <;> rfl

theorem getSchedContext?_scReply_view (st : SystemState) (s : SeLe4n.SchedContextId) :
    (st.getSchedContext? s).map (·.scReply) =
      DonationHeadView.contextHead? (donationHeadViewOf st.objects[s.toObjId]?) := by
  unfold SystemState.getSchedContext?
  cases st.objects[s.toObjId]? with
  | none => rfl
  | some o => cases o <;> rfl

theorem getReply?_caller_view (st : SystemState) (r : SeLe4n.ReplyId) :
    (st.getReply? r).map (·.caller) =
      DonationHeadView.replyCaller? (donationHeadViewOf st.objects[r.toObjId]?) := by
  unfold SystemState.getReply?
  cases st.objects[r.toObjId]? with
  | none => rfl
  | some o => cases o <;> rfl

/-- The head reply, read through the three views. -/
theorem notificationContextHeadReply?_eq_views (st : SystemState) (n : SeLe4n.ObjId) :
    notificationContextHeadReply? st n =
      (((st.getNotification? n).map (·.schedContext)).bind id).bind fun s =>
        ((st.getSchedContext? s).map (·.scReply)).bind id := by
  unfold notificationContextHeadReply?
  cases st.getNotification? n with
  | none => rfl
  | some ntfn =>
    cases h : ntfn.schedContext with
    | none => simp only [h, Option.map_some, Option.bind_some, id, Option.bind_none]
    | some s =>
      simp only [h, Option.map_some, Option.bind_some, id]
      cases st.getSchedContext? s <;> rfl

namespace DonationHeadFrame

/-- **A step moving nothing the check reads keeps the head reply.** -/
theorem headReply_eq {st st' : SystemState} (h : DonationHeadFrame st st') (n : SeLe4n.ObjId) :
    notificationContextHeadReply? st' n = notificationContextHeadReply? st n := by
  rw [notificationContextHeadReply?_eq_views, notificationContextHeadReply?_eq_views,
    getNotification?_schedContext_view, getNotification?_schedContext_view, h n]
  congr 1
  funext s
  rw [getSchedContext?_scReply_view, getSchedContext?_scReply_view, h s.toObjId]

/-- **…and the top lender**, so the check's answer. -/
theorem headLender_eq {st st' : SystemState} (h : DonationHeadFrame st st') (n : SeLe4n.ObjId) :
    notificationContextHeadLender? st' n = notificationContextHeadLender? st n :=
  notificationContextHeadLender?_congr (h.headReply_eq n) fun r _ => by
    have e : (st'.getReply? r).map (·.caller) = (st.getReply? r).map (·.caller) := by
      rw [getReply?_caller_view, getReply?_caller_view, h r.toObjId]
    cases h1 : st'.getReply? r <;> cases h2 : st.getReply? r <;> rw [h1, h2] at e <;>
      simp_all

theorem lenderFlows_eq {st st' : SystemState} (h : DonationHeadFrame st st') (ctx : LabelingContext)
    (n : SeLe4n.ObjId) (tid : SeLe4n.ThreadId) :
    donationLenderFlows ctx st' n tid = donationLenderFlows ctx st n tid :=
  donationLenderFlows_congr (h.headLender_eq n)

end DonationHeadFrame

/-- **The head reply the signal's donation reads is the entry state's.** -/
theorem notificationSignalBoundOnCore_headReply_eq (n : SeLe4n.ObjId) (badge : SeLe4n.Badge)
    (c : CoreId) (st : SystemState) (hInv : st.objects.invExt) :
    notificationContextHeadReply? (notificationSignalBoundOnCore n badge c st).1 n =
      notificationContextHeadReply? st n :=
  (notificationSignalBoundOnCore_donationHeadFrame n badge c st hInv).headReply_eq n

/-- **The head reply the wait's completion reads is the entry state's**: the
consumption and the waiter's return frame move none of what the check reads. -/
theorem notificationWaitOnCore_headReply_eq {n : SeLe4n.ObjId} {w : SeLe4n.ThreadId}
    {c : CoreId} {st st1 : SystemState} {badge : SeLe4n.Badge} (hInv : st.objects.invExt)
    (h : notificationWaitOnCore n w c st = (st1, .ok (some badge)))
    (frame : Architecture.SyscallReturnFrame) :
    notificationContextHeadReply? (Architecture.writeReturnFrameToTcb st1 w frame) n =
      notificationContextHeadReply? st n := by
  have F := notificationWaitOnCore_consumed_donationHeadFrame hInv h
  have I1 : st1.objects.invExt := by
    have := notificationWaitCrossCoreDispatch_preserves_objects_invExt n w c st hInv
    unfold notificationWaitCrossCoreDispatch at this
    rw [h] at this; exact this
  exact (F.trans (DonationHeadFrame.updateTcb st1 w _ I1)).headReply_eq n

/-- **The signal's footprint locks the reply its donation reads**: where the
signal wakes a thread, the head reply the checked donation's lender check reads
on the state the wake leaves is named by the footprint the entry state declares
(`Concurrency.lockSetForSyscall_notificationSignal_covers_donationHeadReply`). -/
theorem sendSignal_donationHeadReply_locked (ops : Concurrency.SyscallLockOperands)
    (st : SystemState) (caller : TCB) (n : SeLe4n.ObjId) (S : LockSet)
    (badge : SeLe4n.Badge) (c : CoreId) (t : SeLe4n.ThreadId) (r : SeLe4n.ReplyId)
    (hInv : st.objects.invExt) (hTcb : st.getTcb? ops.caller = some caller)
    (hNtfn : ops.targetObject = some n)
    (hDecl : Concurrency.lockSetForSyscall .notificationSignal ops st = some S)
    (hT : signalWokenThread? st n = some t)
    (hR : notificationContextHeadReply? (notificationSignalBoundOnCore n badge c st).1 n = some r) :
    ∃ m, (replyLock r, m) ∈ S.pairs := by
  rw [notificationSignalBoundOnCore_headReply_eq n badge c st hInv] at hR
  refine Concurrency.lockSetForSyscall_notificationSignal_covers_donationHeadReply ops st caller n S r
    hTcb hNtfn ?_ hDecl
  unfold Concurrency.signalDonationHeadReply?
  rw [hT]; exact hR

/-- **The wait's footprint locks the reply its completion's donation reads.** -/
theorem completeSignal_donationHeadReply_locked (ops : Concurrency.SyscallLockOperands)
    (st st1 : SystemState) (caller : TCB) (n : SeLe4n.ObjId) (S : LockSet)
    (c : CoreId) (badge : SeLe4n.Badge) (frame : Architecture.SyscallReturnFrame) (r : SeLe4n.ReplyId)
    (hInv : st.objects.invExt) (hTcb : st.getTcb? ops.caller = some caller)
    (hNtfn : ops.targetObject = some n)
    (hDecl : Concurrency.lockSetForSyscall .notificationWait ops st = some S)
    (hW : notificationWaitOnCore n ops.caller c st = (st1, .ok (some badge)))
    (hR : notificationContextHeadReply?
      (Architecture.writeReturnFrameToTcb st1 ops.caller frame) n = some r) :
    ∃ m, (replyLock r, m) ∈ S.pairs := by
  rw [notificationWaitOnCore_headReply_eq hInv hW frame] at hR
  refine Concurrency.lockSetForSyscall_notificationWait_covers_donationHeadReply ops st caller n S r
    hTcb hNtfn ?_ hDecl
  unfold Concurrency.waitDonationHeadReply?
  rw [notificationWaitOnCore_notificationPending hW]
  exact hR

end SeLe4n.Kernel
