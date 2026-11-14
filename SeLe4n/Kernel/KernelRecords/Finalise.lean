-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.KernelRecords.Audit

/-!
# The finalisation keeps the records

WS-ZA ZA6.37.  A final object's finalisation (`finaliseFinalObject`) writes
threads, endpoints, notifications, scheduling contexts, replies, the scheduler
and the cores' holds, never a VSpace root or the ASID table
(`finaliseFinalObject_frame`).  Each thread it moves is cancelled with its fault
record retired, suspended `.Inactive`, or left with its fault fields, so every
fault record stays parked: the finalisation is a `RecordsStep`.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

namespace RecordsStep

/-- **A finalisation write keeping every thread's fault fields.** -/
theorem of_finaliseFrame {st st' : SystemState} (F : FinaliseFrame st st')
    (hK : tcbProjKept faultFields st' st) : RecordsStep st st' :=
  of_finaliseKept F.any hK (by rw [F.rest])

end RecordsStep

namespace RecordsFrame

/-- An object rewritten in its slot by an update keeping every record view. -/
theorem modifyObject (st : SystemState) (k : SeLe4n.ObjId) {f : KernelObject → KernelObject}
    (hInv : st.objects.invExt) (hV : ∀ o, recordViewOf (some (f o)) = recordViewOf (some o)) :
    RecordsFrame st (st.modifyObject k f) := by
  refine ⟨fun x => ?_, rfl, modifyObject_preserves_objects_invExt hInv, rfl⟩
  rw [modifyObject_objects_getElem hInv]
  split
  · rename_i h; subst h
    cases st.objects[k]? with
    | none => rfl
    | some o => exact hV o
  · rfl

/-- An endpoint's queue head popped in place: the endpoint, the successor's and
the head's queue links. -/
theorem storePopHead (st : SystemState) (e : SeLe4n.ObjId) (q : Bool) (head : SeLe4n.ThreadId)
    (next : Option SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    RecordsFrame st (SeLe4n.Kernel.storePopHead st e q head next) := by
  unfold SeLe4n.Kernel.storePopHead
  dsimp only
  have F1 := modifyObject st e (f := popEndpoint q (SeLe4n.ThreadId.optCode next)) hInv
    (fun o => by
      cases o <;> try rfl
      unfold popEndpoint
      cases q <;> cases SeLe4n.ThreadId.optCode next <;> rfl)
  cases next with
  | none => exact F1.trans (updateTcb _ head (f := tcbOffQueue) F1.invExt fun _ => rfl)
  | some n =>
    have F2 := F1.trans (updateTcb _ n (f := tcbAsQueueHead) F1.invExt fun _ => rfl)
    exact F2.trans (updateTcb _ head (f := tcbOffQueue) F2.invExt fun _ => rfl)

end RecordsFrame

namespace RecordsStep

/-- **An endpoint waiter's cancel**: the pop, its fault record retired with its
IPC, and the wake. -/
theorem storeEndpointWaiterCancelled (st : SystemState) (e : SeLe4n.ObjId) (q : Bool)
    (t : SeLe4n.ThreadId) (next : Option SeLe4n.ThreadId) (faulted : Bool)
    (hInv : st.objects.invExt) :
    RecordsStep st (SeLe4n.Kernel.storeEndpointWaiterCancelled st e q t next faulted) := by
  have F1 := RecordsFrame.storePopHead st e q t next hInv
  unfold SeLe4n.Kernel.storeEndpointWaiterCancelled
  split
  · -- A faulted waiter is left `Inactive` with its fault, which parks the record.
    unfold SeLe4n.Kernel.storeEndpointWaiterFaulted
    exact (of_frame F1).trans (updateTcb _ t (f := faultedEndpointWaiterTcb) F1.invExt
      (fun _ _ => TcbStaysParked.of_parked (.inl rfl)))
  unfold SeLe4n.Kernel.storeEndpointWaiterRestarted
  have S2 := (of_frame F1).trans (updateTcb _ t (f := cancelledEndpointWaiterTcb) F1.invExt
    (fun _ _ => TcbStaysParked.of_noFault (TCB.pendingFault_setPendingFault _ none)))
  refine S2.trans (of_frame (RecordsFrame.enqueueRunnableOnCore _ _ t S2.invExt fun x hx => ?_))
  rw [SystemState.updateTcb_getTcb?_self _ _ _ F1.invExt] at hx
  cases hT : (SeLe4n.Kernel.storePopHead st e q t next).getTcb? t with
  | none => rw [hT] at hx; cases hx
  | some y =>
    rw [hT] at hx; cases hx
    simp [cancelledEndpointWaiterTcb]

end RecordsStep

namespace RecordsFrame

/-- A bound context's unbind from its thread: the context, its release link, the
thread's binding codes, and the key hook. -/
theorem cancelBoundDonationOnCore {st st' : SystemState} {t : SeLe4n.ThreadId} {tcb : TCB}
    (hInv : st.objects.invExt) (h : SeLe4n.Kernel.cancelBoundDonationOnCore st t tcb = .ok st') :
    RecordsFrame st st' := by
  unfold SeLe4n.Kernel.cancelBoundDonationOnCore at h
  split at h
  · rename_i scId _
    cases h
    have F1 := updateSchedContext st scId
      (fun sc => { sc with boundThreadCode := 0, isActive := false, donationOrigin := none }) hInv
    have F2 := F1.trans (purgeReplenishment _ scId F1.invExt)
    have F3 := F2.trans (updateTcb _ t
      (f := fun tcb' => { tcb' with scBindingScCode := 0, scBindingOwnerCode := 0 }) F2.invExt
      fun _ => rfl)
    exact F3.trans (markKeyChangeFrom _ _ t F3.invExt)
  · cases h

/-- The pop of a reply off a context no thread holds. -/
theorem finaliseReplyUnheldPop (st : SystemState) (r : Reply) (c : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) : RecordsFrame st (SeLe4n.Kernel.finaliseReplyUnheldPop st r c) := by
  rcases finaliseReplyUnheldPop_cases st r c with e | ⟨_, _, _, _, _, hP, e⟩ |
      ⟨_, _, _, _, _, _, hP, e⟩
  · rw [e]; exact refl hInv
  · rw [e]
    have F := returnUnheldSchedContext hInv hP
    exact F.trans (settleReturnedContext _ _ _ F.invExt)
  · rw [e]; exact severUnheldSchedContext hInv hP

end RecordsFrame

namespace RecordsStep

/-- A wake of a thread `.ready` or carrying no fault. -/
theorem enqueueRunnableOnCore_ready (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) (hR : ∀ x, st.getTcb? t = some x → x.ipcState = .ready) :
    RecordsStep st (SeLe4n.Kernel.enqueueRunnableOnCore st c t) :=
  of_frame (RecordsFrame.enqueueRunnableOnCore st c t hInv hR)

/-- **A notification waiter's cancel and wake.** -/
theorem notificationWaiterCancelled (s : SystemState) (n : SeLe4n.ObjId) (t : SeLe4n.ThreadId)
    (tcb : TCB) (hInv : s.objects.invExt) (hT : s.getTcb? t = some tcb)
    (hC : notificationWaiterCancellable s n t tcb = true) :
    RecordsStep s (wakeCancelledWaiter (Lifecycle.Suspend.cancelIpcBlocking s t tcb) t) := by
  have S1 := cancelIpcBlocking s t tcb hInv
  exact S1.trans (enqueueRunnableOnCore_ready _ _ t S1.invExt fun x hx =>
    cancelIpcBlocking_victim_ready_of_ipcState s t tcb tcb hInv
      ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT) (notificationWaiterCancellable_parts hC).1 rfl
      x ((SystemState.getTcb?_eq_some_iff _ _ _).mp hx))

/-- **A finalised thread's suspend**: off the scheduler, then `.Inactive`. -/
theorem finaliseSuspend (s : SystemState) (t : SeLe4n.ThreadId) (hInv : s.objects.invExt) :
    RecordsStep s ((descheduleAtPlacement s t).updateTcb t finalisedSuspendMark) := by
  have F := RecordsFrame.descheduleAtPlacement s t hInv
  exact (of_frame F).trans (updateTcb _ t F.invExt fun _ _ => TcbStaysParked.of_parked (.inl rfl))

/-- **An endpoint-blocked thread's cancel**: off the queue, its fault record
retired with its IPC. -/
theorem storeEndpointBlockedCancelled (s : SystemState) (e : SeLe4n.ObjId) (q : Bool)
    (t : SeLe4n.ThreadId) (ep : Endpoint) (tcb : TCB) (hInv : s.objects.invExt) :
    RecordsStep s (SeLe4n.Kernel.storeEndpointBlockedCancelled s e q t ep tcb) := by
  have F := FinaliseFrame.storeEndpointBlockedCancelled s e q t ep tcb hInv
  refine ⟨rootViews_of_roots_iff F.any.write.roots_iff, F.asidTable, F.invExt, ?_, by rw [F.rest]⟩
  obtain ⟨X, i, k, hEq⟩ := tcbProjKept.storeEndpointBlockedCancelled_split (g := faultFields)
    s e q t ep tcb hInv (fun _ _ => rfl) (fun _ _ => rfl)
  rw [hEq] at F ⊢
  have i' := SystemState.updateTcb_preserves_objects_invExt _ t tcbOffQueue i
  exact (FaultsStayParked.of_kept k).trans ((FaultsStayParked.of_kept
    (tcbProjKept.updateTcb _ t (f := tcbOffQueue) i fun _ => rfl)).trans (updateTcb _ t i'
      (f := cancelledEndpointWaiterTcb)
      fun _ _ => TcbStaysParked.of_noFault (TCB.pendingFault_setPendingFault _ none)).faults)

/-- **One reply waiter orphaned**: its server forgotten, still reply-blocked, and
off the server's queue. -/
theorem orphanReplyWaiter (s : SystemState) (w x : SeLe4n.ThreadId) (hInv : s.objects.invExt) :
    RecordsStep s (SeLe4n.Kernel.orphanReplyWaiter s w x) := by
  have S1 := mapTcbInPlace s w (g := TCB.serverForgotten) hInv fun t _ =>
    TcbStaysParked.of_ipc rfl rfl (.inr (.inr ⟨_, _, TCB.serverForgotten_ipcState t⟩))
  exact S1.trans (unlinkReplyWaiter _ w x S1.invExt)

end RecordsStep

namespace RecordsStep

/-- **A reply-blocked caller's cancel**, its lent context handed back and its
holder descheduled, then its server's boost reverted. -/
theorem finaliseReplyCancel (s : SystemState) (c : SeLe4n.ThreadId) (t : TCB)
    (hInv : s.objects.invExt) :
    RecordsStep s (finaliseReplyRevert (cancelIpcBlockingReclaimed c t s) t.blockingServer?) := by
  have S1 : RecordsStep s (cancelIpcBlockingMigrated c t s) := by
    unfold cancelIpcBlockingMigrated
    have S := cancelIpcBlocking s c t hInv
    split
    · exact S.trans (of_frame (RecordsFrame.settleReturnedContext _ _ _ S.invExt))
    · exact S
  have S2 : RecordsStep s (cancelIpcBlockingReclaimed c t s) := by
    unfold cancelIpcBlockingReclaimed descheduleUnboundHolder
    split
    · exact S1
    · exact S1.trans (of_frame (RecordsFrame.descheduleAtPlacement _ _ S1.invExt))
  unfold finaliseReplyRevert
  split
  · exact S2.trans (of_frame (RecordsFrame.propagatePipChainCrossCore _ _ _ _ S2.invExt))
  · exact S2

/-- **The finalisation keeps the address-space records and every fault record
parked.** -/
theorem finaliseFinalObject (target : Nat) (st : SystemState) (hInv : st.objects.invExt) :
    RecordsStep st (SeLe4n.Kernel.finaliseFinalObject target st) :=
  finaliseFinalObject_closed (RecordsStep st)
    (fun e q s _ t tcb h _ _ _ _ => h.trans (storeEndpointWaiterCancelled s e q t _ _ h.invExt))
    (fun n s _ t tcb h _ _ hT hC => h.trans (notificationWaiterCancelled s n t tcb h.invExt hT hC))
    (fun n s _ t h _ _ _ _ => h.trans (of_finaliseFrame
      (FinaliseFrame.storeUnbindNotification s t n h.invExt)
      (tcbProjKept.storeUnbindNotification s t n h.invExt fun _ => rfl)))
    (fun s t _ h _ _ _ _ => h.trans (of_frame (RecordsFrame.descheduleAtPlacement s t h.invExt)))
    (fun _ _ _ _ _ _ h _ _ _ _ hOk => h.trans (of_frame (RecordsFrame.cancelBoundDonationOnCore h.invExt hOk)))
    (fun s _ t tcb _ h _ _ _ _ => h.trans (cancelIpcBlocking s t tcb h.invExt))
    (fun s e q t ep tcb h _ _ _ => h.trans (storeEndpointBlockedCancelled s e q t ep tcb h.invExt))
    (fun s t _ h _ _ _ _ _ => h.trans (finaliseSuspend s t h.invExt))
    (fun s t h => h.trans (of_finaliseFrame (FinaliseFrame.releaseCores s t h.invExt)
      (tcbProjKept.of_objects (finaliseThreadReleaseCores_objects s t))))
    (fun s s1 x _ rid r h _ _ hR _ hS _ _ _ _ => by
      have F := RecordsFrame.storeReply h.invExt
        ((SystemState.getReply?_eq_some_iff _ _ _).mp hR) hS
      exact h.trans (of_frame (F.trans (RecordsFrame.updateSchedContext _ _ _ F.invExt))))
    (fun s _ _ c t h _ _ _ _ => h.trans (finaliseReplyCancel s c t h.invExt))
    (fun s s1 _ tid _ h _ _ hEq => by
      subst hEq
      exact h.trans (of_frame (RecordsFrame.updateTcb s tid h.invExt fun _ => rfl)))
    ⟨fun s t h => h.trans (of_frame (RecordsFrame.cancelYieldTo s t h.invExt)),
     fun s c h => h.trans (of_frame (RecordsFrame.completeYieldFrom s c h.invExt))⟩
    (fun s w x _ h _ _ _ => h.trans (orphanReplyWaiter s w x h.invExt))
    (fun s _ r c _ h _ _ _ _ => h.trans (of_frame (RecordsFrame.finaliseReplyUnheldPop s r c h.invExt)))
    (fun s _ _ _ t h _ _ _ _ => h.trans (of_frame (RecordsFrame.cutCancelledCallerHead s t h.invExt)))
    target st (refl hInv)

end RecordsStep

end SeLe4n.Kernel
