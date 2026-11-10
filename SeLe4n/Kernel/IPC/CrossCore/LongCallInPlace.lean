-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n - A Lean Microkernel
  Copyright (C) 2026 Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.CrossCore.LongSendInPlace
import SeLe4n.Kernel.IPC.CrossCore.DeliveredInPlace

/-!
# A call of more than four words, delivered in place

seL4's `doIPCTransfer` copies a call's message as it copies a send's: the
first words register to register, the rest straight from the caller's IPC
buffer into the receiver's (`copyMRs`).  The specification holds the whole
message in the receiver's TCB and stages it.  This module is the call
rendezvous written as the long send's delivery (`LongSendInPlace`): the
receiver woken without the message, the priority walk, then the inline words
written into the receiver's saved registers and each overflow word copied from
the caller's buffer (`deliverLongSendFrame`).

The rendezvous and the walk write no thread's VSpace root or IPC buffer, no
VSpace root and no machine state (`ipcBufferReadsAgree_callWoken`), so every
word the copy reads is the word the specification read before them
(`stageWokenDelivery_performCallRendezvous_long`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-! ## Writes of a call rendezvous that keep every read -/

theorem ipcBufferReadsAgree_mapTcbInPlace_of (X : SystemState) (r : SeLe4n.ThreadId)
    (g : TCB → TCB) (hg : ∀ t, (g t).vspaceRoot = t.vspaceRoot ∧ (g t).ipcBuffer = t.ipcBuffer) :
    ipcBufferReadsAgree (X.mapTcbInPlace r g) X :=
  ipcBufferReadsAgree_mapTcbInPlace X r g hg

theorem ipcBufferReadsAgree_updateTcbAtCode (X : SystemState) (k : Nat) (g : TCB → TCB)
    (hg : ∀ t, (g t).vspaceRoot = t.vspaceRoot ∧ (g t).ipcBuffer = t.ipcBuffer) :
    ipcBufferReadsAgree (X.updateTcbAtCode k g) X := by
  unfold SystemState.updateTcbAtCode
  split
  · exact .refl _
  · exact ipcBufferReadsAgree_mapTcbInPlace X _ g hg

/-- A pop of an endpoint queue keeps every read: it writes the endpoint and
queue links. -/
theorem ipcBufferReadsAgree_storePopHead (st : SystemState) (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (head : SeLe4n.ThreadId) (next : Option SeLe4n.ThreadId)
    (hNo : st.objects.noResizeDue) :
    ipcBufferReadsAgree (storePopHead st endpointId isReceiveQ head next) st := by
  unfold storePopHead
  dsimp only
  have h1 := modifyObject_noResizeDue st endpointId
    (popEndpoint isReceiveQ (ThreadId.optCode next)) hNo
  have a1 := ipcBufferReadsAgree_modifyObject st endpointId
    (popEndpoint isReceiveQ (ThreadId.optCode next)) (ipcBufferViewOf_popEndpoint _ _) hNo
  generalize st.modifyObject endpointId (popEndpoint isReceiveQ (ThreadId.optCode next)) = s1 at h1 a1
  cases next with
  | none =>
    exact (ipcBufferReadsAgree_updateTcb s1 head tcbOffQueue (fun _ => ⟨rfl, rfl⟩) h1).trans a1
  | some n =>
    dsimp only
    have h2 := updateTcb_noResizeDue s1 n tcbAsQueueHead h1
    have a2 := ipcBufferReadsAgree_updateTcb s1 n tcbAsQueueHead (fun _ => ⟨rfl, rfl⟩) h1
    exact (ipcBufferReadsAgree_updateTcb _ head tcbOffQueue (fun _ => ⟨rfl, rfl⟩) h2).trans
      (a2.trans a1)

theorem ipcBufferReadsAgree_of_onlyObjectsScheduler {X X' : SystemState}
    (hO : SystemState.objectsAgreeOffRunLinks X' X)
    (hS : SystemState.onlyObjectsSchedulerDiffer X' X) : ipcBufferReadsAgree X' X :=
  ipcBufferReadsAgree_of_offRunLinks hO (by rw [hS])

/-- A dequeue keeps every read: it writes run-queue links and the scheduler. -/
theorem ipcBufferReadsAgree_removeRunnableOnCore (st : SystemState) (t : SeLe4n.ThreadId)
    (c : Concurrency.CoreId) : ipcBufferReadsAgree (removeRunnableOnCore st t c) st :=
  ipcBufferReadsAgree_of_onlyObjectsScheduler
    (removeRunnableOnCore_objectsAgreeOffRunLinks st t c)
    (removeRunnableOnCore_onlyObjectsSchedulerDiffer st t c)

/-- A reply-waiter link keeps every read: it writes reply-waiter links. -/
theorem ipcBufferReadsAgree_linkReplyWaiter (st : SystemState) (w s : SeLe4n.ThreadId) :
    ipcBufferReadsAgree (st.linkReplyWaiter w s) st := by
  unfold SystemState.linkReplyWaiter
  dsimp only
  generalize st.replyHeadCode s = h
  have a1 := ipcBufferReadsAgree_mapTcbInPlace st w
    (fun x => { x with replyWaiterPrevCode := 0, replyWaiterNextCode := h }) (fun _ => ⟨rfl, rfl⟩)
  generalize st.mapTcbInPlace w
    (fun x => { x with replyWaiterPrevCode := 0, replyWaiterNextCode := h }) = s1 at a1
  have a2 := ipcBufferReadsAgree_updateTcbAtCode s1 h
    (fun x => { x with replyWaiterPrevCode := LinkedQueue.code w }) (fun _ => ⟨rfl, rfl⟩)
  generalize s1.updateTcbAtCode h (fun x => { x with replyWaiterPrevCode := LinkedQueue.code w }) = s2 at a2
  exact (ipcBufferReadsAgree_mapTcbInPlace s2 s (fun x => { x with
    replyWaitersHeadCode := LinkedQueue.code w,
    replyWaitersCount := x.replyWaitersCount + 1 }) (fun _ => ⟨rfl, rfl⟩)).trans (a2.trans a1)

/-- A requeue keeps every read: it writes run-queue links and the scheduler. -/
theorem ipcBufferReadsAgree_runRequeueOnCore (st : SystemState) (c : Concurrency.CoreId)
    (t : SeLe4n.ThreadId) (p : SeLe4n.Priority) :
    ipcBufferReadsAgree (st.runRequeueOnCore c t p) st := by
  have hR := SystemState.runRemoveOnCore_onlyObjectsSchedulerDiffer st c t
  have a1 := ipcBufferReadsAgree_of_offRunLinks
    (SystemState.runRemoveOnCore_objectsAgreeOffRunLinks st c t) (by rw [hR])
  have a2 := ipcBufferReadsAgree_of_offRunLinks
    (SystemState.runEnqueueAdmitted_objectsAgreeOffRunLinks (st.runRemoveOnCore c t) c t p)
    (SystemState.runEnqueueAdmitted_machine _ c t p)
  exact (ipcBufferReadsAgree.of_eq (SystemState.runRequeueOnCore_objects st c t p) rfl).trans
    (a2.trans a1)

theorem markKeyFlagsOver_machine (st : SystemState) (tid : SeLe4n.ThreadId) (rc : Nat) (w : Bool)
    (cs : List Concurrency.CoreId) : (markKeyFlagsOver st tid rc w cs).machine = st.machine := by
  induction cs generalizing st with
  | nil => rfl
  | cons c cs ih =>
    unfold markKeyFlagsOver
    rw [ih]
    split <;> rfl

/-- The key hook keeps every read: it writes reschedule flags. -/
theorem ipcBufferReadsAgree_markKeyChangeParts (st : SystemState) (tid : SeLe4n.ThreadId)
    (p0 : SeLe4n.Priority) (d0 : SeLe4n.Deadline) (dom0 : SeLe4n.DomainId) :
    ipcBufferReadsAgree (markKeyChangeParts st tid p0 d0 dom0) st := by
  refine ipcBufferReadsAgree.of_eq (markKeyChangeParts_objects st tid p0 d0 dom0) ?_
  unfold markKeyChangeParts
  split
  · dsimp only
    split
    · rfl
    · exact markKeyFlagsOver_machine _ _ _ _ _
  · rfl

/-- A priority boost keeps every read: it writes the holder's boost, its
run-queue links and reschedule flags. -/
theorem ipcBufferReadsAgree_updatePipBoostOnCore (st : SystemState) (c : Concurrency.CoreId)
    (tid : SeLe4n.ThreadId) (hNo : st.objects.noResizeDue) :
    ipcBufferReadsAgree (PriorityInheritance.updatePipBoostOnCore st c tid) st := by
  rw [PriorityInheritance.updatePipBoostOnCore_eq_impl]
  unfold PriorityInheritance.updatePipBoostOnCoreImpl
  split
  · dsimp only
    split
    · exact .refl _
    · have a1 := ipcBufferReadsAgree_updateTcb st tid
        (fun x => { x with pipBoostCode := PriorityInheritance.computeMaxWaiterCode st tid })
        (fun _ => ⟨rfl, rfl⟩) hNo
      generalize st.updateTcb tid
        (fun x => { x with pipBoostCode := PriorityInheritance.computeMaxWaiterCode st tid }) = s1 at a1
      refine (ipcBufferReadsAgree_markKeyChangeParts _ _ _ _ _).trans ?_
      split
      · exact (ipcBufferReadsAgree_runRequeueOnCore s1 c tid _).trans a1
      · exact a1
  · exact .refl _

/-- The priority walk keeps every read. -/
theorem ipcBufferReadsAgree_propagatePipChainStateWalk :
    ∀ (n : Nat) (st : SystemState) (tid : SeLe4n.ThreadId), st.objects.noResizeDue →
      ipcBufferReadsAgree (PriorityInheritance.propagatePipChainStateWalk st tid n) st
  | 0, st, _, _ => .refl st
  | n + 1, st, tid, hNo => by
    unfold PriorityInheritance.propagatePipChainStateWalk
    have a1 := ipcBufferReadsAgree_updatePipBoostOnCore st (determineTargetCore st tid) tid hNo
    split
    · exact (ipcBufferReadsAgree_propagatePipChainStateWalk n _ _
        (updatePipBoostOnCore_noResizeDue _ _ _ hNo)).trans a1
    · exact a1

theorem ipcBufferReadsAgree_propagatePipChainCrossCore (st : SystemState) (tid : SeLe4n.ThreadId)
    (ec : Concurrency.CoreId) (hNo : st.objects.noResizeDue) :
    ipcBufferReadsAgree (PriorityInheritance.propagatePipChainCrossCore st tid ec).1 st := by
  rw [PriorityInheritance.propagatePipChainCrossCore_eq_walks]
  exact ipcBufferReadsAgree_propagatePipChainStateWalk _ st tid hNo

/-- **The call rendezvous keeps every read**: it pops the endpoint's queue,
wakes the receiver, blocks the caller on its reply, writes the reply object and
links the caller to the receiver's reply waiters, never a VSpace root, a
buffer address or the machine. -/
theorem ipcBufferReadsAgree_storeCallRendezvousReady (st : SystemState)
    (endpointId : SeLe4n.ObjId) (caller r : SeLe4n.ThreadId) (nextCode : Nat)
    (rid : SeLe4n.ReplyId) (core : Concurrency.CoreId) (hNo : st.objects.noResizeDue) :
    ipcBufferReadsAgree (storeCallRendezvousReady st endpointId caller r nextCode rid core) st := by
  unfold storeCallRendezvousReady
  dsimp only
  have h1 := storePopHead_noResizeDue st endpointId true r (ThreadId.ofOptCode nextCode) hNo
  have a1 := ipcBufferReadsAgree_storePopHead st endpointId true r (ThreadId.ofOptCode nextCode) hNo
  generalize storePopHead st endpointId true r (ThreadId.ofOptCode nextCode) = s1 at h1 a1
  have h2 := updateTcb_noResizeDue s1 r receiverReady h1
  have a2 := ipcBufferReadsAgree_updateTcb s1 r receiverReady (fun _ => ⟨rfl, rfl⟩) h1
  generalize s1.updateTcb r receiverReady = s2 at h2 a2
  have h3 := enqueueRunnableOnCore_noResizeDue s2 (determineTargetCore s2 r) r h2
  have a3 := ipcBufferReadsAgree_enqueueRunnableOnCore s2 (determineTargetCore s2 r) r h2
  generalize enqueueRunnableOnCore s2 (determineTargetCore s2 r) r = s3 at h3 a3
  have h4 := updateTcb_noResizeDue s3 caller (callCallerTcb endpointId r) h3
  have a4 := ipcBufferReadsAgree_updateTcb s3 caller (callCallerTcb endpointId r)
    (fun _ => ⟨rfl, rfl⟩) h3
  generalize s3.updateTcb caller (callCallerTcb endpointId r) = s4 at h4 a4
  have h5 := modifyObject_noResizeDue s4 rid.toObjId (replyWithCaller caller) h4
  have a5 := ipcBufferReadsAgree_modifyObject s4 rid.toObjId (replyWithCaller caller)
    (fun o => by cases o <;> rfl) h4
  generalize s4.modifyObject rid.toObjId (replyWithCaller caller) = s5 at h5 a5
  have g6 : ∀ t : TCB, ({ t with replyObjectCode := SeLe4n.ReplyId.optCode (some rid) } : TCB).vspaceRoot =
      t.vspaceRoot ∧ ({ t with replyObjectCode := SeLe4n.ReplyId.optCode (some rid) } : TCB).ipcBuffer =
      t.ipcBuffer := fun _ => ⟨rfl, rfl⟩
  have h6 := updateTcb_noResizeDue s5 caller
    (fun t => { t with replyObjectCode := SeLe4n.ReplyId.optCode (some rid) }) h5
  have a6 := ipcBufferReadsAgree_updateTcb s5 caller
    (fun t => { t with replyObjectCode := SeLe4n.ReplyId.optCode (some rid) }) g6 h5
  generalize s5.updateTcb caller
    (fun t => { t with replyObjectCode := SeLe4n.ReplyId.optCode (some rid) }) = s6 at h6 a6
  have a7 := ipcBufferReadsAgree_updateTcb s6 r (fun t => { t with pendingReceiveReplyCode := 0 })
    (fun _ => ⟨rfl, rfl⟩) h6
  generalize s6.updateTcb r (fun t => { t with pendingReceiveReplyCode := 0 }) = s7 at a7
  exact (ipcBufferReadsAgree_linkReplyWaiter _ caller r).trans
    ((ipcBufferReadsAgree_removeRunnableOnCore s7 caller core).trans
      (a7.trans (a6.trans (a5.trans (a4.trans (a3.trans (a2.trans a1)))))))

/-- …and so does the priority walk after it: the receiver a call wakes reads
every buffer where the call found it. -/
theorem ipcBufferReadsAgree_callWoken (st : SystemState) (endpointId : SeLe4n.ObjId)
    (caller r : SeLe4n.ThreadId) (nextCode : Nat) (rid : SeLe4n.ReplyId)
    (core : Concurrency.CoreId) (hNo : st.objects.noResizeDue) :
    ipcBufferReadsAgree (PriorityInheritance.propagatePipChainCrossCore
      (storeCallRendezvousReady st endpointId caller r nextCode rid core) r core).1 st :=
  (ipcBufferReadsAgree_propagatePipChainCrossCore _ r core
    (storeCallRendezvousReady_noResizeDue st endpointId caller r nextCode rid core hNo)).trans
    (ipcBufferReadsAgree_storeCallRendezvousReady st endpointId caller r nextCode rid core hNo)

/-! ## The delivery -/

/-- **The long call rendezvous, delivered**: the receiver woken without the
message, the priority walk, then the inline words written into the receiver's
saved registers and the overflow words copied from the caller's buffer into
its own (`deliverLongSendFrame`).  The message is built only where the
receiver is, unexpectedly, not ready. -/
@[noinline] def performCallDeliveredLong (st : SystemState) (endpointId : SeLe4n.ObjId)
    (caller r : SeLe4n.ThreadId) (nextCode : Nat) (rid : SeLe4n.ReplyId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badgeWord : SeLe4n.Badge) (badged : Bool) (core : Concurrency.CoreId) : SystemState :=
  deliverLongSendFrame (PriorityInheritance.propagatePipChainCrossCore
      (storeCallRendezvousReady st endpointId caller r nextCode rid core) r core).1 r
    layout rf len caller badgeWord badged 0

/-- **The staged call rendezvous is the delivered one** for a message of more
than four words, its inline words read in the caller's registers and the rest
in its IPC buffer. -/
theorem stageWokenDelivery_performCallRendezvous_long (st : SystemState)
    (endpointId : SeLe4n.ObjId) (caller r : SeLe4n.ThreadId) (next : Option SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile)
    (len : Nat) (badgeWord : SeLe4n.Badge) (badged : Bool) (core : Concurrency.CoreId)
    (hNo : st.objects.noResizeDue) (hNe : caller ≠ r)
    (hSize : layout.msgRegs.size = 4) (hLen : 4 ≤ len) :
    Architecture.stageWokenDelivery
        (performCallRendezvous st endpointId caller r next rid
          (longSendMessage layout rf st caller len (SeLe4n.Badge.opt badgeWord badged)) core)
        (some r) 0 =
      performCallDeliveredLong st endpointId caller r (ThreadId.optCode next) rid layout rf len
        badgeWord badged core := by
  have hNoS := storeCallRendezvousReady_noResizeDue st endpointId caller r
    (ThreadId.optCode next) rid core hNo
  unfold performCallRendezvous performCallDeliveredLong
  rw [storeCallRendezvous_eq_hold _ _ _ _ _ _ _ _ hNo hNe,
    propagatePipChainCrossCore_msg _ _ _ _ _ _ _ hNoS, Architecture.stageWokenDelivery_some,
    deliverLongSendFrame_eq _ st r caller layout rf len badgeWord badged 0
      (propagatePipChainCrossCore_noResizeDue _ _ _ hNoS)
      (ipcBufferReadsAgree_callWoken st endpointId caller r _ rid core hNo).words hSize hLen]

end SeLe4n.Kernel
