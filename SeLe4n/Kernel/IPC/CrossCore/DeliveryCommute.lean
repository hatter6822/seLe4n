/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyInPlace
import SeLe4n.Kernel.Scheduler.TcbWriteCommute

/-!
# A delivery commutes with the rendezvous's other writes

WS-ZA ZA4.7.  A delivery writes one thread's message slots — its saved
registers, its pending message and its stashed receive reply
(`TCB.withMessageSlots`) — and nothing the
run queue, the reply-waiter queues or the priority walk reads or writes.  On an
object table with no resize due, every write those make is a slot write
(`TcbWriteCommute`), so the delivery commutes with each of them: written first
or written last, the state is the same.  The fast IPC paths use this to write a
delivered message where the specification stages it, after the priority walk,
without building the message.
-/

namespace SeLe4n.Model

/-- A TCB rewritten in its message slots alone: its saved registers, its
pending message and its stashed receive reply. -/
@[inline] def TCB.withMessageSlots (ρ : SeLe4n.RegisterFile → SeLe4n.RegisterFile)
    (μ : Option IpcMessage → Option IpcMessage)
    (π : Option SeLe4n.ReplyId → Option SeLe4n.ReplyId) (t : TCB) : TCB :=
  { t with registerContext := ρ t.registerContext, pendingMessage := μ t.pendingMessage,
           pendingReceiveReply := π t.pendingReceiveReply }

section
variable (ρ : SeLe4n.RegisterFile → SeLe4n.RegisterFile) (μ : Option IpcMessage → Option IpcMessage)
  (π : Option SeLe4n.ReplyId → Option SeLe4n.ReplyId) (t : TCB)
@[simp] theorem TCB.withMessageSlots_pipBoost : (TCB.withMessageSlots ρ μ π t).pipBoost = t.pipBoost := rfl
@[simp] theorem TCB.withMessageSlots_priority : (TCB.withMessageSlots ρ μ π t).priority = t.priority := rfl
@[simp] theorem TCB.withMessageSlots_boostedPriority :
    (TCB.withMessageSlots ρ μ π t).boostedPriority = t.boostedPriority := rfl
@[simp] theorem TCB.withMessageSlots_domain : (TCB.withMessageSlots ρ μ π t).domain = t.domain := rfl
@[simp] theorem TCB.withMessageSlots_runCoreCode :
    (TCB.withMessageSlots ρ μ π t).runCoreCode = t.runCoreCode := rfl
@[simp] theorem TCB.withMessageSlots_ipcState : (TCB.withMessageSlots ρ μ π t).ipcState = t.ipcState := rfl
@[simp] theorem TCB.withMessageSlots_registerContext :
    (TCB.withMessageSlots ρ μ π t).registerContext = ρ t.registerContext := rfl
@[simp] theorem TCB.withMessageSlots_pendingMessage :
    (TCB.withMessageSlots ρ μ π t).pendingMessage = μ t.pendingMessage := rfl
@[simp] theorem TCB.withMessageSlots_pendingReceiveReply :
    (TCB.withMessageSlots ρ μ π t).pendingReceiveReply = π t.pendingReceiveReply := rfl
end

end SeLe4n.Model

namespace SeLe4n.Kernel

open SeLe4n.Model SeLe4n.Kernel.RobinHood SeLe4n.Kernel.Concurrency

section NoResize

/-! Every write the rendezvous makes keeps the object table's size and
capacity, so no resize falls due along the way. -/

theorem updateTcbAtCode_noResizeDue (st : SystemState) (k : Nat) (g : TCB → TCB) :
    (st.updateTcbAtCode k g).objects.noResizeDue ↔ st.objects.noResizeDue := by
  unfold SystemState.updateTcbAtCode
  split <;> exact Iff.rfl

theorem runAppendOnCore_noResizeDue (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) :
    (st.runAppendOnCore c t p).objects.noResizeDue ↔ st.objects.noResizeDue := by
  show (st.runAppendLinks c t p).objects.noResizeDue ↔ _
  unfold SystemState.runAppendLinks
  dsimp only
  rw [updateTcbAtCode_noResizeDue, updateTcbAtCode_noResizeDue]
  exact Iff.rfl

theorem runEnqueueAdmitted_noResizeDue (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) :
    (st.runEnqueueAdmitted c t p).objects.noResizeDue ↔ st.objects.noResizeDue := by
  unfold SystemState.runEnqueueAdmitted
  dsimp only
  split
  · exact Iff.rfl
  · exact runAppendOnCore_noResizeDue st c t p

theorem runUnlinkLinks_noResizeDue (st : SystemState) (t : SeLe4n.ThreadId) (pv nx bpv bnx : Nat) :
    (st.runUnlinkLinks t pv nx bpv bnx).objects.noResizeDue ↔ st.objects.noResizeDue := by
  unfold SystemState.runUnlinkLinks
  dsimp only
  show (SystemState.updateTcbAtCode _ bnx _).objects.noResizeDue ↔ _
  rw [updateTcbAtCode_noResizeDue, updateTcbAtCode_noResizeDue, updateTcbAtCode_noResizeDue,
    updateTcbAtCode_noResizeDue]

theorem runRemoveOnCore_noResizeDue (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId) :
    (st.runRemoveOnCore c t).objects.noResizeDue ↔ st.objects.noResizeDue := by
  unfold SystemState.runRemoveOnCore
  dsimp only
  split
  · exact runUnlinkLinks_noResizeDue st t _ _ _ _
  · exact Iff.rfl

theorem runRequeueOnCore_noResizeDue (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) :
    (st.runRequeueOnCore c t p).objects.noResizeDue ↔ st.objects.noResizeDue :=
  (runEnqueueAdmitted_noResizeDue _ c t p).trans (runRemoveOnCore_noResizeDue st c t)

theorem markKeyFlagsOver_objects (st : SystemState) (tid : SeLe4n.ThreadId) (rc : Nat) (w : Bool)
    (cs : List CoreId) : (markKeyFlagsOver st tid rc w cs).objects = st.objects := by
  induction cs generalizing st with
  | nil => rfl
  | cons c cs ih =>
    unfold markKeyFlagsOver
    rw [ih]
    split <;> rfl

theorem markKeyChangeParts_objects (st : SystemState) (tid : SeLe4n.ThreadId) (p0 : SeLe4n.Priority)
    (d0 : SeLe4n.Deadline) (dom0 : SeLe4n.DomainId) :
    (markKeyChangeParts st tid p0 d0 dom0).objects = st.objects := by
  unfold markKeyChangeParts
  split
  · dsimp only
    split
    · rfl
    · exact markKeyFlagsOver_objects _ _ _ _ _
  · rfl

theorem updatePipBoostOnCore_noResizeDue (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (hNo : st.objects.noResizeDue) :
    (PriorityInheritance.updatePipBoostOnCore st c tid).objects.noResizeDue := by
  rw [PriorityInheritance.updatePipBoostOnCore_eq_impl]
  unfold PriorityInheritance.updatePipBoostOnCoreImpl
  split
  · dsimp only
    split
    · exact hNo
    · rw [markKeyChangeParts_objects]
      have h1 : (st.updateTcb tid fun x =>
          { x with pipBoost := PriorityInheritance.computeMaxWaiterPriority st tid }).objects.noResizeDue := by
        rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNo]; exact hNo
      split
      · exact (runRequeueOnCore_noResizeDue _ c tid _).mpr h1
      · exact h1
  · exact hNo

theorem propagatePipChainStateWalk_noResizeDue (st : SystemState) (tid : SeLe4n.ThreadId)
    (fuel : Nat) (hNo : st.objects.noResizeDue) :
    (PriorityInheritance.propagatePipChainStateWalk st tid fuel).objects.noResizeDue := by
  induction fuel generalizing st tid with
  | zero => exact hNo
  | succ n ih =>
    unfold PriorityInheritance.propagatePipChainStateWalk
    split
    · exact ih _ _ (updatePipBoostOnCore_noResizeDue _ _ _ hNo)
    · exact updatePipBoostOnCore_noResizeDue _ _ _ hNo

end NoResize

section MessageSlots

variable (r : SeLe4n.ThreadId) (ρ : SeLe4n.RegisterFile → SeLe4n.RegisterFile)
  (μ : Option IpcMessage → Option IpcMessage) (π : Option SeLe4n.ReplyId → Option SeLe4n.ReplyId)

/-- The thread's read through the delivery: itself, or its message slots
rewritten. -/
theorem getTcb?_msg_cases (st : SystemState) (y : SeLe4n.ThreadId) :
    (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)).getTcb? y = st.getTcb? y ∨
      (r = y ∧ (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)).getTcb? y =
        (st.getTcb? y).map (TCB.withMessageSlots ρ μ π)) := by
  rw [SystemState.getTcb?_mapTcbInPlace]
  by_cases h : r = y
  · exact .inr ⟨h, by rw [if_pos h]⟩
  · exact .inl (by rw [if_neg h])

theorem runLinkOn_msg (st : SystemState) (c : CoreId) (y : SeLe4n.ThreadId) :
    (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)).runLinkOn c y = st.runLinkOn c y := by
  unfold SystemState.runLinkOn
  rcases getTcb?_msg_cases r ρ μ π st y with h | ⟨_, h⟩ <;> rw [h]
  cases st.getTcb? y <;> rfl

theorem queuedOn_msg (st : SystemState) (c : CoreId) (y : SeLe4n.ThreadId) :
    (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)).queuedOn c y = st.queuedOn c y := by
  unfold SystemState.queuedOn
  rcases getTcb?_msg_cases r ρ μ π st y with h | ⟨_, h⟩ <;> rw [h]
  cases st.getTcb? y <;> rfl

theorem runLinksAdmit_msg (st : SystemState) (c : CoreId) (y : SeLe4n.ThreadId) :
    (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)).runLinksAdmit c y = st.runLinksAdmit c y := by
  unfold SystemState.runLinksAdmit
  rcases getTcb?_msg_cases r ρ μ π st y with h | ⟨_, h⟩ <;> rw [h]
  cases st.getTcb? y <;> rfl

theorem runEnqueueAdmits_msg (st : SystemState) (c : CoreId) (y : SeLe4n.ThreadId) :
    (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)).runEnqueueAdmits c y =
      st.runEnqueueAdmits c y := by
  unfold SystemState.runEnqueueAdmits
  rw [runLinksAdmit_msg]

theorem runnableOnSomeCore_msg (st : SystemState) (y : SeLe4n.ThreadId) :
    runnableOnSomeCore (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)) y =
      runnableOnSomeCore st y := by
  unfold runnableOnSomeCore
  simp only [queuedOn_msg]

theorem wakeDeclines_msg (st : SystemState) (c : CoreId) (y : SeLe4n.ThreadId) :
    wakeDeclines (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)) c y = wakeDeclines st c y := by
  unfold wakeDeclines
  rw [runnableOnSomeCore_msg, runEnqueueAdmits_msg]

theorem determineTargetCore_msg (st : SystemState) (y : SeLe4n.ThreadId) :
    determineTargetCore (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)) y =
      determineTargetCore st y := by
  unfold determineTargetCore
  rcases getTcb?_msg_cases r ρ μ π st y with h | ⟨_, h⟩ <;> rw [h]
  cases st.getTcb? y <;> rfl

theorem runAppendLinks_msg (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) :
    (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)).runAppendLinks c t p =
      (st.runAppendLinks c t p).mapTcbInPlace r (TCB.withMessageSlots ρ μ π) := by
  unfold SystemState.runAppendLinks
  simp only [SystemState.mapTcbInPlace_scheduler]
  rw [SystemState.mapTcbInPlace_swap _ (TCB.withMessageSlots ρ μ π) _ ?_, SystemState.updateTcbAtCode_swap _ _ (TCB.withMessageSlots ρ μ π) _ ?_,
    SystemState.updateTcbAtCode_swap _ _ (TCB.withMessageSlots ρ μ π) _ ?_]
  all_goals intros; rfl

theorem runAppendOnCore_msg (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) :
    (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)).runAppendOnCore c t p =
      (st.runAppendOnCore c t p).mapTcbInPlace r (TCB.withMessageSlots ρ μ π) := by
  unfold SystemState.runAppendOnCore
  rw [runAppendLinks_msg]
  rfl

theorem runEnqueueAdmitted_msg (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) :
    (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)).runEnqueueAdmitted c t p =
      (st.runEnqueueAdmitted c t p).mapTcbInPlace r (TCB.withMessageSlots ρ μ π) := by
  unfold SystemState.runEnqueueAdmitted
  rw [runLinkOn_msg]
  split
  · rfl
  · rw [runAppendOnCore_msg]; rfl

/-- A slot write through `mapTcbObject` at a thread is its TCB write. -/
theorem modifyObject_tcb_msg (st : SystemState) (t : SeLe4n.ThreadId) (f : TCB → TCB)
    (hNo : st.objects.noResizeDue)
    (hc : t = r → ∀ x, f (TCB.withMessageSlots ρ μ π x) = TCB.withMessageSlots ρ μ π (f x)) :
    (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)).modifyObject t.toObjId
        (SystemState.mapTcbObject f) =
      (st.modifyObject t.toObjId (SystemState.mapTcbObject f)).mapTcbInPlace r
        (TCB.withMessageSlots ρ μ π) := by
  rw [SystemState.modifyObject_eq_mapValueAt _ _ _ hNo,
    SystemState.modifyObject_eq_mapValueAt (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)) _ _ hNo,
    SystemState.mapTcbObject_eq_mapTcb]
  exact SystemState.mapTcbInPlace_swap st _ f hc

theorem enqueueRunnableOnCore_msg (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (hNo : st.objects.noResizeDue) :
    enqueueRunnableOnCore (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)) c t =
      (enqueueRunnableOnCore st c t).mapTcbInPlace r (TCB.withMessageSlots ρ μ π) := by
  rw [enqueueRunnableOnCore_eq_impl]
  unfold enqueueRunnableOnCoreImpl
  rw [wakeDeclines_msg]
  have hBody : ∀ prio : SeLe4n.Priority,
      (if wakeDeclines st c t = true then st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)
       else
        let st' := ((st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)).modifyObject t.toObjId
          (SystemState.mapTcbObject fun x => { x with ipcState := .ready })).runEnqueueAdmitted c t prio
        { st' with scheduler := st'.scheduler.markReschedulePendingOnCore c }) =
      (if wakeDeclines st c t = true then st
       else
        let st' := (st.modifyObject t.toObjId
          (SystemState.mapTcbObject fun x => { x with ipcState := .ready })).runEnqueueAdmitted c t prio
        { st' with scheduler := st'.scheduler.markReschedulePendingOnCore c }).mapTcbInPlace r
          (TCB.withMessageSlots ρ μ π) := by
    intro prio
    split
    · rfl
    · dsimp only
      rw [modifyObject_tcb_msg r ρ μ π st t _ hNo ?_, runEnqueueAdmitted_msg]
      all_goals first | rfl | (intros; rfl)
  rcases getTcb?_msg_cases r ρ μ π st t with h | ⟨_, h⟩ <;> rw [h]
  · cases st.getTcb? t with
    | none => rfl
    | some tcb => exact hBody tcb.boostedPriority
  · cases st.getTcb? t with
    | none => rfl
    | some tcb => exact hBody tcb.boostedPriority

theorem runUnlinkLinks_msg (st : SystemState) (t : SeLe4n.ThreadId) (pv nx bpv bnx : Nat) :
    (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)).runUnlinkLinks t pv nx bpv bnx =
      (st.runUnlinkLinks t pv nx bpv bnx).mapTcbInPlace r (TCB.withMessageSlots ρ μ π) := by
  unfold SystemState.runUnlinkLinks
  dsimp only
  rw [SystemState.updateTcbAtCode_swap _ _ (TCB.withMessageSlots ρ μ π) _ ?_, SystemState.updateTcbAtCode_swap _ _ (TCB.withMessageSlots ρ μ π) _ ?_,
    SystemState.updateTcbAtCode_swap _ _ (TCB.withMessageSlots ρ μ π) _ ?_, SystemState.updateTcbAtCode_swap _ _ (TCB.withMessageSlots ρ μ π) _ ?_,
    SystemState.mapTcbInPlace_swap _ (TCB.withMessageSlots ρ μ π) _ ?_]
  all_goals intros; rfl

theorem runMaxCodeWalk_msg (st : SystemState) (c : CoreId) (n k acc : Nat) :
    (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)).runMaxCodeWalk c n k acc =
      st.runMaxCodeWalk c n k acc := by
  rw [SystemState.runMaxCodeWalk_eq, SystemState.runMaxCodeWalk_eq]
  congr 1
  funext y
  exact runLinkOn_msg r ρ μ π st c y

theorem runUnlinkMaxCode_msg (st : SystemState) (c : CoreId) (pv nx bpv bnx : Nat)
    (p : SeLe4n.Priority) :
    (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)).runUnlinkMaxCode c pv nx bpv bnx p =
      st.runUnlinkMaxCode c pv nx bpv bnx p := by
  unfold SystemState.runUnlinkMaxCode
  simp only [SystemState.mapTcbInPlace_scheduler, runMaxCodeWalk_msg]

theorem runRemoveOnCore_msg (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId) :
    (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)).runRemoveOnCore c t =
      (st.runRemoveOnCore c t).mapTcbInPlace r (TCB.withMessageSlots ρ μ π) := by
  unfold SystemState.runRemoveOnCore
  dsimp only
  rw [runLinkOn_msg]
  split
  · dsimp only
    rw [runUnlinkLinks_msg]
    simp only [SystemState.mapTcbInPlace_scheduler]
    have hw : (fun n h => RunQueue.maxPrioCodeWalkBy
        (((st.runUnlinkLinks t (st.runLinkOn c t).prev (st.runLinkOn c t).next
          (st.runLinkOn c t).bucketPrev (st.runLinkOn c t).bucketNext).mapTcbInPlace r
          (TCB.withMessageSlots ρ μ π)).runLinkOn c) n h 0) =
        (fun n h => RunQueue.maxPrioCodeWalkBy
        ((st.runUnlinkLinks t (st.runLinkOn c t).prev (st.runLinkOn c t).next
          (st.runLinkOn c t).bucketPrev (st.runLinkOn c t).bucketNext).runLinkOn c) n h 0) := by
      funext n h
      congr 1
      funext y
      exact runLinkOn_msg r ρ μ π _ c y
    rw [hw]
    rfl
  · rfl

theorem runDescheduleOnCore_msg (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId) :
    (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)).runDescheduleOnCore c t =
      (st.runDescheduleOnCore c t).mapTcbInPlace r (TCB.withMessageSlots ρ μ π) := by
  unfold SystemState.runDescheduleOnCore
  rw [runRemoveOnCore_msg]
  rfl

theorem removeRunnableOnCore_msg (st : SystemState) (t : SeLe4n.ThreadId) (c : CoreId) :
    removeRunnableOnCore (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)) t c =
      (removeRunnableOnCore st t c).mapTcbInPlace r (TCB.withMessageSlots ρ μ π) :=
  runDescheduleOnCore_msg r ρ μ π st c t

theorem runRequeueOnCore_msg (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) :
    (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)).runRequeueOnCore c t p =
      (st.runRequeueOnCore c t p).mapTcbInPlace r (TCB.withMessageSlots ρ μ π) := by
  unfold SystemState.runRequeueOnCore
  rw [runRemoveOnCore_msg, runEnqueueAdmitted_msg]
  rfl

theorem replyViews_msg (st : SystemState) :
    (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)).replyViews = st.replyViews := by
  rw [SystemState.replyViews_mapTcbInPlace st r (g := TCB.withMessageSlots ρ μ π) (gv := id)
    (fun _ => rfl)]
  funext k
  unfold ReplyViews.mapAt
  split
  · cases st.replyViews k <;> rfl
  · rfl

theorem linkReplyWaiter_msg (st : SystemState) (w s : SeLe4n.ThreadId) :
    (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)).linkReplyWaiter w s =
      (st.linkReplyWaiter w s).mapTcbInPlace r (TCB.withMessageSlots ρ μ π) := by
  unfold SystemState.linkReplyWaiter
  dsimp only
  rw [SystemState.replyHeadCode_eq, SystemState.replyHeadCode_eq, replyViews_msg]
  rw [SystemState.mapTcbInPlace_swap _ (TCB.withMessageSlots ρ μ π) _ ?_, SystemState.updateTcbAtCode_swap _ _ (TCB.withMessageSlots ρ μ π) _ ?_,
    SystemState.mapTcbInPlace_swap _ (TCB.withMessageSlots ρ μ π) _ ?_]
  all_goals intros; rfl

theorem unlinkReplyWaiter_msg (st : SystemState) (w s : SeLe4n.ThreadId) :
    (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)).unlinkReplyWaiter w s =
      (st.unlinkReplyWaiter w s).mapTcbInPlace r (TCB.withMessageSlots ρ μ π) := by
  unfold SystemState.unlinkReplyWaiter
  dsimp only
  rw [SystemState.replyPrevCode_eq, SystemState.replyPrevCode_eq, SystemState.replyNextCode_eq,
    SystemState.replyNextCode_eq, replyViews_msg]
  rw [SystemState.updateTcbAtCode_swap _ _ (TCB.withMessageSlots ρ μ π) _ ?_, SystemState.updateTcbAtCode_swap _ _ (TCB.withMessageSlots ρ μ π) _ ?_,
    SystemState.mapTcbInPlace_swap _ (TCB.withMessageSlots ρ μ π) _ ?_, SystemState.mapTcbInPlace_swap _ (TCB.withMessageSlots ρ μ π) _ ?_]
  all_goals intros; rfl

theorem effectiveSchedParams_msg (st : SystemState) (t : TCB) :
    effectiveSchedParams (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)) t =
      effectiveSchedParams st t := by
  unfold effectiveSchedParams
  simp only [SystemState.getSchedContext?_mapTcbInPlace]

theorem effectiveDeadline_msg (st : SystemState) (t : TCB) :
    effectiveDeadline (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)) t =
      effectiveDeadline st t := by
  unfold effectiveDeadline
  simp only [SystemState.getSchedContext?_mapTcbInPlace]

theorem computeMaxWaiterPriority_msg (st : SystemState) (tid : SeLe4n.ThreadId) :
    PriorityInheritance.computeMaxWaiterPriority
        (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)) tid =
      PriorityInheritance.computeMaxWaiterPriority st tid := by
  unfold PriorityInheritance.computeMaxWaiterPriority
  rw [PriorityInheritance.waitersOf_of_replyViews _ _ _ (replyViews_msg r ρ μ π st)]
  dsimp only
  congr 1
  funext acc w
  rcases getTcb?_msg_cases r ρ μ π st w with h | ⟨_, h⟩ <;> rw [h]
  · cases st.getTcb? w with
    | none => rfl
    | some t => simp only [effectiveSchedParams_msg]
  · cases st.getTcb? w with
    | none => rfl
    | some t =>
      simp only [Option.map_some, effectiveSchedParams_msg]
      rfl

theorem blockingServer_msg (st : SystemState) (tid : SeLe4n.ThreadId) :
    PriorityInheritance.blockingServer (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)) tid =
      PriorityInheritance.blockingServer st tid := by
  unfold PriorityInheritance.blockingServer
  rcases getTcb?_msg_cases r ρ μ π st tid with h | ⟨_, h⟩ <;> rw [h]
  cases st.getTcb? tid <;> rfl

theorem markKeyFlagsOver_msg (st : SystemState) (tid : SeLe4n.ThreadId) (rc : Nat) (w : Bool)
    (cs : List CoreId) :
    markKeyFlagsOver (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)) tid rc w cs =
      (markKeyFlagsOver st tid rc w cs).mapTcbInPlace r (TCB.withMessageSlots ρ μ π) := by
  induction cs generalizing st with
  | nil => rfl
  | cons c cs ih =>
    unfold markKeyFlagsOver
    simp only [SystemState.mapTcbInPlace_scheduler]
    split
    · exact ih (st.markReschedulePendingOnCore c)
    · exact ih st

theorem markKeyChangeParts_msg (st : SystemState) (tid : SeLe4n.ThreadId) (p0 : SeLe4n.Priority)
    (d0 : SeLe4n.Deadline) (dom0 : SeLe4n.DomainId) :
    markKeyChangeParts (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)) tid p0 d0 dom0 =
      (markKeyChangeParts st tid p0 d0 dom0).mapTcbInPlace r (TCB.withMessageSlots ρ μ π) := by
  unfold markKeyChangeParts
  have hBody : ∀ t : TCB,
      (if (p0 == t.boostedPriority && d0.val == (effectiveDeadline st t).val &&
            dom0 == t.domain) = true then st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)
       else markKeyFlagsOver (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)) tid t.runCoreCode
          (decide (t.boostedPriority.val < p0.val) || decide (d0.val < (effectiveDeadline st t).val) ||
            dom0 != t.domain) allCores) =
      (if (p0 == t.boostedPriority && d0.val == (effectiveDeadline st t).val &&
            dom0 == t.domain) = true then st
       else markKeyFlagsOver st tid t.runCoreCode
          (decide (t.boostedPriority.val < p0.val) || decide (d0.val < (effectiveDeadline st t).val) ||
            dom0 != t.domain) allCores).mapTcbInPlace r (TCB.withMessageSlots ρ μ π) := by
    intro t
    split
    · rfl
    · exact markKeyFlagsOver_msg r ρ μ π st _ _ _ _
  rcases getTcb?_msg_cases r ρ μ π st tid with h | ⟨_, h⟩ <;> rw [h]
  · cases st.getTcb? tid with
    | none => rfl
    | some t => simp only [effectiveDeadline_msg]; exact hBody t
  · cases st.getTcb? tid with
    | none => rfl
    | some t => simp only [Option.map_some, effectiveDeadline_msg]; exact hBody t

theorem effectiveDeadline_withMessageSlots (st : SystemState) (t : TCB) :
    effectiveDeadline st (TCB.withMessageSlots ρ μ π t) = effectiveDeadline st t := rfl

/-- A TCB update at a thread commutes with the delivery when it is at another
thread or leaves the message slots alone. -/
theorem updateTcb_msg (st : SystemState) (x : SeLe4n.ThreadId) (f : TCB → TCB)
    (hNo : st.objects.noResizeDue)
    (hc : x = r → ∀ t, f (TCB.withMessageSlots ρ μ π t) = TCB.withMessageSlots ρ μ π (f t)) :
    (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)).updateTcb x f =
      (st.updateTcb x f).mapTcbInPlace r (TCB.withMessageSlots ρ μ π) := by
  rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNo,
    SystemState.updateTcb_eq_mapTcbInPlace (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)) _ _ hNo]
  exact SystemState.mapTcbInPlace_swap st _ f hc

theorem updatePipBoostOnCore_msg (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (hNo : st.objects.noResizeDue) :
    PriorityInheritance.updatePipBoostOnCore (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)) c tid =
      (PriorityInheritance.updatePipBoostOnCore st c tid).mapTcbInPlace r
        (TCB.withMessageSlots ρ μ π) := by
  rw [PriorityInheritance.updatePipBoostOnCore_eq_impl]
  unfold PriorityInheritance.updatePipBoostOnCoreImpl
  rw [computeMaxWaiterPriority_msg]
  have hBody : ∀ tcb : TCB,
      (if (tcb.pipBoost == PriorityInheritance.computeMaxWaiterPriority st tid) = true then
          st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)
       else
        markKeyChangeParts
          (if (tcb.runCoreCode == c.val + 1 && tcb.boostedPriority !=
                tcb.priority.raisedBy (PriorityInheritance.computeMaxWaiterPriority st tid)) = true then
            ((st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)).updateTcb tid fun x =>
              { x with pipBoost := PriorityInheritance.computeMaxWaiterPriority st tid }).runRequeueOnCore
              c tid (tcb.priority.raisedBy (PriorityInheritance.computeMaxWaiterPriority st tid))
          else (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)).updateTcb tid fun x =>
              { x with pipBoost := PriorityInheritance.computeMaxWaiterPriority st tid })
          tid tcb.boostedPriority (effectiveDeadline st tcb) tcb.domain) =
      (if (tcb.pipBoost == PriorityInheritance.computeMaxWaiterPriority st tid) = true then st
       else
        markKeyChangeParts
          (if (tcb.runCoreCode == c.val + 1 && tcb.boostedPriority !=
                tcb.priority.raisedBy (PriorityInheritance.computeMaxWaiterPriority st tid)) = true then
            (st.updateTcb tid fun x =>
              { x with pipBoost := PriorityInheritance.computeMaxWaiterPriority st tid }).runRequeueOnCore
              c tid (tcb.priority.raisedBy (PriorityInheritance.computeMaxWaiterPriority st tid))
          else st.updateTcb tid fun x =>
              { x with pipBoost := PriorityInheritance.computeMaxWaiterPriority st tid })
          tid tcb.boostedPriority (effectiveDeadline st tcb) tcb.domain).mapTcbInPlace r
        (TCB.withMessageSlots ρ μ π) := by
    intro tcb
    split
    · rfl
    · rw [updateTcb_msg r ρ μ π st tid _ hNo ?_]
      · split
        · rw [runRequeueOnCore_msg, markKeyChangeParts_msg]
        · rw [markKeyChangeParts_msg]
      · intros; rfl
  rcases getTcb?_msg_cases r ρ μ π st tid with h | ⟨_, h⟩ <;> rw [h]
  · cases st.getTcb? tid with
    | none => rfl
    | some tcb => dsimp only; rw [effectiveDeadline_msg]; exact hBody tcb
  · cases st.getTcb? tid with
    | none => rfl
    | some tcb =>
      simp only [Option.map_some, TCB.withMessageSlots_pipBoost, TCB.withMessageSlots_boostedPriority,
        TCB.withMessageSlots_domain, TCB.withMessageSlots_runCoreCode, TCB.withMessageSlots_priority,
        effectiveDeadline_withMessageSlots, effectiveDeadline_msg]
      exact hBody tcb

theorem propagatePipChainStateWalk_msg (st : SystemState) (tid : SeLe4n.ThreadId) (fuel : Nat)
    (hNo : st.objects.noResizeDue) :
    PriorityInheritance.propagatePipChainStateWalk
        (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)) tid fuel =
      (PriorityInheritance.propagatePipChainStateWalk st tid fuel).mapTcbInPlace r
        (TCB.withMessageSlots ρ μ π) := by
  induction fuel generalizing st tid with
  | zero => rfl
  | succ n ih =>
    unfold PriorityInheritance.propagatePipChainStateWalk
    rw [blockingServer_msg, determineTargetCore_msg, updatePipBoostOnCore_msg r ρ μ π st _ _ hNo]
    split
    · exact ih _ _ (updatePipBoostOnCore_noResizeDue _ _ _ hNo)
    · rfl

/-- **The priority walk commutes with the delivery.** -/
theorem propagatePipChainCrossCore_msg (st : SystemState) (tid : SeLe4n.ThreadId) (ec : CoreId)
    (hNo : st.objects.noResizeDue) :
    (PriorityInheritance.propagatePipChainCrossCore
        (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)) tid ec).1 =
      (PriorityInheritance.propagatePipChainCrossCore st tid ec).1.mapTcbInPlace r
        (TCB.withMessageSlots ρ μ π) := by
  rw [PriorityInheritance.propagatePipChainCrossCore_eq_walks,
    PriorityInheritance.propagatePipChainCrossCore_eq_walks]
  exact propagatePipChainStateWalk_msg r ρ μ π st tid _ hNo

end MessageSlots

end SeLe4n.Kernel
