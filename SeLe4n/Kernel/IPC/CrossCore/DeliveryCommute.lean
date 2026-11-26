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

The commutations are stated once, over the **answer slots** — the message
slots and the fault kind (`TCB.withAnswerSlots`), which a fault restart also
writes — and the message-slot write is their instance at a kept fault kind
(`TCB.withMessageSlots_eq_answerSlots`, WS-SX SX30).
-/

namespace SeLe4n.Model

/-- A TCB rewritten in its message slots alone: its saved registers, its
pending message and its stashed receive reply. -/
@[inline] def TCB.withMessageSlots (ρ : SeLe4n.RegisterFile → SeLe4n.RegisterFile)
    (μ : Option IpcMessage → Option IpcMessage)
    (π : Nat → Nat) (t : TCB) : TCB :=
  { t with registerContext := ρ t.registerContext, pendingMessage := μ t.pendingMessage,
           pendingReceiveReplyCode := π t.pendingReceiveReplyCode }

section
variable (ρ : SeLe4n.RegisterFile → SeLe4n.RegisterFile) (μ : Option IpcMessage → Option IpcMessage)
  (π : Nat → Nat) (t : TCB)
@[simp] theorem TCB.withMessageSlots_pipBoost : (TCB.withMessageSlots ρ μ π t).pipBoost = t.pipBoost := rfl
@[simp] theorem TCB.withMessageSlots_pipBoostCode :
    (TCB.withMessageSlots ρ μ π t).pipBoostCode = t.pipBoostCode := rfl
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
@[simp] theorem TCB.withMessageSlots_pendingReceiveReplyCode :
    (TCB.withMessageSlots ρ μ π t).pendingReceiveReplyCode = π t.pendingReceiveReplyCode := rfl
end

/-- A TCB rewritten in its answer slots alone: its saved registers, its
pending message, its stashed receive reply and its fault kind.  Proof-only:
no transition runs it, so it is compiled nowhere. -/
noncomputable def TCB.withAnswerSlots (ρ : SeLe4n.RegisterFile → SeLe4n.RegisterFile)
    (μ : Option IpcMessage → Option IpcMessage) (π : Nat → Nat) (κ : Nat → Nat) (t : TCB) : TCB :=
  { t with registerContext := ρ t.registerContext, pendingMessage := μ t.pendingMessage,
           pendingReceiveReplyCode := π t.pendingReceiveReplyCode, faultKind := κ t.faultKind }

section
variable (ρ : SeLe4n.RegisterFile → SeLe4n.RegisterFile) (μ : Option IpcMessage → Option IpcMessage)
  (π : Nat → Nat) (κ : Nat → Nat) (t : TCB)
@[simp] theorem TCB.withAnswerSlots_pipBoost : (TCB.withAnswerSlots ρ μ π κ t).pipBoost = t.pipBoost := rfl
@[simp] theorem TCB.withAnswerSlots_pipBoostCode :
    (TCB.withAnswerSlots ρ μ π κ t).pipBoostCode = t.pipBoostCode := rfl
@[simp] theorem TCB.withAnswerSlots_priority : (TCB.withAnswerSlots ρ μ π κ t).priority = t.priority := rfl
@[simp] theorem TCB.withAnswerSlots_boostedPriority :
    (TCB.withAnswerSlots ρ μ π κ t).boostedPriority = t.boostedPriority := rfl
@[simp] theorem TCB.withAnswerSlots_domain : (TCB.withAnswerSlots ρ μ π κ t).domain = t.domain := rfl
@[simp] theorem TCB.withAnswerSlots_runCoreCode :
    (TCB.withAnswerSlots ρ μ π κ t).runCoreCode = t.runCoreCode := rfl
@[simp] theorem TCB.withAnswerSlots_ipcState : (TCB.withAnswerSlots ρ μ π κ t).ipcState = t.ipcState := rfl
@[simp] theorem TCB.withAnswerSlots_registerContext :
    (TCB.withAnswerSlots ρ μ π κ t).registerContext = ρ t.registerContext := rfl
@[simp] theorem TCB.withAnswerSlots_pendingMessage :
    (TCB.withAnswerSlots ρ μ π κ t).pendingMessage = μ t.pendingMessage := rfl
@[simp] theorem TCB.withAnswerSlots_pendingReceiveReplyCode :
    (TCB.withAnswerSlots ρ μ π κ t).pendingReceiveReplyCode = π t.pendingReceiveReplyCode := rfl
@[simp] theorem TCB.withAnswerSlots_faultKind :
    (TCB.withAnswerSlots ρ μ π κ t).faultKind = κ t.faultKind := rfl
end

/-- The delivery's message-slot write is the answer-slot write that keeps the
fault kind, which is how every message-slot commutation below is stated. -/
theorem TCB.withMessageSlots_eq_answerSlots (ρ : SeLe4n.RegisterFile → SeLe4n.RegisterFile)
    (μ : Option IpcMessage → Option IpcMessage) (π : Nat → Nat) :
    TCB.withMessageSlots ρ μ π = TCB.withAnswerSlots ρ μ π id := rfl

/-- The delivered frame is an answer-slot write: the registers staged and the
message dropped. -/
theorem TCB.withDeliveredFrame_eq_answerSlots (f : SeLe4n.Kernel.Architecture.SyscallReturnFrame) :
    (fun t : TCB => t.withDeliveredFrame f) =
      TCB.withAnswerSlots (fun rf => rf.stageDeliveredWords f.x0 f.x1 f.x2 f.x3 f.x4 f.x5)
        (fun _ => none) id id := rfl

/-- The restart is an answer-slot write: the restart frame staged and the
fault kind cleared. -/
theorem TCB.restartAnswer_eq_answerSlots (f : SeLe4n.Kernel.Architecture.FaultRestartFrame) :
    (fun t : TCB => (t.withRestartFrame f).setPendingFault none) =
      TCB.withAnswerSlots (fun rf => rf.stageRestartFrame f) id id (fun _ => 0) := rfl

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
          { x with pipBoostCode := PriorityInheritance.computeMaxWaiterCode st tid }).objects.noResizeDue := by
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

section AnswerSlots

variable (r : SeLe4n.ThreadId) (ρ : SeLe4n.RegisterFile → SeLe4n.RegisterFile)
  (μ : Option IpcMessage → Option IpcMessage) (π : Nat → Nat) (κ : Nat → Nat)

/-- The thread's read through the delivery: itself, or its message slots
rewritten. -/
theorem getTcb?_answer_cases (st : SystemState) (y : SeLe4n.ThreadId) :
    (st.mapTcbInPlace r (TCB.withAnswerSlots ρ μ π κ)).getTcb? y = st.getTcb? y ∨
      (r = y ∧ (st.mapTcbInPlace r (TCB.withAnswerSlots ρ μ π κ)).getTcb? y =
        (st.getTcb? y).map (TCB.withAnswerSlots ρ μ π κ)) := by
  rw [SystemState.getTcb?_mapTcbInPlace]
  by_cases h : r = y
  · exact .inr ⟨h, by rw [if_pos h]⟩
  · exact .inl (by rw [if_neg h])

theorem runLinkOn_answer (st : SystemState) (c : CoreId) (y : SeLe4n.ThreadId) :
    (st.mapTcbInPlace r (TCB.withAnswerSlots ρ μ π κ)).runLinkOn c y = st.runLinkOn c y := by
  unfold SystemState.runLinkOn
  rcases getTcb?_answer_cases r ρ μ π κ st y with h | ⟨_, h⟩ <;> rw [h]
  cases st.getTcb? y <;> rfl

theorem queuedOn_answer (st : SystemState) (c : CoreId) (y : SeLe4n.ThreadId) :
    (st.mapTcbInPlace r (TCB.withAnswerSlots ρ μ π κ)).queuedOn c y = st.queuedOn c y := by
  unfold SystemState.queuedOn
  rcases getTcb?_answer_cases r ρ μ π κ st y with h | ⟨_, h⟩ <;> rw [h]
  cases st.getTcb? y <;> rfl

theorem runLinksAdmit_answer (st : SystemState) (c : CoreId) (y : SeLe4n.ThreadId) :
    (st.mapTcbInPlace r (TCB.withAnswerSlots ρ μ π κ)).runLinksAdmit c y = st.runLinksAdmit c y := by
  unfold SystemState.runLinksAdmit
  rcases getTcb?_answer_cases r ρ μ π κ st y with h | ⟨_, h⟩ <;> rw [h]
  cases st.getTcb? y <;> rfl

theorem runEnqueueAdmits_answer (st : SystemState) (c : CoreId) (y : SeLe4n.ThreadId) :
    (st.mapTcbInPlace r (TCB.withAnswerSlots ρ μ π κ)).runEnqueueAdmits c y =
      st.runEnqueueAdmits c y := by
  unfold SystemState.runEnqueueAdmits
  rw [runLinksAdmit_answer]

theorem runnableOnSomeCore_answer (st : SystemState) (y : SeLe4n.ThreadId) :
    runnableOnSomeCore (st.mapTcbInPlace r (TCB.withAnswerSlots ρ μ π κ)) y =
      runnableOnSomeCore st y := by
  unfold runnableOnSomeCore
  simp only [queuedOn_answer]

theorem wakeDeclines_answer (st : SystemState) (c : CoreId) (y : SeLe4n.ThreadId) :
    wakeDeclines (st.mapTcbInPlace r (TCB.withAnswerSlots ρ μ π κ)) c y = wakeDeclines st c y := by
  unfold wakeDeclines
  rw [runnableOnSomeCore_answer, runEnqueueAdmits_answer]

theorem determineTargetCore_answer (st : SystemState) (y : SeLe4n.ThreadId) :
    determineTargetCore (st.mapTcbInPlace r (TCB.withAnswerSlots ρ μ π κ)) y =
      determineTargetCore st y := by
  unfold determineTargetCore
  rcases getTcb?_answer_cases r ρ μ π κ st y with h | ⟨_, h⟩ <;> rw [h]
  cases st.getTcb? y <;> rfl

theorem runAppendLinks_answer (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) :
    (st.mapTcbInPlace r (TCB.withAnswerSlots ρ μ π κ)).runAppendLinks c t p =
      (st.runAppendLinks c t p).mapTcbInPlace r (TCB.withAnswerSlots ρ μ π κ) := by
  unfold SystemState.runAppendLinks
  simp only [SystemState.mapTcbInPlace_scheduler]
  rw [SystemState.mapTcbInPlace_swap _ (TCB.withAnswerSlots ρ μ π κ) _ ?_, SystemState.updateTcbAtCode_swap _ _ (TCB.withAnswerSlots ρ μ π κ) _ ?_,
    SystemState.updateTcbAtCode_swap _ _ (TCB.withAnswerSlots ρ μ π κ) _ ?_]
  all_goals intros; rfl

theorem runAppendOnCore_answer (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) :
    (st.mapTcbInPlace r (TCB.withAnswerSlots ρ μ π κ)).runAppendOnCore c t p =
      (st.runAppendOnCore c t p).mapTcbInPlace r (TCB.withAnswerSlots ρ μ π κ) := by
  unfold SystemState.runAppendOnCore
  rw [runAppendLinks_answer]
  rfl

theorem runEnqueueAdmitted_answer (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) :
    (st.mapTcbInPlace r (TCB.withAnswerSlots ρ μ π κ)).runEnqueueAdmitted c t p =
      (st.runEnqueueAdmitted c t p).mapTcbInPlace r (TCB.withAnswerSlots ρ μ π κ) := by
  unfold SystemState.runEnqueueAdmitted
  rw [runLinkOn_answer]
  split
  · rfl
  · rw [runAppendOnCore_answer]; rfl

/-- A slot write through `mapTcbObject` at a thread is its TCB write. -/
theorem modifyObject_tcb_answer (st : SystemState) (t : SeLe4n.ThreadId) (f : TCB → TCB)
    (hNo : st.objects.noResizeDue)
    (hc : t = r → ∀ x, f (TCB.withAnswerSlots ρ μ π κ x) = TCB.withAnswerSlots ρ μ π κ (f x)) :
    (st.mapTcbInPlace r (TCB.withAnswerSlots ρ μ π κ)).modifyObject t.toObjId
        (SystemState.mapTcbObject f) =
      (st.modifyObject t.toObjId (SystemState.mapTcbObject f)).mapTcbInPlace r
        (TCB.withAnswerSlots ρ μ π κ) := by
  rw [SystemState.modifyObject_eq_mapValueAt _ _ _ hNo,
    SystemState.modifyObject_eq_mapValueAt (st.mapTcbInPlace r (TCB.withAnswerSlots ρ μ π κ)) _ _ hNo,
    SystemState.mapTcbObject_eq_mapTcb]
  exact SystemState.mapTcbInPlace_swap st _ f hc

theorem enqueueRunnableOnCore_answer (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (hNo : st.objects.noResizeDue) :
    enqueueRunnableOnCore (st.mapTcbInPlace r (TCB.withAnswerSlots ρ μ π κ)) c t =
      (enqueueRunnableOnCore st c t).mapTcbInPlace r (TCB.withAnswerSlots ρ μ π κ) := by
  rw [enqueueRunnableOnCore_eq_impl]
  unfold enqueueRunnableOnCoreImpl
  rw [wakeDeclines_answer]
  have hBody : ∀ prio : SeLe4n.Priority,
      (if wakeDeclines st c t = true then st.mapTcbInPlace r (TCB.withAnswerSlots ρ μ π κ)
       else
        let st' := ((st.mapTcbInPlace r (TCB.withAnswerSlots ρ μ π κ)).modifyObject t.toObjId
          (SystemState.mapTcbObject fun x => (x.setIpcState .ready))).runEnqueueAdmitted c t prio
        { st' with scheduler := st'.scheduler.markReschedulePendingOnCore c }) =
      (if wakeDeclines st c t = true then st
       else
        let st' := (st.modifyObject t.toObjId
          (SystemState.mapTcbObject fun x => (x.setIpcState .ready))).runEnqueueAdmitted c t prio
        { st' with scheduler := st'.scheduler.markReschedulePendingOnCore c }).mapTcbInPlace r
          (TCB.withAnswerSlots ρ μ π κ) := by
    intro prio
    split
    · rfl
    · dsimp only
      rw [modifyObject_tcb_answer r ρ μ π κ st t _ hNo ?_, runEnqueueAdmitted_answer]
      all_goals first | rfl | (intros; rfl)
  rcases getTcb?_answer_cases r ρ μ π κ st t with h | ⟨_, h⟩ <;> rw [h]
  · cases st.getTcb? t with
    | none => rfl
    | some tcb => exact hBody tcb.boostedPriority
  · cases st.getTcb? t with
    | none => rfl
    | some tcb => exact hBody tcb.boostedPriority

theorem runUnlinkLinks_answer (st : SystemState) (t : SeLe4n.ThreadId) (pv nx bpv bnx : Nat) :
    (st.mapTcbInPlace r (TCB.withAnswerSlots ρ μ π κ)).runUnlinkLinks t pv nx bpv bnx =
      (st.runUnlinkLinks t pv nx bpv bnx).mapTcbInPlace r (TCB.withAnswerSlots ρ μ π κ) := by
  unfold SystemState.runUnlinkLinks
  dsimp only
  rw [SystemState.updateTcbAtCode_swap _ _ (TCB.withAnswerSlots ρ μ π κ) _ ?_, SystemState.updateTcbAtCode_swap _ _ (TCB.withAnswerSlots ρ μ π κ) _ ?_,
    SystemState.updateTcbAtCode_swap _ _ (TCB.withAnswerSlots ρ μ π κ) _ ?_, SystemState.updateTcbAtCode_swap _ _ (TCB.withAnswerSlots ρ μ π κ) _ ?_,
    SystemState.mapTcbInPlace_swap _ (TCB.withAnswerSlots ρ μ π κ) _ ?_]
  all_goals intros; rfl

theorem runMaxCodeWalk_answer (st : SystemState) (c : CoreId) (n k acc : Nat) :
    (st.mapTcbInPlace r (TCB.withAnswerSlots ρ μ π κ)).runMaxCodeWalk c n k acc =
      st.runMaxCodeWalk c n k acc := by
  rw [SystemState.runMaxCodeWalk_eq, SystemState.runMaxCodeWalk_eq]
  congr 1
  funext y
  exact runLinkOn_answer r ρ μ π κ st c y

theorem runUnlinkMaxCode_answer (st : SystemState) (c : CoreId) (pv nx bpv bnx : Nat)
    (p : SeLe4n.Priority) :
    (st.mapTcbInPlace r (TCB.withAnswerSlots ρ μ π κ)).runUnlinkMaxCode c pv nx bpv bnx p =
      st.runUnlinkMaxCode c pv nx bpv bnx p := by
  unfold SystemState.runUnlinkMaxCode
  simp only [SystemState.mapTcbInPlace_scheduler, runMaxCodeWalk_answer]

theorem runRemoveOnCore_answer (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId) :
    (st.mapTcbInPlace r (TCB.withAnswerSlots ρ μ π κ)).runRemoveOnCore c t =
      (st.runRemoveOnCore c t).mapTcbInPlace r (TCB.withAnswerSlots ρ μ π κ) := by
  unfold SystemState.runRemoveOnCore
  dsimp only
  rw [runLinkOn_answer]
  split
  · dsimp only
    rw [runUnlinkLinks_answer]
    simp only [SystemState.mapTcbInPlace_scheduler]
    have hw : (fun n h => RunQueue.maxPrioCodeWalkBy
        (((st.runUnlinkLinks t (st.runLinkOn c t).prev (st.runLinkOn c t).next
          (st.runLinkOn c t).bucketPrev (st.runLinkOn c t).bucketNext).mapTcbInPlace r
          (TCB.withAnswerSlots ρ μ π κ)).runLinkOn c) n h 0) =
        (fun n h => RunQueue.maxPrioCodeWalkBy
        ((st.runUnlinkLinks t (st.runLinkOn c t).prev (st.runLinkOn c t).next
          (st.runLinkOn c t).bucketPrev (st.runLinkOn c t).bucketNext).runLinkOn c) n h 0) := by
      funext n h
      congr 1
      funext y
      exact runLinkOn_answer r ρ μ π κ _ c y
    rw [hw]
    rfl
  · rfl

theorem runDescheduleOnCore_answer (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId) :
    (st.mapTcbInPlace r (TCB.withAnswerSlots ρ μ π κ)).runDescheduleOnCore c t =
      (st.runDescheduleOnCore c t).mapTcbInPlace r (TCB.withAnswerSlots ρ μ π κ) := by
  unfold SystemState.runDescheduleOnCore
  rw [runRemoveOnCore_answer]
  rfl

theorem removeRunnableOnCore_answer (st : SystemState) (t : SeLe4n.ThreadId) (c : CoreId) :
    removeRunnableOnCore (st.mapTcbInPlace r (TCB.withAnswerSlots ρ μ π κ)) t c =
      (removeRunnableOnCore st t c).mapTcbInPlace r (TCB.withAnswerSlots ρ μ π κ) :=
  runDescheduleOnCore_answer r ρ μ π κ st c t

theorem runRequeueOnCore_answer (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) :
    (st.mapTcbInPlace r (TCB.withAnswerSlots ρ μ π κ)).runRequeueOnCore c t p =
      (st.runRequeueOnCore c t p).mapTcbInPlace r (TCB.withAnswerSlots ρ μ π κ) := by
  unfold SystemState.runRequeueOnCore
  rw [runRemoveOnCore_answer, runEnqueueAdmitted_answer]
  rfl

theorem replyViews_answer (st : SystemState) :
    (st.mapTcbInPlace r (TCB.withAnswerSlots ρ μ π κ)).replyViews = st.replyViews := by
  rw [SystemState.replyViews_mapTcbInPlace st r (g := TCB.withAnswerSlots ρ μ π κ) (gv := id)
    (fun _ => rfl)]
  funext k
  unfold ReplyViews.mapAt
  split
  · cases st.replyViews k <;> rfl
  · rfl

theorem linkReplyWaiter_answer (st : SystemState) (w s : SeLe4n.ThreadId) :
    (st.mapTcbInPlace r (TCB.withAnswerSlots ρ μ π κ)).linkReplyWaiter w s =
      (st.linkReplyWaiter w s).mapTcbInPlace r (TCB.withAnswerSlots ρ μ π κ) := by
  unfold SystemState.linkReplyWaiter
  dsimp only
  rw [SystemState.replyHeadCode_eq, SystemState.replyHeadCode_eq, replyViews_answer]
  rw [SystemState.mapTcbInPlace_swap _ (TCB.withAnswerSlots ρ μ π κ) _ ?_, SystemState.updateTcbAtCode_swap _ _ (TCB.withAnswerSlots ρ μ π κ) _ ?_,
    SystemState.mapTcbInPlace_swap _ (TCB.withAnswerSlots ρ μ π κ) _ ?_]
  all_goals intros; rfl

theorem unlinkReplyWaiter_answer (st : SystemState) (w s : SeLe4n.ThreadId) :
    (st.mapTcbInPlace r (TCB.withAnswerSlots ρ μ π κ)).unlinkReplyWaiter w s =
      (st.unlinkReplyWaiter w s).mapTcbInPlace r (TCB.withAnswerSlots ρ μ π κ) := by
  unfold SystemState.unlinkReplyWaiter
  dsimp only
  rw [SystemState.replyPrevCode_eq, SystemState.replyPrevCode_eq, SystemState.replyNextCode_eq,
    SystemState.replyNextCode_eq, replyViews_answer]
  rw [SystemState.updateTcbAtCode_swap _ _ (TCB.withAnswerSlots ρ μ π κ) _ ?_, SystemState.updateTcbAtCode_swap _ _ (TCB.withAnswerSlots ρ μ π κ) _ ?_,
    SystemState.mapTcbInPlace_swap _ (TCB.withAnswerSlots ρ μ π κ) _ ?_, SystemState.mapTcbInPlace_swap _ (TCB.withAnswerSlots ρ μ π κ) _ ?_]
  all_goals intros; rfl

theorem effectiveSchedParams_answer (st : SystemState) (t : TCB) :
    effectiveSchedParams (st.mapTcbInPlace r (TCB.withAnswerSlots ρ μ π κ)) t =
      effectiveSchedParams st t := by
  unfold effectiveSchedParams
  simp only [SystemState.getSchedContext?_mapTcbInPlace]

theorem computeMaxWaiterPriority_answer (st : SystemState) (tid : SeLe4n.ThreadId) :
    PriorityInheritance.computeMaxWaiterPriority
        (st.mapTcbInPlace r (TCB.withAnswerSlots ρ μ π κ)) tid =
      PriorityInheritance.computeMaxWaiterPriority st tid := by
  unfold PriorityInheritance.computeMaxWaiterPriority
  rw [PriorityInheritance.waitersOf_of_replyViews _ _ _ (replyViews_answer r ρ μ π κ st)]
  dsimp only
  congr 1
  funext acc w
  rcases getTcb?_answer_cases r ρ μ π κ st w with h | ⟨_, h⟩ <;> rw [h]
  · cases st.getTcb? w with
    | none => rfl
    | some t => simp only [effectiveSchedParams_answer]
  · cases st.getTcb? w with
    | none => rfl
    | some t =>
      simp only [Option.map_some, effectiveSchedParams_answer]
      rfl

theorem blockingServer_answer (st : SystemState) (tid : SeLe4n.ThreadId) :
    PriorityInheritance.blockingServer (st.mapTcbInPlace r (TCB.withAnswerSlots ρ μ π κ)) tid =
      PriorityInheritance.blockingServer st tid := by
  unfold PriorityInheritance.blockingServer
  rcases getTcb?_answer_cases r ρ μ π κ st tid with h | ⟨_, h⟩ <;> rw [h]
  cases st.getTcb? tid <;> rfl

theorem markKeyFlagsOver_answer (st : SystemState) (tid : SeLe4n.ThreadId) (rc : Nat) (w : Bool)
    (cs : List CoreId) :
    markKeyFlagsOver (st.mapTcbInPlace r (TCB.withAnswerSlots ρ μ π κ)) tid rc w cs =
      (markKeyFlagsOver st tid rc w cs).mapTcbInPlace r (TCB.withAnswerSlots ρ μ π κ) := by
  induction cs generalizing st with
  | nil => rfl
  | cons c cs ih =>
    unfold markKeyFlagsOver
    simp only [SystemState.mapTcbInPlace_scheduler]
    split
    · exact ih (st.markReschedulePendingOnCore c)
    · exact ih st

theorem markKeyChangeParts_answer (st : SystemState) (tid : SeLe4n.ThreadId) (p0 : SeLe4n.Priority)
    (d0 : SeLe4n.Deadline) (dom0 : SeLe4n.DomainId) :
    markKeyChangeParts (st.mapTcbInPlace r (TCB.withAnswerSlots ρ μ π κ)) tid p0 d0 dom0 =
      (markKeyChangeParts st tid p0 d0 dom0).mapTcbInPlace r (TCB.withAnswerSlots ρ μ π κ) := by
  unfold markKeyChangeParts
  have hBody : ∀ t : TCB,
      (if (p0 == t.boostedPriority && d0.val == (t.deadline).val &&
            dom0 == t.domain) = true then st.mapTcbInPlace r (TCB.withAnswerSlots ρ μ π κ)
       else markKeyFlagsOver (st.mapTcbInPlace r (TCB.withAnswerSlots ρ μ π κ)) tid t.runCoreCode
          (decide (t.boostedPriority.val < p0.val) || decide (d0.val < (t.deadline).val) ||
            dom0 != t.domain) allCores) =
      (if (p0 == t.boostedPriority && d0.val == (t.deadline).val &&
            dom0 == t.domain) = true then st
       else markKeyFlagsOver st tid t.runCoreCode
          (decide (t.boostedPriority.val < p0.val) || decide (d0.val < (t.deadline).val) ||
            dom0 != t.domain) allCores).mapTcbInPlace r (TCB.withAnswerSlots ρ μ π κ) := by
    intro t
    split
    · rfl
    · exact markKeyFlagsOver_answer r ρ μ π κ st _ _ _ _
  rcases getTcb?_answer_cases r ρ μ π κ st tid with h | ⟨_, h⟩ <;> rw [h]
  · cases st.getTcb? tid with
    | none => rfl
    | some t => exact hBody t
  · cases st.getTcb? tid with
    | none => rfl
    | some t => simp only [Option.map_some]; exact hBody t

theorem deadline_withAnswerSlots (t : TCB) :
    (TCB.withAnswerSlots ρ μ π κ t).deadline = t.deadline := rfl

/-- A TCB update at a thread commutes with the delivery when it is at another
thread or leaves the message slots alone. -/
theorem updateTcb_answer (st : SystemState) (x : SeLe4n.ThreadId) (f : TCB → TCB)
    (hNo : st.objects.noResizeDue)
    (hc : x = r → ∀ t, f (TCB.withAnswerSlots ρ μ π κ t) = TCB.withAnswerSlots ρ μ π κ (f t)) :
    (st.mapTcbInPlace r (TCB.withAnswerSlots ρ μ π κ)).updateTcb x f =
      (st.updateTcb x f).mapTcbInPlace r (TCB.withAnswerSlots ρ μ π κ) := by
  rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNo,
    SystemState.updateTcb_eq_mapTcbInPlace (st.mapTcbInPlace r (TCB.withAnswerSlots ρ μ π κ)) _ _ hNo]
  exact SystemState.mapTcbInPlace_swap st _ f hc

theorem updatePipBoostOnCore_answer (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (hNo : st.objects.noResizeDue) :
    PriorityInheritance.updatePipBoostOnCore (st.mapTcbInPlace r (TCB.withAnswerSlots ρ μ π κ)) c tid =
      (PriorityInheritance.updatePipBoostOnCore st c tid).mapTcbInPlace r
        (TCB.withAnswerSlots ρ μ π κ) := by
  rw [PriorityInheritance.updatePipBoostOnCore_eq_impl]
  unfold PriorityInheritance.updatePipBoostOnCoreImpl
  rw [← PriorityInheritance.optCode_computeMaxWaiterPriority, computeMaxWaiterPriority_answer,
    ← PriorityInheritance.optCode_computeMaxWaiterPriority]
  simp only [SeLe4n.Priority.ofOptCode_optCode]
  have hBody : ∀ tcb : TCB,
      (if (tcb.pipBoostCode == SeLe4n.Priority.optCode (PriorityInheritance.computeMaxWaiterPriority st tid)) = true then
          st.mapTcbInPlace r (TCB.withAnswerSlots ρ μ π κ)
       else
        markKeyChangeParts
          (if (tcb.runCoreCode == c.val + 1 && tcb.boostedPriority !=
                tcb.priority.raisedBy (PriorityInheritance.computeMaxWaiterPriority st tid)) = true then
            ((st.mapTcbInPlace r (TCB.withAnswerSlots ρ μ π κ)).updateTcb tid fun x =>
              { x with pipBoostCode := SeLe4n.Priority.optCode (PriorityInheritance.computeMaxWaiterPriority st tid) }).runRequeueOnCore
              c tid (tcb.priority.raisedBy (PriorityInheritance.computeMaxWaiterPriority st tid))
          else (st.mapTcbInPlace r (TCB.withAnswerSlots ρ μ π κ)).updateTcb tid fun x =>
              { x with pipBoostCode := SeLe4n.Priority.optCode (PriorityInheritance.computeMaxWaiterPriority st tid) })
          tid tcb.boostedPriority (tcb.deadline) tcb.domain) =
      (if (tcb.pipBoostCode == SeLe4n.Priority.optCode (PriorityInheritance.computeMaxWaiterPriority st tid)) = true then st
       else
        markKeyChangeParts
          (if (tcb.runCoreCode == c.val + 1 && tcb.boostedPriority !=
                tcb.priority.raisedBy (PriorityInheritance.computeMaxWaiterPriority st tid)) = true then
            (st.updateTcb tid fun x =>
              { x with pipBoostCode := SeLe4n.Priority.optCode (PriorityInheritance.computeMaxWaiterPriority st tid) }).runRequeueOnCore
              c tid (tcb.priority.raisedBy (PriorityInheritance.computeMaxWaiterPriority st tid))
          else st.updateTcb tid fun x =>
              { x with pipBoostCode := SeLe4n.Priority.optCode (PriorityInheritance.computeMaxWaiterPriority st tid) })
          tid tcb.boostedPriority (tcb.deadline) tcb.domain).mapTcbInPlace r
        (TCB.withAnswerSlots ρ μ π κ) := by
    intro tcb
    split
    · rfl
    · rw [updateTcb_answer r ρ μ π κ st tid _ hNo ?_]
      · split
        · rw [runRequeueOnCore_answer, markKeyChangeParts_answer]
        · rw [markKeyChangeParts_answer]
      · intros; rfl
  rcases getTcb?_answer_cases r ρ μ π κ st tid with h | ⟨_, h⟩ <;> rw [h]
  · cases st.getTcb? tid with
    | none => rfl
    | some tcb => dsimp only; exact hBody tcb
  · cases st.getTcb? tid with
    | none => rfl
    | some tcb =>
      simp only [Option.map_some, TCB.withAnswerSlots_pipBoostCode, TCB.withAnswerSlots_boostedPriority,
        TCB.withAnswerSlots_domain, TCB.withAnswerSlots_runCoreCode, TCB.withAnswerSlots_priority,
        deadline_withAnswerSlots]
      exact hBody tcb

theorem propagatePipChainStateWalk_answer (st : SystemState) (tid : SeLe4n.ThreadId) (fuel : Nat)
    (hNo : st.objects.noResizeDue) :
    PriorityInheritance.propagatePipChainStateWalk
        (st.mapTcbInPlace r (TCB.withAnswerSlots ρ μ π κ)) tid fuel =
      (PriorityInheritance.propagatePipChainStateWalk st tid fuel).mapTcbInPlace r
        (TCB.withAnswerSlots ρ μ π κ) := by
  induction fuel generalizing st tid with
  | zero => rfl
  | succ n ih =>
    unfold PriorityInheritance.propagatePipChainStateWalk
    rw [blockingServer_answer, determineTargetCore_answer, updatePipBoostOnCore_answer r ρ μ π κ st _ _ hNo]
    split
    · exact ih _ _ (updatePipBoostOnCore_noResizeDue _ _ _ hNo)
    · rfl

/-- **The priority walk commutes with the delivery.** -/
theorem propagatePipChainCrossCore_answer (st : SystemState) (tid : SeLe4n.ThreadId) (ec : CoreId)
    (hNo : st.objects.noResizeDue) :
    (PriorityInheritance.propagatePipChainCrossCore
        (st.mapTcbInPlace r (TCB.withAnswerSlots ρ μ π κ)) tid ec).1 =
      (PriorityInheritance.propagatePipChainCrossCore st tid ec).1.mapTcbInPlace r
        (TCB.withAnswerSlots ρ μ π κ) := by
  rw [PriorityInheritance.propagatePipChainCrossCore_eq_walks,
    PriorityInheritance.propagatePipChainCrossCore_eq_walks]
  exact propagatePipChainStateWalk_answer r ρ μ π κ st tid _ hNo

end AnswerSlots

/-! ## The message-slot write

Each commutation of the delivery's message-slot write is the answer-slot
commutation above at a kept fault kind (`TCB.withMessageSlots_eq_answerSlots`). -/

section MessageSlots

variable (r : SeLe4n.ThreadId) (ρ : SeLe4n.RegisterFile → SeLe4n.RegisterFile)
  (μ : Option IpcMessage → Option IpcMessage) (π : Nat → Nat)

/-- The thread's read through the delivery: itself, or its message slots
rewritten. -/
theorem getTcb?_msg_cases (st : SystemState) (y : SeLe4n.ThreadId) :
    (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)).getTcb? y = st.getTcb? y ∨
      (r = y ∧ (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)).getTcb? y =
        (st.getTcb? y).map (TCB.withMessageSlots ρ μ π)) := by
  rw [TCB.withMessageSlots_eq_answerSlots] at *
  apply getTcb?_answer_cases <;> assumption

theorem runLinkOn_msg (st : SystemState) (c : CoreId) (y : SeLe4n.ThreadId) :
    (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)).runLinkOn c y = st.runLinkOn c y := by
  rw [TCB.withMessageSlots_eq_answerSlots] at *
  apply runLinkOn_answer <;> assumption

theorem queuedOn_msg (st : SystemState) (c : CoreId) (y : SeLe4n.ThreadId) :
    (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)).queuedOn c y = st.queuedOn c y := by
  rw [TCB.withMessageSlots_eq_answerSlots] at *
  apply queuedOn_answer <;> assumption

theorem runLinksAdmit_msg (st : SystemState) (c : CoreId) (y : SeLe4n.ThreadId) :
    (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)).runLinksAdmit c y = st.runLinksAdmit c y := by
  rw [TCB.withMessageSlots_eq_answerSlots] at *
  apply runLinksAdmit_answer <;> assumption

theorem runEnqueueAdmits_msg (st : SystemState) (c : CoreId) (y : SeLe4n.ThreadId) :
    (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)).runEnqueueAdmits c y =
      st.runEnqueueAdmits c y := by
  rw [TCB.withMessageSlots_eq_answerSlots] at *
  apply runEnqueueAdmits_answer <;> assumption

theorem runnableOnSomeCore_msg (st : SystemState) (y : SeLe4n.ThreadId) :
    runnableOnSomeCore (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)) y =
      runnableOnSomeCore st y := by
  rw [TCB.withMessageSlots_eq_answerSlots] at *
  apply runnableOnSomeCore_answer <;> assumption

theorem wakeDeclines_msg (st : SystemState) (c : CoreId) (y : SeLe4n.ThreadId) :
    wakeDeclines (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)) c y = wakeDeclines st c y := by
  rw [TCB.withMessageSlots_eq_answerSlots] at *
  apply wakeDeclines_answer <;> assumption

theorem determineTargetCore_msg (st : SystemState) (y : SeLe4n.ThreadId) :
    determineTargetCore (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)) y =
      determineTargetCore st y := by
  rw [TCB.withMessageSlots_eq_answerSlots] at *
  apply determineTargetCore_answer <;> assumption

theorem runAppendLinks_msg (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) :
    (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)).runAppendLinks c t p =
      (st.runAppendLinks c t p).mapTcbInPlace r (TCB.withMessageSlots ρ μ π) := by
  rw [TCB.withMessageSlots_eq_answerSlots] at *
  apply runAppendLinks_answer <;> assumption

theorem runAppendOnCore_msg (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) :
    (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)).runAppendOnCore c t p =
      (st.runAppendOnCore c t p).mapTcbInPlace r (TCB.withMessageSlots ρ μ π) := by
  rw [TCB.withMessageSlots_eq_answerSlots] at *
  apply runAppendOnCore_answer <;> assumption

theorem runEnqueueAdmitted_msg (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) :
    (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)).runEnqueueAdmitted c t p =
      (st.runEnqueueAdmitted c t p).mapTcbInPlace r (TCB.withMessageSlots ρ μ π) := by
  rw [TCB.withMessageSlots_eq_answerSlots] at *
  apply runEnqueueAdmitted_answer <;> assumption

/-- A slot write through `mapTcbObject` at a thread is its TCB write. -/
theorem modifyObject_tcb_msg (st : SystemState) (t : SeLe4n.ThreadId) (f : TCB → TCB)
    (hNo : st.objects.noResizeDue)
    (hc : t = r → ∀ x, f (TCB.withMessageSlots ρ μ π x) = TCB.withMessageSlots ρ μ π (f x)) :
    (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)).modifyObject t.toObjId
        (SystemState.mapTcbObject f) =
      (st.modifyObject t.toObjId (SystemState.mapTcbObject f)).mapTcbInPlace r
        (TCB.withMessageSlots ρ μ π) := by
  rw [TCB.withMessageSlots_eq_answerSlots] at *
  apply modifyObject_tcb_answer <;> assumption

theorem enqueueRunnableOnCore_msg (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (hNo : st.objects.noResizeDue) :
    enqueueRunnableOnCore (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)) c t =
      (enqueueRunnableOnCore st c t).mapTcbInPlace r (TCB.withMessageSlots ρ μ π) := by
  rw [TCB.withMessageSlots_eq_answerSlots] at *
  apply enqueueRunnableOnCore_answer <;> assumption

theorem runUnlinkLinks_msg (st : SystemState) (t : SeLe4n.ThreadId) (pv nx bpv bnx : Nat) :
    (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)).runUnlinkLinks t pv nx bpv bnx =
      (st.runUnlinkLinks t pv nx bpv bnx).mapTcbInPlace r (TCB.withMessageSlots ρ μ π) := by
  rw [TCB.withMessageSlots_eq_answerSlots] at *
  apply runUnlinkLinks_answer <;> assumption

theorem runMaxCodeWalk_msg (st : SystemState) (c : CoreId) (n k acc : Nat) :
    (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)).runMaxCodeWalk c n k acc =
      st.runMaxCodeWalk c n k acc := by
  rw [TCB.withMessageSlots_eq_answerSlots] at *
  apply runMaxCodeWalk_answer <;> assumption

theorem runUnlinkMaxCode_msg (st : SystemState) (c : CoreId) (pv nx bpv bnx : Nat)
    (p : SeLe4n.Priority) :
    (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)).runUnlinkMaxCode c pv nx bpv bnx p =
      st.runUnlinkMaxCode c pv nx bpv bnx p := by
  rw [TCB.withMessageSlots_eq_answerSlots] at *
  apply runUnlinkMaxCode_answer <;> assumption

theorem runRemoveOnCore_msg (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId) :
    (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)).runRemoveOnCore c t =
      (st.runRemoveOnCore c t).mapTcbInPlace r (TCB.withMessageSlots ρ μ π) := by
  rw [TCB.withMessageSlots_eq_answerSlots] at *
  apply runRemoveOnCore_answer <;> assumption

theorem runDescheduleOnCore_msg (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId) :
    (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)).runDescheduleOnCore c t =
      (st.runDescheduleOnCore c t).mapTcbInPlace r (TCB.withMessageSlots ρ μ π) := by
  rw [TCB.withMessageSlots_eq_answerSlots] at *
  apply runDescheduleOnCore_answer <;> assumption

theorem removeRunnableOnCore_msg (st : SystemState) (t : SeLe4n.ThreadId) (c : CoreId) :
    removeRunnableOnCore (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)) t c =
      (removeRunnableOnCore st t c).mapTcbInPlace r (TCB.withMessageSlots ρ μ π) := by
  rw [TCB.withMessageSlots_eq_answerSlots] at *
  apply removeRunnableOnCore_answer <;> assumption

theorem runRequeueOnCore_msg (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) :
    (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)).runRequeueOnCore c t p =
      (st.runRequeueOnCore c t p).mapTcbInPlace r (TCB.withMessageSlots ρ μ π) := by
  rw [TCB.withMessageSlots_eq_answerSlots] at *
  apply runRequeueOnCore_answer <;> assumption

theorem replyViews_msg (st : SystemState) :
    (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)).replyViews = st.replyViews := by
  rw [TCB.withMessageSlots_eq_answerSlots] at *
  apply replyViews_answer <;> assumption

theorem linkReplyWaiter_msg (st : SystemState) (w s : SeLe4n.ThreadId) :
    (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)).linkReplyWaiter w s =
      (st.linkReplyWaiter w s).mapTcbInPlace r (TCB.withMessageSlots ρ μ π) := by
  rw [TCB.withMessageSlots_eq_answerSlots] at *
  apply linkReplyWaiter_answer <;> assumption

theorem unlinkReplyWaiter_msg (st : SystemState) (w s : SeLe4n.ThreadId) :
    (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)).unlinkReplyWaiter w s =
      (st.unlinkReplyWaiter w s).mapTcbInPlace r (TCB.withMessageSlots ρ μ π) := by
  rw [TCB.withMessageSlots_eq_answerSlots] at *
  apply unlinkReplyWaiter_answer <;> assumption

theorem effectiveSchedParams_msg (st : SystemState) (t : TCB) :
    effectiveSchedParams (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)) t =
      effectiveSchedParams st t := by
  rw [TCB.withMessageSlots_eq_answerSlots] at *
  apply effectiveSchedParams_answer <;> assumption

theorem computeMaxWaiterPriority_msg (st : SystemState) (tid : SeLe4n.ThreadId) :
    PriorityInheritance.computeMaxWaiterPriority
        (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)) tid =
      PriorityInheritance.computeMaxWaiterPriority st tid := by
  rw [TCB.withMessageSlots_eq_answerSlots] at *
  apply computeMaxWaiterPriority_answer <;> assumption

theorem blockingServer_msg (st : SystemState) (tid : SeLe4n.ThreadId) :
    PriorityInheritance.blockingServer (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)) tid =
      PriorityInheritance.blockingServer st tid := by
  rw [TCB.withMessageSlots_eq_answerSlots] at *
  apply blockingServer_answer <;> assumption

theorem markKeyFlagsOver_msg (st : SystemState) (tid : SeLe4n.ThreadId) (rc : Nat) (w : Bool)
    (cs : List CoreId) :
    markKeyFlagsOver (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)) tid rc w cs =
      (markKeyFlagsOver st tid rc w cs).mapTcbInPlace r (TCB.withMessageSlots ρ μ π) := by
  rw [TCB.withMessageSlots_eq_answerSlots] at *
  apply markKeyFlagsOver_answer <;> assumption

theorem markKeyChangeParts_msg (st : SystemState) (tid : SeLe4n.ThreadId) (p0 : SeLe4n.Priority)
    (d0 : SeLe4n.Deadline) (dom0 : SeLe4n.DomainId) :
    markKeyChangeParts (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)) tid p0 d0 dom0 =
      (markKeyChangeParts st tid p0 d0 dom0).mapTcbInPlace r (TCB.withMessageSlots ρ μ π) := by
  rw [TCB.withMessageSlots_eq_answerSlots] at *
  apply markKeyChangeParts_answer <;> assumption

theorem deadline_withMessageSlots (st : SystemState) (t : TCB) :
    (TCB.withMessageSlots ρ μ π t).deadline = t.deadline := rfl

/-- A TCB update at a thread commutes with the delivery when it is at another
thread or leaves the message slots alone. -/
theorem updateTcb_msg (st : SystemState) (x : SeLe4n.ThreadId) (f : TCB → TCB)
    (hNo : st.objects.noResizeDue)
    (hc : x = r → ∀ t, f (TCB.withMessageSlots ρ μ π t) = TCB.withMessageSlots ρ μ π (f t)) :
    (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)).updateTcb x f =
      (st.updateTcb x f).mapTcbInPlace r (TCB.withMessageSlots ρ μ π) := by
  rw [TCB.withMessageSlots_eq_answerSlots] at *
  apply updateTcb_answer <;> assumption

theorem updatePipBoostOnCore_msg (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (hNo : st.objects.noResizeDue) :
    PriorityInheritance.updatePipBoostOnCore (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)) c tid =
      (PriorityInheritance.updatePipBoostOnCore st c tid).mapTcbInPlace r
        (TCB.withMessageSlots ρ μ π) := by
  rw [TCB.withMessageSlots_eq_answerSlots] at *
  apply updatePipBoostOnCore_answer <;> assumption

theorem propagatePipChainStateWalk_msg (st : SystemState) (tid : SeLe4n.ThreadId) (fuel : Nat)
    (hNo : st.objects.noResizeDue) :
    PriorityInheritance.propagatePipChainStateWalk
        (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)) tid fuel =
      (PriorityInheritance.propagatePipChainStateWalk st tid fuel).mapTcbInPlace r
        (TCB.withMessageSlots ρ μ π) := by
  rw [TCB.withMessageSlots_eq_answerSlots] at *
  apply propagatePipChainStateWalk_answer <;> assumption

/-- **The priority walk commutes with the delivery.** -/
theorem propagatePipChainCrossCore_msg (st : SystemState) (tid : SeLe4n.ThreadId) (ec : CoreId)
    (hNo : st.objects.noResizeDue) :
    (PriorityInheritance.propagatePipChainCrossCore
        (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)) tid ec).1 =
      (PriorityInheritance.propagatePipChainCrossCore st tid ec).1.mapTcbInPlace r
        (TCB.withMessageSlots ρ μ π) := by
  rw [TCB.withMessageSlots_eq_answerSlots] at *
  apply propagatePipChainCrossCore_answer <;> assumption

end MessageSlots

end SeLe4n.Kernel
