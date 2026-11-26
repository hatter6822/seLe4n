/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.IPC.CrossCore.TransferCommute

/-!
# The answer to a caller commutes with the receive side's writes

WS-SX SX30.  A `.replyRecv` answers the caller it replies to
(`replyRecvAnswerCaller`): on an ordinary reply the delivered message is
staged into the caller's saved registers (`stageDeliveredMessage`), and on a
faulted caller the fault is answered — a restart frame installed with the
fault record cleared (`applyFaultRestart`), or the thread abandoned.  seL4's
`doReplyTransfer` writes that answer before `handleRecv` runs; the
specification writes it last.

Both the message stage and the restart write one thread's **answer slots** —
its saved registers, its pending message, its stashed receive reply and its
fault kind (`TCB.withAnswerSlots`) — and nothing the run queue, the
reply-waiter queues or the priority walk reads or writes.  On an object table
with no resize due every write those make is a slot write
(`TcbWriteCommute`), so the answer commutes with each of them: written first or
written last, the state is the same.  The delivery's message-slot write
(`TCB.withMessageSlots`, `DeliveryCommute`) is the instance that keeps the
fault kind (`TCB.withMessageSlots_eq_answerSlots`).

The stage also records the message's overflow words on the physical-write
ledger, so each step is shown to commute with a recording too (`_ledger`):
every step here leaves the ledger alone.  The receive side's own capability
transfer records the badges it unwraps, so where both record, the two orders
leave the ledger's entries in different orders; the answer-first equality
carries that as a premise.
-/

namespace SeLe4n.Model

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
fault kind. -/
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

/-! ## Stores

The receive side's stores write objects already there, so on a table with no
resize due each is a slot write and commutes with any thread write at another
key, or at the same key when the two writes commute. -/

section Stores

variable {G : TCB → TCB} (x : SeLe4n.ThreadId)

/-- An insert at a present key commutes with a slot write at another key. -/

theorem RHTable.insert_mapValueAt_comm_ne {α β : Type} [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (x k : α) (F : β → β) (v obj : β) (hNo : t.noResizeDue)
    (hk : t.get? k = some v) (hx : x ≠ k) :
    (t.mapValueAt x F).insert k obj = (t.insert k obj).mapValueAt x F := by
  have hk' : (t.mapValueAt x F).get? k = some v := by
    rw [RHTable.get?_mapValueAt, hk]
    have : (x == k) = false := by simp [hx]
    rw [this]; rfl
  rw [RHTable.insert_eq_mapValueAt _ (RHTable.findsInPlace_of_get? hNo hk),
    RHTable.insert_eq_mapValueAt _
      (RHTable.findsInPlace_of_get? ((RHTable.noResizeDue_mapValueAt t x F).mpr hNo) hk')]
  exact (RHTable.mapValueAt_comm _ _ _ hx).symm

/-- A store at a present key other than the thread's, which keeps the index
and the kinds, commutes with the thread write. -/

theorem storeObject_mapTcbInPlace_ne (Z : SystemState) (k : SeLe4n.ObjId) (o0 o : KernelObject)
    (hk : Z.objects[k]? = some o0) (hne : k ≠ x.toObjId) (hNo : Z.objects.noResizeDue)
    (hL : storeLeavesIndexAndTypes Z k o.objectType = true) :
    storeObject k o (Z.mapTcbInPlace x G) =
      .ok ((), ({ Z with objects := Z.objects.insert k o } : SystemState).mapTcbInPlace x G) := by
  have hk' : (Z.mapTcbInPlace x G).objects[k]? = some o0 := by
    rw [SystemState.objects_mapTcbInPlace, hk]
    have : (x.toObjId == k) = false := by simp [Ne.symm hne]
    rw [this]; rfl
  have hL' : storeLeavesIndexAndTypes (Z.mapTcbInPlace x G) k o.objectType = true := by
    unfold storeLeavesIndexAndTypes storeKeepsKind at hL ⊢; rw [hk']; rw [hk] at hL; exact hL
  have hg : Z.objects.get? k = some o0 := by
    simpa only [RHTable_getElem?_eq_get?] using hk
  rw [storeObject_eq_of_leaves hL']
  unfold SystemState.mapTcbInPlace
  simp only [Except.ok.injEq, Prod.mk.injEq, true_and]
  rw [RHTable.insert_mapValueAt_comm_ne _ _ _ _ _ _ hNo hg (Ne.symm hne)]

/-- A thread that is there is stored over in its kind. -/

theorem storeLeavesIndexAndTypes_tcb_of_getTcb? {Z : SystemState} {t : SeLe4n.ThreadId} {tcb : TCB}
    (h : Z.getTcb? t = some tcb) : storeLeavesIndexAndTypes Z t.toObjId .tcb = true := by
  unfold storeLeavesIndexAndTypes storeKeepsKind
  rw [(SystemState.getTcb?_eq_some_iff _ _ _).mp h]; rfl

/-- A TCB update at a thread commutes with the thread write when it is at
another thread or commutes with it there. -/

theorem modifyTcb_mapTcbInPlace (Z : SystemState) (t : SeLe4n.ThreadId) (f : TCB → TCB)
    (hNo : Z.objects.noResizeDue) (hc : t = x → ∀ y, f (G y) = G (f y)) :
    modifyTcb (Z.mapTcbInPlace x G) t f = (modifyTcb Z t f).map (·.mapTcbInPlace x G) := by
  by_cases hR : t.isReserved = true
  · unfold modifyTcb lookupTcb; simp only [hR, ↓reduceIte]; rfl
  · have hR' : t.isReserved = false := by simpa using hR
    have hGet := SystemState.getTcb?_mapTcbInPlace Z x G t
    cases hT : Z.getTcb? t with
    | none =>
      have hT' : (Z.mapTcbInPlace x G).getTcb? t = none := by rw [hGet, hT]; split <;> rfl
      unfold modifyTcb lookupTcb; simp only [hR', hT, hT', Bool.false_eq_true, ↓reduceIte]; rfl
    | some tcb =>
      have hT' : (Z.mapTcbInPlace x G).getTcb? t = some (if x = t then G tcb else tcb) := by
        rw [hGet, hT]; split <;> rfl
      rw [modifyTcb_eq_updateTcb f hR' hT (storeLeavesIndexAndTypes_tcb_of_getTcb? hT),
        modifyTcb_eq_updateTcb f hR' hT' (storeLeavesIndexAndTypes_tcb_of_getTcb? hT')]
      show Except.ok _ = Except.ok _
      rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNo,
        SystemState.updateTcb_eq_mapTcbInPlace (Z.mapTcbInPlace x G) _ _ hNo]
      exact congrArg Except.ok (SystemState.mapTcbInPlace_swap Z G f hc)

/-- A store of a non-thread object at a present key, which keeps the index and
the kinds, commutes with the thread write wherever it is. -/
theorem storeObject_mapTcbInPlace_of_fixed (Z : SystemState) (k : SeLe4n.ObjId) (o0 o : KernelObject)
    (hk : Z.objects[k]? = some o0) (hNo : Z.objects.noResizeDue)
    (hFix : KernelObject.mapTcb G o = o) (hFix0 : KernelObject.mapTcb G o0 = o0)
    (hL : storeLeavesIndexAndTypes Z k o.objectType = true) :
    storeObject k o (Z.mapTcbInPlace x G) =
      .ok ((), ({ Z with objects := Z.objects.insert k o } : SystemState).mapTcbInPlace x G) := by
  have hk' : (Z.mapTcbInPlace x G).objects[k]? = some o0 := by
    rw [SystemState.objects_mapTcbInPlace, hk]; split <;> simp [hFix0]
  have hL' : storeLeavesIndexAndTypes (Z.mapTcbInPlace x G) k o.objectType = true := by
    unfold storeLeavesIndexAndTypes storeKeepsKind at hL ⊢; rw [hk']; rw [hk] at hL; exact hL
  have hg : Z.objects.get? k = some o0 := by
    simpa only [RHTable_getElem?_eq_get?] using hk
  rw [storeObject_eq_of_leaves hL']
  unfold SystemState.mapTcbInPlace
  simp only [Except.ok.injEq, Prod.mk.injEq, true_and]
  rw [SeLe4n.Kernel.RHTable.insert_mapValueAt_comm _ _ _ _ _ _ hNo hg hFix]

end Stores

/-! ## The pop

A receive pops its endpoint queue's head.  The answered thread may sit behind
the head, whose successor link the pop rewrites; the answer leaves queue links
alone, so the two commute whenever the head is not the answered thread. -/

section Pop

variable (r : SeLe4n.ThreadId) (ρ : SeLe4n.RegisterFile → SeLe4n.RegisterFile)
  (μ : Option IpcMessage → Option IpcMessage) (π : Nat → Nat) (κ : Nat → Nat)

theorem lookupTcb_answer_ne (Z : SystemState) (t : SeLe4n.ThreadId) (h : t ≠ r) :
    lookupTcb (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ π κ)) t = lookupTcb Z t := by
  unfold lookupTcb
  rw [SystemState.getTcb?_mapTcbInPlace, if_neg (Ne.symm h)]

theorem lookupTcb_answer (Z : SystemState) (t : SeLe4n.ThreadId) :
    lookupTcb (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ π κ)) t =
      if r = t then (lookupTcb Z t).map (TCB.withAnswerSlots ρ μ π κ) else lookupTcb Z t := by
  unfold lookupTcb
  rw [SystemState.getTcb?_mapTcbInPlace]
  split <;> split <;> rfl

theorem storeTcbQueueLinks_answer (Z : SystemState) (t : SeLe4n.ThreadId) (p : Option SeLe4n.ThreadId)
    (pp : Option QueuePPrev) (n : Option SeLe4n.ThreadId) (hNo : Z.objects.noResizeDue) :
    storeTcbQueueLinks (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ π κ)) t p pp n =
      (storeTcbQueueLinks Z t p pp n).map (·.mapTcbInPlace r (TCB.withAnswerSlots ρ μ π κ)) := by
  unfold storeTcbQueueLinks
  exact modifyTcb_mapTcbInPlace r Z t _ hNo (fun _ _ => rfl)

theorem getObject?_answer_endpoint (Z : SystemState) (k : SeLe4n.ObjId) (ep : Endpoint)
    (h : Z.getObject? k = some (.endpoint ep)) :
    (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ π κ)).getObject? k = some (.endpoint ep) := by
  unfold SystemState.getObject? at h ⊢
  rw [SystemState.objects_mapTcbInPlace, h]; split <;> rfl

theorem insert_present_noResizeDue (Z : SystemState) (k : SeLe4n.ObjId) (o0 o : KernelObject)
    (hk : Z.objects[k]? = some o0) (hNo : Z.objects.noResizeDue) :
    ({ Z with objects := Z.objects.insert k o } : SystemState).objects.noResizeDue := by
  have hg : Z.objects.get? k = some o0 := by simpa only [RHTable_getElem?_eq_get?] using hk
  show (Z.objects.insert k o).noResizeDue
  rw [RHTable.insert_eq_mapValueAt _ (RHTable.findsInPlace_of_get? hNo hg)]
  exact (RHTable.noResizeDue_mapValueAt _ _ _).mpr hNo

theorem modifyTcb_noResizeDue (Z Z' : SystemState) (t : SeLe4n.ThreadId) (f : TCB → TCB)
    (hNo : Z.objects.noResizeDue) (h : modifyTcb Z t f = .ok Z') : Z'.objects.noResizeDue := by
  by_cases hR : t.isReserved = true
  · unfold modifyTcb lookupTcb at h; simp only [hR, ↓reduceIte] at h; cases h
  · have hR' : t.isReserved = false := by simpa using hR
    cases hT : Z.getTcb? t with
    | none => unfold modifyTcb lookupTcb at h; simp only [hR', hT, Bool.false_eq_true, ↓reduceIte] at h; cases h
    | some tcb =>
      rw [modifyTcb_eq_updateTcb f hR' hT (storeLeavesIndexAndTypes_tcb_of_getTcb? hT)] at h
      cases h
      exact updateTcb_noResizeDue _ _ _ hNo

/-- The pop's tail, after the endpoint store: the successor's links, then the
head's. -/

theorem popTail_answer (st1 : SystemState) (tid : SeLe4n.ThreadId) (headTcb : TCB) (htid : tid ≠ r)
    (hNo : st1.objects.noResizeDue) :
    (match (match headTcb.queueNext with
      | none => Except.ok (st1.mapTcbInPlace r (TCB.withAnswerSlots ρ μ π κ))
      | some nextTid =>
          match lookupTcb (st1.mapTcbInPlace r (TCB.withAnswerSlots ρ μ π κ)) nextTid with
          | none => Except.error KernelError.objectNotFound
          | some nextTcb => storeTcbQueueLinks (st1.mapTcbInPlace r (TCB.withAnswerSlots ρ μ π κ))
              nextTid none (some .endpointHead) nextTcb.queueNext) with
     | .error e => Except.error e
     | .ok st2 =>
        match storeTcbQueueLinks st2 tid none none none with
        | .error e => Except.error e
        | .ok st3 => Except.ok (tid, headTcb, st3)) =
    (match (match (match headTcb.queueNext with
      | none => Except.ok st1
      | some nextTid =>
          match lookupTcb st1 nextTid with
          | none => Except.error KernelError.objectNotFound
          | some nextTcb => storeTcbQueueLinks st1 nextTid none (some .endpointHead) nextTcb.queueNext) with
     | .error e => Except.error e
     | .ok st2 =>
        match storeTcbQueueLinks st2 tid none none none with
        | .error e => Except.error e
        | .ok st3 => Except.ok (tid, headTcb, st3)) with
     | .ok (t, tcb, Z') => Except.ok (t, tcb, Z'.mapTcbInPlace r (TCB.withAnswerSlots ρ μ π κ))
     | .error e => Except.error e) := by
  have hTail : ∀ st2 : SystemState, st2.objects.noResizeDue →
      (match storeTcbQueueLinks (st2.mapTcbInPlace r (TCB.withAnswerSlots ρ μ π κ)) tid none none none with
        | .error e => Except.error e
        | .ok st3 => Except.ok (tid, headTcb, st3)) =
      (match (match storeTcbQueueLinks st2 tid none none none with
        | .error e => Except.error e
        | .ok st3 => Except.ok (tid, headTcb, st3)) with
       | .ok (t, tcb, Z') => Except.ok (t, tcb, Z'.mapTcbInPlace r (TCB.withAnswerSlots ρ μ π κ))
       | .error e => Except.error e) := by
    intro st2 hNo2
    rw [storeTcbQueueLinks_answer r ρ μ π κ st2 tid none none none hNo2]
    cases storeTcbQueueLinks st2 tid none none none <;> rfl
  cases hN : headTcb.queueNext with
  | none => exact hTail st1 hNo
  | some n =>
    dsimp only
    rw [lookupTcb_answer]
    cases hL : lookupTcb st1 n with
    | none => simp only [Option.map_none, ite_self]
    | some nT =>
      have hQ : ∀ y : TCB, (if r = n then some (TCB.withAnswerSlots ρ μ π κ y) else some y).isSome := by
        intro y; split <;> rfl
      have hStep : ∀ nT' : TCB, nT'.queueNext = nT.queueNext →
          (match storeTcbQueueLinks (st1.mapTcbInPlace r (TCB.withAnswerSlots ρ μ π κ)) n none
              (some .endpointHead) nT'.queueNext with
            | .error e => Except.error e
            | .ok st2 => match storeTcbQueueLinks st2 tid none none none with
                | .error e => Except.error e
                | .ok st3 => Except.ok (tid, headTcb, st3)) =
          (match (match storeTcbQueueLinks st1 n none (some .endpointHead) nT.queueNext with
              | .error e => Except.error e
              | .ok st2 => match storeTcbQueueLinks st2 tid none none none with
                  | .error e => Except.error e
                  | .ok st3 => Except.ok (tid, headTcb, st3)) with
            | .ok (t, tcb, Z') => Except.ok (t, tcb, Z'.mapTcbInPlace r (TCB.withAnswerSlots ρ μ π κ))
            | .error e => Except.error e) := by
        intro nT' hq
        rw [hq, storeTcbQueueLinks_answer r ρ μ π κ st1 n _ _ _ hNo]
        cases hS : storeTcbQueueLinks st1 n none (some .endpointHead) nT.queueNext with
        | error e => rfl
        | ok st2 => exact hTail st2 (modifyTcb_noResizeDue _ _ _ _ hNo hS)
      by_cases hrn : r = n
      · rw [if_pos hrn, Option.map_some]
        exact hStep _ rfl
      · rw [if_neg hrn]
        exact hStep _ rfl

/-- **The pop commutes with the answer** when the popped head is not the
answered thread: the answered thread may be the head's successor, whose queue
links the pop rewrites and the answer leaves alone. -/

theorem endpointQueuePopHead_answer (Z : SystemState) (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (ep : Endpoint) (hEp : Z.getObject? endpointId = some (.endpoint ep))
    (hHead : (if isReceiveQ then ep.receiveQ else ep.sendQ).head ≠ some r)
    (hNo : Z.objects.noResizeDue) :
    endpointQueuePopHead endpointId isReceiveQ (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ π κ)) =
      match endpointQueuePopHead endpointId isReceiveQ Z with
      | .ok (t, tcb, Z') => .ok (t, tcb, Z'.mapTcbInPlace r (TCB.withAnswerSlots ρ μ π κ))
      | .error e => .error e := by
  have hEp' := getObject?_answer_endpoint r ρ μ π κ Z endpointId ep hEp
  have hk : Z.objects[endpointId]? = some (.endpoint ep) := hEp
  unfold endpointQueuePopHead
  rw [hEp, hEp']
  dsimp only
  cases hH : (if isReceiveQ then ep.receiveQ else ep.sendQ).head with
  | none => rfl
  | some tid =>
    have htid : tid ≠ r := fun h => hHead (by rw [hH, h])
    dsimp only
    rw [lookupTcb_answer_ne r ρ μ π κ Z tid htid]
    cases hT : lookupTcb Z tid with
    | none => rfl
    | some headTcb =>
      dsimp only
      have hL : ∀ e : Endpoint, storeLeavesIndexAndTypes Z endpointId
          (KernelObject.endpoint e).objectType = true := fun e => by
        unfold storeLeavesIndexAndTypes storeKeepsKind; rw [hk]; rfl
      have hNo1 : ∀ e : Endpoint,
          ({ Z with objects := Z.objects.insert endpointId (.endpoint e) } : SystemState).objects.noResizeDue :=
        fun e => insert_present_noResizeDue Z endpointId _ _ hk hNo
      rw [storeObject_mapTcbInPlace_of_fixed r Z endpointId _ _ hk hNo rfl rfl (hL _),
        storeObject_eq_of_leaves (hL _)]
      dsimp only
      exact popTail_answer r ρ μ π κ _ tid headTcb htid (hNo1 _)

end Pop

/-! ## The ledger

Recording physical writes touches the ledger alone, which none of the run
queue's, the reply-waiter queues' or the priority walk's steps reads or writes;
so each commutes with a recording. -/

section Ledger

open Architecture

variable (ws : List PhysicalWrite)

theorem mapTcbInPlace_ledger (st : SystemState) (t : SeLe4n.ThreadId) (g : TCB → TCB) :
    (recordPhysicalWrites st ws).mapTcbInPlace t g = recordPhysicalWrites (st.mapTcbInPlace t g) ws := rfl

theorem updateTcbAtCode_ledger (st : SystemState) (k : Nat) (g : TCB → TCB) :
    (recordPhysicalWrites st ws).updateTcbAtCode k g = recordPhysicalWrites (st.updateTcbAtCode k g) ws := by
  unfold SystemState.updateTcbAtCode; split <;> rfl

theorem runLinkOn_ledger (st : SystemState) (c : CoreId) (y : SeLe4n.ThreadId) :
    (recordPhysicalWrites st ws).runLinkOn c y = st.runLinkOn c y := rfl

theorem runUnlinkLinks_ledger (st : SystemState) (t : SeLe4n.ThreadId) (pv nx bpv bnx : Nat) :
    (recordPhysicalWrites st ws).runUnlinkLinks t pv nx bpv bnx =
      recordPhysicalWrites (st.runUnlinkLinks t pv nx bpv bnx) ws := by
  rw [SystemState.runUnlinkLinks_eq_impl]; rfl

theorem runRemoveOnCore_ledger (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId) :
    (recordPhysicalWrites st ws).runRemoveOnCore c t = recordPhysicalWrites (st.runRemoveOnCore c t) ws := by
  unfold SystemState.runRemoveOnCore
  simp only [runLinkOn_ledger]
  by_cases h : (st.runLinkOn c t).queued
  · simp only [h, if_true, runUnlinkLinks_ledger]; rfl
  · simp only [h, if_false, Bool.false_eq_true]; rfl

theorem removeRunnableOnCore_ledger (st : SystemState) (t : SeLe4n.ThreadId) (c : CoreId) :
    removeRunnableOnCore (recordPhysicalWrites st ws) t c = recordPhysicalWrites (removeRunnableOnCore st t c) ws := by
  show (recordPhysicalWrites st ws).runDescheduleOnCore c t = _
  unfold SystemState.runDescheduleOnCore
  rw [runRemoveOnCore_ledger]; rfl

theorem modifyObject_ledger (st : SystemState) (o : SeLe4n.ObjId) (f : KernelObject → KernelObject) :
    (recordPhysicalWrites st ws).modifyObject o f = recordPhysicalWrites (st.modifyObject o f) ws := rfl

theorem updateTcb_ledger (st : SystemState) (x : SeLe4n.ThreadId) (f : TCB → TCB)
    (hNo : st.objects.noResizeDue) :
    (recordPhysicalWrites st ws).updateTcb x f = recordPhysicalWrites (st.updateTcb x f) ws := by
  rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNo,
    SystemState.updateTcb_eq_mapTcbInPlace (recordPhysicalWrites st ws) _ _ hNo]; rfl

theorem runAppendLinks_ledger (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId) (p : SeLe4n.Priority) :
    (recordPhysicalWrites st ws).runAppendLinks c t p = recordPhysicalWrites (st.runAppendLinks c t p) ws := by
  unfold SystemState.runAppendLinks
  simp only [recordPhysicalWrites_scheduler, mapTcbInPlace_ledger, updateTcbAtCode_ledger]

theorem runAppendOnCore_ledger (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId) (p : SeLe4n.Priority) :
    (recordPhysicalWrites st ws).runAppendOnCore c t p = recordPhysicalWrites (st.runAppendOnCore c t p) ws := by
  unfold SystemState.runAppendOnCore; rw [runAppendLinks_ledger]; rfl

theorem runEnqueueAdmitted_ledger (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId) (p : SeLe4n.Priority) :
    (recordPhysicalWrites st ws).runEnqueueAdmitted c t p =
      recordPhysicalWrites (st.runEnqueueAdmitted c t p) ws := by
  unfold SystemState.runEnqueueAdmitted
  simp only [runLinkOn_ledger]
  by_cases h : (st.runLinkOn c t).queued
  · simp only [h, if_true]; rfl
  · simp only [h, if_false, Bool.false_eq_true, runAppendOnCore_ledger]; rfl

theorem enqueueRunnableOnCore_ledger (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId) :
    enqueueRunnableOnCore (recordPhysicalWrites st ws) c t =
      recordPhysicalWrites (enqueueRunnableOnCore st c t) ws := by
  rw [enqueueRunnableOnCore_eq_impl]
  unfold enqueueRunnableOnCoreImpl
  show (match st.getTcb? t with
    | some tcb => if wakeDeclines (recordPhysicalWrites st ws) c t then recordPhysicalWrites st ws
        else _
    | none => recordPhysicalWrites st ws) = _
  cases st.getTcb? t with
  | none => rfl
  | some tcb =>
    show (if wakeDeclines st c t then _ else _) = _
    by_cases h : wakeDeclines st c t
    · simp only [h, if_true]
    · simp only [h, if_false, Bool.false_eq_true, modifyObject_ledger, runEnqueueAdmitted_ledger]; rfl

theorem runRequeueOnCore_ledger (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId) (p : SeLe4n.Priority) :
    (recordPhysicalWrites st ws).runRequeueOnCore c t p = recordPhysicalWrites (st.runRequeueOnCore c t p) ws := by
  unfold SystemState.runRequeueOnCore
  rw [runRemoveOnCore_ledger, runEnqueueAdmitted_ledger]; rfl

theorem linkReplyWaiter_ledger (st : SystemState) (w s : SeLe4n.ThreadId) :
    (recordPhysicalWrites st ws).linkReplyWaiter w s = recordPhysicalWrites (st.linkReplyWaiter w s) ws := by
  unfold SystemState.linkReplyWaiter
  simp only [mapTcbInPlace_ledger, updateTcbAtCode_ledger]; rfl

theorem unlinkReplyWaiter_ledger (st : SystemState) (w s : SeLe4n.ThreadId) :
    (recordPhysicalWrites st ws).unlinkReplyWaiter w s = recordPhysicalWrites (st.unlinkReplyWaiter w s) ws := by
  unfold SystemState.unlinkReplyWaiter
  simp only [mapTcbInPlace_ledger, updateTcbAtCode_ledger]; rfl

theorem markKeyFlagsOver_ledger (st : SystemState) (tid : SeLe4n.ThreadId) (rc : Nat) (w : Bool)
    (cs : List CoreId) :
    markKeyFlagsOver (recordPhysicalWrites st ws) tid rc w cs =
      recordPhysicalWrites (markKeyFlagsOver st tid rc w cs) ws := by
  induction cs generalizing st with
  | nil => rfl
  | cons c cs ih =>
    unfold markKeyFlagsOver
    simp only [recordPhysicalWrites_scheduler]
    split
    · exact ih (st.markReschedulePendingOnCore c)
    · exact ih st

theorem markKeyChangeParts_ledger (st : SystemState) (tid : SeLe4n.ThreadId) (p0 : SeLe4n.Priority)
    (d0 : SeLe4n.Deadline) (dom0 : SeLe4n.DomainId) :
    markKeyChangeParts (recordPhysicalWrites st ws) tid p0 d0 dom0 =
      recordPhysicalWrites (markKeyChangeParts st tid p0 d0 dom0) ws := by
  unfold markKeyChangeParts
  show (match st.getTcb? tid with | some t => _ | none => _) = _
  cases st.getTcb? tid with
  | none => rfl
  | some t =>
    dsimp only
    split
    · rfl
    · exact markKeyFlagsOver_ledger ws st _ _ _ _

theorem updatePipBoostOnCore_ledger (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (hNo : st.objects.noResizeDue) :
    PriorityInheritance.updatePipBoostOnCore (recordPhysicalWrites st ws) c tid =
      recordPhysicalWrites (PriorityInheritance.updatePipBoostOnCore st c tid) ws := by
  rw [PriorityInheritance.updatePipBoostOnCore_eq_impl]
  unfold PriorityInheritance.updatePipBoostOnCoreImpl
  show (match st.getTcb? tid with | some tcb => _ | none => _) = _
  cases st.getTcb? tid with
  | none => rfl
  | some tcb =>
    dsimp only
    rw [← PriorityInheritance.optCode_computeMaxWaiterPriority,
      PriorityInheritance.computeMaxWaiterPriority_frame st (recordPhysicalWrites st ws) tid rfl,
      PriorityInheritance.optCode_computeMaxWaiterPriority]
    split
    · rfl
    · rw [updateTcb_ledger ws st tid _ hNo]
      split
      · rw [runRequeueOnCore_ledger, markKeyChangeParts_ledger]
      · rw [markKeyChangeParts_ledger]

theorem propagatePipChainStateWalk_ledger (st : SystemState) (tid : SeLe4n.ThreadId) (fuel : Nat)
    (hNo : st.objects.noResizeDue) :
    PriorityInheritance.propagatePipChainStateWalk (recordPhysicalWrites st ws) tid fuel =
      recordPhysicalWrites (PriorityInheritance.propagatePipChainStateWalk st tid fuel) ws := by
  induction fuel generalizing st tid with
  | zero => rfl
  | succ n ih =>
    unfold PriorityInheritance.propagatePipChainStateWalk
    show (match PriorityInheritance.blockingServer st tid with | some s => _ | none => _) = _
    rw [show determineTargetCore (recordPhysicalWrites st ws) tid = determineTargetCore st tid from rfl,
      updatePipBoostOnCore_ledger ws st _ _ hNo]
    cases PriorityInheritance.blockingServer st tid with
    | none => rfl
    | some s => exact ih _ _ (updatePipBoostOnCore_noResizeDue _ _ _ hNo)

theorem propagatePipChainCrossCore_ledger (st : SystemState) (tid : SeLe4n.ThreadId) (ec : CoreId)
    (hNo : st.objects.noResizeDue) :
    (PriorityInheritance.propagatePipChainCrossCore (recordPhysicalWrites st ws) tid ec).1 =
      recordPhysicalWrites (PriorityInheritance.propagatePipChainCrossCore st tid ec).1 ws := by
  rw [PriorityInheritance.propagatePipChainCrossCore_eq_walks,
    PriorityInheritance.propagatePipChainCrossCore_eq_walks]
  exact propagatePipChainStateWalk_ledger ws st tid _ hNo

end Ledger

/-! ## The answer is an answer-slot write -/

section AnswerWrite

open Architecture

/-- **Staging a delivered message is an answer-slot write**: on a table with no
resize due, a ready thread holding a message has its delivered frame written
into its registers and its message dropped, and the overflow words recorded;
any other thread is left alone. -/
theorem stageDeliveredMessage_eq_answerSlots (X : SystemState) (c : SeLe4n.ThreadId) (n : Nat)
    (hNo : X.objects.noResizeDue) :
    stageDeliveredMessage X c n =
      match X.getTcb? c with
      | some t =>
          if t.ipcState = .ready then
            match t.pendingMessage with
            | some m =>
                recordPhysicalWrites
                  (X.mapTcbInPlace c (TCB.withAnswerSlots
                    (fun rf => rf.stageDeliveredWords
                      (returnFrameOfMessage m n (messageOverflowWrites X t m).length).x0
                      (returnFrameOfMessage m n (messageOverflowWrites X t m).length).x1
                      (returnFrameOfMessage m n (messageOverflowWrites X t m).length).x2
                      (returnFrameOfMessage m n (messageOverflowWrites X t m).length).x3
                      (returnFrameOfMessage m n (messageOverflowWrites X t m).length).x4
                      (returnFrameOfMessage m n (messageOverflowWrites X t m).length).x5)
                    (fun _ => none) id id))
                  (messageOverflowWrites X t m)
            | none => X
          else X
      | none => X := by
  unfold stageDeliveredMessage
  cases X.getTcb? c with
  | none => rfl
  | some t =>
    dsimp only
    split
    · cases t.pendingMessage with
      | none => rfl
      | some m =>
        dsimp only
        unfold writeDeliveredFrameToTcb
        rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNo]
        rfl
    · rfl

/-- **The restart is an answer-slot write** on a table with no resize due. -/
theorem applyFaultRestart_eq_answerSlots (X : SystemState) (c : SeLe4n.ThreadId)
    (f : FaultRestartFrame) (hNo : X.objects.noResizeDue) :
    applyFaultRestart X c f =
      X.mapTcbInPlace c (TCB.withAnswerSlots (fun rf => rf.stageRestartFrame f) id id (fun _ => 0)) := by
  unfold applyFaultRestart
  rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNo]
  rfl

/-- The overflow words a delivery writes read the thread only through its
IPC-buffer cell and address. -/
theorem overflowDeliveryWrites_congr_tcb (X : SystemState) (t t' : TCB)
    (hCell : t'.spaceCells = t.spaceCells) (hBuf : t'.ipcBuffer = t.ipcBuffer) :
    ∀ (ws : List SeLe4n.RegValue) (idx : Nat),
      overflowDeliveryWrites X t' ws idx = overflowDeliveryWrites X t ws idx
  | [], _ => rfl
  | w :: rest, idx => by
      unfold overflowDeliveryWrites
      have hP : IpcBufferRead.ipcBufferSlotPAddr? X t' idx true =
          IpcBufferRead.ipcBufferSlotPAddr? X t idx true := by
        unfold IpcBufferRead.ipcBufferSlotPAddr? IpcBufferRead.lookupIPCBuffer
        rw [hCell, hBuf]
      rw [hP, overflowDeliveryWrites_congr_tcb X t t' hCell hBuf rest (idx + 1)]

theorem messageOverflowWrites_congr_tcb (X : SystemState) (t t' : TCB) (m : IpcMessage)
    (hCell : t'.spaceCells = t.spaceCells) (hBuf : t'.ipcBuffer = t.ipcBuffer) :
    messageOverflowWrites X t' m = messageOverflowWrites X t m :=
  overflowDeliveryWrites_congr_tcb X t t' hCell hBuf _ 0

/-- **The stage commutes with a step that commutes with its writes.**  `F`
commutes with the caller's answer-slot write and with the ledger, keeps the
caller's TCB up to a rewrite `g` of fields the stage does not read, and reads
the same IPC-buffer frames: then staging first and staging last agree. -/
theorem stageDeliveredMessage_commute (F : SystemState → SystemState) (X : SystemState)
    (c : SeLe4n.ThreadId) (n : Nat)
    (hNo : X.objects.noResizeDue) (hNoF : (F X).objects.noResizeDue)
    (hM : ∀ ρ μ π κ, F (X.mapTcbInPlace c (TCB.withAnswerSlots ρ μ π κ)) =
      (F X).mapTcbInPlace c (TCB.withAnswerSlots ρ μ π κ))
    (hR : ∀ (Y : SystemState) ws, F (recordPhysicalWrites Y ws) = recordPhysicalWrites (F Y) ws)
    (g : TCB → TCB) (hT : (F X).getTcb? c = (X.getTcb? c).map g)
    (hgIpc : ∀ t, (g t).ipcState = t.ipcState) (hgMsg : ∀ t, (g t).pendingMessage = t.pendingMessage)
    (hgCell : ∀ t, (g t).spaceCells = t.spaceCells) (hgBuf : ∀ t, (g t).ipcBuffer = t.ipcBuffer)
    (hFrames : ∀ t m, messageOverflowWrites (F X) t m = messageOverflowWrites X t m) :
    F (stageDeliveredMessage X c n) = stageDeliveredMessage (F X) c n := by
  rw [stageDeliveredMessage_eq_answerSlots X c n hNo,
    stageDeliveredMessage_eq_answerSlots (F X) c n hNoF, hT]
  cases X.getTcb? c with
  | none => rfl
  | some t =>
    simp only [Option.map_some, hgIpc, hgMsg]
    split
    · cases t.pendingMessage with
      | none => rfl
      | some m =>
        simp only
        rw [hR, hM, messageOverflowWrites_congr_tcb (F X) t (g t) m (hgCell t) (hgBuf t), hFrames]
    · rfl

/-- **The restart commutes with a step that commutes with its write.** -/
theorem applyFaultRestart_commute (F : SystemState → SystemState) (X : SystemState)
    (c : SeLe4n.ThreadId) (f : FaultRestartFrame)
    (hNo : X.objects.noResizeDue) (hNoF : (F X).objects.noResizeDue)
    (hM : ∀ ρ μ π κ, F (X.mapTcbInPlace c (TCB.withAnswerSlots ρ μ π κ)) =
      (F X).mapTcbInPlace c (TCB.withAnswerSlots ρ μ π κ)) :
    F (applyFaultRestart X c f) = applyFaultRestart (F X) c f := by
  rw [applyFaultRestart_eq_answerSlots X c f hNo, applyFaultRestart_eq_answerSlots (F X) c f hNoF, hM]

end AnswerWrite

end SeLe4n.Kernel
