-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.QueueLabels.Finalise
import SeLe4n.Kernel.KernelRecords.Timer

/-! # The timer: frames

WS-SX SX11.2.  A timeout takes its thread off its endpoint's queue and makes it
`.ready`; the rest of the tick (the replenishments, the charge, the reschedule)
writes no IPC state.  So the tick moves no thread onto an endpoint.  The proofs
follow the records' own (`KernelRecords/Timer.lean`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

namespace QueueLabelsFrame

/-- **The IPC abort**: the queue removal, then the thread made `.ready`. -/
theorem abortPendingIpcOnEndpoint {epId : SeLe4n.ObjId} {isReceiveQ : Bool}
    {tid : SeLe4n.ThreadId} {st st' : SystemState} (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.abortPendingIpcOnEndpoint epId isReceiveQ tid st = .ok st') :
    QueueLabelsFrame st st' := by
  unfold _root_.SeLe4n.Kernel.abortPendingIpcOnEndpoint at h
  split at h
  · cases h
  · rename_i st1 hR
    split at h
    · cases h
    · rename_i tcb hT
      dsimp only at h
      split at h
      · cases h
      · rename_i hS
        cases h
        have F := RecordsFrame.endpointQueueRemove hInv hR
        exact (of_frame F).trans (storeObject_tcb F.invExt (lookupTcb_some_objects _ _ _ hT) hS
          (TcbWaitsKept.of_noWait (by
            rw [TCB.withReturnFrame_ipcState, TCB.ipcState_setIpcState]; simp)))

/-- **A timeout**: the abort, the wake, the reply-waiter unlink and the chain
revert. -/
theorem timeoutThread {epId : SeLe4n.ObjId} {isReceiveQ : Bool} {tid : SeLe4n.ThreadId}
    {ec : CoreId} {st : SystemState} {r : SystemState × Option (CoreId × Concurrency.SgiKind)}
    (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.timeoutThread epId isReceiveQ tid ec st = .ok r) :
    QueueLabelsFrame st r.1 := by
  unfold _root_.SeLe4n.Kernel.timeoutThread at h
  split at h
  · cases h
  · rename_i st2 hA
    obtain ⟨S0, hRdy⟩ := RecordsStep.abortPendingIpcOnEndpoint hInv hA
    have S := abortPendingIpcOnEndpoint hInv hA
    have S1 := S.trans (of_frame (RecordsFrame.wakeThread st2 tid ec S.invExt hRdy))
    dsimp only at h
    split at h
    · rename_i server _
      rw [Except.ok.injEq] at h; subst h
      have S2 := S1.trans (unlinkReplyWaiter _ tid server S1.invExt)
      exact S2.trans (of_frame (RecordsFrame.revertPriorityInheritance _ _ _ S2.invExt))
    · rw [Except.ok.injEq] at h; subst h; exact S1

/-- The bound-context timeout pass: a fold of timeouts. -/
theorem timeoutBlockedThreads (st : SystemState) (scId : SeLe4n.SchedContextId) (ec : CoreId)
    (hInv : st.objects.invExt) :
    QueueLabelsFrame st (_root_.SeLe4n.Kernel.timeoutBlockedThreads st scId ec).1 := by
  rw [timeoutBlockedThreads_eq_fold]; delta timeoutBlockedThreadStep
  suffices H : ∀ (l : List SeLe4n.ThreadId)
      (acc : SystemState × List (SeLe4n.ThreadId × KernelError) × List (CoreId × Concurrency.SgiKind)),
      QueueLabelsFrame st acc.1 →
      QueueLabelsFrame st (l.foldl (fun acc tid =>
        let (st', errs, sgis) := acc
        match st'.getTcb? tid with
        | some tcb =>
          match tcbBlockingInfo tcb with
          | some (epId, isReceiveQ) =>
            match _root_.SeLe4n.Kernel.timeoutThread epId isReceiveQ tid ec st' with
            | .ok r => (r.1, errs, sgis ++ r.2.toList)
            | .error e => (st', errs ++ [(tid, e)], sgis)
          | none => (st', errs, sgis)
        | none => (st', errs, sgis)) acc).1 from
    H _ _ (refl hInv)
  intro l
  induction l with
  | nil => intro acc h; exact h
  | cons x xs ih =>
    intro acc h
    simp only [List.foldl_cons]
    apply ih
    obtain ⟨s, e, g⟩ := acc
    dsimp only
    split
    · split
      · split
        · rename_i r hT
          exact h.trans (timeoutThread h.invExt hT)
        · exact h
      · exact h
    · exact h

theorem budgetExhaustOnCore (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline × SeLe4n.DomainId)
    (scId : SeLe4n.SchedContextId) (sc : SchedContext) (hSc : st.getSchedContext? scId = some sc)
    (ticks : Nat) (hInv : st.objects.invExt) :
    QueueLabelsFrame st (_root_.SeLe4n.Kernel.budgetExhaustOnCore st c tid k scId sc hSc ticks) :=
  have F := RecordsFrame.chain (RecordsFrame.spendBudgetOnCore st c tid scId sc hSc _ ticks)
    (RecordsFrame.markKeyChangeFor _ tid k) hInv
  have S := (of_frame F).trans (timeoutBlockedThreads _ scId c F.invExt)
  S.trans (of_frame (RecordsFrame.withScheduler _ _ S.invExt))

/-- The tick's charge of a thread: a slice or budget step. -/
theorem timerTickBudgetOnCore {st : SystemState} {c : CoreId} {tid : SeLe4n.ThreadId} {tcb : TCB}
    {hTcb : st.getTcb? tid = some tcb} {r : SystemState × Bool} (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.timerTickBudgetOnCore st c tid tcb hTcb = r) :
    QueueLabelsFrame st r.1 := by
  subst h
  unfold _root_.SeLe4n.Kernel.timerTickBudgetOnCore
  split
  · split
    · exact of_frame (RecordsFrame.sliceExpireOnCore st c tid tcb hTcb hInv)
    · exact of_frame (RecordsFrame.rewriteObject_tcb hTcb _ (by rfl)
        (SystemState.rewriteAdmissible_tcb hTcb _) hInv)
  all_goals
    split
    · rename_i sc hSc _
      dsimp only
      split
      · exact budgetExhaustOnCore st c tid _ _ sc hSc 1 hInv
      · exact of_frame (RecordsFrame.rewriteObject_schedContext hSc _
          (SystemState.rewriteAdmissible_schedContext hSc _) hInv)
    · exact refl hInv

/-- **The timer tick moves no thread onto an endpoint.** -/
theorem timerTickOnCore (st : SystemState) (c : CoreId) (hInv : st.objects.invExt) :
    QueueLabelsFrame st (_root_.SeLe4n.Kernel.timerTickOnCore st c) := by
  have hP : QueueLabelsFrame st (timerTickOnCorePrepared st c) :=
    of_frame (RecordsFrame.chain (fun h => RecordsFrame.withScheduler st
      (st.scheduler.setLastTimeoutErrorsOnCore c []) h)
      (RecordsFrame.processReplenishmentsDueOnCore _ c st.machine.timer) hInv)
  refine timerTickOnCore_of (P := QueueLabelsFrame st) st c hP ?_ ?_ ?_
  · intro s hs
    exact hs.trans (of_frame
      (RecordsFrame.handleRescheduleSgiOnCore hs.invExt (handleRescheduleSgiOnCore_eq_state s c)))
  · intro s hs
    exact hs.trans (of_frame
      (RecordsFrame.scheduleEffectiveOnCore hs.invExt (scheduleEffectiveOnCore_eq_state s c)))
  · intro tid tcb hTcb st3 b hb
    exact hP.trans (timerTickBudgetOnCore hP.invExt hb)

end QueueLabelsFrame

end SeLe4n.Kernel
