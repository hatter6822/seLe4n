-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.KernelRecords.SchedulingArms
import SeLe4n.Kernel.MappingRecordStage.Scheduling

/-!
# The timer path and the yield keep the records

WS-ZA ZA6.37.  A slice or budget charge, a reschedule and a replenishment write
counters, contexts, run-queue links and the scheduler, so each is a
`RecordsFrame`.  A budget exhaustion times out the context's IPC-blocked thread:
the abort makes it `.ready` with its fault retired (`abortPendingIpcOnEndpoint`
clears it, as seL4's `cancelIPC` resets `tcbFault`), so every fault record
stays parked, and the timeout keeps the reply-waiter queues by its own theorem.
The tick is therefore a `RecordsStage`.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

namespace RecordsFrame

/-- One queue neighbour's links patched. -/
theorem neighbourPatch (st : SystemState) (nid? : Option SeLe4n.ThreadId) (upd : TCB → TCB)
    (hU : ∀ t, (upd t).recordView = t.recordView) (hInv : st.objects.invExt) :
    RecordsFrame st { st with objects := queueNeighbourPatch st.objects nid? upd } := by
  unfold queueNeighbourPatch
  split
  · exact of_objects_eq hInv rfl rfl
  · split
    · rename_i t h
      exact insert hInv (by rw [h]; simp [hU])
    · exact of_objects_eq hInv rfl rfl

/-- **The endpoint-queue removal keeps every record view**: two neighbour
patches, an endpoint rewrite and the removed thread's links cleared. -/
theorem endpointQueueRemove {endpointId : SeLe4n.ObjId} {isReceiveQ : Bool}
    {tid : SeLe4n.ThreadId} {st st' : SystemState} (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.endpointQueueRemove endpointId isReceiveQ tid st = .ok st') :
    RecordsFrame st st' := by
  obtain ⟨ep, ep', tcb, hEp, hT, rfl⟩ := endpointQueueRemove_objects_eq h
  have hTo := lookupTcb_some_objects st tid tcb hT
  have F1 := neighbourPatch st tcb.queuePrev (queueUnlinkPredecessor tcb) (fun _ => rfl) hInv
  have F2 := F1.andThen fun h =>
    neighbourPatch _ tcb.queueNext (queueUnlinkSuccessor tcb) (fun _ => rfl) h
  have F3 := F2.andThen fun h => insert (k := endpointId) (o := .endpoint ep') h
    (by rw [F2.views, hEp]; rfl)
  exact F3.andThen fun h => insert (k := tid.toObjId)
    (o := .tcb (tcbWithQueueLinks tcb none none none)) h (by rw [F3.views, hTo]; rfl)

end RecordsFrame

namespace RecordsStep

/-- **The IPC abort**: the queue removal, then the aborted thread made `.ready`
with its fault retired.  The thread it leaves is `.ready`. -/
theorem abortPendingIpcOnEndpoint {epId : SeLe4n.ObjId} {isReceiveQ : Bool}
    {tid : SeLe4n.ThreadId} {st st' : SystemState} (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.abortPendingIpcOnEndpoint epId isReceiveQ tid st = .ok st') :
    RecordsStep st st' ∧ ∀ x, st'.getTcb? tid = some x → x.ipcState = .ready := by
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
        refine ⟨(of_frame F).trans (storeObject_tcb F.invExt (lookupTcb_some_objects _ _ _ hT) hS
          (TcbStaysParked.of_noFault ?_)), fun x hx => ?_⟩
        · exact TCB.pendingFault_setPendingFault _ none
        · have hO := (SystemState.getTcb?_eq_some_iff _ _ _).mp hx
          rw [storeObject_objects_eq _ _ _ _ F.invExt hS] at hO
          cases hO
          exact (TCB.withReturnFrame_ipcState _ _).trans (TCB.ipcState_setIpcState _ .ready)

/-- **A timeout**: the abort, the wake, the reply-waiter unlink and the chain
revert. -/
theorem timeoutThread {epId : SeLe4n.ObjId} {isReceiveQ : Bool} {tid : SeLe4n.ThreadId}
    {ec : CoreId} {st : SystemState} {r : SystemState × Option (CoreId × Concurrency.SgiKind)}
    (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.timeoutThread epId isReceiveQ tid ec st = .ok r) :
    RecordsStep st r.1 := by
  unfold _root_.SeLe4n.Kernel.timeoutThread at h
  split at h
  · cases h
  · rename_i st2 hA
    obtain ⟨S, hRdy⟩ := abortPendingIpcOnEndpoint hInv hA
    have S1 := S.trans (of_frame (RecordsFrame.wakeThread st2 tid ec S.invExt hRdy))
    dsimp only at h
    split at h
    · rename_i server _
      rw [Except.ok.injEq] at h; subst h
      have S2 := S1.trans (unlinkReplyWaiter _ tid server S1.invExt)
      exact S2.trans (of_frame (RecordsFrame.revertPriorityInheritance _ _ _ S2.invExt))
    · rw [Except.ok.injEq] at h; subst h; exact S1

end RecordsStep

namespace RecordsFrame

theorem sliceExpireOnCore (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hTcb : st.getTcb? tid = some tcb) (hInv : st.objects.invExt) :
    RecordsFrame st (_root_.SeLe4n.Kernel.sliceExpireOnCore st c tid tcb hTcb) := by
  unfold _root_.SeLe4n.Kernel.sliceExpireOnCore
  refine (rewriteObject_tcb hTcb _ ?_ _ hInv).andThen fun h => runEnqueueOnCore _ _ _ _ h
  rfl

theorem spendBudgetOnCore (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (sc : SchedContext) (hSc : st.getSchedContext? scId = some sc)
    (start ticks : Nat) (hInv : st.objects.invExt) :
    RecordsFrame st (_root_.SeLe4n.Kernel.spendBudgetOnCore st c tid scId sc hSc start ticks) := by
  unfold _root_.SeLe4n.Kernel.spendBudgetOnCore replenishOnCore
  exact ((rewriteObject_schedContext hSc _ _ hInv).andThen fun h => releasePlace _ c scId h).andThen
    fun h => runEnqueueOnCore _ _ _ _ h

theorem idleFallbackOnCore (st : SystemState) (c : CoreId) (hInv : st.objects.invExt) :
    RecordsFrame st (_root_.SeLe4n.Kernel.idleFallbackOnCore st c) := by
  unfold _root_.SeLe4n.Kernel.idleFallbackOnCore dispatchIdleOnCore
  split
  · exact ((runRemoveOnCore st c _ hInv).andThen fun h => restoreIncomingContextOnCore _ c _ h).andThen
      fun h => withScheduler _ _ h
  · exact withScheduler _ _ hInv

/-- The reschedule: the register save, then the idle fallback or the dequeue,
restore and current-slot write of the chosen thread, then the flag clear. -/
theorem scheduleEffectiveOnCore {st st' : SystemState} {c : CoreId} (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.scheduleEffectiveOnCore st c = .ok st') : RecordsFrame st st' := by
  unfold _root_.SeLe4n.Kernel.scheduleEffectiveOnCore at h
  split at h
  · cases h
  · rw [Except.ok.injEq] at h; subst h
    exact ((saveOutgoingContextOnCore st c hInv).andThen fun h => idleFallbackOnCore _ c h).andThen
      fun h => clearReschedulePendingOnCore _ c h
  · split at h
    · split at h
      · rw [Except.ok.injEq] at h; subst h
        rename_i tid _ _ _ _ _
        exact (((saveOutgoingContextOnCore st c hInv).andThen fun h => runRemoveOnCore _ c tid h).andThen
          fun h => restoreIncomingContextOnCore _ c tid h).andThen fun h => withScheduler _ _ h
      · cases h
    · cases h

/-- The yield's charge: the slice end, or the budget forfeit with the key hook. -/
theorem yieldChargeOnCore {st st' : SystemState} {c : CoreId} {tid : SeLe4n.ThreadId}
    (hInv : st.objects.invExt) (h : _root_.SeLe4n.Kernel.yieldChargeOnCore st c tid = .ok st') :
    RecordsFrame st st' := by
  unfold _root_.SeLe4n.Kernel.yieldChargeOnCore at h
  split at h
  · cases h
  · rename_i tcb hTcb _
    split at h
    · rw [Except.ok.injEq] at h; subst h
      exact sliceExpireOnCore st c tid tcb hTcb hInv
    all_goals
      split at h
      · rename_i sc hSc _
        rw [Except.ok.injEq] at h; subst h
        exact (spendBudgetOnCore st c tid _ sc hSc _ _ hInv).andThen fun h => markKeyChangeFor _ _ _ h
      · cases h

/-- **The yield keeps the records' reads**: the charge and the reschedule. -/
theorem yieldOnCore {st st' : SystemState} {c : CoreId} (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.yieldOnCore st c = .ok st') : RecordsFrame st st' := by
  unfold _root_.SeLe4n.Kernel.yieldOnCore at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i hC
      exact (yieldChargeOnCore hInv hC).andThen fun h' => scheduleEffectiveOnCore h' h

/-- One due replenishment: the refill and the wake of a runnable bound thread,
under the refill's key hook (flags only). -/
theorem processOneReplenishmentOnCore (st : SystemState) (c : CoreId)
    (scId : SeLe4n.SchedContextId) (now : Nat) (hInv : st.objects.invExt) :
    RecordsFrame st (_root_.SeLe4n.Kernel.processOneReplenishmentOnCore st c scId now) := by
  have hRefill : RecordsFrame st (refillSchedContext st scId now) := by
    unfold refillSchedContext; exact updateSchedContext _ _ _ hInv
  unfold _root_.SeLe4n.Kernel.processOneReplenishmentOnCore
  refine RecordsFrame.andThen (b := refillWakeOnCore st c scId now) ?_ fun h =>
    of_objects_eq h (markRefillKeyChange_objects _ _ _)
      (markRefillKeyChange_extract_frame SystemState.asidTable _ _ _ fun _ _ => rfl)
  unfold refillWakeOnCore
  dsimp only
  split
  · rename_i tid hW
    split
    · exact hRefill
    · refine (hRefill.andThen fun h => wakeThread _ tid c h ?_).andThen fun h => withScheduler _ _ h
      intro x hx
      have hA : ((refillSchedContext st scId now).getTcb? tid).any TCB.isRunnable = true := by
        unfold replenishWakeTarget at hW
        dsimp only at hW
        repeat' split at hW
        all_goals first | cases hW | exact (Option.filter_eq_some_iff.mp hW).2
      rw [hx] at hA
      simp only [Option.any_some, TCB.isRunnable, Bool.and_eq_true, decide_eq_true_eq] at hA
      exact hA.1
  · exact hRefill

/-- The replenishment drain: a fold of refills and placements. -/
theorem processReplenishmentsDueOnCore (st : SystemState) (c : CoreId) (now : Nat)
    (hInv : st.objects.invExt) :
    RecordsFrame st (_root_.SeLe4n.Kernel.processReplenishmentsDueOnCore st c now) := by
  unfold _root_.SeLe4n.Kernel.processReplenishmentsDueOnCore
  exact drainDueOnCore_induction (RecordsFrame st) c now
    (fun s scId h => h.andThen fun h' => processOneReplenishmentOnCore s c scId now h')
    (fun s scId h => h.andThen fun h' => releasePlace s c scId h') _ st (refl hInv)

end RecordsFrame

namespace RecordsStage

/-- A frame from any state whose store keeps its invariant. -/
theorem of_frameK {st st' : SystemState} (F : st.objects.invExt → RecordsFrame st st') :
    RecordsStage st st' := fun h => (F (KernelRecords.objects_invExt h)).preserves h

/-- **A timeout keeps the records.** -/
theorem timeoutThread {epId : SeLe4n.ObjId} {isReceiveQ : Bool} {tid : SeLe4n.ThreadId}
    {ec : CoreId} {st : SystemState} {r : SystemState × Option (CoreId × Concurrency.SgiKind)}
    (h : _root_.SeLe4n.Kernel.timeoutThread epId isReceiveQ tid ec st = .ok r) :
    RecordsStage st r.1 := fun hK => by
  have hInv := KernelRecords.objects_invExt hK
  obtain ⟨s, g⟩ := r
  exact (RecordsStep.timeoutThread hInv h).preserves (fun hC =>
    timeoutThread_preserves_replyWaitersConsistent _ _ _ _ hInv hC h) hK

/-- The bound-context timeout pass: a fold of timeouts. -/
theorem timeoutBlockedThreads (st : SystemState) (scId : SeLe4n.SchedContextId) (ec : CoreId) :
    RecordsStage st (_root_.SeLe4n.Kernel.timeoutBlockedThreads st scId ec).1 := by
  rw [timeoutBlockedThreads_eq_fold]; delta timeoutBlockedThreadStep
  suffices H : ∀ (l : List SeLe4n.ThreadId)
      (acc : SystemState × List (SeLe4n.ThreadId × KernelError) × List (CoreId × Concurrency.SgiKind)),
      RecordsStage st acc.1 →
      RecordsStage st (l.foldl (fun acc tid =>
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
    H _ _ (RecordsStage.refl st)
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
          exact h.trans (timeoutThread hT)
        · exact h
      · exact h
    · exact h

theorem budgetExhaustOnCore (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline × SeLe4n.DomainId)
    (scId : SeLe4n.SchedContextId) (sc : SchedContext) (hSc : st.getSchedContext? scId = some sc)
    (ticks : Nat) :
    RecordsStage st (_root_.SeLe4n.Kernel.budgetExhaustOnCore st c tid k scId sc hSc ticks) :=
  ((of_frameK (RecordsFrame.chain (RecordsFrame.spendBudgetOnCore st c tid scId sc hSc _ ticks)
    (RecordsFrame.markKeyChangeFor _ tid k))).trans (timeoutBlockedThreads _ scId c)).trans
    (of_frameK fun h => RecordsFrame.withScheduler _ _ h)

/-- The tick's charge of a thread: a slice or budget step. -/
theorem timerTickBudgetOnCore {st : SystemState} {c : CoreId} {tid : SeLe4n.ThreadId} {tcb : TCB}
    {hTcb : st.getTcb? tid = some tcb} {r : SystemState × Bool}
    (h : _root_.SeLe4n.Kernel.timerTickBudgetOnCore st c tid tcb hTcb = r) : RecordsStage st r.1 := by
  subst h
  unfold _root_.SeLe4n.Kernel.timerTickBudgetOnCore
  split
  · split
    · exact of_frameK (RecordsFrame.sliceExpireOnCore st c tid tcb hTcb)
    · exact of_frameK (RecordsFrame.rewriteObject_tcb hTcb _ (by rfl)
        (SystemState.rewriteAdmissible_tcb hTcb _))
  all_goals
    split
    · rename_i sc hSc _
      dsimp only
      split
      · exact budgetExhaustOnCore st c tid _ _ sc hSc 1
      · exact of_frameK (RecordsFrame.rewriteObject_schedContext hSc _
          (SystemState.rewriteAdmissible_schedContext hSc _))
    · exact RecordsStage.refl _

/-- **The timer tick keeps the records**: the diagnostic clear, the
replenishment drain, the charge (whose exhaustion times out the context's
blocked thread), and the reschedule or the scheduling point. -/
theorem timerTickOnCore (st : SystemState) (c : CoreId) :
    RecordsStage st (_root_.SeLe4n.Kernel.timerTickOnCore st c) := by
  have hP : RecordsStage st (timerTickOnCorePrepared st c) :=
    of_frameK (RecordsFrame.chain (fun h => RecordsFrame.withScheduler st
      (st.scheduler.setLastTimeoutErrorsOnCore c []) h)
      (RecordsFrame.processReplenishmentsDueOnCore _ c st.machine.timer))
  refine timerTickOnCore_of (P := RecordsStage st) st c hP ?_ ?_ ?_
  · intro s hs
    exact hs.trans (of_frameK fun h =>
      RecordsFrame.handleRescheduleSgiOnCore h (handleRescheduleSgiOnCore_eq_state s c))
  · intro s hs
    exact hs.trans (of_frameK fun h =>
      RecordsFrame.scheduleEffectiveOnCore h (scheduleEffectiveOnCore_eq_state s c))
  · intro tid tcb hTcb st3 b hb
    exact hP.trans (timerTickBudgetOnCore hb)

end RecordsStage

end SeLe4n.Kernel
