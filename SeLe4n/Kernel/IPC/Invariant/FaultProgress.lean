-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.CrossCore.Fault

/-!
# WS-RR RR4.19 — the fault-progress theorem

The finding this phase closes: before RR4, a data or instruction abort set
`x0` and returned to the faulting instruction with `ELR_EL1` restored
verbatim, so a user thread touching an unmapped page wedged its core forever.

The theorem that makes that livelock **unrepresentable** has two halves, and
both are proved here:

* **No arm resumes the thread.**  `faultDeliverOnCore` is total and has exactly
  two dispositions; on *both* the faulting thread leaves the transition
  neither in its core's run queue nor as its current thread
  (`faultDeliverOnCore_leaves_thread_not_runnable`).  So its core cannot
  dispatch it, and in particular cannot dispatch it back to the instruction
  that faulted.

* **Getting back is a handler decision.**  The only transition that installs a
  restart frame is `faultReplyOnCore`, whose outcome is a function of the
  message the *handler* sent (`faultReplyOnCore_outcome_eq`), admitted only
  from the `replyTarget` the delivery's Call recorded, and consumed exactly
  once (`applyFaultRestart` retires `pendingFault`, and
  `faultReplyOnCore_rejects_unfaulted` refuses a thread carrying none).

## What the first half costs

The delivery composes the live `.call` chain, which after the rendezvous runs
the SchedContext donation and the cross-core priority-inheritance walk.  So
"the caller is still not runnable at the end" is not immediate from the
rendezvous: §1 establishes that neither leg can *add* a thread to a run queue
or make one current.  Both are true by inspection — `updatePipBoostOnCore`
migrates a bucket only for a thread already in the queue, and touches no
`current` slot at all — and §1 is that inspection, machine-checked, including
the induction over the chain walk's fuel.
-/

namespace SeLe4n.Kernel

open SeLe4n
open SeLe4n.Model
open SeLe4n.Kernel.Architecture
open SeLe4n.Kernel.Concurrency

-- ============================================================================
-- §1  The priority-inheritance walk cannot make a thread runnable
-- ============================================================================

/-- The priority boost migrates a run-queue *bucket*; it never admits a thread
the queue did not already hold.  The migration arm is guarded on
`tid ∈ runQueueOnCore c`, so a thread outside the queue is outside it after —
including the boosted thread itself. -/
theorem updatePipBoostOnCore_not_mem_of_not_mem (st : SystemState) (c c' : CoreId)
    (tid other : SeLe4n.ThreadId)
    (h : other ∉ st.scheduler.runQueueOnCore c') :
    other ∉ (PriorityInheritance.updatePipBoostOnCore st c tid).scheduler.runQueueOnCore c' := by
  simp only [PriorityInheritance.updatePipBoostOnCore]
  split
  · split
    · exact h
    · split
      · rename_i _ _ _ _ hMem
        split
        · by_cases hcc : c = c'
          · subst hcc
            simp only [SchedulerState.setRunQueueOnCore_runQueueOnCore_self]
            intro hIn
            rcases (RunQueue.mem_insert _ tid _ other).mp hIn with hRem | hEq
            · exact h ((RunQueue.mem_remove _ tid other).mp hRem).1
            · exact h (hEq ▸ hMem)
          · simpa only [SchedulerState.setRunQueueOnCore_runQueueOnCore_ne _ c c' _ hcc]
              using h
        · exact h
      · exact h
  · exact h

/-- The boost never writes any core's `current` slot — the lift of
`updatePipBoostOnCore_currentOnCore` to the walk's step. -/
theorem pipBoostWithWake_currentOnCore (st : SystemState) (tid : SeLe4n.ThreadId)
    (ec c' : CoreId) :
    (PriorityInheritance.pipBoostWithWake st tid ec).1.scheduler.currentOnCore c'
      = st.scheduler.currentOnCore c' :=
  PriorityInheritance.updatePipBoostOnCore_currentOnCore st _ c' tid

/-- One walk step admits no new run-queue member. -/
theorem pipBoostWithWake_not_mem_of_not_mem (st : SystemState) (tid other : SeLe4n.ThreadId)
    (ec c' : CoreId) (h : other ∉ st.scheduler.runQueueOnCore c') :
    other ∉ (PriorityInheritance.pipBoostWithWake st tid ec).1.scheduler.runQueueOnCore c' :=
  updatePipBoostOnCore_not_mem_of_not_mem st _ c' tid other h

/-- **The whole chain walk admits no new run-queue member.**  By induction on
the walk's fuel: each link is a `pipBoostWithWake`, and the recursion threads
the boosted state forward. -/
theorem propagatePipChainCrossCore_not_mem_of_not_mem :
    ∀ (fuel : Nat) (st : SystemState) (startTid other : SeLe4n.ThreadId) (ec c' : CoreId),
      other ∉ st.scheduler.runQueueOnCore c' →
      other ∉ (PriorityInheritance.propagatePipChainCrossCore st startTid ec fuel).1.scheduler.runQueueOnCore c'
  | 0, st, startTid, other, ec, c', h => by
      rw [PriorityInheritance.propagatePipChainCrossCore_zero]; exact h
  | n + 1, st, startTid, other, ec, c', h => by
      rw [PriorityInheritance.propagatePipChainCrossCore_step]
      simp only
      have hStep := pipBoostWithWake_not_mem_of_not_mem st startTid other ec c' h
      cases PriorityInheritance.blockingServer st startTid with
      | none => simpa using hStep
      | some nextServer =>
          simpa using propagatePipChainCrossCore_not_mem_of_not_mem n
            (PriorityInheritance.pipBoostWithWake st startTid ec).1 nextServer other ec c' hStep

/-- **The whole chain walk writes no core's `current` slot.** -/
theorem propagatePipChainCrossCore_currentOnCore :
    ∀ (fuel : Nat) (st : SystemState) (startTid : SeLe4n.ThreadId) (ec c' : CoreId),
      (PriorityInheritance.propagatePipChainCrossCore st startTid ec fuel).1.scheduler.currentOnCore c'
        = st.scheduler.currentOnCore c'
  | 0, st, startTid, ec, c' => by
      rw [PriorityInheritance.propagatePipChainCrossCore_zero]
  | n + 1, st, startTid, ec, c' => by
      rw [PriorityInheritance.propagatePipChainCrossCore_step]
      simp only
      cases PriorityInheritance.blockingServer st startTid with
      | none => simpa using pipBoostWithWake_currentOnCore st startTid ec c'
      | some nextServer =>
          have hTail := propagatePipChainCrossCore_currentOnCore n
            (PriorityInheritance.pipBoostWithWake st startTid ec).1 nextServer ec c'
          simp only at hTail ⊢
          rw [hTail]
          exact pipBoostWithWake_currentOnCore st startTid ec c'

-- ============================================================================
-- §2  The Call chain leaves its caller descheduled
-- ============================================================================

/-- Both of `endpointCallOnCore`'s success paths end in
`removeRunnableOnCore … caller executingCore`: the rendezvous arm blocks the
caller `.blockedOnReply`, the queued arm `.blockedOnCall`, and each
deschedules it. -/
theorem endpointCallOnCore_deschedules_caller
    (epId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (executingCore : CoreId) (st st' : SystemState)
    (sgi? : Option (CoreId × SgiKind))
    (hStep : endpointCallOnCore epId caller msg executingCore st = (st', .ok sgi?)) :
    ∃ stPre, st' = removeRunnableOnCore stPre caller executingCore := by
  unfold endpointCallOnCore at hStep
  repeat' split at hStep
  all_goals (try (simp only [] at hStep))
  all_goals (repeat' split at hStep)
  all_goals first
    | exact ⟨_, (congrArg Prod.fst hStep).symm⟩
    | simp_all

/-- WS-RR RR4.19: a caller that completed a cross-core `endpointCallOnCore`
is neither queued on nor current on the core it called from. -/
theorem endpointCallOnCore_caller_not_runnable
    (epId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (executingCore : CoreId) (st st' : SystemState)
    (sgi? : Option (CoreId × SgiKind))
    (hStep : endpointCallOnCore epId caller msg executingCore st = (st', .ok sgi?)) :
    caller ∉ st'.scheduler.runQueueOnCore executingCore ∧
    st'.scheduler.currentOnCore executingCore ≠ some caller := by
  obtain ⟨stPre, rfl⟩ :=
    endpointCallOnCore_deschedules_caller epId caller msg executingCore st st' sgi? hStep
  exact ⟨removeRunnableOnCore_not_mem_self stPre caller executingCore,
         removeRunnableOnCore_currentOnCore_ne_self stPre caller executingCore⟩

/-- A message carrying no capabilities makes the WithCaps leg exactly the
rendezvous: `endpointCallWithCapsOnCore` short-circuits its transfer on
`msg.caps.isEmpty`.  A fault message is such a message
(`faultMessage_caps`), which is why the fault delivery inherits the
rendezvous's descheduling directly. -/
theorem endpointCallWithCapsOnCore_caller_not_runnable
    (epId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (rights : AccessRightSet) (cspaceRoot : SeLe4n.ObjId) (slotBase : SeLe4n.Slot)
    (executingCore : CoreId) (st st' : SystemState)
    (summary : CapTransferSummary) (sgi? : Option (CoreId × SgiKind))
    (hNoCaps : msg.caps.isEmpty = true)
    (hStep : endpointCallWithCapsOnCore epId caller msg rights cspaceRoot slotBase
        executingCore st = (st', .ok (summary, sgi?))) :
    caller ∉ st'.scheduler.runQueueOnCore executingCore ∧
    st'.scheduler.currentOnCore executingCore ≠ some caller := by
  rw [endpointCallWithCapsOnCore_no_caps epId caller msg rights cspaceRoot slotBase
    executingCore st hNoCaps] at hStep
  cases hCall : endpointCallOnCore epId caller
      { msg with capsGranted := rights.mem AccessRight.grant } executingCore st with
  | mk stC res =>
      rw [hCall] at hStep
      simp only at hStep
      cases res with
      | error e => exact absurd (congrArg Prod.snd hStep) (by simp [Except.map])
      | ok sgi =>
          have hEq : stC = st' := congrArg Prod.fst hStep
          subst hEq
          exact endpointCallOnCore_caller_not_runnable epId caller _ executingCore st stC
            sgi hCall

/-- WS-RR RR4.19: **the live `.call` chain leaves its caller descheduled**, for
a message that transfers no capabilities.

The rendezvous deschedules the caller; the donation leg writes no scheduler
slot at all (`applyCallDonationOnCore_runQueue_current_eq`); and the
priority-inheritance walk migrates buckets of threads already queued and
touches no `current` slot (§1).  So the caller comes out of the chain exactly
as the rendezvous left it. -/
theorem endpointCallCrossCoreDispatch_caller_not_runnable
    (epId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (rights : AccessRightSet) (cspaceRoot : SeLe4n.ObjId) (slotBase : SeLe4n.Slot)
    (executingCore : CoreId) (st st' : SystemState)
    (summary : CapTransferSummary) (sgi? : Option (CoreId × SgiKind))
    (hNoCaps : msg.caps.isEmpty = true)
    (hStep : endpointCallCrossCoreDispatch epId caller msg rights cspaceRoot slotBase
        executingCore st = (st', .ok (summary, sgi?))) :
    caller ∉ st'.scheduler.runQueueOnCore executingCore ∧
    st'.scheduler.currentOnCore executingCore ≠ some caller := by
  unfold endpointCallCrossCoreDispatch at hStep
  simp only at hStep
  cases hWc : endpointCallWithCapsOnCore epId caller msg rights cspaceRoot slotBase
      executingCore st with
  | mk stW resW =>
      rw [hWc] at hStep
      cases resW with
      | error e => exact absurd (congrArg Prod.snd hStep) (by simp)
      | ok r =>
          obtain ⟨summaryW, sgiW⟩ := r
          have hW := endpointCallWithCapsOnCore_caller_not_runnable epId caller msg rights
            cspaceRoot slotBase executingCore st stW summaryW sgiW hNoCaps hWc
          simp only at hStep
          -- The donation / PIP tail either returns `stW` unchanged or extends it.
          split at hStep
          · -- a receiver was waiting: the donation + PIP legs run
            rename_i receiverTid _
            split at hStep
            · rename_i callerV receiverV _ _
              split at hStep
              · exact absurd (congrArg Prod.snd hStep) (by simp)
              · rename_i stD hDon
                have hDonSched := applyCallDonationOnCore_runQueue_current_eq stW stD
                  callerV receiverV _ _ executingCore hDon
                have hEq : (PriorityInheritance.propagatePipChainCrossCore stD receiverTid
                    executingCore).1 = st' := congrArg Prod.fst hStep
                subst hEq
                refine ⟨?_, ?_⟩
                · exact propagatePipChainCrossCore_not_mem_of_not_mem _ stD receiverTid
                    caller executingCore executingCore (by rw [hDonSched.1]; exact hW.1)
                · rw [propagatePipChainCrossCore_currentOnCore _ stD receiverTid
                    executingCore executingCore, hDonSched.2]
                  exact hW.2
            · exact absurd (congrArg Prod.snd hStep) (by simp)
          · -- no receiver was waiting: the caller queued, and the tail is the
            -- WithCaps post-state unchanged
            have hEq : stW = st' := congrArg Prod.fst hStep
            exact hEq ▸ hW

-- ============================================================================
-- §3  RR4.19 — the progress theorem
-- ============================================================================

/-- The states from which core `c` can dispatch `tid`: in its run queue, or
already its current thread.  A thread outside both cannot execute on `c`, and
therefore cannot re-execute the instruction it faulted on. -/
def dispatchableOnCore (st : SystemState) (tid : SeLe4n.ThreadId) (c : CoreId) : Prop :=
  tid ∈ st.scheduler.runQueueOnCore c ∨ st.scheduler.currentOnCore c = some tid

/-- WS-RR RR4.19 (**the progress theorem**): after a fault is delivered, the
faulting thread is not dispatchable on the core it faulted on — on **either**
disposition.

Delivered, it is blocked on the handler's endpoint awaiting a reply;
suspended, it is descheduled and `.Inactive`.  There is no third arm and no
error arm, so there is no path on which a faulting thread returns to its
faulting instruction: getting back requires a *later* transition to make it
runnable, and §RR4.14/RR4.15 show the only one that does is the handler's
reply. -/
theorem faultDeliverOnCore_not_dispatchable (st : SystemState)
    (tid : SeLe4n.ThreadId) (f : Fault) (ctx : FaultContext) (c : CoreId) :
    ¬ dispatchableOnCore (faultDeliverOnCore st tid f ctx c).1 tid c := by
  have hNot : tid ∉ (faultDeliverOnCore st tid f ctx c).1.scheduler.runQueueOnCore c ∧
      (faultDeliverOnCore st tid f ctx c).1.scheduler.currentOnCore c ≠ some tid := by
    rcases hRes : resolveFaultHandler st tid with e | tgt
    · simp only [faultDeliverOnCore, hRes, recordPendingFault_scheduler_eq]
      exact faultSuspendOnCore_not_runnable _ tid c
    · rcases hCall : endpointCallCrossCoreDispatch tgt.endpoint tid
          (faultMessage f ctx tgt.cap.badge) tgt.cap.rights tgt.cspaceRoot
          (SeLe4n.Slot.ofNat 0) c st with ⟨stC, res⟩
      cases res with
      | error e =>
          simp only [faultDeliverOnCore, hRes, hCall, recordPendingFault_scheduler_eq]
          exact faultSuspendOnCore_not_runnable _ tid c
      | ok r =>
          obtain ⟨summary, sgi?⟩ := r
          simp only [faultDeliverOnCore, hRes, hCall, recordPendingFault_scheduler_eq,
            Architecture.stageWokenDelivery_scheduler_eq]
          exact endpointCallCrossCoreDispatch_caller_not_runnable tgt.endpoint tid _
            tgt.cap.rights tgt.cspaceRoot (SeLe4n.Slot.ofNat 0) c st stC summary sgi?
            (by rw [faultMessage_caps f ctx tgt.cap.badge]; rfl) hCall
  rintro (hQ | hC)
  · exact hNot.1 hQ
  · exact hNot.2 hC

/-- WS-RR RR4.19: the same statement in the shape the callers use — the two
conjuncts rather than the negated disjunction. -/
theorem faultDeliverOnCore_leaves_thread_not_runnable (st : SystemState)
    (tid : SeLe4n.ThreadId) (f : Fault) (ctx : FaultContext) (c : CoreId) :
    tid ∉ (faultDeliverOnCore st tid f ctx c).1.scheduler.runQueueOnCore c ∧
    (faultDeliverOnCore st tid f ctx c).1.scheduler.currentOnCore c ≠ some tid := by
  have h := faultDeliverOnCore_not_dispatchable st tid f ctx c
  unfold dispatchableOnCore at h
  exact ⟨fun hQ => h (Or.inl hQ), fun hC => h (Or.inr hC)⟩

/-- WS-RR RR4.19/RR4.20: **the flow-checked delivery inherits the progress
guarantee.**

This is the theorem the live entry needs.  `faultEntryStep` calls the
*checked* delivery — the same asymmetry the live syscall path avoids, since
`syscallEntryChecked` gates every endpoint operation — so RR4.19's statement
has to hold of the gated arm, not only of the arm underneath it.  It does,
and for the reason the gate was written that way: a denied flow takes the
RR4.9 suspend, whose `not_runnable` is the same lemma the unresolvable-handler
arm uses.  A policy refusal therefore cannot reintroduce the livelock. -/
theorem faultDeliverOnCoreChecked_not_dispatchable (lctx : LabelingContext)
    (st : SystemState) (tid : SeLe4n.ThreadId) (f : Fault) (ctx : FaultContext)
    (c : CoreId) :
    ¬ dispatchableOnCore (faultDeliverOnCoreChecked lctx st tid f ctx c).1 tid c := by
  unfold dispatchableOnCore faultDeliverOnCoreChecked
  have hSusp : ¬ (tid ∈ (recordPendingFault (faultSuspendOnCore st tid c) tid
        { fault := f, context := ctx }).scheduler.runQueueOnCore c ∨
      (recordPendingFault (faultSuspendOnCore st tid c) tid
        { fault := f, context := ctx }).scheduler.currentOnCore c = some tid) := by
    simp only [recordPendingFault_scheduler_eq]
    rintro (hQ | hC)
    · exact (faultSuspendOnCore_not_runnable st tid c).1 hQ
    · exact (faultSuspendOnCore_not_runnable st tid c).2 hC
  cases hRes : resolveFaultHandler st tid with
  | error e => simpa only [hRes] using hSusp
  | ok tgt =>
      by_cases hGate : endpointFlowGate lctx tgt.endpoint (lctx.threadLabelOf tid)
          (lctx.endpointLabelOf tgt.endpoint) = true
      · simp only [hGate, if_true]
        exact faultDeliverOnCore_not_dispatchable st tid f ctx c
      · simp only [Bool.not_eq_true] at hGate
        simpa only [hRes, hGate, Bool.false_eq_true, if_false] using hSusp

/-- WS-RR RR4.20: the checked delivery's conjunct form, for callers. -/
theorem faultDeliverOnCoreChecked_leaves_thread_not_runnable (lctx : LabelingContext)
    (st : SystemState) (tid : SeLe4n.ThreadId) (f : Fault) (ctx : FaultContext)
    (c : CoreId) :
    tid ∉ (faultDeliverOnCoreChecked lctx st tid f ctx c).1.scheduler.runQueueOnCore c ∧
    (faultDeliverOnCoreChecked lctx st tid f ctx c).1.scheduler.currentOnCore c
      ≠ some tid := by
  have h := faultDeliverOnCoreChecked_not_dispatchable lctx st tid f ctx c
  unfold dispatchableOnCore at h
  exact ⟨fun hQ => h (Or.inl hQ), fun hC => h (Or.inr hC)⟩

end SeLe4n.Kernel
