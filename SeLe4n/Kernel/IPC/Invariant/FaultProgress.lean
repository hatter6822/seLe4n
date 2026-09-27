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
--
-- **WS-RR RR8.12 (Cut 4)**: this section's two frames moved to
-- `SeLe4n/Kernel/Scheduler/PriorityInheritance/Propagate.lean`, beside the walk
-- they are about, and its three `_not_mem_of_not_mem` forms were retired with
-- them: `propagatePipChainCrossCore_mem_runQueueOnCore` is the biconditional,
-- and `updatePipBoostOnCore_mem_runQueueOnCore` (which `Propagate.lean` has
-- carried since WS-RR RR2.6) was already the step-level answer this section had
-- restated one direction of.
--
-- The relocation is this project's *a shared answer must be reachable from
-- every asker* rule rather than tidying.  The suspend pipeline's placement
-- payoff (`suspendThreadOnCore_holder_unplaced` since `v0.35.158`;
-- `suspendThreadOnCore_holder_still_placed` until the reclaim stopped waking the
-- holder, in `IPC/CrossCore/Cancellation.lean`) needs the walk's run-queue and
-- `current` frames, and this module imports `IPC.CrossCore.Fault`, which imports that one
-- — so the second asker could not have reached the answer and would have grown
-- its own.  §2 and §3 below consume the relocated names through the
-- `PriorityInheritance` namespace.
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
    (rights : AccessRightSet) (slotBase : SeLe4n.Slot)
    (executingCore : CoreId) (st st' : SystemState)
    (summary : CapTransferSummary) (sgi? : Option (CoreId × SgiKind))
    (hNoCaps : msg.caps.isEmpty = true)
    (hStep : endpointCallWithCapsOnCore epId caller msg rights slotBase
        executingCore st = (st', .ok (summary, sgi?))) :
    caller ∉ st'.scheduler.runQueueOnCore executingCore ∧
    st'.scheduler.currentOnCore executingCore ≠ some caller := by
  rw [endpointCallWithCapsOnCore_no_caps epId caller msg rights slotBase
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
    (rights : AccessRightSet) (slotBase : SeLe4n.Slot)
    (executingCore : CoreId) (st st' : SystemState)
    (summary : CapTransferSummary) (sgi? : Option (CoreId × SgiKind))
    (hNoCaps : msg.caps.isEmpty = true)
    (hStep : endpointCallCrossCoreDispatch epId caller msg rights slotBase
        executingCore st = (st', .ok (summary, sgi?))) :
    caller ∉ st'.scheduler.runQueueOnCore executingCore ∧
    st'.scheduler.currentOnCore executingCore ≠ some caller := by
  unfold endpointCallCrossCoreDispatch at hStep
  simp only at hStep
  cases hWc : endpointCallWithCapsOnCore epId caller msg rights slotBase
      executingCore st with
  | mk stW resW =>
      rw [hWc] at hStep
      cases resW with
      | error e => exact absurd (congrArg Prod.snd hStep) (by simp)
      | ok r =>
          obtain ⟨summaryW, sgiW⟩ := r
          have hW := endpointCallWithCapsOnCore_caller_not_runnable epId caller msg rights
            slotBase executingCore st stW summaryW sgiW hNoCaps hWc
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
                · rw [PriorityInheritance.propagatePipChainCrossCore_mem_runQueueOnCore _ stD
                    receiverTid caller executingCore executingCore, hDonSched.1]
                  exact hW.1
                · rw [PriorityInheritance.propagatePipChainCrossCore_currentOnCore _ stD receiverTid
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
          (faultMessage f ctx tgt.cap.badge) tgt.cap.rights
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
            tgt.cap.rights (SeLe4n.Slot.ofNat 0) c st stC summary sgi?
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

/-- **WS-BP BP7.6**: the reschedule handler makes no thread dispatchable on its
core except the one it chose, and it chooses from that core's run queue — so a
thread that was not dispatchable there stays so.  The queue's well-formedness is
what ties the chooser's bucket scan to membership
(`chooseThreadEffectiveOnCore_some_mem_runQueueOnCore`). -/
theorem handleRescheduleSgiOnCore_preserves_not_dispatchable
    (st st' : SystemState) (c : CoreId) (u : SeLe4n.ThreadId)
    (hwf : (st.scheduler.runQueueOnCore c).wellFormed)
    (hStep : handleRescheduleSgiOnCore st c = .ok st')
    (h : ¬ dispatchableOnCore st u c) :
    ¬ dispatchableOnCore st' u c := by
  unfold dispatchableOnCore at h ⊢
  have hQ : u ∉ st.scheduler.runQueueOnCore c := fun hm => h (Or.inl hm)
  have hC : st.scheduler.currentOnCore c ≠ some u := fun hc => h (Or.inr hc)
  unfold handleRescheduleSgiOnCore at hStep
  split at hStep
  · exact absurd hStep (by simp)
  · rw [← Except.ok.inj hStep]; exact h
  · split at hStep
    · rename_i tid hChoose _
      have hMem : tid ∈ st.scheduler.runQueueOnCore c :=
        (RunQueue.mem_toList_iff_mem _ tid).mp
          (chooseThreadEffectiveOnCore_some_mem_runQueueOnCore st c tid hwf hChoose)
      have hu : u ≠ tid := fun hEq => hQ (hEq ▸ hMem)
      obtain ⟨hQ', hC'⟩ :=
        switchToThreadOnCore_preserves_not_dispatchable_onCore st st' c tid u hu hStep hQ hC
      rintro (hm | hc)
      · exact hQ' hm
      · exact hC' hc
    · rw [← Except.ok.inj hStep]; exact h

-- ============================================================================
-- §4  WS-BP BP7.6 — the delivery keeps every run queue well-formed
-- ============================================================================
--
-- The reschedule handler above chooses from the executing core's run queue, and
-- ties that choice to membership through the queue's well-formedness.  So the
-- fault entry's progress theorem needs the queue well-formed on the state the
-- delivery LEAVES, and a hypothesis stated there is a statement about a state no
-- caller holds.  This section is what lets it be stated on the pre-state instead:
-- every step of the delivery either leaves the scheduler alone, removes a thread,
-- enqueues one, re-buckets one, or moves replenishments — and each of those keeps
-- every core's queue well-formed.

/-- **WS-BP BP7.6**: every core's run queue satisfies `RunQueue.wellFormed`. -/
def runQueuesWellFormed (s : SchedulerState) : Prop :=
  ∀ c : CoreId, (s.runQueueOnCore c).wellFormed

/-- A removal keeps every core's queue well-formed. -/
theorem runQueuesWellFormed_removeRunnableOnCore (st : SystemState)
    (tid : SeLe4n.ThreadId) (c : CoreId) (h : runQueuesWellFormed st.scheduler) :
    runQueuesWellFormed (removeRunnableOnCore st tid c).scheduler := fun c' =>
  removeRunnableOnCore_preserves_runQueueOnCore_wellFormed st tid c c' (h c')

/-- A wake keeps every core's queue well-formed: it is one insert. -/
theorem runQueuesWellFormed_wakeThread (st : SystemState)
    (tid : SeLe4n.ThreadId) (ec : CoreId) (h : runQueuesWellFormed st.scheduler) :
    runQueuesWellFormed (wakeThread st tid ec).1.scheduler := fun c' => by
  rw [wakeThread_state_eq_enqueue]
  by_cases hc : determineTargetCore st tid = c'
  · subst hc; exact enqueueRunnableOnCore_preserves_runQueueOnCore_wellFormed st _ tid (h _)
  · rw [enqueueRunnableOnCore_runQueueOnCore_ne st _ c' tid hc]; exact h c'

/-- The cross-core call donation keeps every core's queue well-formed: the
rebinding writes no scheduler state and the migration writes no run queue. -/
theorem runQueuesWellFormed_applyCallDonationOnCore
    (st st'' : SystemState) (callerVtid receiverVtid : SeLe4n.ValidThreadId)
    (donorHome doneeHome : CoreId) (h : runQueuesWellFormed st.scheduler)
    (hStep : applyCallDonationOnCore st callerVtid receiverVtid donorHome doneeHome = .ok st'') :
    runQueuesWellFormed st''.scheduler := by
  obtain ⟨st1, hDon, harm⟩ := applyCallDonationOnCore_ok_decompose st st'' callerVtid
    receiverVtid donorHome doneeHome hStep
  have h1 : runQueuesWellFormed st1.scheduler := by
    rw [applyCallDonation_scheduler_eq st callerVtid receiverVtid st1 hDon]; exact h
  rcases harm with ⟨_, hEq⟩ | ⟨scId, _, hEq⟩ <;> subst hEq
  · exact h1
  · intro c'; rw [migrateSchedContextReplenishment_runQueueOnCore]; exact h1 c'

/-- The bare cross-core Call leg keeps every core's queue well-formed. -/
theorem endpointCallOnCore_preserves_runQueuesWellFormed
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (executingCore : CoreId) (st : SystemState) (h : runQueuesWellFormed st.scheduler) :
    runQueuesWellFormed
      (endpointCallOnCore endpointId caller msg executingCore st).1.scheduler := by
  unfold endpointCallOnCore
  by_cases hSz1 : msg.registers.size > maxMessageRegisters
  · simp only [if_pos hSz1]; exact h
  by_cases hSz2 : msg.caps.size > maxExtraCaps
  · simp only [if_neg hSz1, if_pos hSz2]; exact h
  simp only [if_neg hSz1, if_neg hSz2]
  cases hEp : st.getEndpoint? endpointId with
  | none => simp only; split <;> exact h
  | some ep =>
    simp only
    cases hHead : ep.receiveQ.head with
    | none =>
      simp only
      cases hEnq : endpointQueueEnqueue endpointId false caller st with
      | error e => simp only; exact h
      | ok st' =>
        simp only
        have h1 : runQueuesWellFormed st'.scheduler := by
          rw [endpointQueueEnqueue_scheduler_eq endpointId false caller st st' hEnq]; exact h
        cases hMsg : storeTcbIpcStateAndMessage st' caller (.blockedOnCall endpointId) (some msg) with
        | error e => simp only; exact h
        | ok st'' =>
          simp only
          have h2 : runQueuesWellFormed st''.scheduler := by
            rw [storeTcbIpcStateAndMessage_scheduler_eq st' st'' caller _ _ hMsg]; exact h1
          exact runQueuesWellFormed_removeRunnableOnCore st'' caller executingCore h2
    | some headTid =>
      simp only
      cases hPop : endpointQueuePopHead endpointId true st with
      | error e => simp only; exact h
      | ok pair =>
        simp only
        have hPop' : endpointQueuePopHead endpointId true st
            = .ok (pair.1, pair.2.1, pair.2.2) := by rw [hPop]
        have h1 : runQueuesWellFormed pair.2.2.scheduler := by
          rw [endpointQueuePopHead_scheduler_eq endpointId true st pair.2.2 pair.1 hPop']; exact h
        cases hMsg : storeTcbIpcStateAndMessage pair.2.2 pair.1 .ready (some msg) with
        | error e => simp only; exact h
        | ok st2 =>
          simp only
          have h2 : runQueuesWellFormed st2.scheduler := by
            rw [storeTcbIpcStateAndMessage_scheduler_eq pair.2.2 st2 pair.1 _ _ hMsg]; exact h1
          have h3 := runQueuesWellFormed_wakeThread st2 pair.1 executingCore h2
          cases hCS : storeTcbIpcStateAndMessage (wakeThread st2 pair.1 executingCore).1 caller
              (.blockedOnReply endpointId (some pair.1)) none with
          | error e => simp only; exact h
          | ok st4 =>
            simp only
            have h4 : runQueuesWellFormed st4.scheduler := by
              rw [storeTcbIpcStateAndMessage_scheduler_eq _ st4 caller _ _ hCS]; exact h3
            cases hLink : SystemState.linkServerStashedReply caller pair.1 st4 with
            | error e => simp only; exact h
            | ok pL =>
              obtain ⟨_, st5⟩ := pL
              simp only
              have h5 : runQueuesWellFormed st5.scheduler := by
                rw [linkServerStashedReply_scheduler_eq st4 st5 caller pair.1 hLink]; exact h4
              exact runQueuesWellFormed_removeRunnableOnCore st5 caller executingCore h5

/-- ...and the leg with capability transfer: the transfer writes no scheduler. -/
theorem endpointCallWithCapsOnCore_preserves_runQueuesWellFormed
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (endpointRights : AccessRightSet)
    (receiverSlotBase : SeLe4n.Slot) (executingCore : CoreId) (st : SystemState)
    (h : runQueuesWellFormed st.scheduler) :
    runQueuesWellFormed (endpointCallWithCapsOnCore endpointId caller msg
      endpointRights receiverSlotBase executingCore st).1.scheduler := by
  have hBare := endpointCallOnCore_preserves_runQueuesWellFormed endpointId caller
    { msg with capsGranted := endpointRights.mem AccessRight.grant } executingCore st h
  unfold endpointCallWithCapsOnCore
  cases hCall : endpointCallOnCore endpointId caller
      { msg with capsGranted := endpointRights.mem AccessRight.grant } executingCore st with
  | mk stCall res =>
    rw [hCall] at hBare
    cases res with
    | error e => exact hBare
    | ok sgi =>
      simp only
      cases hEp : st.getEndpoint? endpointId with
      | none => simp only; split <;> exact hBare
      | some ep =>
        simp only
        cases hHead : ep.receiveQ.head with
        | none => simp only; split <;> exact hBare
        | some receiverId =>
          simp only
          split
          · exact hBare
          · cases hRoot : lookupCspaceRoot stCall receiverId with
            | none => exact hBare
            | some recvRoot =>
              simp only
              cases hUnwrap : ipcUnwrapCaps
                  { msg with capsGranted := endpointRights.mem AccessRight.grant }
                  recvRoot receiverSlotBase
                  (endpointRights.mem AccessRight.grant) stCall with
              | error e => exact hBare
              | ok pair =>
                obtain ⟨summary, stFinal⟩ := pair
                simp only
                rw [ipcUnwrapCaps_preserves_scheduler _ recvRoot receiverSlotBase _ stCall
                  stFinal summary hUnwrap]
                exact hBare

/-- ...and the whole live `.call` chain: leg, donation, chain walk. -/
theorem endpointCallCrossCoreDispatch_preserves_runQueuesWellFormed
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (endpointRights : AccessRightSet)
    (receiverSlotBase : SeLe4n.Slot) (executingCore : CoreId) (st : SystemState)
    (h : runQueuesWellFormed st.scheduler) :
    runQueuesWellFormed (endpointCallCrossCoreDispatch endpointId caller msg
      endpointRights receiverSlotBase executingCore st).1.scheduler := by
  have hWc := endpointCallWithCapsOnCore_preserves_runQueuesWellFormed endpointId caller
    msg endpointRights receiverSlotBase executingCore st h
  unfold endpointCallCrossCoreDispatch
  cases hWcEq : endpointCallWithCapsOnCore endpointId caller msg endpointRights
      receiverSlotBase executingCore st with
  | mk stW resW =>
      rw [hWcEq] at hWc
      simp only at hWc ⊢
      cases resW with
      | error e => exact hWc
      | ok r =>
          obtain ⟨summaryW, sgiW⟩ := r
          simp only
          split
          · split
            · split
              · exact hWc
              · rename_i stD hDon
                intro c'
                exact PriorityInheritance.propagatePipChainCrossCore_preserves_runQueueOnCore_wellFormed
                  _ _ _ _ c'
                  (runQueuesWellFormed_applyCallDonationOnCore _ _ _ _ _ _ hWc hDon c')
            · exact hWc
          · exact hWc

/-- **WS-BP BP7.6**: the fault delivery keeps every core's run queue well-formed,
on both dispositions. -/
theorem faultDeliverOnCore_preserves_runQueuesWellFormed (st : SystemState)
    (tid : SeLe4n.ThreadId) (f : Fault) (ctx : FaultContext) (executingCore : CoreId)
    (h : runQueuesWellFormed st.scheduler) :
    runQueuesWellFormed (faultDeliverOnCore st tid f ctx executingCore).1.scheduler := by
  have hFail : ∀ tf : ThreadFault, runQueuesWellFormed
      (recordPendingFault (faultSuspendOnCore st tid executingCore) tid tf).scheduler := by
    intro tf
    rw [recordPendingFault_scheduler_eq, faultSuspendOnCore_scheduler_eq]
    exact runQueuesWellFormed_removeRunnableOnCore st tid executingCore h
  unfold faultDeliverOnCore
  cases hRes : resolveFaultHandler st tid with
  | error e => exact hFail _
  | ok tgt =>
      simp only
      cases hCall : endpointCallCrossCoreDispatch tgt.endpoint tid
          (faultMessage f ctx tgt.cap.badge) tgt.cap.rights
          (SeLe4n.Slot.ofNat 0) executingCore st with
      | mk stC resC =>
          have hC := endpointCallCrossCoreDispatch_preserves_runQueuesWellFormed
            tgt.endpoint tid (faultMessage f ctx tgt.cap.badge) tgt.cap.rights
            (SeLe4n.Slot.ofNat 0) executingCore st h
          rw [hCall] at hC
          simp only at hC
          cases resC with
          | error e => exact hFail _
          | ok r =>
              obtain ⟨summary, sgi?⟩ := r
              simp only
              rw [recordPendingFault_scheduler_eq, Architecture.stageWokenDelivery_scheduler_eq]
              exact hC

/-- **WS-BP BP7.6**: ...and the flow-checked delivery the fault entries run. -/
theorem faultDeliverOnCoreChecked_preserves_runQueuesWellFormed (lctx : LabelingContext)
    (st : SystemState) (tid : SeLe4n.ThreadId) (f : Fault) (ctx : FaultContext)
    (c : CoreId) (h : runQueuesWellFormed st.scheduler) :
    runQueuesWellFormed (faultDeliverOnCoreChecked lctx st tid f ctx c).1.scheduler := by
  have hSusp : runQueuesWellFormed (recordPendingFault (faultSuspendOnCore st tid c) tid
      { fault := f, context := ctx }).scheduler := by
    rw [recordPendingFault_scheduler_eq, faultSuspendOnCore_scheduler_eq]
    exact runQueuesWellFormed_removeRunnableOnCore st tid c h
  unfold faultDeliverOnCoreChecked
  cases hRes : resolveFaultHandler st tid with
  | error e => simpa only [hRes] using hSusp
  | ok tgt =>
      by_cases hGate : endpointFlowGate lctx tgt.endpoint (lctx.threadLabelOf tid)
          (lctx.endpointLabelOf tgt.endpoint) = true
      · simp only [hGate, if_true]
        exact faultDeliverOnCore_preserves_runQueuesWellFormed st tid f ctx c h
      · simp only [Bool.not_eq_true] at hGate
        simpa only [hRes, hGate, Bool.false_eq_true, if_false] using hSusp

end SeLe4n.Kernel
