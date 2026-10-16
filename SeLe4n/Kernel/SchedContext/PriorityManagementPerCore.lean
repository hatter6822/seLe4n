-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- WS-SM SM8.B: PRODUCTION.  The per-core priority-control transitions.  Enters
-- the production import closure through the live `.tcbSetPriority` /
-- `.tcbSetMCPriority` dispatch arms (`API.dispatchCapabilityOnly`).

import SeLe4n.Kernel.SchedContext.PriorityManagement
import SeLe4n.Kernel.Lifecycle.Suspend

/-!
# WS-SM SM8.B — per-core priority control

`setPriorityOp` and `setMCPriorityOp` (`SchedContext/PriorityManagement.lean`)
are the single-core priority-control transitions, and **both were boot-pinned in
two places**:

* the run-queue **bucket migration** read and wrote `runQueueOnCore bootCoreId`,
  so for a thread queued on a secondary core the membership test failed and the
  migration was a silent no-op — the priority field changed while the run
  queue's cached band did not, leaving the scheduler dispatching the thread at
  its **old** priority indefinitely (a demotion that never takes effect; the
  PIP-inversion case `migrateRunQueueBucket` exists to prevent, one core over);
* the **preemption check** read `currentOnCore bootCoreId`, so demoting a thread
  running on a secondary core never rescheduled that core.

`setPriorityOnCore` / `setMCPriorityOnCore` are the per-core forms, built like
their SM6.E sibling `suspendThreadOnCore`: the bucket migrates on the target's
**home** core (`determineTargetCore`), and the preemption gate is keyed on the
core that is **actually running** the target (`runningCoreOf?`, the SM6.E
review-4 resolution — an unbound thread can be current on a secondary core while
its home is the boot core), running inline when that is the executing core and
surfacing a `.reschedule` SGI when it is remote.

Every authority check, priority-source update and capping rule is shared with
the single-core transitions, so what changes is *where* the effects land.
-/

namespace SeLe4n.Kernel.SchedContext.PriorityManagement

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId SgiKind bootCoreId)

/-- WS-SM SM8.B: the priority ops' preemption seam — the local/remote reschedule
decision, factored out so the SGI discipline is provable arm-by-arm.

* the target is not running anywhere: nothing to preempt;
* it is running on the **executing** core: reschedule inline, surface nothing;
* it is running on a **remote** core: surface that core's `.reschedule` SGI.

A raise never preempts (`shouldPreempt = false` at the call sites), so this fires
only where the target may have lost the core it holds. -/
def priorityRescheduleOnCore (st : SystemState) (running? : Option CoreId)
    (executingCore : CoreId) (shouldPreempt : Bool) :
    Except KernelError (SystemState × Option (CoreId × SgiKind)) :=
  if shouldPreempt then
    match running? with
    | some rc =>
        if rc == executingCore then
          match handleRescheduleSgiOnCore st executingCore with
          | .ok st' => .ok (st', none)
          | .error e => .error e
        else .ok (st, some (rc, SgiKind.reschedule))
    | none => .ok (st, none)
  else .ok (st, none)

/-- **WS-ZA ZA5.2**: the seam's state, which every arm has — the local
reschedule never refuses (`handleRescheduleSgiOnCore_eq_state`), so the seam
never does either (`priorityRescheduleOnCore_eq_state`). -/
@[inline] def priorityRescheduleOnCoreState (st : SystemState) (running? : Option CoreId)
    (executingCore : CoreId) (shouldPreempt : Bool) : SystemState :=
  if shouldPreempt then
    match running? with
    | some rc => if rc == executingCore then handleRescheduleOnCoreState st executingCore else st
    | none => st
  else st

theorem priorityRescheduleOnCore_eq_state (st : SystemState) (running? : Option CoreId)
    (executingCore : CoreId) (shouldPreempt : Bool) :
    ∃ sgi, priorityRescheduleOnCore st running? executingCore shouldPreempt =
      .ok (priorityRescheduleOnCoreState st running? executingCore shouldPreempt, sgi) := by
  unfold priorityRescheduleOnCore priorityRescheduleOnCoreState
  by_cases hP : shouldPreempt = true
  · simp only [hP, ↓reduceIte]
    cases running? with
    | none => exact ⟨none, rfl⟩
    | some rc =>
      by_cases hE : (rc == executingCore) = true
      · simp only [hE, ↓reduceIte, handleRescheduleSgiOnCore_eq_state]
        exact ⟨none, rfl⟩
      · simp only [hE, Bool.false_eq_true, ↓reduceIte]
        exact ⟨_, rfl⟩
  · simp only [hP, Bool.false_eq_true, ↓reduceIte]
    exact ⟨none, rfl⟩

-- WS-BP BP7.6 (v0.36.19): `priorityRescheduleEnqueueOnly` and
-- `priorityRescheduleOnCoreLive` are retired.  They gated the local preemption on
-- the context-restore seam; the restore is live, so the priority arms run
-- `priorityRescheduleOnCore` itself, and a caller that demotes itself below a
-- queued thread keeps its result (`Architecture.stageCallerReturn_stages_switched_out`).

/-- WS-SM SM8.B: every SGI this seam surfaces is a `.reschedule` for a core other
than the executing one — a local preemption is applied, never posted. -/
theorem priorityRescheduleOnCore_sgi_shape (st st' : SystemState)
    (running? : Option CoreId) (ec c : CoreId) (sp : Bool) (k : SgiKind)
    (h : priorityRescheduleOnCore st running? ec sp = .ok (st', some (c, k))) :
    k = SgiKind.reschedule ∧ c ≠ ec ∧ running? = some c := by
  unfold priorityRescheduleOnCore at h
  split at h
  · split at h
    · next rc _ =>
      split at h
      · -- The local arm returns the handler's `(st', none)`, so a `some` SGI
        -- is absurd.
        repeat' split at h
        all_goals simp_all
      · next hne =>
        rw [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨-, hSgi⟩ := h
        simp only [Option.some.injEq, Prod.mk.injEq] at hSgi
        obtain ⟨hc, hk⟩ := hSgi
        subst hc; subst hk
        exact ⟨rfl, by simpa using hne, rfl⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- WS-SM SM8.B: a raise (or any non-preempting change) leaves the state alone
and surfaces nothing. -/
theorem priorityRescheduleOnCore_no_preempt (st : SystemState)
    (running? : Option CoreId) (ec : CoreId) :
    priorityRescheduleOnCore st running? ec false = .ok (st, none) := by
  simp [priorityRescheduleOnCore]

/-- WS-RR (bind/unbind affinity closure): the preemption seam's **state**
outcomes — the post-state is the input state (the no-preempt, no-target and
remote arms all pass it through) or the executing core's reschedule receiver
ran on it (the local arm).  The decomposition the unbind wrapper's
invariant-preservation theorems case on: everything the seam can do to the
state is one of these two, so a frame for `handleRescheduleSgiOnCore` is a
frame for the whole seam. -/
theorem priorityRescheduleOnCore_state_cases (st st' : SystemState)
    (running? : Option CoreId) (ec : CoreId) (sp : Bool)
    (sgi? : Option (CoreId × SgiKind))
    (h : priorityRescheduleOnCore st running? ec sp = .ok (st', sgi?)) :
    st' = st ∨ handleRescheduleSgiOnCore st ec = .ok st' := by
  unfold priorityRescheduleOnCore at h
  split at h
  · split at h
    · next rc _ =>
      split at h
      · -- local arm: the receiver ran inline
        split at h
        · next stH hH =>
          rw [Except.ok.injEq, Prod.mk.injEq] at h
          exact Or.inr (by rw [hH, h.1])
        · exact absurd h (by simp)
      · -- remote arm: state passed through, SGI surfaced
        rw [Except.ok.injEq, Prod.mk.injEq] at h
        exact Or.inl h.1.symm
    · -- running nowhere: state passed through
      rw [Except.ok.injEq, Prod.mk.injEq] at h
      exact Or.inl h.1.symm
  · -- no preempt requested: state passed through
    rw [Except.ok.injEq, Prod.mk.injEq] at h
    exact Or.inl h.1.symm

/-- The state the priority write leaves before the chain walk keeps the object
store's invariant: the source write is the only object write, and the re-bucket
and the flag touch the scheduler only.  The walk's own preservation needs it. -/
theorem markKeyChangeFor_migrate_updatePrioritySource_objects_invExt (st : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (newPriority : SeLe4n.Priority) (home : CoreId)
    (k : SeLe4n.Priority × SeLe4n.Deadline × SeLe4n.DomainId) (hObjInv : st.objects.invExt) :
    (markKeyChangeFor
      (migrateRunQueueBucketOnCore (updatePrioritySource st tid tcb newPriority) tid newPriority
        home) tid k).objects.invExt := by
  rw [markKeyChangeFor_objects]
  exact migrateRunQueueBucketOnCore_objects_invExt _ _ _ _
    (updatePrioritySource_preserves_objects_invExt st tid tcb newPriority hObjInv)

/-- WS-SM SM8.B: the priority ops' **shared state effect** — write the new value
to whichever field owns the thread's priority, re-bucket it on its home core, and
run the preemption seam on the core actually running it.

Both `setPriorityOnCore` and `setMCPriorityOnCore` perform exactly this once
their own authority and capping rules have decided *what* value to write and
*whether* it can preempt, so naming it removes a four-line duplicate that would
otherwise have to be kept in step by eye — and gives the information-flow layer
one write-set obligation to discharge instead of two copies of it. -/
def applyPriorityChangeOnCore (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (newPriority : SeLe4n.Priority) (executingCore : CoreId) (shouldPreempt : Bool) :
    Except KernelError (SystemState × Option (CoreId × SgiKind)) :=
  priorityRescheduleOnCore
    -- The reschedule-SGI accumulator (KSC-1): after the write and the
    -- re-bucket, flag the target's core exactly when its effective key
    -- changed (a queued target) or dropped (a current one).  Then, when the
    -- target is reply-blocked on a server, re-walk the inheritance chain from
    -- that server, whose boost was computed from the target's old priority.
    (PriorityInheritance.repropagateFromWaiter
      (markKeyChangeFor
        (migrateRunQueueBucketOnCore (updatePrioritySource st tid tcb newPriority) tid newPriority
          (determineTargetCore st tid))
        tid (effectiveSchedParams st tcb))
      tid executingCore st.objectIndex.length)
    (Lifecycle.Suspend.runningCoreOf? st tid) executingCore shouldPreempt

/-- WS-SM SM8.B: a non-preempting change (a raise, or a ceiling that does not
bite) surfaces no SGI. -/
theorem applyPriorityChangeOnCore_no_preempt (st : SystemState) (tid : SeLe4n.ThreadId)
    (tcb : TCB) (newPriority : SeLe4n.Priority) (executingCore : CoreId) :
    applyPriorityChangeOnCore st tid tcb newPriority executingCore false
      = .ok (PriorityInheritance.repropagateFromWaiter
              (markKeyChangeFor
                (migrateRunQueueBucketOnCore (updatePrioritySource st tid tcb newPriority) tid
                  newPriority (determineTargetCore st tid))
                tid (effectiveSchedParams st tcb))
              tid executingCore st.objectIndex.length, none) := by
  simp [applyPriorityChangeOnCore, priorityRescheduleOnCore]

/-- WS-SM SM8.B (operation): **set a thread's priority, across cores.**

`setPriorityOp`'s per-core form.  Identical authority (`validatePriorityAuthority`
against the caller's MCP) and identical priority-source update; the two
boot-pinned effects are replaced:

* the bucket migrates on `determineTargetCore st vTargetTid.val` — the target's
  own home core, which is the queue it is actually in;
* the preemption gate is keyed on `runningCoreOf? st vTargetTid.val`, so a
  demotion of a thread running on a remote core surfaces that core's SGI instead
  of silently doing nothing.

Both cores are resolved from the **pre-state**, before the priority write, so
the transition acts on the placement it observed. -/
def setPriorityOnCore (st : SystemState) (vCallerTid vTargetTid : SeLe4n.ValidThreadId)
    (newPriority : SeLe4n.Priority) (executingCore : CoreId) :
    Except KernelError (SystemState × Option (CoreId × SgiKind)) :=
  match st.getTcb? vCallerTid.val with
  | some callerTcb =>
    match validatePriorityAuthority callerTcb newPriority with
    | .error e => .error e
    | .ok () =>
      match st.getTcb? vTargetTid.val with
      | some targetTcb =>
        let oldPriority := getCurrentPriority st targetTcb
        applyPriorityChangeOnCore st vTargetTid.val targetTcb newPriority executingCore
          (decide (newPriority.val < oldPriority.val))
      | none => .error .invalidArgument
  | none => .error .invalidArgument

/-- WS-SM SM8.B (operation): **set a thread's maximum controlled priority, across
cores.**  `setMCPriorityOp`'s per-core form; the capping rule is unchanged, and
when the cap bites it re-buckets on the target's home core and preempts the core
actually running it. -/
def setMCPriorityOnCore (st : SystemState) (vCallerTid vTargetTid : SeLe4n.ValidThreadId)
    (newMCP : SeLe4n.Priority) (executingCore : CoreId) :
    Except KernelError (SystemState × Option (CoreId × SgiKind)) :=
  match st.getTcb? vCallerTid.val with
  | some callerTcb =>
    match validatePriorityAuthority callerTcb newMCP with
    | .error e => .error e
    | .ok () =>
      match st.getTcbWitnessed? vTargetTid.val with
      | some ⟨targetTcb, hTarget⟩ =>
        let targetTcb' := { targetTcb with maxControlledPriority := newMCP }
        -- `v0.35.71`: the ceiling write is the typed rewrite under the witness
        -- the lookup carries, as in `setMCPriorityOp`.
        let stMcp := st.rewriteObject vTargetTid.val.toObjId (.tcb targetTcb')
          (SystemState.rewriteAdmissible_tcb hTarget targetTcb')
        let currentPrio := getCurrentPriority stMcp targetTcb'
        if currentPrio.val > newMCP.val then
          applyPriorityChangeOnCore stMcp vTargetTid.val targetTcb' newMCP executingCore true
        else
          .ok (stMcp, none)
      | none => .error .invalidArgument
  | none => .error .invalidArgument

/-- WS-ZA ZA5.2: `setMCPriorityOnCore`'s checks for the case that writes only
the ceiling, read before anything is written: both threads are stored TCBs, the
caller may grant `newMCP`, and the target's priority does not exceed it, so no
re-bucket or preemption follows.  When they pass the operation is the in-slot
write (`setMCPriorityOnCore_of_admitted`); a ceiling that bites takes the
general path. -/
@[inline] def setMCPriorityAdmitted (st : SystemState)
    (vCallerTid vTargetTid : SeLe4n.ValidThreadId) (newMCP : SeLe4n.Priority) : Bool :=
  match st.getTcb? vCallerTid.val with
  | none => false
  | some callerTcb =>
    match validatePriorityAuthority callerTcb newMCP with
    | .error _ => false
    | .ok () =>
      match st.getTcb? vTargetTid.val with
      | none => false
      | some targetTcb => !decide (targetTcb.priority.val > newMCP.val)

theorem setMCPriorityOnCore_of_admitted (st : SystemState)
    (vCallerTid vTargetTid : SeLe4n.ValidThreadId) (newMCP : SeLe4n.Priority)
    (executingCore : CoreId) (h : setMCPriorityAdmitted st vCallerTid vTargetTid newMCP = true) :
    setMCPriorityOnCore st vCallerTid vTargetTid newMCP executingCore =
      .ok (st.updateTcb vTargetTid.val (fun t => { t with maxControlledPriority := newMCP }),
        none) := by
  unfold setMCPriorityAdmitted at h
  cases hC : st.getTcb? vCallerTid.val with
  | none => simp [hC] at h
  | some callerTcb =>
    cases hA : validatePriorityAuthority callerTcb newMCP with
    | error e => simp [hC, hA] at h
    | ok u =>
      cases hT : st.getTcb? vTargetTid.val with
      | none => simp [hC, hA, hT] at h
      | some targetTcb =>
        simp only [hC, hA, hT, Bool.not_eq_true', decide_eq_false_iff_not] at h
        unfold setMCPriorityOnCore
        rw [SystemState.getTcbWitnessed?_eq_some hT]
        simp only [hC, hA, getCurrentPriority_eq_priority, h, ↓reduceIte]
        rw [SystemState.rewriteObject_tcb_eq_updateTcb hT
          (fun t => { t with maxControlledPriority := newMCP })]

/-- WS-ZA ZA5.2: the priority change's state effect (`applyPriorityChangeOnCore`
before its preemption seam), with every read of the pre-state — the home core,
the thread's old key as its three parts, the chain walk's fuel — made before the
first write, so neither the state nor the thread's TCB is held across a write
and each is written in its slot (`applyPriorityChangeState_eq`). -/
@[inline] def applyPriorityChangeState (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (newPriority : SeLe4n.Priority) (executingCore : CoreId) : SystemState :=
  let home := determineTargetCore st tid
  let p0 := tcb.boostedPriority
  let d0 := effectiveDeadline st tcb
  let dom0 := tcb.domain
  let fuel := st.objectIndex.length
  let st1 := updatePrioritySource st tid tcb newPriority
  let st2 := migrateRunQueueBucketOnCore st1 tid newPriority home
  let st3 := markKeyChangeParts st2 tid p0 d0 dom0
  PriorityInheritance.repropagateFromWaiter st3 tid executingCore fuel

theorem applyPriorityChangeState_eq (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (newPriority : SeLe4n.Priority) (executingCore : CoreId) :
    applyPriorityChangeState st tid tcb newPriority executingCore =
      PriorityInheritance.repropagateFromWaiter
        (markKeyChangeFor
          (migrateRunQueueBucketOnCore (updatePrioritySource st tid tcb newPriority) tid
            newPriority (determineTargetCore st tid))
          tid (effectiveSchedParams st tcb))
        tid executingCore st.objectIndex.length := by
  rw [markKeyChangeFor_eq_parts, effectiveSchedParams_eq_parts]
  rfl

/-- WS-ZA ZA5.2: `setPriorityOnCore`'s state effect when it is admitted: the
target's TCB read and the change applied (`applyPriorityChangeState`). -/
@[inline] def setPriorityPerform (st : SystemState) (tid : SeLe4n.ThreadId)
    (newPriority : SeLe4n.Priority) (executingCore : CoreId) : SystemState :=
  match st.getTcb? tid with
  | some tcb => applyPriorityChangeState st tid tcb newPriority executingCore
  | none => st

/-- WS-ZA ZA5.2: `setPriorityOnCore`'s checks, read before anything is written:
the caller is a stored TCB whose maximum controlled priority admits the new one,
the target is a stored TCB, and the change does not demote a thread the executing
core runs (that reschedule runs here and may refuse, so it takes the general
path).  When they pass the operation's state is `setPriorityPerform`
(`setPriorityOnCore_of_admitted`). -/
@[inline] def setPriorityAdmitted (st : SystemState)
    (vCallerTid vTargetTid : SeLe4n.ValidThreadId) (newPriority : SeLe4n.Priority)
    (executingCore : CoreId) : Bool :=
  match st.getTcb? vCallerTid.val with
  | none => false
  | some callerTcb =>
    match validatePriorityAuthority callerTcb newPriority with
    | .error _ => false
    | .ok () =>
      match st.getTcb? vTargetTid.val with
      | none => false
      | some targetTcb =>
        !(decide (newPriority.val < (getCurrentPriority st targetTcb).val) &&
          (runningCoreOf? st vTargetTid.val).isEqSome executingCore)

theorem setPriorityOnCore_of_admitted (st : SystemState)
    (vCallerTid vTargetTid : SeLe4n.ValidThreadId) (newPriority : SeLe4n.Priority)
    (executingCore : CoreId)
    (h : setPriorityAdmitted st vCallerTid vTargetTid newPriority executingCore = true) :
    ∃ sgi, setPriorityOnCore st vCallerTid vTargetTid newPriority executingCore =
      .ok (setPriorityPerform st vTargetTid.val newPriority executingCore, sgi) := by
  unfold setPriorityAdmitted at h
  cases hC : st.getTcb? vCallerTid.val with
  | none => simp [hC] at h
  | some callerTcb =>
    cases hA : validatePriorityAuthority callerTcb newPriority with
    | error e => simp [hC, hA] at h
    | ok u =>
      cases hT : st.getTcb? vTargetTid.val with
      | none => simp [hC, hA, hT] at h
      | some targetTcb =>
        simp only [hC, hA, hT] at h
        unfold setPriorityOnCore setPriorityPerform applyPriorityChangeOnCore
        simp only [hC, hA, hT, applyPriorityChangeState_eq]
        unfold priorityRescheduleOnCore
        by_cases hP : decide (newPriority.val < (getCurrentPriority st targetTcb).val) = true
        · rw [if_pos hP]
          rw [hP, Bool.true_and, Bool.not_eq_true'] at h
          cases hR : runningCoreOf? st vTargetTid.val with
          | none => exact ⟨none, rfl⟩
          | some rc =>
            rw [hR] at h
            have hNe : (rc == executingCore) = false := h
            simp only [hNe, Bool.false_eq_true, ↓reduceIte]
            exact ⟨_, rfl⟩
        · rw [if_neg hP]
          exact ⟨none, rfl⟩

/-- WS-SM SM8.B: a rejected authority check leaves the state untouched — both
per-core ops are fail-closed, exactly as their single-core originals. -/
theorem setPriorityOnCore_authority_rejected (st : SystemState)
    (vCallerTid vTargetTid : SeLe4n.ValidThreadId) (newPriority : SeLe4n.Priority)
    (executingCore : CoreId) (callerTcb : TCB) (e : KernelError)
    (hCaller : st.getTcb? vCallerTid.val = some callerTcb)
    (hAuth : validatePriorityAuthority callerTcb newPriority = .error e) :
    setPriorityOnCore st vCallerTid vTargetTid newPriority executingCore = .error e := by
  simp [setPriorityOnCore, hCaller, hAuth]

theorem setMCPriorityOnCore_authority_rejected (st : SystemState)
    (vCallerTid vTargetTid : SeLe4n.ValidThreadId) (newMCP : SeLe4n.Priority)
    (executingCore : CoreId) (callerTcb : TCB) (e : KernelError)
    (hCaller : st.getTcb? vCallerTid.val = some callerTcb)
    (hAuth : validatePriorityAuthority callerTcb newMCP = .error e) :
    setMCPriorityOnCore st vCallerTid vTargetTid newMCP executingCore = .error e := by
  simp [setMCPriorityOnCore, hCaller, hAuth]

/-- WS-SM SM8.B: an absent caller is rejected before anything is read. -/
theorem setPriorityOnCore_no_caller (st : SystemState)
    (vCallerTid vTargetTid : SeLe4n.ValidThreadId) (newPriority : SeLe4n.Priority)
    (executingCore : CoreId) (hCaller : st.getTcb? vCallerTid.val = none) :
    setPriorityOnCore st vCallerTid vTargetTid newPriority executingCore
      = .error .invalidArgument := by
  simp [setPriorityOnCore, hCaller]

/-- WS-SM SM8.B: **a raise surfaces no SGI.**  Preemption is gated on the
priority strictly decreasing, so raising a thread's priority never posts one —
the higher band is picked up by the next scheduling decision on its own core. -/
theorem setPriorityOnCore_raise_no_sgi (st st' : SystemState)
    (vCallerTid vTargetTid : SeLe4n.ValidThreadId) (newPriority : SeLe4n.Priority)
    (executingCore : CoreId) (sgi : Option (CoreId × SgiKind)) (callerTcb targetTcb : TCB)
    (hCaller : st.getTcb? vCallerTid.val = some callerTcb)
    (hAuth : validatePriorityAuthority callerTcb newPriority = .ok ())
    (hTarget : st.getTcb? vTargetTid.val = some targetTcb)
    (hRaise : ¬ (newPriority.val < (getCurrentPriority st targetTcb).val))
    (hStep : setPriorityOnCore st vCallerTid vTargetTid newPriority executingCore
      = .ok (st', sgi)) :
    sgi = none := by
  simp only [setPriorityOnCore, hCaller, hAuth, hTarget] at hStep
  rw [show (decide (newPriority.val < (getCurrentPriority st targetTcb).val)) = false by
        simp [hRaise], applyPriorityChangeOnCore_no_preempt] at hStep
  rw [Except.ok.injEq, Prod.mk.injEq] at hStep
  exact hStep.2.symm

end SeLe4n.Kernel.SchedContext.PriorityManagement
