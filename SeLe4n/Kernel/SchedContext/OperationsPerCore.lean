-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- WS-SM SM8.B: PRODUCTION.  The per-core SchedContext operations.  Enters the
-- production import closure through the live `.schedContextUnbind` dispatch arm
-- (`API.dispatchCapabilityOnly`).

import SeLe4n.Kernel.SchedContext.Operations
import SeLe4n.Kernel.SchedContext.PriorityManagementPerCore
import SeLe4n.Kernel.SchedContext.NotificationLink

/-!
# WS-SM SM8.B — per-core SchedContext operations

`schedContextUnbind` (`SchedContext/Operations.lean`) revokes a thread's
SchedContext, which **demotes it** to its legacy TCB priority.  Its Z5-H1
preemption guard cleared the thread's `current` slot "to force rescheduling",
and PR #861 review round 14 added the requeue that clearing `current` had been
missing.  Neither is a scheduling point:

* `syscallDispatchCrossCoreEntry` performs no local scheduling — it commits the
  verified post-state and fires the *diff-recovered* SGIs;
* `crossCoreSgiBody` deliberately emits nothing for the **executing** core,
  because a local reschedule is supposed to have run inline.

So a thread that unbound its own SchedContext returned to userspace still
executing while the model said its core had no current thread.  Found by
PR #861 review round 15.

The consequence is a **fail-closed rejection**, not misrouting (round 43
corrected this note, which claimed the latter).  The executing core is
threaded from the entry, never re-derived with a `bootCoreId` fallback (the
state-scanning resolver that had one was deleted at `v0.36.46`), and
resolution runs first — `syscallDispatchFromAbi`
reads `currentOnCore` for the *issuing* core and returns `.illegalState` with
the state unmodified when it is empty
(`Platform.FFI.syscallDispatchFromAbi_illegalState_when_no_current`, mounted at
the entry as `SyscallDispatchEntry.vacatedCore_next_syscall_rejected`).  So the
defect is that the core is stranded and its thread's next syscall is refused,
which is bad enough on its own terms and needs no overstating.

`schedContextUnbindOnCore` is the per-core form, built like its siblings
`suspendThreadOnCore` (SM6.E) and `setPriorityOnCore`: it resolves the core
**actually running** the demoted thread from the pre-state (`runningCoreOf?`,
not the queue home — the two agree on committed states only through the
placement invariant, WS-ZA ZA6.3, and SM6.E introduced it when they did not) and
runs the shared preemption seam `priorityRescheduleOnCore`, rescheduling inline
when that core is the executing one and surfacing its `.reschedule` SGI when it
is remote.

Delegating to the scheduler rather than hand-editing `current` is what makes
this correct: `handleRescheduleSgiOnCore` re-selects against the **post-unbind**
priority and switches only if a candidate outranks it (`switchToThreadOnCore`
requeues the outgoing thread through `preemptCurrentOnCore`), so the demoted
thread either keeps its core legitimately or is preempted and queued — never
stranded, and never running a thread the model has forgotten.
-/

namespace SeLe4n.Kernel.SchedContextOps

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId SgiKind bootCoreId)

/-- WS-SM SM8.B: the thread a SchedContext's scheduler effects act on — its
bound thread, read from the pre-state.

Single-sourced here in production because two consumers need it and a second
copy would drift: this module resolves the core to reschedule, and the
information-flow write set `schedContextWriteSet`
(`InformationFlow/NonInterferenceCrossCore.lean`) resolves the core to declare.
Both must name the same thread or the declared bound is not the transition's. -/
def schedContextBoundThread? (st : SystemState) (scObjId : SeLe4n.ObjId) :
    Option SeLe4n.ThreadId :=
  match st.getSchedContext? (SeLe4n.SchedContextId.ofObjId scObjId) with
  | some sc => sc.boundThread
  | none    => none

/-- WS-SM SM8.B: the core actually running the SchedContext's bound thread, if
any — the core whose scheduling decision the unbind invalidates. -/
def schedContextRunningCore? (st : SystemState) (scObjId : SeLe4n.ObjId) :
    Option CoreId :=
  match schedContextBoundThread? st scObjId with
  | some tid => Lifecycle.Suspend.runningCoreOf? st tid
  | none     => none

/-- **WS-ZA ZA5.2**: the compiled `schedContextRunningCore?`, the bound thread
read from the context's code, so no `Option` is built for it. -/
@[inline] def schedContextRunningCoreImpl (st : SystemState) (scObjId : SeLe4n.ObjId) :
    Option CoreId :=
  match st.getSchedContext? (SeLe4n.SchedContextId.ofObjId scObjId) with
  | some sc =>
    match sc.boundThreadCode with
    | 0 => none
    | k + 1 => Lifecycle.Suspend.runningCoreOf? st ⟨k⟩
  | none => none

@[csimp] theorem schedContextRunningCore?_eq_impl :
    @schedContextRunningCore? = @schedContextRunningCoreImpl := by
  funext st scObjId
  unfold schedContextRunningCore? schedContextBoundThread? schedContextRunningCoreImpl
  cases st.getSchedContext? (SeLe4n.SchedContextId.ofObjId scObjId) with
  | none => rfl
  | some sc =>
    have hB : sc.boundThread = SeLe4n.ThreadId.ofOptCode sc.boundThreadCode := rfl
    simp only [hB]
    cases sc.boundThreadCode <;> rfl

/-- WS-SM SM8.B (operation): **unbind a SchedContext, across cores.**

`schedContextUnbind`'s per-core form.  The revocation itself is unchanged — same
authority, same object writes, same home-core requeue — and what is added is the
scheduling point the single-core form never had: the core running the demoted
thread re-runs its scheduler, inline when it is the executing core and via a
`.reschedule` SGI when it is remote.

The running core is resolved from the **pre-state**, before the demotion, so the
transition acts on the placement it observed. -/
def schedContextUnbindOnCore (vScId : SeLe4n.ValidObjId) (executingCore : CoreId)
    (st : SystemState) : Except KernelError (SystemState × Option (CoreId × SgiKind)) :=
  let running? := schedContextRunningCore? st vScId.val
  match schedContextUnbind vScId st with
  | .error e      => .error e
  | .ok ((), st') =>
      SchedContext.PriorityManagement.priorityRescheduleOnCore st' running? executingCore true

/-- WS-SM SM8.B: the per-core wrapper is fail-closed — it rejects exactly what
the single-core transition rejects, and adds no state change on the error path. -/
theorem schedContextUnbindOnCore_error (vScId : SeLe4n.ValidObjId)
    (executingCore : CoreId) (st : SystemState) (e : KernelError)
    (hStep : schedContextUnbind vScId st = .error e) :
    schedContextUnbindOnCore vScId executingCore st = .error e := by
  simp [schedContextUnbindOnCore, hStep]

/-- WS-SM SM8.B: a SchedContext whose bound thread is running **nowhere** needs
no scheduling point, and the wrapper is then exactly the single-core transition:
same state, no SGI.  This is also the single-core bridge — on one core a thread
is current on `bootCoreId` or nowhere, so a syscall entry on the boot core
sees no change of behaviour. -/
theorem schedContextUnbindOnCore_no_running_core (vScId : SeLe4n.ValidObjId)
    (executingCore : CoreId) (st st' : SystemState)
    (hRunning : schedContextRunningCore? st vScId.val = none)
    (hStep : schedContextUnbind vScId st = .ok ((), st')) :
    schedContextUnbindOnCore vScId executingCore st = .ok (st', none) := by
  simp [schedContextUnbindOnCore, hRunning, hStep,
        SchedContext.PriorityManagement.priorityRescheduleOnCore]

/-- WS-SM SM8.B: **every SGI this operation surfaces is a `.reschedule` for a
core other than the executing one**, and that core is genuinely the one running
the demoted thread.  A local preemption is applied inline, never posted. -/
theorem schedContextUnbindOnCore_sgi_shape (vScId : SeLe4n.ValidObjId)
    (executingCore : CoreId) (st st' : SystemState) (c : CoreId) (k : SgiKind)
    (hStep : schedContextUnbindOnCore vScId executingCore st = .ok (st', some (c, k))) :
    k = SgiKind.reschedule ∧ c ≠ executingCore
      ∧ schedContextRunningCore? st vScId.val = some c := by
  unfold schedContextUnbindOnCore at hStep
  simp only [] at hStep
  split at hStep
  · exact absurd hStep (by simp)
  · next u stMid hUnbind =>
    obtain ⟨hk, hne, hTarget⟩ :=
      SchedContext.PriorityManagement.priorityRescheduleOnCore_sgi_shape
        stMid st' _ executingCore c true k hStep
    exact ⟨hk, hne, hTarget⟩

/-- WS-SM SM8.B: the demoted thread's core is **rescheduled, not merely
cleared** — when it is the executing core the handler runs inline, so the
post-state's `current` slot is the scheduler's own decision rather than the
`none` the Z5-H1 guard used to leave behind.

Unconditional again as of PR #861 review round 34.  Round 28 gated this arm on
the context-restore seam and gave the theorem an `hSeam` premise; round 33
showed the gate was wrong here — `schedContextUnbind` clears the executing
core's `current` (the Z5-H1 guard) precisely *in order to* force a reschedule,
so suppressing the tail leaves a core with nothing current, which is the
round-15 defect this scheduling point was added to fix.

A gate is only sound where the state it leaves behind is coherent, which is
why this path was never gated; since WS-BP BP7.6 no scheduling point is. -/
theorem schedContextUnbindOnCore_local_reschedules (vScId : SeLe4n.ValidObjId)
    (executingCore : CoreId) (st stMid st' : SystemState)
    (hRunning : schedContextRunningCore? st vScId.val = some executingCore)
    (hUnbind : schedContextUnbind vScId st = .ok ((), stMid))
    (hStep : schedContextUnbindOnCore vScId executingCore st = .ok (st', none)) :
    handleRescheduleSgiOnCore stMid executingCore = .ok st' := by
  unfold schedContextUnbindOnCore at hStep
  simp only [hRunning, hUnbind,
             SchedContext.PriorityManagement.priorityRescheduleOnCore] at hStep
  simp only [beq_self_eq_true, if_true] at hStep
  split at hStep
  · next st'' h => rw [Except.ok.injEq, Prod.mk.injEq] at hStep; rw [h, hStep.1]
  · exact absurd hStep (by simp)

/-! ## `SchedContext_Unbind` (seL4-MCS `invokeSchedContext_Unbind`)

seL4-MCS refuses the invocation `IllegalOperation` when the context is bound to
the thread the invoking core is running (`decodeSchedContextInvocation`,
`SchedContextUnbind`: `sc->scTcb == ksCurThread`), and otherwise unbinds the
context's thread (`schedContext_unbindAllTCBs`) and its notification
(`schedContext_unbindNtfn`).  A context bound to no thread is unbound from its
notification alone and the invocation succeeds.

The refusal comes first, so the thread unbind never runs on the executing
core's own current thread: the preemption seam of `schedContextUnbindOnCore`
then only ever surfaces a remote core's `.reschedule`, and the compiled perform
below is the single-core unbind's. -/

/-- **seL4-MCS's `SchedContext_Unbind`**, across cores: refused `objectNotFound`
for an absent context and `illegalState` (seL4's `IllegalOperation`) when its
thread is the executing core's current one; a context bound to no thread loses
its notification link alone; otherwise its thread is unbound
(`schedContextUnbindOnCore`), then its notification. -/
def schedContextUnbindAllOnCore (vScId : SeLe4n.ValidObjId) (executingCore : CoreId)
    (st : SystemState) : Except KernelError (SystemState × Option (CoreId × SgiKind)) :=
  match st.getSchedContext? (SeLe4n.SchedContextId.ofObjId vScId.val) with
  | none => .error .objectNotFound
  | some sc =>
    match sc.boundThreadCode with
    | 0 => .ok (unbindSchedContextNotification st (SeLe4n.SchedContextId.ofObjId vScId.val), none)
    | _ + 1 =>
      if schedContextRunningCore? st vScId.val == some executingCore then .error .illegalState
      else
        match schedContextUnbindOnCore vScId executingCore st with
        | .error e => .error e
        | .ok (st', sgi) =>
          .ok (unbindSchedContextNotification st' (SeLe4n.SchedContextId.ofObjId vScId.val), sgi)

/-- **Whether `schedContextUnbindAllOnCore` succeeds**, read before any write. -/
@[inline] def schedContextUnbindAllAdmitted (st : SystemState) (vScId : SeLe4n.ValidObjId)
    (executingCore : CoreId) : Bool :=
  match st.getSchedContext? (SeLe4n.SchedContextId.ofObjId vScId.val) with
  | none => false
  | some sc =>
    match sc.boundThreadCode with
    | 0 => true
    | _ + 1 =>
      !(schedContextRunningCore? st vScId.val == some executingCore) &&
        schedContextUnbindAdmitted st vScId

/-- **The admitted unbind's state**: the single-core unbind (the identity on a
context bound to no thread), then the notification's. -/
@[inline] def schedContextUnbindAllPerform (st : SystemState) (vScId : SeLe4n.ValidObjId) :
    SystemState :=
  unbindSchedContextNotification (schedContextUnbindPerform st vScId)
    (SeLe4n.SchedContextId.ofObjId vScId.val)

/-- The single-core perform on a context bound to no thread is the identity. -/
theorem schedContextUnbindPerform_of_unbound {st : SystemState} {vScId : SeLe4n.ValidObjId}
    {sc : SchedContext} (hS : st.getSchedContext? (SeLe4n.SchedContextId.ofObjId vScId.val) = some sc)
    (h0 : sc.boundThreadCode = 0) : schedContextUnbindPerform st vScId = st := by
  unfold schedContextUnbindPerform
  rw [SystemState.getSchedContextWitnessed?_eq_some hS]
  have hB : sc.boundThread = none := by
    show SeLe4n.ThreadId.ofOptCode sc.boundThreadCode = none
    rw [h0]; rfl
  simp only [hB]

/-- An admitted unbind succeeds with the perform's state. -/
theorem schedContextUnbindAllOnCore_of_admitted (st : SystemState) (vScId : SeLe4n.ValidObjId)
    (executingCore : CoreId) (h : schedContextUnbindAllAdmitted st vScId executingCore = true) :
    ∃ sgi, schedContextUnbindAllOnCore vScId executingCore st =
      .ok (schedContextUnbindAllPerform st vScId, sgi) := by
  unfold schedContextUnbindAllAdmitted at h
  unfold schedContextUnbindAllOnCore schedContextUnbindAllPerform
  cases hS : st.getSchedContext? (SeLe4n.SchedContextId.ofObjId vScId.val) with
  | none => simp [hS] at h
  | some sc =>
    simp only [hS] at h ⊢
    cases hC : sc.boundThreadCode with
    | zero => rw [schedContextUnbindPerform_of_unbound hS hC]; exact ⟨none, rfl⟩
    | succ k =>
      simp only [hC, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
      obtain ⟨hR, hA⟩ := h
      simp only [hR, Bool.false_eq_true, ↓reduceIte]
      unfold schedContextUnbindOnCore
      rw [schedContextUnbind_of_admitted st vScId hA]
      obtain ⟨sgi, hP⟩ := SchedContext.PriorityManagement.priorityRescheduleOnCore_eq_state
        (schedContextUnbindPerform st vScId) (schedContextRunningCore? st vScId.val) executingCore true
      simp only [hP]
      refine ⟨sgi, ?_⟩
      unfold SchedContext.PriorityManagement.priorityRescheduleOnCoreState
      cases hRc : schedContextRunningCore? st vScId.val with
      | none => rfl
      | some rc =>
        rw [hRc] at hR
        have : (rc == executingCore) = false := by
          cases hE : (rc == executingCore)
          · rfl
          · rw [beq_iff_eq] at hE; subst hE; simp at hR
        simp [this]

/-- **The per-core thread unbind off the executing core is the single-core
unbind**: its preemption seam then surfaces at most a remote core's SGI and
writes nothing. -/
theorem schedContextUnbindOnCore_remote {vScId : SeLe4n.ValidObjId} {executingCore : CoreId}
    {st stU : SystemState} {sgi : Option (CoreId × SgiKind)}
    (hR : schedContextRunningCore? st vScId.val ≠ some executingCore)
    (h : schedContextUnbindOnCore vScId executingCore st = .ok (stU, sgi)) :
    schedContextUnbind vScId st = .ok ((), stU) := by
  unfold schedContextUnbindOnCore at h
  simp only [] at h
  split at h
  · cases h
  · rename_i stMid hUn
    rw [hUn]
    unfold SchedContext.PriorityManagement.priorityRescheduleOnCore at h
    simp only [↓reduceIte] at h
    cases hRc : schedContextRunningCore? st vScId.val with
    | none => rw [hRc] at h; cases h; rfl
    | some rc =>
      rw [hRc] at h hR
      have : (rc == executingCore) = false := by
        cases hE : (rc == executingCore)
        · rfl
        · rw [beq_iff_eq] at hE; subst hE; exact absurd rfl hR
      simp only [this, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at h
      rw [h.1]

/-- **What a successful unbind did**: on a context bound to no thread, nothing
before the notification's unbind; otherwise the per-core thread unbind, on a
context whose thread is not the executing core's current one.  Then the
notification's unbind. -/
theorem schedContextUnbindAllOnCore_ok {vScId : SeLe4n.ValidObjId} {executingCore : CoreId}
    {st st' : SystemState} {sgi : Option (CoreId × SgiKind)}
    (h : schedContextUnbindAllOnCore vScId executingCore st = .ok (st', sgi)) :
    ∃ stU, (stU = st ∧ sgi = none ∨
        (schedContextRunningCore? st vScId.val ≠ some executingCore ∧
          schedContextUnbindOnCore vScId executingCore st = .ok (stU, sgi) ∧
          schedContextUnbind vScId st = .ok ((), stU))) ∧
      st' = unbindSchedContextNotification stU (SeLe4n.SchedContextId.ofObjId vScId.val) := by
  unfold schedContextUnbindAllOnCore at h
  cases hS : st.getSchedContext? (SeLe4n.SchedContextId.ofObjId vScId.val) with
  | none => simp [hS] at h
  | some sc =>
    simp only [hS] at h
    cases hC : sc.boundThreadCode with
    | zero =>
      simp only [hC, Except.ok.injEq, Prod.mk.injEq] at h
      exact ⟨st, Or.inl ⟨rfl, h.2.symm⟩, h.1.symm⟩
    | succ k =>
      simp only [hC] at h
      by_cases hR : (schedContextRunningCore? st vScId.val == some executingCore) = true
      · simp [hR] at h
      · simp only [hR, Bool.false_eq_true, ↓reduceIte] at h
        cases hU : schedContextUnbindOnCore vScId executingCore st with
        | error e => simp [hU] at h
        | ok p =>
          obtain ⟨stU, sgiU⟩ := p
          simp only [hU, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨h1, h2⟩ := h
          subst h2
          have hNe : schedContextRunningCore? st vScId.val ≠ some executingCore :=
            fun e => hR (by rw [e]; exact beq_self_eq_true _)
          exact ⟨stU, Or.inr ⟨hNe, rfl, schedContextUnbindOnCore_remote hNe hU⟩, h1.symm⟩

/-- **The unbind never runs the executing core's own reschedule**: seL4-MCS's
refusal of the current thread's context precedes the thread unbind, so every
SGI the unbind surfaces is a remote core's `.reschedule`. -/
theorem schedContextUnbindAllOnCore_refuses_current (vScId : SeLe4n.ValidObjId)
    (executingCore : CoreId) (st : SystemState)
    (hRunning : schedContextRunningCore? st vScId.val = some executingCore) :
    schedContextUnbindAllOnCore vScId executingCore st = .error .illegalState := by
  unfold schedContextUnbindAllOnCore
  have hR' := hRunning
  unfold schedContextRunningCore? schedContextBoundThread? at hR'
  cases hS : st.getSchedContext? (SeLe4n.SchedContextId.ofObjId vScId.val) with
  | none => rw [hS] at hR'; cases hR'
  | some sc =>
    rw [hS] at hR'
    simp only [] at hR' ⊢
    cases hC : sc.boundThreadCode with
    | zero =>
      have hB : sc.boundThread = none := by
        show SeLe4n.ThreadId.ofOptCode sc.boundThreadCode = none
        rw [hC]; rfl
      rw [hB] at hR'; cases hR'
    | succ k => simp [hRunning]

end SeLe4n.Kernel.SchedContextOps
