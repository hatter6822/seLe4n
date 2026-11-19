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
SchedContext, which **demotes it** to its legacy TCB priority, and its Z5-H1
preemption guard clears the thread's `current` slot.  Neither is a scheduling
point: `syscallDispatchCrossCoreEntry` performs no local scheduling, and
`crossCoreSgiBody` emits nothing for the executing core (PR #861 review rounds
14, 15 and 43 traced the stranded core this once left; the executing core is
threaded from the entry, never re-derived).

`schedContextUnbindOnCore` is the per-core form: it resolves the core
**actually running** the demoted thread from the pre-state (`runningCoreOf?`,
not the queue home), refuses the context when that core is the executing one
(seL4-MCS's `IllegalOperation` for `sc->scTcb == ksCurThread`), and otherwise
surfaces a `.reschedule` SGI to the remote core running the thread.

The live `.schedContextUnbind` arm runs `schedContextUnbindAllOnCore`, seL4-MCS's
`invokeSchedContext_Unbind`: it refuses the context of the executing core's own
current thread (`.illegalState`, through `schedContextUnbindOnCore`), so the
thread unbind it runs never reschedules locally and its compiled perform is the
single-core unbind; it then unbinds the
context's notification (`schedContext_unbindNtfn`,
`unbindSchedContextNotification`).  A context bound to no thread has only its
notification unbound.
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

/-- **Whether the context's bound thread is the current thread of `core`**:
`schedContextRunningCore? st scObjId = some core`, asked without building the
`some core` the comparison would otherwise box (a kernel entry allocates
nothing; the unbind's decode check asks this on every call). -/
@[inline] def schedContextRunsOn (st : SystemState) (scObjId : SeLe4n.ObjId)
    (core : CoreId) : Bool :=
  match schedContextRunningCore? st scObjId with
  | some rc => rc == core
  | none => false

theorem schedContextRunsOn_iff {st : SystemState} {scObjId : SeLe4n.ObjId} {core : CoreId} :
    schedContextRunsOn st scObjId core = true ↔ schedContextRunningCore? st scObjId = some core := by
  unfold schedContextRunsOn
  cases schedContextRunningCore? st scObjId <;> simp

/-- WS-SM SM8.B (operation): **unbind a SchedContext's thread, across cores.**

`schedContextUnbind`'s per-core form, seL4-MCS's thread half of
`invokeSchedContext_Unbind` behind its decode check.  A context whose thread the
executing core is running is refused `.illegalState` (seL4's `IllegalOperation`
for `sc->scTcb == ksCurThread`), so the unbind never strands the executing core;
otherwise the revocation is the single-core one — same authority, same object
writes, same home-core requeue — and the core running the demoted thread, which
is then a remote one, is surfaced as a `.reschedule` SGI so it re-runs its
scheduler.

The running core is resolved from the **pre-state**, before the demotion, so the
transition acts on the placement it observed. -/
def schedContextUnbindOnCore (vScId : SeLe4n.ValidObjId) (executingCore : CoreId)
    (st : SystemState) : Except KernelError (SystemState × Option (CoreId × SgiKind)) :=
  if schedContextRunsOn st vScId.val executingCore then .error .illegalState
  else
    match schedContextUnbind vScId st with
    | .error e      => .error e
    | .ok ((), st') =>
        match schedContextRunningCore? st vScId.val with
        | some rc => .ok (st', some (rc, SgiKind.reschedule))
        | none => .ok (st', none)

/-- **What a successful per-core thread unbind did**: its context's thread is
not the executing core's current one, its state is the single-core unbind's,
and its SGI is the running core's `.reschedule`, if any. -/
theorem schedContextUnbindOnCore_ok {vScId : SeLe4n.ValidObjId} {executingCore : CoreId}
    {st st' : SystemState} {sgi : Option (CoreId × SgiKind)}
    (h : schedContextUnbindOnCore vScId executingCore st = .ok (st', sgi)) :
    schedContextRunningCore? st vScId.val ≠ some executingCore ∧
      schedContextUnbind vScId st = .ok ((), st') ∧
      sgi = (match schedContextRunningCore? st vScId.val with
        | some rc => some (rc, SgiKind.reschedule)
        | none => none) := by
  unfold schedContextUnbindOnCore at h
  by_cases hR : schedContextRunsOn st vScId.val executingCore = true
  · simp [hR] at h
  · simp only [hR, Bool.false_eq_true, ↓reduceIte] at h
    refine ⟨fun e => hR (schedContextRunsOn_iff.mpr e), ?_⟩
    cases hU : schedContextUnbind vScId st with
    | error e => rw [hU] at h; cases h
    | ok p =>
      obtain ⟨⟨⟩, stU⟩ := p
      rw [hU] at h
      simp only [] at h
      cases hRc : schedContextRunningCore? st vScId.val with
      | none =>
        rw [hRc] at h; simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨h1, h2⟩ := h; subst h1; subst h2; exact ⟨rfl, rfl⟩
      | some rc =>
        rw [hRc] at h; simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨h1, h2⟩ := h; subst h1; subst h2; exact ⟨rfl, rfl⟩

/-- WS-SM SM8.B: the per-core wrapper is fail-closed — it rejects what the
single-core transition rejects, and adds no state change on the error path. -/
theorem schedContextUnbindOnCore_error (vScId : SeLe4n.ValidObjId)
    (executingCore : CoreId) (st : SystemState) (e : KernelError)
    (hStep : schedContextUnbind vScId st = .error e) :
    ∃ e', schedContextUnbindOnCore vScId executingCore st = .error e' := by
  unfold schedContextUnbindOnCore
  split
  · exact ⟨_, rfl⟩
  · rw [hStep]; exact ⟨e, rfl⟩

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
  simp [schedContextUnbindOnCore, schedContextRunsOn, hRunning, hStep]

/-- WS-SM SM8.B: **every SGI this operation surfaces is a `.reschedule` for a
core other than the executing one**, and that core is genuinely the one running
the demoted thread.  The executing core's own current thread is refused, so no
local preemption exists to apply. -/
theorem schedContextUnbindOnCore_sgi_shape (vScId : SeLe4n.ValidObjId)
    (executingCore : CoreId) (st st' : SystemState) (c : CoreId) (k : SgiKind)
    (hStep : schedContextUnbindOnCore vScId executingCore st = .ok (st', some (c, k))) :
    k = SgiKind.reschedule ∧ c ≠ executingCore
      ∧ schedContextRunningCore? st vScId.val = some c := by
  obtain ⟨hNe, _, hS⟩ := schedContextUnbindOnCore_ok hStep
  cases hRc : schedContextRunningCore? st vScId.val with
  | none => rw [hRc] at hS; cases hS
  | some rc =>
    rw [hRc] at hS hNe
    simp only [Option.some.injEq, Prod.mk.injEq] at hS
    obtain ⟨h1, h2⟩ := hS
    subst h1; subst h2
    exact ⟨rfl, fun e => hNe (by rw [e]), rfl⟩

/-- **The per-core thread unbind refuses the executing core's own current
thread's context**, before any write. -/
theorem schedContextUnbindOnCore_refuses_current (vScId : SeLe4n.ValidObjId)
    (executingCore : CoreId) (st : SystemState)
    (hRunning : schedContextRunningCore? st vScId.val = some executingCore) :
    schedContextUnbindOnCore vScId executingCore st = .error .illegalState := by
  simp [schedContextUnbindOnCore, schedContextRunsOn_iff.mpr hRunning]

/-! ## `SchedContext_Unbind` (seL4-MCS `invokeSchedContext_Unbind`)

seL4-MCS refuses the invocation `IllegalOperation` when the context is bound to
the thread the invoking core is running (`decodeSchedContextInvocation`,
`SchedContextUnbind`: `sc->scTcb == ksCurThread`), and otherwise unbinds the
context's thread (`schedContext_unbindAllTCBs`) and its notification
(`schedContext_unbindNtfn`).  A context bound to no thread is unbound from its
notification alone and the invocation succeeds.

The refusal is the per-core thread unbind's own (`schedContextUnbindOnCore`), so
the thread unbind never runs on the executing core's own current thread: it
only ever surfaces a remote core's `.reschedule`, and the compiled perform
below is the single-core unbind's. -/

/-- **seL4-MCS's `SchedContext_Unbind`**, across cores: refused `objectNotFound`
for an absent context; a context bound to no thread loses its notification link
alone; otherwise its thread is unbound (`schedContextUnbindOnCore`, which
refuses `illegalState` — seL4's `IllegalOperation` — when that thread is the
executing core's current one), then its notification. -/
def schedContextUnbindAllOnCore (vScId : SeLe4n.ValidObjId) (executingCore : CoreId)
    (st : SystemState) : Except KernelError (SystemState × Option (CoreId × SgiKind)) :=
  match st.getSchedContext? (SeLe4n.SchedContextId.ofObjId vScId.val) with
  | none => .error .objectNotFound
  | some sc =>
    match sc.boundThreadCode with
    | 0 => .ok (unbindSchedContextNotification st (SeLe4n.SchedContextId.ofObjId vScId.val), none)
    | _ + 1 =>
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
      !schedContextRunsOn st vScId.val executingCore &&
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
      unfold schedContextUnbindOnCore
      simp only [hR, Bool.false_eq_true, ↓reduceIte]
      rw [schedContextUnbind_of_admitted st vScId hA]
      cases schedContextRunningCore? st vScId.val with
      | none => exact ⟨none, rfl⟩
      | some rc => exact ⟨_, rfl⟩

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
      cases hU : schedContextUnbindOnCore vScId executingCore st with
      | error e => simp [hU] at h
      | ok p =>
        obtain ⟨stU, sgiU⟩ := p
        simp only [hU, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨h1, h2⟩ := h
        subst h2
        obtain ⟨hNe, hUn, _⟩ := schedContextUnbindOnCore_ok hU
        exact ⟨stU, Or.inr ⟨hNe, rfl, hUn⟩, h1.symm⟩

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
    | succ k => simp only [schedContextUnbindOnCore_refuses_current vScId executingCore st hRunning]

end SeLe4n.Kernel.SchedContextOps
