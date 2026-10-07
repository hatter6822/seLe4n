-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Model.State

/-!
# Per-core slot confinement — the predicate

A transition's per-core writes, as the set of cores whose six observable
scheduler slots (run queue, current thread, active domain, domain time
remaining, domain schedule index, banked registers) it may touch.
`observableSlotsConfinedToCores st st' cs` says every core outside `cs` comes
through unchanged; `observableSlotsConfinedToCore` is its one-core instance
and `observableSlotsAgreeOn` the six slots of one core, compared.

Two consumers read it.  The footprint-coverage bridge
`footprintCoversWrites_of_confined` (`SyscallSchedContainment.lean`) turns a
transition's write set into the run-queue clause of its declared lock
footprint, which is why the predicate is production.  The staged per-core
non-interference stack (`InformationFlow/NonInterferencePerCore.lean`,
`crossCoreNonInterference`) takes it as the per-core premise.  The
per-transition instantiations are the sibling modules under
`SlotConfinement/`, imported together by `SeLe4n.Kernel.SlotConfinement`.

Until WS-LS LS2.3 this was `NonInterferencePerCore` §1/§1b.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId bootCoreId)

/-- SM8.B.1: **the per-core observable slots a step writes are confined to core
`c₀`.**

One field per component of `PerCoreObservableFragment`, each quantified over
the cores the step must *not* touch.  This is the formal content of the plan's
`transitionRunsOnCore τ c'`: a transition "runs on core `c₀`" exactly when
every other core's scheduler slots and register bank come through unchanged.

Note the register clause.  Under SM5.I each core banks its own `RegisterFile`
inside one `MachineState`, so "the transition did not touch another core's
registers" is a genuine obligation rather than a structural fact. -/
structure observableSlotsConfinedToCore (st st' : SystemState) (c₀ : CoreId) : Prop where
  runQueue : ∀ c, c ≠ c₀ →
    st'.scheduler.runQueueOnCore c = st.scheduler.runQueueOnCore c
  current : ∀ c, c ≠ c₀ →
    st'.scheduler.currentOnCore c = st.scheduler.currentOnCore c
  activeDomain : ∀ c, c ≠ c₀ →
    st'.scheduler.activeDomainOnCore c = st.scheduler.activeDomainOnCore c
  domainTimeRemaining : ∀ c, c ≠ c₀ →
    st'.scheduler.domainTimeRemainingOnCore c = st.scheduler.domainTimeRemainingOnCore c
  domainScheduleIndex : ∀ c, c ≠ c₀ →
    st'.scheduler.domainScheduleIndexOnCore c = st.scheduler.domainScheduleIndexOnCore c
  regs : ∀ c, c ≠ c₀ → st'.machine.regsOnCore c = st.machine.regsOnCore c

theorem observableSlotsConfinedToCore_refl (st : SystemState) (c₀ : CoreId) :
    observableSlotsConfinedToCore st st c₀ :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
   fun _ _ => rfl⟩

/-- SM8.B.1: confinement composes — a two-step transition that keeps its writes
on core `c₀` at each step keeps them there overall.  This is what lets the
per-operation lifts in §4 be assembled from the primitive frames rather than
re-derived from each compound operation's definition. -/
theorem observableSlotsConfinedToCore_trans {st stMid st' : SystemState} {c₀ : CoreId}
    (h₁ : observableSlotsConfinedToCore st stMid c₀)
    (h₂ : observableSlotsConfinedToCore stMid st' c₀) :
    observableSlotsConfinedToCore st st' c₀ :=
  ⟨fun c hc => (h₂.runQueue c hc).trans (h₁.runQueue c hc),
   fun c hc => (h₂.current c hc).trans (h₁.current c hc),
   fun c hc => (h₂.activeDomain c hc).trans (h₁.activeDomain c hc),
   fun c hc => (h₂.domainTimeRemaining c hc).trans (h₁.domainTimeRemaining c hc),
   fun c hc => (h₂.domainScheduleIndex c hc).trans (h₁.domainScheduleIndex c hc),
   fun c hc => (h₂.regs c hc).trans (h₁.regs c hc)⟩

/-- KSC-1: a step that leaves the scheduler alone **except the reschedule flags**
and the machine alone is confined to every core — no observable slot is a flag.
The discharge for the scheduling-context binding writers, whose key-change hook
raises flags on the cores the rebound threads sit on. -/
theorem observableSlotsConfinedToCore_of_scheduler_except_reschedule_machine_eq
    {st st' : SystemState} (c₀ : CoreId)
    (hSched : st'.scheduler =
      { st.scheduler with reschedulePending := st'.scheduler.reschedulePending })
    (hMach : st'.machine = st.machine) :
    observableSlotsConfinedToCore st st' c₀ :=
  ⟨fun _ _ => by rw [hSched]; rfl, fun _ _ => by rw [hSched]; rfl,
   fun _ _ => by rw [hSched]; rfl, fun _ _ => by rw [hSched]; rfl,
   fun _ _ => by rw [hSched]; rfl, fun _ _ => by rw [hMach]⟩

/-- SM8.B.1: a step that leaves the scheduler and the machine alone is confined
to **every** core — the discharge every object-store-only operation uses. -/
theorem observableSlotsConfinedToCore_of_scheduler_machine_eq {st st' : SystemState}
    (c₀ : CoreId) (hSched : st'.scheduler = st.scheduler) (hMach : st'.machine = st.machine) :
    observableSlotsConfinedToCore st st' c₀ :=
  observableSlotsConfinedToCore_of_scheduler_except_reschedule_machine_eq c₀
    (by rw [hSched]) hMach

/-- SM8.B.1: a step that leaves the scheduler alone and every core's register
bank alone is confined to every core.  Weaker premise than
`…_of_scheduler_machine_eq`: it admits a machine write that misses the register
banks, which is exactly what a timer advance is. -/
theorem observableSlotsConfinedToCore_of_scheduler_regs_eq {st st' : SystemState}
    (c₀ : CoreId) (hSched : st'.scheduler = st.scheduler)
    (hRegs : ∀ c, st'.machine.regsOnCore c = st.machine.regsOnCore c) :
    observableSlotsConfinedToCore st st' c₀ :=
  ⟨fun _ _ => by rw [hSched], fun _ _ => by rw [hSched], fun _ _ => by rw [hSched],
   fun _ _ => by rw [hSched], fun _ _ => by rw [hSched], fun c _ => hRegs c⟩

/-- SM8.B.1: a step that changes nothing at all is confined to any core — the
discharge the read-only and decode-failure operations use. -/
theorem observableSlotsConfinedToCore_of_eq {st st' : SystemState} (c₀ : CoreId)
    (h : st' = st) : observableSlotsConfinedToCore st st' c₀ := by
  cases h; exact observableSlotsConfinedToCore_refl _ c₀

-- ============================================================================
-- §1a  The single-core agreement primitive
-- ============================================================================
--
-- `crossCoreNonInterference` never uses confinement as such: it uses the six
-- component equalities **at the one core the observer sits on**.  Naming that
-- weaker fact separately is what lets the substantive proof exist once while
-- several different write-set disciplines feed it — confinement to one core
-- (§1), confinement to a *set* of cores (§1b, which the genuinely cross-core
-- SM6 transitions need, since an endpoint call writes the receiver's home core
-- *and* the caller's), and any future discipline that can produce agreement at
-- a given core.

/-- SM8.B.2: **core `c`'s six observable slots agree between two states.**
Exactly the per-core half of the observer's view at core `c`, with no claim
about any other core. -/
structure observableSlotsAgreeOn (st st' : SystemState) (c : CoreId) : Prop where
  runQueue : st'.scheduler.runQueueOnCore c = st.scheduler.runQueueOnCore c
  current : st'.scheduler.currentOnCore c = st.scheduler.currentOnCore c
  activeDomain : st'.scheduler.activeDomainOnCore c = st.scheduler.activeDomainOnCore c
  domainTimeRemaining :
    st'.scheduler.domainTimeRemainingOnCore c = st.scheduler.domainTimeRemainingOnCore c
  domainScheduleIndex :
    st'.scheduler.domainScheduleIndexOnCore c = st.scheduler.domainScheduleIndexOnCore c
  regs : st'.machine.regsOnCore c = st.machine.regsOnCore c

/-- SM8.B.1: confinement to core `c₀` gives agreement at every *other* core. -/
theorem observableSlotsConfinedToCore.agreeOn {st st' : SystemState} {c c₀ : CoreId}
    (h : observableSlotsConfinedToCore st st' c₀) (hne : c ≠ c₀) :
    observableSlotsAgreeOn st st' c :=
  ⟨h.runQueue c hne, h.current c hne, h.activeDomain c hne,
   h.domainTimeRemaining c hne, h.domainScheduleIndex c hne, h.regs c hne⟩

-- ============================================================================
-- §1b  Confinement to a *set* of cores
-- ============================================================================
--
-- The single-core form cannot state what the SM6 cross-core transitions do.
-- `endpointCallOnCore` wakes the receiver on the receiver's home core and
-- deschedules the caller on the caller's own core: two per-core write targets,
-- and in the interesting case two *different* ones.  Widening the single-core
-- predicate to "some core" would be useless (it would exempt every core); the
-- honest generalisation names the write set.

/-- SM8.B.2: **the per-core observable slots a step writes are confined to the
cores in `cs`.**  The `cs = [c₀]` instance is `observableSlotsConfinedToCore`
(`observableSlotsConfinedToCores_singleton_iff`); the genuinely cross-core SM6
transitions instantiate it at two-element lists. -/
structure observableSlotsConfinedToCores (st st' : SystemState) (cs : List CoreId) : Prop where
  runQueue : ∀ c, c ∉ cs →
    st'.scheduler.runQueueOnCore c = st.scheduler.runQueueOnCore c
  current : ∀ c, c ∉ cs →
    st'.scheduler.currentOnCore c = st.scheduler.currentOnCore c
  activeDomain : ∀ c, c ∉ cs →
    st'.scheduler.activeDomainOnCore c = st.scheduler.activeDomainOnCore c
  domainTimeRemaining : ∀ c, c ∉ cs →
    st'.scheduler.domainTimeRemainingOnCore c = st.scheduler.domainTimeRemainingOnCore c
  domainScheduleIndex : ∀ c, c ∉ cs →
    st'.scheduler.domainScheduleIndexOnCore c = st.scheduler.domainScheduleIndexOnCore c
  regs : ∀ c, c ∉ cs → st'.machine.regsOnCore c = st.machine.regsOnCore c

/-- SM8.B.2: set-confinement gives agreement at every core outside the set. -/
theorem observableSlotsConfinedToCores.agreeOn {st st' : SystemState} {c : CoreId}
    {cs : List CoreId} (h : observableSlotsConfinedToCores st st' cs) (hne : c ∉ cs) :
    observableSlotsAgreeOn st st' c :=
  ⟨h.runQueue c hne, h.current c hne, h.activeDomain c hne,
   h.domainTimeRemaining c hne, h.domainScheduleIndex c hne, h.regs c hne⟩

theorem observableSlotsConfinedToCores_refl (st : SystemState) (cs : List CoreId) :
    observableSlotsConfinedToCores st st cs :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
   fun _ _ => rfl⟩

/-- SM8.B.2: the one-core instance is exactly `observableSlotsConfinedToCore`. -/
theorem observableSlotsConfinedToCores_singleton_iff {st st' : SystemState} {c₀ : CoreId} :
    observableSlotsConfinedToCores st st' [c₀] ↔ observableSlotsConfinedToCore st st' c₀ := by
  constructor
  · intro h
    exact ⟨fun c hc => h.runQueue c (by simpa using hc),
      fun c hc => h.current c (by simpa using hc),
      fun c hc => h.activeDomain c (by simpa using hc),
      fun c hc => h.domainTimeRemaining c (by simpa using hc),
      fun c hc => h.domainScheduleIndex c (by simpa using hc),
      fun c hc => h.regs c (by simpa using hc)⟩
  · intro h
    exact ⟨fun c hc => h.runQueue c (by simpa using hc),
      fun c hc => h.current c (by simpa using hc),
      fun c hc => h.activeDomain c (by simpa using hc),
      fun c hc => h.domainTimeRemaining c (by simpa using hc),
      fun c hc => h.domainScheduleIndex c (by simpa using hc),
      fun c hc => h.regs c (by simpa using hc)⟩

theorem observableSlotsConfinedToCores_of_single {st st' : SystemState} {c₀ : CoreId}
    (h : observableSlotsConfinedToCore st st' c₀) :
    observableSlotsConfinedToCores st st' [c₀] :=
  observableSlotsConfinedToCores_singleton_iff.mpr h

/-- SM8.B.2: **widening the declared write set is always sound.**  The direction
that matters: a step confined to `cs` is confined to any superset, so two steps
with different write sets compose into their union. -/
theorem observableSlotsConfinedToCores_mono {st st' : SystemState} {cs cs' : List CoreId}
    (hsub : ∀ c, c ∈ cs → c ∈ cs') (h : observableSlotsConfinedToCores st st' cs) :
    observableSlotsConfinedToCores st st' cs' :=
  ⟨fun c hc => h.runQueue c (fun hm => hc (hsub c hm)),
   fun c hc => h.current c (fun hm => hc (hsub c hm)),
   fun c hc => h.activeDomain c (fun hm => hc (hsub c hm)),
   fun c hc => h.domainTimeRemaining c (fun hm => hc (hsub c hm)),
   fun c hc => h.domainScheduleIndex c (fun hm => hc (hsub c hm)),
   fun c hc => h.regs c (fun hm => hc (hsub c hm))⟩

/-- SM8.B.2: **composition accumulates write sets.**  A two-step transition
writing `cs₁` then `cs₂` writes `cs₁ ++ cs₂` — the rule that assembles a
cross-core IPC transition (store the objects, wake on the receiver's home core,
deschedule on the caller's) from its primitive frames. -/
theorem observableSlotsConfinedToCores_trans {st stMid st' : SystemState}
    {cs₁ cs₂ : List CoreId}
    (h₁ : observableSlotsConfinedToCores st stMid cs₁)
    (h₂ : observableSlotsConfinedToCores stMid st' cs₂) :
    observableSlotsConfinedToCores st st' (cs₁ ++ cs₂) :=
  have hl : ∀ {c : CoreId}, c ∉ cs₁ ++ cs₂ → c ∉ cs₁ :=
    fun hc hm => hc (List.mem_append.mpr (Or.inl hm))
  have hr : ∀ {c : CoreId}, c ∉ cs₁ ++ cs₂ → c ∉ cs₂ :=
    fun hc hm => hc (List.mem_append.mpr (Or.inr hm))
  ⟨fun c hc => (h₂.runQueue c (hr hc)).trans (h₁.runQueue c (hl hc)),
   fun c hc => (h₂.current c (hr hc)).trans (h₁.current c (hl hc)),
   fun c hc => (h₂.activeDomain c (hr hc)).trans (h₁.activeDomain c (hl hc)),
   fun c hc => (h₂.domainTimeRemaining c (hr hc)).trans (h₁.domainTimeRemaining c (hl hc)),
   fun c hc => (h₂.domainScheduleIndex c (hr hc)).trans (h₁.domainScheduleIndex c (hl hc)),
   fun c hc => (h₂.regs c (hr hc)).trans (h₁.regs c (hl hc))⟩

/-- SM8.B.2: a step touching neither the scheduler (the reschedule flags aside:
no observable slot is a flag) nor any register bank is confined to the **empty**
write set — the strongest confinement statement there is, and the one every
object-store-only step in a cross-core pipeline gets. -/
theorem observableSlotsConfinedToCores_nil_of_scheduler_regs_eq {st st' : SystemState}
    (hSched : st'.scheduler =
      { st.scheduler with reschedulePending := st'.scheduler.reschedulePending })
    (hRegs : ∀ c, st'.machine.regsOnCore c = st.machine.regsOnCore c) :
    observableSlotsConfinedToCores st st' [] :=
  ⟨fun _ _ => by rw [hSched]; rfl, fun _ _ => by rw [hSched]; rfl,
   fun _ _ => by rw [hSched]; rfl, fun _ _ => by rw [hSched]; rfl,
   fun _ _ => by rw [hSched]; rfl, fun c _ => hRegs c⟩

/-- KSC-1: the machine-frame reading of the above — the discharge for the
scheduling-context binding writers, whose key-change hook raises flags only. -/
theorem observableSlotsConfinedToCores_nil_of_scheduler_except_reschedule_machine_eq
    {st st' : SystemState}
    (hSched : st'.scheduler =
      { st.scheduler with reschedulePending := st'.scheduler.reschedulePending })
    (hMach : st'.machine = st.machine) :
    observableSlotsConfinedToCores st st' [] :=
  observableSlotsConfinedToCores_nil_of_scheduler_regs_eq hSched (fun _ => by rw [hMach])

theorem observableSlotsConfinedToCores_nil_of_scheduler_machine_eq {st st' : SystemState}
    (hSched : st'.scheduler = st.scheduler) (hMach : st'.machine = st.machine) :
    observableSlotsConfinedToCores st st' [] :=
  observableSlotsConfinedToCores_nil_of_scheduler_except_reschedule_machine_eq
    (by rw [hSched]) hMach

theorem observableSlotsConfinedToCores_of_eq {st st' : SystemState} (cs : List CoreId)
    (h : st' = st) : observableSlotsConfinedToCores st st' cs := by
  cases h; exact observableSlotsConfinedToCores_refl _ cs

/-- SM8.B.2: the empty write set is confined to any write set — the arm every
scheduler-silent branch of a cross-core transition takes.  (A transition whose
*declared* set is `cs` may of course write nothing on some path; declaring the
union is what makes the theorem one statement rather than one per path.) -/
theorem observableSlotsConfinedToCores_widen {st st' : SystemState} {cs : List CoreId}
    (h : observableSlotsConfinedToCores st st' []) :
    observableSlotsConfinedToCores st st' cs :=
  observableSlotsConfinedToCores_mono (fun _ hm => absurd hm (List.not_mem_nil)) h

/-- SM8.B.2: a per-core-silent prefix followed by a step writing exactly `c`
lands inside the singleton `[c]`.  The composition shape every "several object
stores, then one scheduler write" pipeline takes; stated once so those proofs do
not each re-derive `[] ++ [c] = [c]`. -/
theorem observableSlotsConfinedToCores_widen_cons {st stMid st' : SystemState} {c : CoreId}
    (h₁ : observableSlotsConfinedToCores st stMid [])
    (h₂ : observableSlotsConfinedToCores stMid st' [c]) :
    observableSlotsConfinedToCores st st' [c] :=
  observableSlotsConfinedToCores_mono (fun _ hm => hm)
    (List.nil_append [c] ▸ observableSlotsConfinedToCores_trans h₁ h₂)

/-- SM8.B.2: a transition that writes no core at all is confined to *any*
declared set — the arm every fail-closed or wake-free path of a cross-core
transition takes.  A synonym for `_widen` with the argument order the pipeline
proofs read more naturally. -/
theorem observableSlotsConfinedToCores_widen_any {st st' : SystemState} {cs : List CoreId}
    (h : observableSlotsConfinedToCores st st' []) :
    observableSlotsConfinedToCores st st' cs :=
  observableSlotsConfinedToCores_widen h

end SeLe4n.Kernel
