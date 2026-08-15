-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- STATUS: staged for WS-SM SM8.B per-core non-interference
-- (see docs/planning/SMP_INFORMATION_FLOW_PLAN.md §5 SM8.B).

import SeLe4n.Kernel.InformationFlow.ObservableStatePerCore
import SeLe4n.Kernel.InformationFlow.Invariant.Composition
import SeLe4n.Kernel.Concurrency.Locks.WithLockSet
-- The SM6.A/SM6.B cross-core non-interference modules own the `*_machine_eq`
-- frames for the IPC primitives (`storeTcbIpcState{,AndMessage}`,
-- `storeTcbQueueLinks`, `endpointQueue{PopHead,Enqueue}`).  §4 composes them
-- into the per-operation confinement lemmas rather than re-deriving them.
--
-- Every operation lifted in this module is confined to the **boot core**, so
-- every application of §2 here has `c' = bootCoreId`.  The instantiations at
-- transitions that genuinely write a *remote* core live in the companion
-- module `InformationFlow.NonInterferenceCrossCore`, which needs §1b's
-- set-of-cores confinement (an endpoint call writes two cores) and is the
-- reason §1b exists.
import SeLe4n.Kernel.IPC.CrossCore.EndpointCallNiPerCore
import SeLe4n.Kernel.IPC.CrossCore.NotificationSignalNI

/-!
# WS-SM SM8.B — Per-core non-interference

Plan `docs/planning/SMP_INFORMATION_FLOW_PLAN.md` §3.3 / §5 sub-tasks
SM8.B.1 … SM8.B.5, SM8.B.12, SM8.B.13.  SM8.A mounted the observer `(c, L)`
and the state it sees; this module proves that **transitions** leave that view
alone.

## The shape of the argument

`ObservableState.onCore` factors into a **shared** fragment (seven
label-filtered, core-independent components) and a **per-core** fragment (six
components read off core `c`'s scheduler slots and register bank) — and SM8.A's
`ObservableState.ofFragments_eta` makes that factoring a bijection, so proving
both halves unchanged *is* proving the view unchanged.  Every theorem here is
that decomposition applied to a different premise:

* §2 `crossCoreNonInterference` (plan Theorem 3.3.1) — a transition whose
  per-core writes are confined to core `c'` leaves core `c ≠ c'`'s per-core
  fragment untouched *by construction*, so the observer's view moves only if
  the shared fragment moves.
* §3 `nonInterference_perCore` — the existing single-core NI surface
  (`NonInterferenceStep` + `step_preserves_projection`) supplies the shared
  half at *every* core, because the shared fragment of the per-core view **is**
  the shared fragment of the global projection
  (`onCore_sharedFragment_eq_globalProjection`).  The boot core is the global
  projection itself; every other core is §2 at `c' = bootCoreId`.
* §4 lifts all thirty-five `KernelOperation` variants.
* §6 carries the result through the SM3 two-phase-locking bracket.

## On the plan's proof sketch

Plan §3.3 discharges Theorem 3.3.1 from serializability (Corollary 2.1.11):
"c-observable state writes happen only with c's locks held, which c' does not
have".  That argument is not available on the live path — SM3.C.9 still defers
wrapping the `@[export]` bodies in `withLockSet`, and v0.32.142 serialises
kernel entry with one global ticket lock rather than the per-object fine locks.
The theorem is therefore proven from the **frame** premises directly, which
assumes strictly less (no lock discipline at all) and so concludes strictly
more.  §6 supplies the missing direction as a *bridge*: a lock set disjoint
from the observer's visible objects yields exactly the shared-frame premise,
so once SM3.C.9 lands the plan's argument becomes a corollary rather than an
assumption.

Axiom-clean: every declaration depends only on the standard foundational
axioms (`propext` / `Quot.sound` / `Classical.choice`), checked exhaustively.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId bootCoreId)

-- ============================================================================
-- §1  The two frame premises
-- ============================================================================

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

/-- SM8.B.1: a step that leaves the scheduler and the machine alone is confined
to **every** core — the discharge every object-store-only operation uses. -/
theorem observableSlotsConfinedToCore_of_scheduler_machine_eq {st st' : SystemState}
    (c₀ : CoreId) (hSched : st'.scheduler = st.scheduler) (hMach : st'.machine = st.machine) :
    observableSlotsConfinedToCore st st' c₀ :=
  ⟨fun _ _ => by rw [hSched], fun _ _ => by rw [hSched], fun _ _ => by rw [hSched],
   fun _ _ => by rw [hSched], fun _ _ => by rw [hSched], fun _ _ => by rw [hMach]⟩

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

/-- SM8.B.2: a step touching neither the scheduler nor any register bank is
confined to the **empty** write set — the strongest confinement statement there
is, and the one every object-store-only step in a cross-core pipeline gets. -/
theorem observableSlotsConfinedToCores_nil_of_scheduler_regs_eq {st st' : SystemState}
    (hSched : st'.scheduler = st.scheduler)
    (hRegs : ∀ c, st'.machine.regsOnCore c = st.machine.regsOnCore c) :
    observableSlotsConfinedToCores st st' [] :=
  ⟨fun _ _ => by rw [hSched], fun _ _ => by rw [hSched], fun _ _ => by rw [hSched],
   fun _ _ => by rw [hSched], fun _ _ => by rw [hSched], fun c _ => hRegs c⟩

theorem observableSlotsConfinedToCores_nil_of_scheduler_machine_eq {st st' : SystemState}
    (hSched : st'.scheduler = st.scheduler) (hMach : st'.machine = st.machine) :
    observableSlotsConfinedToCores st st' [] :=
  observableSlotsConfinedToCores_nil_of_scheduler_regs_eq hSched (fun _ => by rw [hMach])

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

/-- SM8.B.2: **the shared half of the observer's view is unchanged.**

One field per component of `SharedObservableFragment`.  Stated at the
*projection* level rather than at the state level on purpose: `projectObjects`
and friends already carry the label filter, so a transition that rewrites a
non-observable object satisfies these clauses without any further reasoning —
which is exactly the situation every non-interference hypothesis sets up.
`sharedViewUnchanged_of_globalProjection` and
`sharedViewUnchanged_of_state_frames` are the two constructors callers use. -/
structure sharedViewUnchanged (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState) : Prop where
  objects : projectObjects ctx observer st' = projectObjects ctx observer st
  services : projectServicePresence ctx observer st' = projectServicePresence ctx observer st
  irqHandlers : projectIrqHandlers ctx observer st' = projectIrqHandlers ctx observer st
  objectIndex : projectObjectIndex ctx observer st' = projectObjectIndex ctx observer st
  domainSchedule : projectDomainSchedule ctx observer st' = projectDomainSchedule ctx observer st
  memory : projectMemory ctx observer st' = projectMemory ctx observer st
  serviceRegistry :
    projectServiceRegistry ctx observer st' = projectServiceRegistry ctx observer st

theorem sharedViewUnchanged_refl (ctx : LabelingContext) (observer : IfObserver)
    (st : SystemState) : sharedViewUnchanged ctx observer st st :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem sharedViewUnchanged_trans {ctx : LabelingContext} {observer : IfObserver}
    {st stMid st' : SystemState}
    (h₁ : sharedViewUnchanged ctx observer st stMid)
    (h₂ : sharedViewUnchanged ctx observer stMid st') :
    sharedViewUnchanged ctx observer st st' :=
  ⟨h₂.objects.trans h₁.objects, h₂.services.trans h₁.services,
   h₂.irqHandlers.trans h₁.irqHandlers, h₂.objectIndex.trans h₁.objectIndex,
   h₂.domainSchedule.trans h₁.domainSchedule, h₂.memory.trans h₁.memory,
   h₂.serviceRegistry.trans h₁.serviceRegistry⟩

/-- SM8.B.2 (the constructor the single-core NI surface supplies): preserving
the whole global projection preserves its shared half.

The seven components are read off `projectState` by `congrArg`, which is what
makes `nonInterference_perCore` a corollary of the existing
`step_preserves_projection` rather than a re-proof of it. -/
theorem sharedViewUnchanged_of_globalProjection (ctx : LabelingContext)
    (observer : IfObserver) {st st' : SystemState}
    (h : projectState ctx observer st' = projectState ctx observer st) :
    sharedViewUnchanged ctx observer st st' :=
  ⟨congrArg ObservableState.objects h, congrArg ObservableState.services h,
   congrArg ObservableState.irqHandlers h, congrArg ObservableState.objectIndex h,
   congrArg ObservableState.domainSchedule h, congrArg ObservableState.memory h,
   congrArg ObservableState.serviceRegistry h⟩

/-- SM8.B.2 (the constructor a *state-level* frame supplies): a transition that
leaves every **observable** object alone, and leaves the object index, the
service store, the IRQ table, physical memory and the domain schedule alone,
does not move the shared half of any observer's view.

The `objects` premise is restricted to observable ids deliberately: it is the
plan's "does not mutate any object `o` with `labelOf o ⊑ L`", and it subsumes
the plan's separate "does not signal a notification observable by `(c, L)`"
clause, since signalling a notification writes that notification's object. -/
theorem sharedViewUnchanged_of_state_frames (ctx : LabelingContext) (observer : IfObserver)
    {st st' : SystemState}
    (hObjects : ∀ oid, objectObservable ctx observer oid = true →
      st'.objects[oid]? = st.objects[oid]?)
    (hIndex : st'.objectIndex = st.objectIndex)
    (hServices : st'.services = st.services)
    (hIrq : st'.irqHandlers = st.irqHandlers)
    (hMemory : st'.machine.memory = st.machine.memory)
    (hDomSched : st'.scheduler.domainSchedule = st.scheduler.domainSchedule) :
    sharedViewUnchanged ctx observer st st' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · funext oid
    simp only [projectObjects]
    by_cases hObs : objectObservable ctx observer oid = true
    · rw [if_pos hObs, if_pos hObs, hObjects oid hObs]
    · simp only [Bool.not_eq_true] at hObs
      rw [if_neg (by simp [hObs]), if_neg (by simp [hObs])]
  · funext sid; simp only [projectServicePresence, lookupService]; rw [hServices]
  · funext irq; simp only [projectIrqHandlers]; rw [hIrq]
  · simp only [projectObjectIndex]; rw [hIndex]
  · simp only [projectDomainSchedule]; rw [hDomSched]
  · exact projectMemory_eq_of_memory_eq _ _ _ _ hMemory
  · exact projectServiceRegistry_eq_of_services_eq _ _ _ _ hServices

-- ============================================================================
-- §1b  The per-core view's two fragments, spelled out
-- ============================================================================

/-- Definition-pinning: the shared fragment of the SM4.D per-core projection.
Stated for a general `IfObserver` (SM8.A's `onCore_sharedFragment` is the
`ObservableState.onCore` restatement at `IfObserver.ofLabel L`). -/
@[simp] theorem projectStateOnCore_sharedFragment (ctx : LabelingContext)
    (observer : IfObserver) (st : SystemState) (c : CoreId) :
    (projectStateOnCore ctx observer st c).sharedFragment =
      { objects := projectObjects ctx observer st
        services := projectServicePresence ctx observer st
        irqHandlers := projectIrqHandlers ctx observer st
        objectIndex := projectObjectIndex ctx observer st
        domainSchedule := projectDomainSchedule ctx observer st
        memory := projectMemory ctx observer st
        serviceRegistry := projectServiceRegistry ctx observer st } := rfl

/-- Definition-pinning: the per-core fragment of the SM4.D per-core projection —
every component an `…OnCore c` read, core `c` and no other. -/
@[simp] theorem projectStateOnCore_perCoreFragment (ctx : LabelingContext)
    (observer : IfObserver) (st : SystemState) (c : CoreId) :
    (projectStateOnCore ctx observer st c).perCoreFragment =
      { runnable := projectRunnableOnCore ctx observer st c
        current := projectCurrentOnCore ctx observer st c
        activeDomain := projectActiveDomainOnCore ctx observer st c
        domainTimeRemaining := projectDomainTimeRemainingOnCore ctx observer st c
        domainScheduleIndex := projectDomainScheduleIndexOnCore ctx observer st c
        machineRegs := projectMachineRegsOnCore ctx observer st c } := rfl

-- ============================================================================
-- §2  SM8.B.2 — `crossCoreNonInterference` (plan Theorem 3.3.1)
-- ============================================================================

/-- SM8.B.2 (plan Theorem 3.3.1): **a transition on core `c'` is invisible to an
observer on core `c ≠ c'` unless it moves the shared, label-filtered half of the
view.**

The two premises are the plan's two, restated as frames:

* `hRuns` is `transitionRunsOnCore τ c'` — the transition's per-core writes stay
  on core `c'`;
* `hShared` is `transitionDoesntMutateLabelLeqObjects` **and**
  `transitionDoesntSignalLabelObservableNotification` together, generalised to
  every shared component (signalling a notification writes its object, so the
  plan's second clause is the `objects` field of the first).

The conclusion is the plan's, on the SM4.D per-core projection; the
`ObservableState.onCore` restatement of Definition 3.2.1 is
`crossCoreNonInterference_onCore` below, and the observer-pair form is
`crossCoreNonInterference_observer`.

Proof: SM8.A's field partition is a bijection, so the view is determined by its
two fragments.  `hRuns` gives core `c`'s per-core fragment through the six SM4.D
frame lemmas (each names only core `c`, which `hne` puts outside the written
core); `hShared` gives the shared fragment componentwise. -/
theorem crossCoreNonInterference_of_agreeOn (ctx : LabelingContext) (observer : IfObserver)
    {st st' : SystemState} {c : CoreId}
    (hAgree : observableSlotsAgreeOn st st' c)
    (hShared : sharedViewUnchanged ctx observer st st') :
    projectStateOnCore ctx observer st' c = projectStateOnCore ctx observer st c := by
  refine ObservableState.ext_fragments ?_ ?_
  · simp only [projectStateOnCore_sharedFragment, SharedObservableFragment.mk.injEq]
    exact ⟨hShared.objects, hShared.services, hShared.irqHandlers, hShared.objectIndex,
      hShared.domainSchedule, hShared.memory, hShared.serviceRegistry⟩
  · simp only [projectStateOnCore_perCoreFragment, PerCoreObservableFragment.mk.injEq]
    exact ⟨projectRunnableOnCore_frame _ _ hAgree.runQueue,
      projectCurrentOnCore_frame _ _ hAgree.current,
      projectActiveDomainOnCore_frame _ _ hAgree.activeDomain,
      projectDomainTimeRemainingOnCore_frame _ _ hAgree.domainTimeRemaining,
      projectDomainScheduleIndexOnCore_frame _ _ hAgree.domainScheduleIndex,
      projectMachineRegsOnCore_frame _ _ hAgree.current hAgree.regs⟩

theorem crossCoreNonInterference (ctx : LabelingContext) (observer : IfObserver)
    {st st' : SystemState} {c c' : CoreId}
    (hne : c ≠ c')
    (hRuns : observableSlotsConfinedToCore st st' c')
    (hShared : sharedViewUnchanged ctx observer st st') :
    projectStateOnCore ctx observer st' c = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference_of_agreeOn ctx observer (hRuns.agreeOn hne) hShared

/-- SM8.B.2 (**the genuinely multi-core form**): a transition whose per-core
writes stay within the core set `cs` is invisible to an observer on any core
outside `cs`, unless it moves the shared half.

This is the form the SM6 cross-core transitions satisfy, and the reason §1b
exists: `endpointCallOnCore` writes the receiver's home core *and* the caller's
own core, so no single-core statement covers it.  `NonInterferenceCrossCore`
instantiates this at each cross-core transition with the write set read off the
transition's own definition.

Note what is **not** required: nothing about the *labels* of the threads
involved.  The SM6 per-core NI results are conditional on the woken thread being
non-observable (`wakeThread_preserves_projectionOnCore` takes `hHighThread`);
this says that a wake of even a **fully visible** thread on core `c'` is
invisible on core `c ∉ cs`, because that core's slots did not move.  The label
hypotheses are needed only for the *shared* half. -/
theorem crossCoreNonInterference_ofCores (ctx : LabelingContext) (observer : IfObserver)
    {st st' : SystemState} {c : CoreId} {cs : List CoreId}
    (hne : c ∉ cs)
    (hRuns : observableSlotsConfinedToCores st st' cs)
    (hShared : sharedViewUnchanged ctx observer st st') :
    projectStateOnCore ctx observer st' c = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference_of_agreeOn ctx observer (hRuns.agreeOn hne) hShared

/-- SM8.B.2 (plan Definition 3.2.1 form): the same statement about
`ObservableState.onCore c L`, the observable state the plan's Theorem 3.3.1
names. -/
theorem crossCoreNonInterference_onCore (ctx : LabelingContext) (L : SecurityLabel)
    {st st' : SystemState} {c c' : CoreId}
    (hne : c ≠ c')
    (hRuns : observableSlotsConfinedToCore st st' c')
    (hShared : sharedViewUnchanged ctx (IfObserver.ofLabel L) st st') :
    ObservableState.onCore ctx c L st' = ObservableState.onCore ctx c L st :=
  crossCoreNonInterference ctx (IfObserver.ofLabel L) hne hRuns hShared

/-- SM8.B.2 (observer form): stated for the SM8.A observer value `(c, L)`, so a
caller quantifying over observers has one thing to quantify over. -/
theorem crossCoreNonInterference_observer (ctx : LabelingContext) (o : PerCoreObserver)
    {st st' : SystemState} {c' : CoreId}
    (hne : o.core ≠ c')
    (hRuns : observableSlotsConfinedToCore st st' c')
    (hShared : sharedViewUnchanged ctx o.toIfObserver st st') :
    lowEquivalentForObserver ctx o st' st :=
  crossCoreNonInterference ctx o.toIfObserver hne hRuns hShared

/-- SM8.B.2 (the state-level corollary): the form whose premises can be read off
a transition's definition — the transition writes only core `c'`'s slots, and
every object it rewrites is one the observer cannot see. -/
theorem crossCoreNonInterference_of_state_frames (ctx : LabelingContext)
    (observer : IfObserver) {st st' : SystemState} {c c' : CoreId}
    (hne : c ≠ c')
    (hRuns : observableSlotsConfinedToCore st st' c')
    (hObjects : ∀ oid, objectObservable ctx observer oid = true →
      st'.objects[oid]? = st.objects[oid]?)
    (hIndex : st'.objectIndex = st.objectIndex)
    (hServices : st'.services = st.services)
    (hIrq : st'.irqHandlers = st.irqHandlers)
    (hMemory : st'.machine.memory = st.machine.memory)
    (hDomSched : st'.scheduler.domainSchedule = st.scheduler.domainSchedule) :
    projectStateOnCore ctx observer st' c = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference ctx observer hne hRuns
    (sharedViewUnchanged_of_state_frames ctx observer hObjects hIndex hServices hIrq
      hMemory hDomSched)

-- ============================================================================
-- §3  SM8.B.1 — `nonInterference_perCore` (the single-core surface, generalised)
-- ============================================================================

/-- SM8.B.1 (the reusable core): whole-projection preservation plus boot-core
confinement gives per-core preservation on **every** core.

Factored out of `nonInterference_perCore` because the same two premises are what
the SM3 lock bracket (§6) and the release-grade dispatch bridge (§7) supply —
neither of those is a `NonInterferenceStep`. -/
theorem lowEquivalent_smp_of_projection_and_confinement (ctx : LabelingContext)
    (observer : IfObserver) {st st' : SystemState}
    (hProj : projectState ctx observer st' = projectState ctx observer st)
    (hConfined : observableSlotsConfinedToCore st st' bootCoreId) :
    lowEquivalent_smp ctx observer st' st := by
  intro c
  show projectStateOnCore ctx observer st' c = projectStateOnCore ctx observer st c
  by_cases hc : c = bootCoreId
  · cases hc
    exact hProj
  · exact crossCoreNonInterference ctx observer hc hConfined
      (sharedViewUnchanged_of_globalProjection ctx observer hProj)

/-- SM8.B.2: the shared half of a view is **core-independent**, so per-core
projection equality at *any* single core already pins it.

`sharedViewUnchanged_of_globalProjection` is the `c = bootCoreId` instance.  This
is what lets a transition that only has a per-core projection fact — because it
runs on a secondary core — still supply the shared premise
`crossCoreNonInterference` needs. -/
theorem sharedViewUnchanged_of_projectionOnCore (ctx : LabelingContext)
    (observer : IfObserver) {st st' : SystemState} {c : CoreId}
    (h : projectStateOnCore ctx observer st' c = projectStateOnCore ctx observer st c) :
    sharedViewUnchanged ctx observer st st' := by
  have hFrag : (projectStateOnCore ctx observer st' c).sharedFragment
      = (projectStateOnCore ctx observer st c).sharedFragment := congrArg _ h
  simp only [projectStateOnCore_sharedFragment, SharedObservableFragment.mk.injEq] at hFrag
  exact ⟨hFrag.1, hFrag.2.1, hFrag.2.2.1, hFrag.2.2.2.1, hFrag.2.2.2.2.1,
    hFrag.2.2.2.2.2.1, hFrag.2.2.2.2.2.2⟩

/-- SM8.B.1 (**the same bridge at an arbitrary core**): per-core preservation on
the one core a transition writes, plus confinement to that core, gives
preservation on **every** core.

`lowEquivalent_smp_of_projection_and_confinement` is the `c' = bootCoreId`
instance, and it is the *only* instance that can be fed by a whole-projection
hypothesis, because `projectState` **is** the boot core's view
(`projectStateOnCore_bootCore`).  For a transition that runs on a secondary core
and writes that core's scheduler slots, boot-core confinement is simply false —
so a statement pinned to it says nothing about ordinary SMP execution, however
general its conclusion looks.  This form takes the executing core as a
parameter, which is what the SM3 lock bracket needs once the bracketed entry is
allowed to run somewhere other than the boot core. -/
theorem lowEquivalent_smp_of_projectionOnCore_and_confinement (ctx : LabelingContext)
    (observer : IfObserver) {st st' : SystemState} {c' : CoreId}
    (hProjOn : projectStateOnCore ctx observer st' c' = projectStateOnCore ctx observer st c')
    (hConfined : observableSlotsConfinedToCore st st' c') :
    lowEquivalent_smp ctx observer st' st := by
  intro c
  show projectStateOnCore ctx observer st' c = projectStateOnCore ctx observer st c
  by_cases hc : c = c'
  · cases hc
    exact hProjOn
  · exact crossCoreNonInterference ctx observer hc hConfined
      (sharedViewUnchanged_of_projectionOnCore ctx observer hProjOn)

/-- SM8.B.1: the boot-core bridge is the general one at `c' = bootCoreId`.

Stated so the generalisation is checked against the theorem it generalises rather
than asserted — if the two ever diverge this stops elaborating. -/
theorem lowEquivalent_smp_of_projection_and_confinement_eq_atCore (ctx : LabelingContext)
    (observer : IfObserver) {st st' : SystemState}
    (hProj : projectState ctx observer st' = projectState ctx observer st)
    (hConfined : observableSlotsConfinedToCore st st' bootCoreId) :
    lowEquivalent_smp ctx observer st' st :=
  lowEquivalent_smp_of_projectionOnCore_and_confinement ctx observer
    (c' := bootCoreId) hProj hConfined

/-- SM8.B.1 (headline): **every `NonInterferenceStep` whose per-core writes stay
on the boot core preserves the observer's view on *every* core.**

The existing single-core surface proves one thing —
`step_preserves_projection`, the *global* projection is preserved — and that
already carries the whole shared half at every core, because the shared
fragment of the per-core view **is** the shared fragment of the global
projection (`onCore_sharedFragment_eq_globalProjection`).  What it cannot carry
is the per-core half away from the boot core, and that is exactly what
`hConfined` supplies.

So the two cores split:

* `c = bootCoreId` — the per-core view *is* `projectState`
  (`projectStateOnCore_bootCore`), so this is `step_preserves_projection`
  verbatim;
* `c ≠ bootCoreId` — §2 at `c' = bootCoreId`.

`hConfined` is not decoration.  Four `NonInterferenceStep` constructors
(`syscallDispatchHigh`, `endpointCallWithDonationHigh`,
`endpointReplyWithReversionHigh`, `handleInterrupt`) carry only a whole-state
projection hypothesis and no operational one, so they range over transitions
that genuinely do write another core — the live cross-core dispatch is one.
For those the premise must be supplied; §4 proves it for the other thirty-one
from the operations' own semantics. -/
theorem nonInterference_perCore (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (hIdxComplete : objectIndexSetComplete st)
    (hObjSetInv : st.objectIndexSet.table.invExt)
    (hStep : NonInterferenceStep ctx observer st st')
    (hConfined : observableSlotsConfinedToCore st st' bootCoreId) :
    lowEquivalent_smp ctx observer st' st :=
  lowEquivalent_smp_of_projection_and_confinement ctx observer
    (step_preserves_projection ctx observer st st' hObjInv hIdxComplete hObjSetInv hStep)
    hConfined

/-- SM8.B.1 (observer form): the per-core headline, stated at one observer. -/
theorem nonInterference_perCore_observer (ctx : LabelingContext) (o : PerCoreObserver)
    (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (hIdxComplete : objectIndexSetComplete st)
    (hObjSetInv : st.objectIndexSet.table.invExt)
    (hStep : NonInterferenceStep ctx o.toIfObserver st st')
    (hConfined : observableSlotsConfinedToCore st st' bootCoreId) :
    lowEquivalentForObserver ctx o st' st :=
  nonInterference_perCore ctx o.toIfObserver st st' hObjInv hIdxComplete hObjSetInv
    hStep hConfined o.core

/-- SM8.B.1 (two-sided): the per-core lift of `composedNonInterference_step`.
Two low-equivalent states stepped by (possibly different) confined NI steps stay
low-equivalent **on every core**. -/
theorem composedNonInterference_step_perCore (ctx : LabelingContext) (observer : IfObserver)
    (s₁ s₂ s₁' s₂' : SystemState)
    (hLow : lowEquivalent_smp ctx observer s₁ s₂)
    (hObjInv₁ : s₁.objects.invExt) (hObjInv₂ : s₂.objects.invExt)
    (hIdxComplete₁ : objectIndexSetComplete s₁) (hIdxComplete₂ : objectIndexSetComplete s₂)
    (hObjSetInv₁ : s₁.objectIndexSet.table.invExt)
    (hObjSetInv₂ : s₂.objectIndexSet.table.invExt)
    (hStep₁ : NonInterferenceStep ctx observer s₁ s₁')
    (hStep₂ : NonInterferenceStep ctx observer s₂ s₂')
    (hConfined₁ : observableSlotsConfinedToCore s₁ s₁' bootCoreId)
    (hConfined₂ : observableSlotsConfinedToCore s₂ s₂' bootCoreId) :
    lowEquivalent_smp ctx observer s₁' s₂' := by
  intro c
  have h₁ := nonInterference_perCore ctx observer s₁ s₁' hObjInv₁ hIdxComplete₁ hObjSetInv₁
    hStep₁ hConfined₁ c
  have h₂ := nonInterference_perCore ctx observer s₂ s₂' hObjInv₂ hIdxComplete₂ hObjSetInv₂
    hStep₂ hConfined₂ c
  exact lowEquivalentOnCore_trans h₁ (lowEquivalentOnCore_trans (hLow c) (h₂.symm))

/-- SM8.B.1: the per-core result implies the live single-core one — instantiate
at the boot core.  This is the direction that makes the SM8.B surface a
*strengthening* of the release-grade NI statement rather than a parallel one. -/
theorem nonInterference_perCore_to_singleCore (ctx : LabelingContext)
    (observer : IfObserver) (st st' : SystemState)
    (h : lowEquivalent_smp ctx observer st' st) : lowEquivalent ctx observer st' st :=
  lowEquivalent_smp_to_singleCore ctx observer st' st h

/-- SM8.B.1 (trace form): a `NonInterferenceTrace` all of whose steps are
boot-core-confined preserves the observer's view on every core.

The confinement premise is stated as "every reachable intermediate pair is
confined", which is the composable form: `observableSlotsConfinedToCore_trans`
folds the chain, and each step's own confinement comes from §4. -/
theorem trace_preserves_projectionOnCore (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState) (c : CoreId)
    (hTrace : NonInterferenceTrace ctx observer st st')
    (hConfined : observableSlotsConfinedToCore st st' bootCoreId)
    (hc : c ≠ bootCoreId) :
    projectStateOnCore ctx observer st' c = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference ctx observer hc hConfined
    (sharedViewUnchanged_of_globalProjection ctx observer
      (trace_preserves_projection ctx observer st st' hTrace))


-- ============================================================================
-- §4  SM8.B.3 — the thirty-five per-operation lifts
-- ============================================================================
--
-- §4a proves the confinement premise of §3 for each kernel operation the
-- `KernelOperation` taxonomy names; §4b instantiates `nonInterference_perCore`
-- at each one.
--
-- Confinement is *derived*, not assumed, wherever the constructor pins the
-- operation's semantics.  That is a strengthening of the SM4.C / SM4.D
-- precedent, whose per-core preservation theorems carry the same fact as an
-- `hOtherIdle` / `hNonBootIdle` hypothesis with a "SM5 discharges it" note; the
-- lemmas below discharge it, so a caller of the SM8.B surface supplies nothing.
--
-- Three families cover almost everything:
--
--   * object-store steps          — scheduler and machine untouched;
--   * boot-pinned scheduler steps — every write is `set…OnCore bootCoreId`, so
--                                   the SM4.B `_ne` algebra frames every other
--                                   core;
--   * identity steps              — read-only operations and decode failures.
--
-- The exception is the four catch-all constructors (`syscallDispatchHigh`,
-- `endpointCallWithDonationHigh`, `endpointReplyWithReversionHigh`,
-- `handleInterrupt`).  Those carry a whole-state projection hypothesis and no
-- operational one, so they range over transitions that *do* write a remote core
-- — the live cross-core dispatch among them.  Their lifts take the confinement
-- premise explicitly; §5 records that this is exactly four, and why.

/-! ### §4a  Confinement of the primitive state mutators -/

/-- Writing one object leaves every core's scheduler slots and register bank
alone. -/
theorem storeObject_confinedToCore (st st' : SystemState) (oid : SeLe4n.ObjId)
    (obj : KernelObject) (c₀ : CoreId) (hStep : storeObject oid obj st = .ok ((), st')) :
    observableSlotsConfinedToCore st st' c₀ :=
  observableSlotsConfinedToCore_of_scheduler_machine_eq c₀
    (storeObject_scheduler_eq st st' oid obj hStep)
    (storeObject_machine_eq st st' oid obj hStep)

/-- Writing one capability reference leaves the scheduler and the machine
alone. -/
theorem storeCapabilityRef_confinedToCore (st st' : SystemState) (ref : SlotRef)
    (target : Option CapTarget) (c₀ : CoreId)
    (hStep : storeCapabilityRef ref target st = .ok ((), st')) :
    observableSlotsConfinedToCore st st' c₀ :=
  observableSlotsConfinedToCore_of_scheduler_machine_eq c₀
    (storeCapabilityRef_preserves_scheduler st st' ref target hStep)
    (storeCapabilityRef_preserves_machine st st' ref target hStep)

theorem storeTcbIpcState_confinedToCore (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState) (c₀ : CoreId)
    (hStep : storeTcbIpcState st tid ipc = .ok st') :
    observableSlotsConfinedToCore st st' c₀ :=
  observableSlotsConfinedToCore_of_scheduler_machine_eq c₀
    (storeTcbIpcState_scheduler_eq st st' tid ipc hStep)
    (storeTcbIpcState_machine_eq st st' tid ipc hStep)

theorem storeTcbIpcStateAndMessage_confinedToCore (st st' : SystemState)
    (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState) (msg : Option IpcMessage) (c₀ : CoreId)
    (hStep : storeTcbIpcStateAndMessage st tid ipc msg = .ok st') :
    observableSlotsConfinedToCore st st' c₀ :=
  observableSlotsConfinedToCore_of_scheduler_machine_eq c₀
    (storeTcbIpcStateAndMessage_scheduler_eq st st' tid ipc msg hStep)
    (storeTcbIpcStateAndMessage_machine_eq st st' tid ipc msg hStep)

theorem storeTcbQueueLinks_confinedToCore (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (prev : Option SeLe4n.ThreadId) (pprev : Option QueuePPrev)
    (next : Option SeLe4n.ThreadId) (c₀ : CoreId)
    (hStep : storeTcbQueueLinks st tid prev pprev next = .ok st') :
    observableSlotsConfinedToCore st st' c₀ :=
  observableSlotsConfinedToCore_of_scheduler_machine_eq c₀
    (storeTcbQueueLinks_scheduler_eq st st' tid prev pprev next hStep)
    (storeTcbQueueLinks_machine_eq st st' tid prev pprev next hStep)

/-- `storeTcbReceiveComplete` is a TCB write routed through `storeObject`, so it
frames the scheduler and the machine.  Proved here rather than composed from a
`…_machine_eq` because the IPC layer states only the scheduler half. -/
theorem storeTcbReceiveComplete_confinedToCore (st st' : SystemState)
    (tid : SeLe4n.ThreadId) (msg : Option IpcMessage) (c₀ : CoreId)
    (hStep : storeTcbReceiveComplete st tid msg = .ok st') :
    observableSlotsConfinedToCore st st' c₀ := by
  unfold storeTcbReceiveComplete at hStep
  cases hTcb : lookupTcb st tid with
  | none => simp [hTcb] at hStep
  | some tcb =>
    simp only [hTcb] at hStep
    cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := .ready, pendingMessage := msg, pendingReceiveReply := none }) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      simp only [hStore] at hStep
      have hEq := Except.ok.inj hStep; subst hEq
      exact storeObject_confinedToCore st pair.2 _ _ c₀ hStore

theorem endpointQueuePopHead_confinedToCore (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (st st' : SystemState) (tid : SeLe4n.ThreadId) {headTcb : TCB} (c₀ : CoreId)
    (hStep : endpointQueuePopHead endpointId isReceiveQ st = .ok (tid, headTcb, st')) :
    observableSlotsConfinedToCore st st' c₀ :=
  observableSlotsConfinedToCore_of_scheduler_machine_eq c₀
    (endpointQueuePopHead_scheduler_eq endpointId isReceiveQ st st' tid hStep)
    (endpointQueuePopHead_machine_eq endpointId isReceiveQ st st' tid hStep)

theorem endpointQueueEnqueue_confinedToCore (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (tid : SeLe4n.ThreadId) (st st' : SystemState) (c₀ : CoreId)
    (hStep : endpointQueueEnqueue endpointId isReceiveQ tid st = .ok st') :
    observableSlotsConfinedToCore st st' c₀ :=
  observableSlotsConfinedToCore_of_scheduler_machine_eq c₀
    (endpointQueueEnqueue_scheduler_eq endpointId isReceiveQ tid st st' hStep)
    (endpointQueueEnqueue_machine_eq endpointId isReceiveQ tid st st' hStep)

theorem linkCallerReply_confinedToCore (st st' : SystemState) (caller : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (c₀ : CoreId)
    (hStep : SystemState.linkCallerReply caller rid st = .ok ((), st')) :
    observableSlotsConfinedToCore st st' c₀ :=
  observableSlotsConfinedToCore_of_scheduler_machine_eq c₀
    (linkCallerReply_scheduler_eq st st' caller rid hStep)
    (linkCallerReply_machine_eq st st' caller rid hStep)

theorem linkServerStashedReply_confinedToCore (st st' : SystemState)
    (caller server : SeLe4n.ThreadId) (c₀ : CoreId)
    (hStep : SystemState.linkServerStashedReply caller server st = .ok ((), st')) :
    observableSlotsConfinedToCore st st' c₀ :=
  observableSlotsConfinedToCore_of_scheduler_machine_eq c₀
    (linkServerStashedReply_scheduler_eq st st' caller server hStep)
    (linkServerStashedReply_machine_eq st st' caller server hStep)

theorem consumeCallerReply_confinedToCore (st st' : SystemState) (caller : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (c₀ : CoreId)
    (hStep : SystemState.consumeCallerReply caller rid st = .ok ((), st')) :
    observableSlotsConfinedToCore st st' c₀ :=
  observableSlotsConfinedToCore_of_scheduler_machine_eq c₀
    (SystemState.consumeCallerReply_scheduler_eq st st' caller rid hStep)
    (SystemState.consumeCallerReply_machine_eq st st' caller rid hStep)

theorem cleanupPreReceiveDonation_confinedToCore (st : SystemState)
    (receiver : SeLe4n.ThreadId) (c₀ : CoreId) :
    observableSlotsConfinedToCore st (cleanupPreReceiveDonation st receiver) c₀ :=
  observableSlotsConfinedToCore_of_scheduler_machine_eq c₀
    (cleanupPreReceiveDonation_scheduler_eq st receiver)
    (cleanupPreReceiveDonation_machine_eq st receiver)

/-! #### Boot-pinned scheduler steps

Every single-core scheduler mutator writes through `set…OnCore bootCoreId`, so
the SM4.B cross-core independence algebra frames every other core.  These are
the lemmas that make the "single-core operations do not touch another core"
discipline a theorem instead of a convention. -/

/-- `ensureRunnable` inserts into **the boot core's** run queue and touches
nothing else. -/
theorem ensureRunnable_confinedToBootCore (st : SystemState) (tid : SeLe4n.ThreadId) :
    observableSlotsConfinedToCore st (ensureRunnable st tid) bootCoreId := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro c hc <;>
    unfold ensureRunnable <;>
    (split
     · rfl
     · split <;> simp [Ne.symm hc])

/-- `removeRunnable` removes from **the boot core's** run queue and clears the
boot core's current slot; every other core is untouched. -/
theorem removeRunnable_confinedToBootCore (st : SystemState) (tid : SeLe4n.ThreadId) :
    observableSlotsConfinedToCore st (removeRunnable st tid) bootCoreId := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro c hc <;> simp [removeRunnable, Ne.symm hc]

/-- `setCurrentThread` writes the boot core's current slot. -/
theorem setCurrentThread_confinedToBootCore (st st' : SystemState)
    (tid : Option SeLe4n.ThreadId) (hStep : setCurrentThread tid st = .ok ((), st')) :
    observableSlotsConfinedToCore st st' bootCoreId := by
  unfold setCurrentThread at hStep
  simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
  obtain ⟨_, hEq⟩ := hStep
  subst hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro c hc <;> simp [Ne.symm hc]

/-- `saveOutgoingContext` writes the outgoing thread's TCB and nothing else. -/
theorem saveOutgoingContext_confinedToCore (st : SystemState) (c₀ : CoreId) :
    observableSlotsConfinedToCore st (saveOutgoingContext st) c₀ := by
  refine observableSlotsConfinedToCore_of_scheduler_machine_eq c₀ ?_ ?_ <;>
    unfold saveOutgoingContext <;>
    (split
     · rfl
     · split <;> rfl)

/-- `restoreIncomingContext` writes **the boot core's** register bank. -/
theorem restoreIncomingContext_confinedToBootCore (st : SystemState) (tid : SeLe4n.ThreadId) :
    observableSlotsConfinedToCore st (restoreIncomingContext st tid) bootCoreId := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro c hc <;>
    unfold restoreIncomingContext <;> split <;>
    simp [MachineState.regsOnCore_setRegsOnCore_ne _ _ _ _ (Ne.symm hc)]


/-- Advancing the machine timer touches neither the scheduler nor any core's
register bank. -/
theorem machineTick_confinedToCore (st : SystemState) (c₀ : CoreId) :
    observableSlotsConfinedToCore st { st with machine := tick st.machine } c₀ :=
  observableSlotsConfinedToCore_of_scheduler_regs_eq c₀ rfl (fun _ => rfl)

/-- A direct write to **the boot core's** run-queue slot. -/
theorem setRunQueueBootCore_confinedToBootCore (st : SystemState)
    (q : SeLe4n.Kernel.RunQueue) :
    observableSlotsConfinedToCore st
      { st with scheduler := st.scheduler.setRunQueueOnCore bootCoreId q } bootCoreId := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro c hc <;> simp [Ne.symm hc]

/-- `chooseThread` is a pure read — the state comes through untouched. -/
theorem chooseThread_confinedToCore (st st' : SystemState) (next : Option SeLe4n.ThreadId)
    (c₀ : CoreId) (hStep : chooseThread st = .ok (next, st')) :
    observableSlotsConfinedToCore st st' c₀ :=
  observableSlotsConfinedToCore_of_eq c₀ (chooseThread_preserves_state st st' next hStep)

/-- SM8.B.3: `schedule` writes only the boot core.

Every leg is a boot-pinned write: the context save is an object write, the
dequeue is `setRunQueueOnCore bootCoreId`, the context restore is
`setRegsOnCore bootCoreId`, and the dispatch is `setCurrentOnCore bootCoreId`.
This *discharges* the `hOtherIdle` premise the SM4.C per-core preservation
theorems carry for the same operation. -/
theorem schedule_confinedToBootCore (st st' : SystemState)
    (hStep : SeLe4n.Kernel.schedule st = .ok ((), st')) :
    observableSlotsConfinedToCore st st' bootCoreId := by
  unfold SeLe4n.Kernel.schedule at hStep
  cases hChoose : chooseThread st with
  | error e => simp [hChoose] at hStep
  | ok pair =>
    obtain ⟨next, stC⟩ := pair
    have hStEq : stC = st := chooseThread_preserves_state st stC next hChoose
    subst stC
    cases next with
    | none =>
      simp only [hChoose] at hStep
      refine observableSlotsConfinedToCore_trans
        (saveOutgoingContext_confinedToCore st bootCoreId) ?_
      exact setCurrentThread_confinedToBootCore _ st' none hStep
    | some tid =>
      -- `simp only [hChoose]` here rather than before the `cases`: with `next`
      -- now a constructor the outer match iota-reduces, so `split` below sees
      -- the operation's own object-store match and reduces it *in place* —
      -- without naming the raw scrutinee, which is what the AK7 cascade metric
      -- counts.
      simp only [hChoose] at hStep
      split at hStep
      · split at hStep
        · refine observableSlotsConfinedToCore_trans ?_
            (setCurrentThread_confinedToBootCore _ st' (some tid) hStep)
          refine observableSlotsConfinedToCore_trans ?_
            (restoreIncomingContext_confinedToBootCore _ tid)
          refine observableSlotsConfinedToCore_trans
            (saveOutgoingContext_confinedToCore st bootCoreId) ?_
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro c hc <;> simp [Ne.symm hc]
        · simp at hStep
      · simp at hStep

/-- SM8.B.3: `handleYield` writes only the boot core (re-enqueue at the boot
core's run queue, then `schedule`). -/
theorem handleYield_confinedToBootCore (st st' : SystemState)
    (hStep : SeLe4n.Kernel.handleYield st = .ok ((), st')) :
    observableSlotsConfinedToCore st st' bootCoreId := by
  unfold SeLe4n.Kernel.handleYield at hStep
  cases hCur : st.scheduler.currentOnCore bootCoreId with
  | none => simp [hCur] at hStep
  | some tid =>
    simp only [hCur] at hStep
    split at hStep
    · refine observableSlotsConfinedToCore_trans ?_ (schedule_confinedToBootCore _ st' hStep)
      exact setRunQueueBootCore_confinedToBootCore st _
    · simp at hStep

/-- SM8.B.3: `timerTick` writes only the boot core.  The timer advance is
machine-level but touches no register bank; the preemption leg re-enqueues at
the boot core's run queue and delegates to `schedule`. -/
theorem timerTick_confinedToBootCore (st st' : SystemState)
    (hStep : SeLe4n.Kernel.timerTick st = .ok ((), st')) :
    observableSlotsConfinedToCore st st' bootCoreId := by
  unfold SeLe4n.Kernel.timerTick at hStep
  cases hCur : st.scheduler.currentOnCore bootCoreId with
  | none =>
    simp only [hCur, Except.ok.injEq, Prod.mk.injEq] at hStep
    obtain ⟨_, hEq⟩ := hStep
    subst hEq
    exact machineTick_confinedToCore st bootCoreId
  | some tid =>
    simp only [hCur] at hStep
    split at hStep
    · split at hStep
      · -- time slice expired: object write + timer + boot-core re-enqueue + schedule
        refine observableSlotsConfinedToCore_trans ?_ (schedule_confinedToBootCore _ st' hStep)
        refine ⟨?_, ?_, ?_, ?_, ?_, fun c _ => rfl⟩ <;> intro c hc <;> simp [Ne.symm hc]
      · simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
        obtain ⟨_, hEq⟩ := hStep
        subst hEq
        exact observableSlotsConfinedToCore_of_scheduler_regs_eq bootCoreId rfl (fun _ => rfl)
    · simp at hStep


/-- The `_fromTcb` store variants wrap `storeObject` directly (no lookup), so
they frame the scheduler and the machine unconditionally. -/
theorem storeTcbIpcState_fromTcb_confinedToCore (st st' : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (ipc : ThreadIpcState) (c₀ : CoreId)
    (hStep : storeTcbIpcState_fromTcb st tid tcb ipc = .ok st') :
    observableSlotsConfinedToCore st st' c₀ := by
  unfold storeTcbIpcState_fromTcb at hStep
  cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc }) st with
  | error e => simp [hStore] at hStep
  | ok pair =>
    simp only [hStore] at hStep
    have hEq := Except.ok.inj hStep; subst hEq
    exact storeObject_confinedToCore st pair.2 _ _ c₀ hStore

theorem storeTcbIpcStateAndMessage_fromTcb_confinedToCore (st st' : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (ipc : ThreadIpcState) (msg : Option IpcMessage)
    (c₀ : CoreId)
    (hStep : storeTcbIpcStateAndMessage_fromTcb st tid tcb ipc msg = .ok st') :
    observableSlotsConfinedToCore st st' c₀ := by
  unfold storeTcbIpcStateAndMessage_fromTcb at hStep
  cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc, pendingMessage := msg }) st with
  | error e => simp [hStore] at hStep
  | ok pair =>
    simp only [hStore] at hStep
    have hEq := Except.ok.inj hStep; subst hEq
    exact storeObject_confinedToCore st pair.2 _ _ c₀ hStore

/-! #### The IPC transitions

Each is a chain of object-store steps plus at most one `ensureRunnable` /
`removeRunnable`, and every one of those is boot-pinned.  The case skeletons
mirror the SM6.D.2 `…_passiveServerIdleFrameOnCore` proofs (same operations,
same branch structure, different payload). -/

/-- SM8.B.3: `notificationSignal` writes only the boot core. -/
theorem notificationSignal_confinedToBootCore (st st' : SystemState)
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge)
    (hStep : SeLe4n.Kernel.notificationSignal notificationId badge st = .ok ((), st')) :
    observableSlotsConfinedToCore st st' bootCoreId := by
  unfold SeLe4n.Kernel.notificationSignal at hStep
  cases hObj : st.objects[notificationId]? with
  | none => simp [hObj] at hStep
  | some obj =>
    cases obj with
    | notification ntfn =>
      simp only [hObj] at hStep
      cases hTail : ntfn.waitingThreads.tail? with
      | none =>
        simp only [hTail] at hStep
        exact storeObject_confinedToCore st st' notificationId _ bootCoreId hStep
      | some p =>
        obtain ⟨waiter, rest⟩ := p
        simp only [hTail] at hStep
        split at hStep
        · simp at hStep
        · next st1 hStore =>
          split at hStep
          · simp at hStep
          · next st2 hStore2 =>
            simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep
            subst hEq
            refine observableSlotsConfinedToCore_trans
              (storeObject_confinedToCore st st1 notificationId _ bootCoreId hStore) ?_
            refine observableSlotsConfinedToCore_trans
              (storeTcbIpcStateAndMessage_confinedToCore st1 st2 waiter _ _ bootCoreId hStore2) ?_
            exact ensureRunnable_confinedToBootCore st2 waiter
    | tcb _ | cnode _ | endpoint _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ =>
      simp [hObj] at hStep

/-- SM8.B.3: `notificationWait` writes only the boot core. -/
theorem notificationWait_confinedToBootCore (st st' : SystemState)
    (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId)
    (result : Option SeLe4n.Badge)
    (hStep : SeLe4n.Kernel.notificationWait notificationId waiter st = .ok (result, st')) :
    observableSlotsConfinedToCore st st' bootCoreId := by
  unfold SeLe4n.Kernel.notificationWait at hStep
  cases hObj : st.objects[notificationId]? with
  | none => simp [hObj] at hStep
  | some obj =>
    cases obj with
    | notification ntfn =>
      simp only [hObj] at hStep
      cases hBadge : ntfn.pendingBadge with
      | some badge =>
        simp only [hBadge] at hStep
        split at hStep
        · simp at hStep
        · next st1 hStore =>
          split at hStep
          · simp at hStep
          · next st2 hStore2 =>
            simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep
            subst hEq
            exact observableSlotsConfinedToCore_trans
              (storeObject_confinedToCore st st1 notificationId _ bootCoreId hStore)
              (storeTcbIpcState_confinedToCore st1 st2 waiter _ bootCoreId hStore2)
      | none =>
        simp only [hBadge] at hStep
        cases hTcb : lookupTcb st waiter with
        | none => simp [hTcb] at hStep
        | some tcb =>
          simp only [hTcb] at hStep
          split at hStep
          · simp at hStep
          · split at hStep
            · simp at hStep
            · next wt' _ =>
              split at hStep
              · simp at hStep
              · next st1 hStore =>
                split at hStep
                · simp at hStep
                · next st2 hStore2 =>
                  simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
                  obtain ⟨_, hEq⟩ := hStep
                  subst hEq
                  refine observableSlotsConfinedToCore_trans
                    (storeObject_confinedToCore st st1 notificationId _ bootCoreId hStore) ?_
                  refine observableSlotsConfinedToCore_trans
                    (storeTcbIpcState_fromTcb_confinedToCore st1 st2 waiter tcb _ bootCoreId
                      hStore2) ?_
                  exact removeRunnable_confinedToBootCore st2 waiter
    | tcb _ | cnode _ | endpoint _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ =>
      simp [hObj] at hStep

/-- SM8.B.3: `endpointSendDual` writes only the boot core. -/
theorem endpointSendDual_confinedToBootCore (st st' : SystemState)
    (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId) (msg : IpcMessage)
    (hStep : endpointSendDual endpointId sender msg st = .ok ((), st')) :
    observableSlotsConfinedToCore st st' bootCoreId := by
  unfold endpointSendDual at hStep
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj =>
    cases obj with
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : ep.receiveQ.head with
      | some _ =>
        simp only [hHead] at hStep
        split at hStep
        · simp at hStep
        · next receiver headTcb st1 hPop =>
          split at hStep
          · simp at hStep
          · next st2 hStore =>
            simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep
            subst hEq
            refine observableSlotsConfinedToCore_trans
              (endpointQueuePopHead_confinedToCore endpointId true st st1 receiver
                (headTcb := headTcb) bootCoreId hPop) ?_
            refine observableSlotsConfinedToCore_trans
              (storeTcbReceiveComplete_confinedToCore st1 st2 receiver (some msg)
                bootCoreId hStore) ?_
            exact ensureRunnable_confinedToBootCore st2 receiver
      | none =>
        simp only [hHead] at hStep
        split at hStep
        · simp at hStep
        · next st1 hEnq =>
          split at hStep
          · simp at hStep
          · next st2 hStore =>
            simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep
            subst hEq
            refine observableSlotsConfinedToCore_trans
              (endpointQueueEnqueue_confinedToCore endpointId false sender st st1 bootCoreId
                hEnq) ?_
            refine observableSlotsConfinedToCore_trans
              (storeTcbIpcStateAndMessage_confinedToCore st1 st2 sender _ _ bootCoreId hStore) ?_
            exact removeRunnable_confinedToBootCore st2 sender
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ =>
      simp [hObj] at hStep


/-- `returnDonatedSchedContext` rewrites the donor/donee TCBs and the
SchedContext; it touches neither the scheduler nor the machine. -/
theorem returnDonatedSchedContext_confinedToCore (st st' : SystemState)
    (receiver : SeLe4n.ThreadId) (scId : SeLe4n.SchedContextId)
    (originalOwner : SeLe4n.ThreadId) (c₀ : CoreId)
    (hStep : returnDonatedSchedContext st receiver scId originalOwner = .ok st') :
    observableSlotsConfinedToCore st st' c₀ :=
  observableSlotsConfinedToCore_of_scheduler_machine_eq c₀
    (returnDonatedSchedContext_scheduler_eq st st' receiver scId originalOwner hStep)
    (returnDonatedSchedContext_machine_eq st st' receiver scId originalOwner hStep)

/-- The checked pre-receive donation cleanup is either the identity or a
`returnDonatedSchedContext`, so it is confined to every core. -/
theorem cleanupPreReceiveDonationChecked_confinedToCore (st st' : SystemState)
    (receiver : SeLe4n.ThreadId) (c₀ : CoreId)
    (hStep : cleanupPreReceiveDonationChecked st receiver = .ok st') :
    observableSlotsConfinedToCore st st' c₀ := by
  unfold cleanupPreReceiveDonationChecked at hStep
  cases hTcb : lookupTcb st receiver with
  | none =>
    simp only [hTcb, Except.ok.injEq] at hStep
    exact observableSlotsConfinedToCore_of_eq c₀ hStep.symm
  | some recvTcb =>
    simp only [hTcb] at hStep
    cases hBind : recvTcb.schedContextBinding with
    | donated scId originalOwner =>
      simp only [hBind] at hStep
      exact returnDonatedSchedContext_confinedToCore st st' receiver scId originalOwner c₀ hStep
    | unbound | bound _ =>
      simp only [hBind, Except.ok.injEq] at hStep
      exact observableSlotsConfinedToCore_of_eq c₀ hStep.symm

/-- SM8.B.3: `endpointReceiveDual` writes only the boot core.

The rendezvous leg branches on the dequeued sender's `ipcState` (the `Call`
arm links a reply object, every other arm is a plain `Send`), so the case
analysis is over `ThreadIpcState` rather than over the `if` — the `if`'s
condition *is* that match, and splitting the `if` directly leaves the two
paths interleaved with unreachable arms. -/
theorem endpointReceiveDual_confinedToBootCore (st st' : SystemState)
    (endpointId : SeLe4n.ObjId) (receiver senderId : SeLe4n.ThreadId)
    (replyId : Option SeLe4n.ReplyId)
    (hStep : endpointReceiveDual endpointId receiver replyId st = .ok (senderId, st')) :
    observableSlotsConfinedToCore st st' bootCoreId := by
  unfold endpointReceiveDual at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj =>
    cases obj with
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : ep.sendQ.head with
      | some _ =>
        simp only [hHead] at hStep
        cases hPop : endpointQueuePopHead endpointId false st with
        | error e => simp [hPop] at hStep
        | ok triple =>
          obtain ⟨sender, senderTcb, st1⟩ := triple
          simp only [hPop] at hStep
          have hPopC := endpointQueuePopHead_confinedToCore endpointId false st st1 sender
            (headTcb := senderTcb) bootCoreId hPop
          cases hIpc : senderTcb.ipcState with
          | blockedOnCall epId =>
            -- Call rendezvous: block the caller `.blockedOnReply`, link its Reply
            -- object, then complete the receiver.  `hIpc` reduces the `if`'s
            -- condition (which *is* the `ipcState` match) to `True`.
            simp only [hIpc, ↓reduceIte] at hStep
            cases hStore : storeTcbIpcStateAndMessage st1 sender
                (.blockedOnReply endpointId (some receiver)) none with
            | error e => simp [hStore] at hStep
            | ok st2 =>
              simp only [hStore] at hStep
              cases hRid : replyId with
              | none => simp [hRid] at hStep
              | some rid =>
                simp only [hRid] at hStep
                cases hLink : SystemState.linkCallerReply sender rid st2 with
                | error e => simp [hLink] at hStep
                | ok pairL =>
                  simp only [hLink] at hStep
                  cases hStore2 : storeTcbIpcStateAndMessage pairL.2 receiver .ready
                      senderTcb.pendingMessage with
                  | error e => simp [hStore2] at hStep
                  | ok st3 =>
                    simp only [hStore2, Except.ok.injEq, Prod.mk.injEq] at hStep
                    obtain ⟨_, hEq⟩ := hStep
                    subst hEq
                    refine observableSlotsConfinedToCore_trans hPopC ?_
                    refine observableSlotsConfinedToCore_trans
                      (storeTcbIpcStateAndMessage_confinedToCore st1 st2 sender _ _ bootCoreId
                        hStore) ?_
                    refine observableSlotsConfinedToCore_trans
                      (linkCallerReply_confinedToCore st2 pairL.2 sender rid bootCoreId hLink) ?_
                    exact storeTcbIpcStateAndMessage_confinedToCore pairL.2 st3 receiver _ _
                      bootCoreId hStore2
          | ready | blockedOnSend _ | blockedOnReceive _ | blockedOnNotification _
          | blockedOnReply _ _ =>
            -- Send rendezvous: wake the sender `.ready`, then complete the receiver.
            all_goals (
              simp only [hIpc] at hStep
              split at hStep
              · contradiction
              · cases hStore : storeTcbIpcStateAndMessage st1 sender .ready none with
                | error e => simp [hStore] at hStep
                | ok st2 =>
                  simp only [hStore] at hStep
                  cases hStore2 : storeTcbIpcStateAndMessage (ensureRunnable st2 sender) receiver
                      .ready senderTcb.pendingMessage with
                  | error e => simp [hStore2] at hStep
                  | ok st3 =>
                    simp only [hStore2, Except.ok.injEq, Prod.mk.injEq] at hStep
                    obtain ⟨_, hEq⟩ := hStep
                    subst hEq
                    refine observableSlotsConfinedToCore_trans hPopC ?_
                    refine observableSlotsConfinedToCore_trans
                      (storeTcbIpcStateAndMessage_confinedToCore st1 st2 sender _ _ bootCoreId
                        hStore) ?_
                    refine observableSlotsConfinedToCore_trans
                      (ensureRunnable_confinedToBootCore st2 sender) ?_
                    exact storeTcbIpcStateAndMessage_confinedToCore _ st3 receiver _ _ bootCoreId
                      hStore2)
      | none =>
        simp only [hHead] at hStep
        cases hClean : cleanupPreReceiveDonationChecked st receiver with
        | error e => simp [hClean] at hStep
        | ok stClean =>
          simp only [hClean] at hStep
          have hCleanC := cleanupPreReceiveDonationChecked_confinedToCore st stClean receiver
            bootCoreId hClean
          cases hEnq : endpointQueueEnqueue endpointId true receiver stClean with
          | error e => simp [hEnq] at hStep
          | ok st1 =>
            simp only [hEnq] at hStep
            have hEnqC := endpointQueueEnqueue_confinedToCore endpointId true receiver stClean st1
              bootCoreId hEnq
            cases hStore : storeTcbIpcState st1 receiver (.blockedOnReceive endpointId) with
            | error e => simp [hStore] at hStep
            | ok st2 =>
              simp only [hStore] at hStep
              have hStoreC := storeTcbIpcState_confinedToCore st1 st2 receiver _ bootCoreId hStore
              cases hGet : st2.getTcb? receiver with
              | none =>
                simp only [hGet, Except.ok.injEq, Prod.mk.injEq] at hStep
                obtain ⟨_, hEq⟩ := hStep
                subst hEq
                exact observableSlotsConfinedToCore_trans hCleanC
                  (observableSlotsConfinedToCore_trans hEnqC
                    (observableSlotsConfinedToCore_trans hStoreC
                      (removeRunnable_confinedToBootCore st2 receiver)))
              | some rTcb =>
                simp only [hGet] at hStep
                split at hStep
                · cases hStash : storeObject receiver.toObjId
                      (.tcb { rTcb with pendingReceiveReply := replyId }) st2 with
                  | error e => simp [hStash] at hStep
                  | ok pairS =>
                    simp only [hStash, Except.ok.injEq, Prod.mk.injEq] at hStep
                    obtain ⟨_, hEq⟩ := hStep
                    subst hEq
                    refine observableSlotsConfinedToCore_trans hCleanC ?_
                    refine observableSlotsConfinedToCore_trans hEnqC ?_
                    refine observableSlotsConfinedToCore_trans hStoreC ?_
                    refine observableSlotsConfinedToCore_trans
                      (storeObject_confinedToCore st2 pairS.2 receiver.toObjId _ bootCoreId
                        hStash) ?_
                    exact removeRunnable_confinedToBootCore pairS.2 receiver
                · simp at hStep
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ =>
      simp [hObj] at hStep

/-- SM8.B.3: `endpointCall` writes only the boot core. -/
theorem endpointCall_confinedToBootCore (st st' : SystemState)
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (hStep : endpointCall endpointId caller msg st = .ok ((), st')) :
    observableSlotsConfinedToCore st st' bootCoreId := by
  unfold endpointCall at hStep
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj =>
    cases obj with
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : ep.receiveQ.head with
      | some _ =>
        simp only [hHead] at hStep
        split at hStep
        · simp at hStep
        · next receiver recvTcb st1 hPop =>
          split at hStep
          · simp at hStep
          · next st2 hStore =>
            split at hStep
            · simp at hStep
            · next st4 hStore2 =>
              split at hStep
              · simp at hStep
              · next st5 hLink =>
                simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
                obtain ⟨_, hEq⟩ := hStep
                subst hEq
                refine observableSlotsConfinedToCore_trans
                  (endpointQueuePopHead_confinedToCore endpointId true st st1 receiver
                    (headTcb := recvTcb) bootCoreId hPop) ?_
                refine observableSlotsConfinedToCore_trans
                  (storeTcbIpcStateAndMessage_confinedToCore st1 st2 receiver _ _ bootCoreId
                    hStore) ?_
                refine observableSlotsConfinedToCore_trans
                  (ensureRunnable_confinedToBootCore st2 receiver) ?_
                refine observableSlotsConfinedToCore_trans
                  (storeTcbIpcStateAndMessage_confinedToCore _ st4 caller _ _ bootCoreId
                    hStore2) ?_
                refine observableSlotsConfinedToCore_trans
                  (linkServerStashedReply_confinedToCore st4 st5 caller receiver bootCoreId
                    hLink) ?_
                exact removeRunnable_confinedToBootCore st5 caller
      | none =>
        simp only [hHead] at hStep
        split at hStep
        · simp at hStep
        · next st1 hEnq =>
          split at hStep
          · simp at hStep
          · next st2 hStore =>
            simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep
            subst hEq
            refine observableSlotsConfinedToCore_trans
              (endpointQueueEnqueue_confinedToCore endpointId false caller st st1 bootCoreId
                hEnq) ?_
            refine observableSlotsConfinedToCore_trans
              (storeTcbIpcStateAndMessage_confinedToCore st1 st2 caller _ _ bootCoreId hStore) ?_
            exact removeRunnable_confinedToBootCore st2 caller
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ =>
      simp [hObj] at hStep

/-- SM8.B.3: `endpointReply` writes only the boot core. -/
theorem endpointReply_confinedToBootCore (st st' : SystemState)
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage)
    (hStep : endpointReply replier target msg st = .ok ((), st')) :
    observableSlotsConfinedToCore st st' bootCoreId := by
  unfold endpointReply at hStep
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hTcb : lookupTcb st target with
  | none => simp [hTcb] at hStep
  | some tcb =>
    simp only [hTcb] at hStep
    split at hStep
    · next _ replyTarget =>
      split at hStep
      · simp at hStep
      · next expected _ =>
        split at hStep
        · split at hStep
          · simp at hStep
          · next st1 hStore =>
            have hStoreC := storeTcbIpcStateAndMessage_fromTcb_confinedToCore st st1 target tcb
              .ready (some msg) bootCoreId hStore
            split at hStep
            · next rid _ =>
              refine observableSlotsConfinedToCore_trans hStoreC ?_
              refine observableSlotsConfinedToCore_trans
                (ensureRunnable_confinedToBootCore st1 target) ?_
              exact consumeCallerReply_confinedToCore _ st' target rid bootCoreId hStep
            · simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
              obtain ⟨_, hEq⟩ := hStep
              subst hEq
              exact observableSlotsConfinedToCore_trans hStoreC
                (ensureRunnable_confinedToBootCore st1 target)
        · simp at hStep
    · simp at hStep

/-- SM8.B.3: `endpointReplyRecv` writes only the boot core — both legs. -/
theorem endpointReplyRecv_confinedToBootCore (st st' : SystemState)
    (endpointId : SeLe4n.ObjId) (receiver replyTarget : SeLe4n.ThreadId) (msg : IpcMessage)
    (replyId : Option SeLe4n.ReplyId)
    (hStep : endpointReplyRecv endpointId receiver replyTarget msg replyId st = .ok ((), st')) :
    observableSlotsConfinedToCore st st' bootCoreId := by
  unfold endpointReplyRecv at hStep
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hTcb : lookupTcb st replyTarget with
  | none => simp [hTcb] at hStep
  | some tcb =>
    simp only [hTcb] at hStep
    split at hStep
    · next _ expectedReplier =>
      split at hStep
      · simp at hStep
      · next expected _ =>
        split at hStep
        · split at hStep
          · simp at hStep
          · next st1 hStore =>
            have hStoreC := storeTcbIpcStateAndMessage_fromTcb_confinedToCore st st1 replyTarget
              tcb .ready (some msg) bootCoreId hStore
            have hRunC := ensureRunnable_confinedToBootCore st1 replyTarget
            split at hStep
            · simp at hStep
            · next st3 hConsume =>
              have hConsumeC : observableSlotsConfinedToCore (ensureRunnable st1 replyTarget) st3
                  bootCoreId := by
                split at hConsume
                · next rid _ =>
                  exact consumeCallerReply_confinedToCore _ st3 replyTarget rid bootCoreId hConsume
                · simp only [Except.ok.injEq, Prod.mk.injEq] at hConsume
                  exact observableSlotsConfinedToCore_of_eq bootCoreId hConsume.2.symm
              split at hStep
              · simp at hStep
              · next pair hRecv =>
                simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
                obtain ⟨_, hEq⟩ := hStep
                subst hEq
                refine observableSlotsConfinedToCore_trans hStoreC ?_
                refine observableSlotsConfinedToCore_trans hRunC ?_
                refine observableSlotsConfinedToCore_trans hConsumeC ?_
                exact endpointReceiveDual_confinedToBootCore st3 _ endpointId receiver _ replyId
                  hRecv
        · simp at hStep
    · simp at hStep


/-! #### CDT and capability-store steps

The capability operations thread through the CDT bookkeeping fields, which the
scheduler and the machine do not read and which no per-core slot lives in. -/

/-- A CDT-field-only rewrite frames the scheduler and every register bank. -/
theorem attachSlotToCdtNode_confinedToCore (st : SystemState) (ref : SlotRef)
    (node : CdtNodeId) (c₀ : CoreId) :
    observableSlotsConfinedToCore st (SystemState.attachSlotToCdtNode st ref node) c₀ :=
  observableSlotsConfinedToCore_of_scheduler_machine_eq c₀ rfl rfl

theorem detachSlotFromCdt_confinedToCore (st : SystemState) (ref : SlotRef) (c₀ : CoreId) :
    observableSlotsConfinedToCore st (SystemState.detachSlotFromCdt st ref) c₀ := by
  refine observableSlotsConfinedToCore_of_scheduler_machine_eq c₀ ?_ ?_ <;>
    unfold SystemState.detachSlotFromCdt <;> split <;> rfl

theorem ensureCdtNodeForSlot_confinedToCore (st : SystemState) (ref : SlotRef) (c₀ : CoreId) :
    observableSlotsConfinedToCore st (SystemState.ensureCdtNodeForSlot st ref).2 c₀ := by
  refine observableSlotsConfinedToCore_of_scheduler_machine_eq c₀ ?_ ?_ <;>
    unfold SystemState.ensureCdtNodeForSlot <;> split <;> rfl

theorem cdtEdge_confinedToCore (st : SystemState) (cdt' : CapDerivationTree) (c₀ : CoreId) :
    observableSlotsConfinedToCore st { st with cdt := cdt' } c₀ :=
  observableSlotsConfinedToCore_of_scheduler_machine_eq c₀ rfl rfl

theorem cspaceLookupSlot_confinedToCore (st st' : SystemState) (addr : CSpaceAddr)
    (cap : Capability) (c₀ : CoreId) (hStep : cspaceLookupSlot addr st = .ok (cap, st')) :
    observableSlotsConfinedToCore st st' c₀ :=
  observableSlotsConfinedToCore_of_eq c₀ (cspaceLookupSlot_preserves_state st st' addr cap hStep)

theorem cspaceInsertSlot_confinedToCore (st st' : SystemState) (dst : CSpaceAddr)
    (cap : Capability) (c₀ : CoreId) (hStep : cspaceInsertSlot dst cap st = .ok ((), st')) :
    observableSlotsConfinedToCore st st' c₀ :=
  observableSlotsConfinedToCore_of_scheduler_machine_eq c₀
    (cspaceInsertSlot_preserves_scheduler st st' dst cap hStep)
    (cspaceInsertSlot_preserves_machine st st' dst cap hStep)

theorem cspaceDeleteSlotCore_confinedToCore (st st' : SystemState) (addr : CSpaceAddr)
    (c₀ : CoreId) (hStep : cspaceDeleteSlotCore addr st = .ok ((), st')) :
    observableSlotsConfinedToCore st st' c₀ := by
  unfold cspaceDeleteSlotCore at hStep
  cases hObj : st.objects[addr.cnode]? with
  | none => simp [hObj] at hStep
  | some obj =>
    cases obj with
    | cnode cn =>
      simp only [hObj] at hStep
      cases hStore : storeObject addr.cnode (.cnode (cn.remove addr.slot)) st with
      | error e => simp [hStore] at hStep
      | ok pair =>
        simp only [hStore] at hStep
        cases hRef : storeCapabilityRef addr none pair.2 with
        | error e => simp [hRef] at hStep
        | ok pairR =>
          simp only [hRef, Except.ok.injEq, Prod.mk.injEq] at hStep
          obtain ⟨_, hEq⟩ := hStep
          subst hEq
          refine observableSlotsConfinedToCore_trans
            (storeObject_confinedToCore st pair.2 addr.cnode _ c₀ hStore) ?_
          refine observableSlotsConfinedToCore_trans
            (storeCapabilityRef_confinedToCore pair.2 pairR.2 addr none c₀ hRef) ?_
          exact detachSlotFromCdt_confinedToCore pairR.2 addr c₀
    | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ =>
      simp [hObj] at hStep

/-- SM8.B.3: `cspaceDeleteSlot` writes only the object store and the CDT. -/
theorem cspaceDeleteSlot_confinedToCore (st st' : SystemState) (addr : CSpaceAddr) (c₀ : CoreId)
    (hStep : SeLe4n.Kernel.cspaceDeleteSlot addr st = .ok ((), st')) :
    observableSlotsConfinedToCore st st' c₀ := by
  unfold SeLe4n.Kernel.cspaceDeleteSlot at hStep
  split at hStep
  · simp at hStep
  · exact cspaceDeleteSlotCore_confinedToCore st st' addr c₀ hStep

/-- SM8.B.3: `cspaceCopy` writes only the object store and the CDT. -/
theorem cspaceCopy_confinedToCore (st st' : SystemState) (src dst : CSpaceAddr) (c₀ : CoreId)
    (hStep : SeLe4n.Kernel.cspaceCopy src dst st = .ok ((), st')) :
    observableSlotsConfinedToCore st st' c₀ := by
  unfold SeLe4n.Kernel.cspaceCopy at hStep
  cases hL : cspaceLookupSlot src st with
  | error e => simp [hL] at hStep
  | ok pair =>
    obtain ⟨cap, stL⟩ := pair
    have hEqL : stL = st := cspaceLookupSlot_preserves_state st stL src cap hL
    subst stL
    simp only [hL] at hStep
    cases hNN : cap.toNonNull? with
    | none => simp [hNN] at hStep
    | some capNN =>
      simp only [hNN] at hStep
      cases hIns : cspaceInsertSlot dst capNN.val st with
      | error e => simp [hIns] at hStep
      | ok pairI =>
        simp only [hIns, Except.ok.injEq, Prod.mk.injEq] at hStep
        obtain ⟨_, hEq⟩ := hStep
        subst hEq
        refine observableSlotsConfinedToCore_trans
          (cspaceInsertSlot_confinedToCore st pairI.2 dst capNN.val c₀ hIns) ?_
        refine observableSlotsConfinedToCore_trans
          (ensureCdtNodeForSlot_confinedToCore pairI.2 src c₀) ?_
        refine observableSlotsConfinedToCore_trans
          (ensureCdtNodeForSlot_confinedToCore _ dst c₀) ?_
        exact cdtEdge_confinedToCore _ _ c₀

/-- SM8.B.3: `cspaceMove` writes only the object store and the CDT. -/
theorem cspaceMove_confinedToCore (st st' : SystemState) (src dst : CSpaceAddr) (c₀ : CoreId)
    (hStep : SeLe4n.Kernel.cspaceMove src dst st = .ok ((), st')) :
    observableSlotsConfinedToCore st st' c₀ := by
  unfold SeLe4n.Kernel.cspaceMove at hStep
  split at hStep
  · simp at hStep
  · cases hL : cspaceLookupSlot src st with
    | error e => simp [hL] at hStep
    | ok pair =>
      obtain ⟨cap, stL⟩ := pair
      have hEqL : stL = st := cspaceLookupSlot_preserves_state st stL src cap hL
      subst stL
      simp only [hL] at hStep
      cases hNN : cap.toNonNull? with
      | none => simp [hNN] at hStep
      | some capNN =>
        simp only [hNN] at hStep
        cases hIns : cspaceInsertSlot dst capNN.val st with
        | error e => simp [hIns] at hStep
        | ok pairI =>
          simp only [hIns] at hStep
          have hInsC := cspaceInsertSlot_confinedToCore st pairI.2 dst capNN.val c₀ hIns
          cases hDel : cspaceDeleteSlotCore src pairI.2 with
          | error e => simp [hDel] at hStep
          | ok pairD =>
            simp only [hDel] at hStep
            have hDelC := cspaceDeleteSlotCore_confinedToCore pairI.2 pairD.2 src c₀ hDel
            cases hNode : SystemState.lookupCdtNodeOfSlot pairI.2 src with
            | none =>
              simp only [hNode, Except.ok.injEq, Prod.mk.injEq] at hStep
              obtain ⟨_, hEq⟩ := hStep
              subst hEq
              exact observableSlotsConfinedToCore_trans hInsC hDelC
            | some srcNode =>
              simp only [hNode, Except.ok.injEq, Prod.mk.injEq] at hStep
              obtain ⟨_, hEq⟩ := hStep
              subst hEq
              exact observableSlotsConfinedToCore_trans hInsC
                (observableSlotsConfinedToCore_trans hDelC
                  (attachSlotToCdtNode_confinedToCore pairD.2 dst srcNode c₀))


/-- SM8.B.3: `cspaceMint` writes only the object store (the derived cap lands
through `cspaceInsertSlot`). -/
theorem cspaceMint_confinedToCore (st st' : SystemState) (src dst : CSpaceAddr)
    (rights : AccessRightSet) (badge : Option SeLe4n.Badge) (c₀ : CoreId)
    (hStep : SeLe4n.Kernel.cspaceMint src dst rights badge st = .ok ((), st')) :
    observableSlotsConfinedToCore st st' c₀ := by
  unfold SeLe4n.Kernel.cspaceMint at hStep
  cases hL : cspaceLookupSlot src st with
  | error e => simp [hL] at hStep
  | ok pair =>
    obtain ⟨parent, stL⟩ := pair
    have hEqL : stL = st := cspaceLookupSlot_preserves_state st stL src parent hL
    subst stL
    simp only [hL] at hStep
    cases hNN : parent.toNonNull? with
    | none => simp [hNN] at hStep
    | some parentNN =>
      simp only [hNN] at hStep
      cases hMint : mintDerivedCap parentNN rights badge with
      | error e => simp [hMint] at hStep
      | ok child =>
        simp only [hMint] at hStep
        exact cspaceInsertSlot_confinedToCore st st' dst child c₀ hStep

/-- SM8.B.3: `cspaceRevoke` writes only the object store and the capability
reference map. -/
theorem cspaceRevoke_confinedToCore (st st' : SystemState) (addr : CSpaceAddr) (c₀ : CoreId)
    (hStep : SeLe4n.Kernel.cspaceRevoke addr st = .ok ((), st')) :
    observableSlotsConfinedToCore st st' c₀ := by
  unfold SeLe4n.Kernel.cspaceRevoke at hStep
  cases hL : cspaceLookupSlot addr st with
  | error e => simp [hL] at hStep
  | ok pair =>
    obtain ⟨parent, stL⟩ := pair
    have hEqL : stL = st := cspaceLookupSlot_preserves_state st stL addr parent hL
    subst stL
    simp only [hL] at hStep
    cases hObj : st.objects[addr.cnode]? with
    | none => simp [hObj] at hStep
    | some obj =>
      cases obj with
      | cnode cn =>
        simp only [hObj] at hStep
        cases hStore : storeObject addr.cnode
            (.cnode (cn.revokeTargetLocal addr.slot parent.target)) st with
        | error e => simp [hStore] at hStep
        | ok pairS =>
          simp only [hStore, Except.ok.injEq, Prod.mk.injEq] at hStep
          obtain ⟨_, hEq⟩ := hStep
          subst hEq
          refine observableSlotsConfinedToCore_trans
            (storeObject_confinedToCore st pairS.2 addr.cnode _ c₀ hStore) ?_
          exact observableSlotsConfinedToCore_of_scheduler_machine_eq c₀
            (revokeAndClearRefsState_preserves_scheduler cn addr.slot parent.target addr.cnode
              pairS.2)
            (revokeAndClearRefsState_preserves_machine cn addr.slot parent.target addr.cnode
              pairS.2)
      | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ =>
        simp [hObj] at hStep

/-- SM8.B.3: `cspaceMutate` writes only the object store and the capability
reference map. -/
theorem cspaceMutate_confinedToCore (st st' : SystemState) (addr : CSpaceAddr)
    (rights : AccessRightSet) (badge : Option SeLe4n.Badge) (c₀ : CoreId)
    (hStep : SeLe4n.Kernel.cspaceMutate addr rights badge st = .ok ((), st')) :
    observableSlotsConfinedToCore st st' c₀ := by
  unfold SeLe4n.Kernel.cspaceMutate at hStep
  cases hL : cspaceLookupSlot addr st with
  | error e => simp [hL] at hStep
  | ok pair =>
    obtain ⟨cap, stL⟩ := pair
    have hEqL : stL = st := cspaceLookupSlot_preserves_state st stL addr cap hL
    subst stL
    simp only [hL] at hStep
    split at hStep
    · simp at hStep
    · split at hStep
      · cases hObj : st.objects[addr.cnode]? with
        | none => simp [hObj] at hStep
        | some obj =>
          cases obj with
          | cnode cn =>
            simp only [hObj] at hStep
            split at hStep
            · simp at hStep
            · next stMid hStore =>
              refine observableSlotsConfinedToCore_trans
                (storeObject_confinedToCore st stMid addr.cnode _ c₀ hStore) ?_
              exact storeCapabilityRef_confinedToCore stMid st' addr _ c₀ hStep
          | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _
          | schedContext _ | reply _ => simp [hObj] at hStep
      · simp at hStep

/-- SM8.B.3: `lifecycleRetypeObject` writes only the object store (it installs
the new object through `storeObject`). -/
theorem lifecycleRetypeObject_confinedToCore (st st' : SystemState) (authority : CSpaceAddr)
    (target : SeLe4n.ObjId) (newObj : KernelObject) (c₀ : CoreId)
    (hStep : Internal.lifecycleRetypeObject authority target newObj st = .ok ((), st')) :
    observableSlotsConfinedToCore st st' c₀ := by
  obtain ⟨_, _, _, _, _, _, hStore⟩ :=
    lifecycleRetypeObject_ok_as_storeObject st st' authority target newObj hStep
  exact storeObject_confinedToCore st st' target newObj c₀ hStore

/-- SM8.B.3: `lifecycleRevokeDeleteRetype` writes only the object store, the
capability reference map and the CDT. -/
theorem lifecycleRevokeDeleteRetype_confinedToCore (st st' : SystemState)
    (authority cleanup : CSpaceAddr) (target : SeLe4n.ObjId) (newObj : KernelObject)
    (c₀ : CoreId)
    (hStep : lifecycleRevokeDeleteRetype authority cleanup target newObj st = .ok ((), st')) :
    observableSlotsConfinedToCore st st' c₀ := by
  unfold lifecycleRevokeDeleteRetype at hStep
  split at hStep
  · simp at hStep
  · cases hRev : SeLe4n.Kernel.cspaceRevoke cleanup st with
    | error e => simp [hRev] at hStep
    | ok pairR =>
      simp only [hRev] at hStep
      have hRevC := cspaceRevoke_confinedToCore st pairR.2 cleanup c₀ hRev
      cases hDel : SeLe4n.Kernel.cspaceDeleteSlot cleanup pairR.2 with
      | error e => simp [hDel] at hStep
      | ok pairD =>
        simp only [hDel] at hStep
        have hDelC := cspaceDeleteSlot_confinedToCore pairR.2 pairD.2 cleanup c₀ hDel
        cases hLook : cspaceLookupSlot cleanup pairD.2 with
        | ok _ => simp [hLook] at hStep
        | error e =>
          cases e with
          | invalidCapability =>
            simp only [hLook] at hStep
            exact observableSlotsConfinedToCore_trans hRevC
              (observableSlotsConfinedToCore_trans hDelC
                (lifecycleRetypeObject_confinedToCore pairD.2 st' authority target newObj c₀
                  hStep))
          | _ => simp [hLook] at hStep

/-- SM8.B.3: `vspaceMapPage` writes only the VSpace root object. -/
theorem vspaceMapPage_confinedToCore (st st' : SystemState) (asid : SeLe4n.ASID)
    (vaddr : SeLe4n.VAddr) (paddr : SeLe4n.PAddr) (perms : PagePermissions) (c₀ : CoreId)
    (hStep : Architecture.vspaceMapPage asid vaddr paddr perms st = .ok ((), st')) :
    observableSlotsConfinedToCore st st' c₀ := by
  unfold Architecture.vspaceMapPage at hStep
  cases hRoot : Architecture.resolveAsidRoot st asid with
  | none => simp [hRoot] at hStep
  | some pair =>
    obtain ⟨rootId, root⟩ := pair
    simp only [hRoot] at hStep
    split at hStep
    · simp at hStep
    · split at hStep
      · simp at hStep
      · cases hMap : root.mapPage vaddr paddr perms with
        | none => simp [hMap] at hStep
        | some root' =>
          simp only [hMap] at hStep
          exact storeObject_confinedToCore st st' rootId _ c₀ hStep

/-- SM8.B.3: `vspaceUnmapPage` writes only the VSpace root object. -/
theorem vspaceUnmapPage_confinedToCore (st st' : SystemState) (asid : SeLe4n.ASID)
    (vaddr : SeLe4n.VAddr) (c₀ : CoreId)
    (hStep : Architecture.vspaceUnmapPage asid vaddr st = .ok ((), st')) :
    observableSlotsConfinedToCore st st' c₀ := by
  unfold Architecture.vspaceUnmapPage at hStep
  cases hRoot : Architecture.resolveAsidRoot st asid with
  | none => simp [hRoot] at hStep
  | some pair =>
    obtain ⟨rootId, root⟩ := pair
    simp only [hRoot] at hStep
    cases hUnmap : root.unmapPage vaddr with
    | none => simp [hUnmap] at hStep
    | some root' =>
      simp only [hUnmap] at hStep
      exact storeObject_confinedToCore st st' rootId _ c₀ hStep

/-- SM8.B.3: `vspaceLookup` is a pure read. -/
theorem vspaceLookup_confinedToCore (st st' : SystemState) (asid : SeLe4n.ASID)
    (vaddr : SeLe4n.VAddr) (paddr : SeLe4n.PAddr) (c₀ : CoreId)
    (hStep : Architecture.vspaceLookup asid vaddr st = .ok (paddr, st')) :
    observableSlotsConfinedToCore st st' c₀ :=
  observableSlotsConfinedToCore_of_eq c₀ (vspaceLookup_preserves_state st asid vaddr paddr st' hStep)

/-- SM8.B.3: `registerService` writes only the service registry. -/
theorem registerService_confinedToCore (st st' : SystemState) (reg : ServiceRegistration)
    (c₀ : CoreId) (hStep : registerService reg st = .ok ((), st')) :
    observableSlotsConfinedToCore st st' c₀ := by
  refine observableSlotsConfinedToCore_of_scheduler_machine_eq c₀
    (registerService_preserves_scheduler st st' reg hStep) ?_
  unfold registerService at hStep
  split at hStep
  · cases hStep
  · split at hStep
    · cases hStep
    · cases hTarget : reg.endpointCap.target with
      | object epId =>
        simp only [hTarget] at hStep
        cases hObj : st.objects[epId]? with
        | none => simp [hObj] at hStep
        | some obj =>
          cases obj <;> simp [hObj] at hStep
          case endpoint ep =>
            split at hStep
            · cases hStep
            · split at hStep
              · cases hStep
              · simp at hStep; cases hStep; rfl
      | cnodeSlot => simp [hTarget] at hStep
      | replyCap => simp [hTarget] at hStep

/-- SM8.B.3: the checked service registration is either the unchecked one or a
denial, so it is confined too. -/
theorem registerServiceChecked_confinedToCore (ctx : LabelingContext) (st st' : SystemState)
    (caller : SeLe4n.ThreadId) (reg : ServiceRegistration) (c₀ : CoreId)
    (hStep : registerServiceChecked ctx caller reg st = .ok ((), st')) :
    observableSlotsConfinedToCore st st' c₀ := by
  have hFlow := enforcementSoundness_registerServiceChecked ctx caller reg st st' hStep
  rw [registerServiceChecked_eq_registerService_when_allowed ctx caller reg st hFlow] at hStep
  exact registerService_confinedToCore st st' reg c₀ hStep


/-! ### §4b  The thirty-five per-operation non-interference theorems

One theorem per `KernelOperation` variant.  Each takes exactly the hypotheses
its `NonInterferenceStep` constructor takes — no more — and concludes
`lowEquivalent_smp`, i.e. the observer's view is preserved on **every** core,
not merely on the boot core.  The confinement premise of
`nonInterference_perCore` is discharged from §4a for all thirty-one
operationally-specified constructors.

The four catch-all constructors (`syscallDispatchHigh`,
`endpointCallWithDonationHigh`, `endpointReplyWithReversionHigh`,
`handleInterrupt`) take it as an explicit argument, because they range over
transitions whose bodies the inductive does not pin — the live cross-core
dispatch is one of them, and it genuinely writes a remote core's run queue.
Supplying the premise there is the honest treatment, not a gap: the SM6 phases
prove the corresponding cross-core statements directly
(`endpointCallOnCore_call_path_NI_smp`, `notificationSignalOnCore_NI_smp`,
`endpointReplyOnCore_NI_smp`), and §5 records the split as a checked fact. -/

theorem nonInterference_perCore_chooseThread (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState) (next : Option SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt) (hIdxComplete : objectIndexSetComplete st)
    (hObjSetInv : st.objectIndexSet.table.invExt)
    (hStep : SeLe4n.Kernel.chooseThread st = .ok (next, st')) :
    lowEquivalent_smp ctx observer st' st :=
  nonInterference_perCore ctx observer st st' hObjInv hIdxComplete hObjSetInv
    (.chooseThread next hStep) (chooseThread_confinedToCore st st' next bootCoreId hStep)

theorem nonInterference_perCore_endpointSendDual (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState) (eid : SeLe4n.ObjId) (sender : SeLe4n.ThreadId) (msg : IpcMessage)
    (hObjInv : st.objects.invExt) (hIdxComplete : objectIndexSetComplete st)
    (hObjSetInv : st.objectIndexSet.table.invExt)
    (hEndpointHigh : objectObservable ctx observer eid = false)
    (hSenderHigh : threadObservable ctx observer sender = false)
    (hSenderObjHigh : objectObservable ctx observer sender.toObjId = false)
    (hCoherent : ∀ tid : SeLe4n.ThreadId, threadObservable ctx observer tid = false →
      objectObservable ctx observer tid.toObjId = false)
    (hStep : endpointSendDual eid sender msg st = .ok ((), st'))
    (hRecvQueueHeadHigh : ∀ ep receiver, st.objects[eid]? = some (.endpoint ep) →
      ep.receiveQ.head = some receiver → threadObservable ctx observer receiver = false)
    (hRecvQueueNextHigh : ∀ ep receiver recvTcb nextTid,
      st.objects[eid]? = some (.endpoint ep) → ep.receiveQ.head = some receiver →
      st.objects[receiver.toObjId]? = some (.tcb recvTcb) → recvTcb.queueNext = some nextTid →
      objectObservable ctx observer nextTid.toObjId = false)
    (hSendQueueTailHigh : ∀ ep tailTid, st.objects[eid]? = some (.endpoint ep) →
      ep.sendQ.tail = some tailTid → objectObservable ctx observer tailTid.toObjId = false) :
    lowEquivalent_smp ctx observer st' st :=
  nonInterference_perCore ctx observer st st' hObjInv hIdxComplete hObjSetInv
    (.endpointSendDual eid sender msg hEndpointHigh hSenderHigh hSenderObjHigh hCoherent hStep
      hRecvQueueHeadHigh hRecvQueueNextHigh hSendQueueTailHigh)
    (endpointSendDual_confinedToBootCore st st' eid sender msg hStep)

theorem nonInterference_perCore_cspaceMint (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState) (src dst : CSpaceAddr) (rights : AccessRightSet)
    (badge : Option SeLe4n.Badge)
    (hObjInv : st.objects.invExt) (hIdxComplete : objectIndexSetComplete st)
    (hObjSetInv : st.objectIndexSet.table.invExt)
    (hSrcHigh : objectObservable ctx observer src.cnode = false)
    (hDstHigh : objectObservable ctx observer dst.cnode = false)
    (hStep : SeLe4n.Kernel.cspaceMint src dst rights badge st = .ok ((), st')) :
    lowEquivalent_smp ctx observer st' st :=
  nonInterference_perCore ctx observer st st' hObjInv hIdxComplete hObjSetInv
    (.cspaceMint src dst rights badge hSrcHigh hDstHigh hStep)
    (cspaceMint_confinedToCore st st' src dst rights badge bootCoreId hStep)

theorem nonInterference_perCore_cspaceRevoke (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState) (addr : CSpaceAddr)
    (hObjInv : st.objects.invExt) (hIdxComplete : objectIndexSetComplete st)
    (hObjSetInv : st.objectIndexSet.table.invExt)
    (hAddrHigh : objectObservable ctx observer addr.cnode = false)
    (hStep : SeLe4n.Kernel.cspaceRevoke addr st = .ok ((), st')) :
    lowEquivalent_smp ctx observer st' st :=
  nonInterference_perCore ctx observer st st' hObjInv hIdxComplete hObjSetInv
    (.cspaceRevoke addr hAddrHigh hStep)
    (cspaceRevoke_confinedToCore st st' addr bootCoreId hStep)

theorem nonInterference_perCore_lifecycleRetype (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState) (authority : CSpaceAddr) (target : SeLe4n.ObjId)
    (newObj : KernelObject)
    (hObjInv : st.objects.invExt) (hIdxComplete : objectIndexSetComplete st)
    (hObjSetInv : st.objectIndexSet.table.invExt)
    (hTargetHigh : objectObservable ctx observer target = false)
    (hStep : Internal.lifecycleRetypeObject authority target newObj st = .ok ((), st')) :
    lowEquivalent_smp ctx observer st' st :=
  nonInterference_perCore ctx observer st st' hObjInv hIdxComplete hObjSetInv
    (.lifecycleRetype authority target newObj hTargetHigh hStep)
    (lifecycleRetypeObject_confinedToCore st st' authority target newObj bootCoreId hStep)

theorem nonInterference_perCore_lifecycleRevokeDeleteRetype (ctx : LabelingContext)
    (observer : IfObserver) (st st' : SystemState) (authority cleanup : CSpaceAddr)
    (target : SeLe4n.ObjId) (newObj : KernelObject)
    (hObjInv : st.objects.invExt) (hIdxComplete : objectIndexSetComplete st)
    (hObjSetInv : st.objectIndexSet.table.invExt)
    (hCleanupHigh : objectObservable ctx observer cleanup.cnode = false)
    (hTargetHigh : objectObservable ctx observer target = false)
    (hStep : lifecycleRevokeDeleteRetype authority cleanup target newObj st = .ok ((), st')) :
    lowEquivalent_smp ctx observer st' st :=
  nonInterference_perCore ctx observer st st' hObjInv hIdxComplete hObjSetInv
    (.lifecycleRevokeDeleteRetype authority cleanup target newObj hCleanupHigh hTargetHigh hStep)
    (lifecycleRevokeDeleteRetype_confinedToCore st st' authority cleanup target newObj bootCoreId
      hStep)

theorem nonInterference_perCore_notificationSignal (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState) (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge)
    (hObjInv : st.objects.invExt) (hIdxComplete : objectIndexSetComplete st)
    (hObjSetInv : st.objectIndexSet.table.invExt)
    (hNtfnHigh : objectObservable ctx observer notificationId = false)
    (hCoherent : ∀ tid : SeLe4n.ThreadId, threadObservable ctx observer tid = false →
      objectObservable ctx observer tid.toObjId = false)
    (hWaiterDomain : ∀ ntfn tid, st.objects[notificationId]? = some (.notification ntfn) →
      tid ∈ ntfn.waitingThreads → threadObservable ctx observer tid = false)
    (hStep : SeLe4n.Kernel.notificationSignal notificationId badge st = .ok ((), st')) :
    lowEquivalent_smp ctx observer st' st :=
  nonInterference_perCore ctx observer st st' hObjInv hIdxComplete hObjSetInv
    (.notificationSignal notificationId badge hNtfnHigh hCoherent hWaiterDomain hStep)
    (notificationSignal_confinedToBootCore st st' notificationId badge hStep)

theorem nonInterference_perCore_notificationWait (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState) (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId)
    (result : Option SeLe4n.Badge)
    (hObjInv : st.objects.invExt) (hIdxComplete : objectIndexSetComplete st)
    (hObjSetInv : st.objectIndexSet.table.invExt)
    (hNtfnHigh : objectObservable ctx observer notificationId = false)
    (hWaiterHigh : threadObservable ctx observer waiter = false)
    (hWaiterObjHigh : objectObservable ctx observer waiter.toObjId = false)
    (hStep : SeLe4n.Kernel.notificationWait notificationId waiter st = .ok (result, st')) :
    lowEquivalent_smp ctx observer st' st :=
  nonInterference_perCore ctx observer st st' hObjInv hIdxComplete hObjSetInv
    (.notificationWait notificationId waiter result hNtfnHigh hWaiterHigh hWaiterObjHigh hStep)
    (notificationWait_confinedToBootCore st st' notificationId waiter result hStep)

theorem nonInterference_perCore_cspaceInsertSlot (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState) (dst : CSpaceAddr) (cap : Capability)
    (hObjInv : st.objects.invExt) (hIdxComplete : objectIndexSetComplete st)
    (hObjSetInv : st.objectIndexSet.table.invExt)
    (hDstHigh : objectObservable ctx observer dst.cnode = false)
    (hStep : cspaceInsertSlot dst cap st = .ok ((), st')) :
    lowEquivalent_smp ctx observer st' st :=
  nonInterference_perCore ctx observer st st' hObjInv hIdxComplete hObjSetInv
    (.cspaceInsertSlot dst cap hDstHigh hStep)
    (cspaceInsertSlot_confinedToCore st st' dst cap bootCoreId hStep)

theorem nonInterference_perCore_schedule (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState)
    (hObjInv : st.objects.invExt) (hIdxComplete : objectIndexSetComplete st)
    (hObjSetInv : st.objectIndexSet.table.invExt)
    (hCurrentHigh : ∀ t, st.scheduler.currentOnCore bootCoreId = some t →
      threadObservable ctx observer t = false)
    (hAllRunnable : ∀ tid, tid ∈ st.scheduler.runnable →
      threadObservable ctx observer tid = false)
    (hStep : SeLe4n.Kernel.schedule st = .ok ((), st')) :
    lowEquivalent_smp ctx observer st' st :=
  nonInterference_perCore ctx observer st st' hObjInv hIdxComplete hObjSetInv
    (.schedule hCurrentHigh hAllRunnable hStep) (schedule_confinedToBootCore st st' hStep)

theorem nonInterference_perCore_vspaceMapPage (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState) (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) (paddr : SeLe4n.PAddr)
    (hObjInv : st.objects.invExt) (hIdxComplete : objectIndexSetComplete st)
    (hObjSetInv : st.objectIndexSet.table.invExt)
    (hRootHigh : ∀ rootId root, Architecture.resolveAsidRoot st asid = some (rootId, root) →
      objectObservable ctx observer rootId = false)
    (hStep : Architecture.vspaceMapPage asid vaddr paddr default st = .ok ((), st')) :
    lowEquivalent_smp ctx observer st' st :=
  nonInterference_perCore ctx observer st st' hObjInv hIdxComplete hObjSetInv
    (.vspaceMapPage asid vaddr paddr hRootHigh hStep)
    (vspaceMapPage_confinedToCore st st' asid vaddr paddr default bootCoreId hStep)

theorem nonInterference_perCore_vspaceUnmapPage (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState) (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (hObjInv : st.objects.invExt) (hIdxComplete : objectIndexSetComplete st)
    (hObjSetInv : st.objectIndexSet.table.invExt)
    (hRootHigh : ∀ rootId root, Architecture.resolveAsidRoot st asid = some (rootId, root) →
      objectObservable ctx observer rootId = false)
    (hStep : Architecture.vspaceUnmapPage asid vaddr st = .ok ((), st')) :
    lowEquivalent_smp ctx observer st' st :=
  nonInterference_perCore ctx observer st st' hObjInv hIdxComplete hObjSetInv
    (.vspaceUnmapPage asid vaddr hRootHigh hStep)
    (vspaceUnmapPage_confinedToCore st st' asid vaddr bootCoreId hStep)

theorem nonInterference_perCore_vspaceLookup (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState) (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) (paddr : SeLe4n.PAddr)
    (hObjInv : st.objects.invExt) (hIdxComplete : objectIndexSetComplete st)
    (hObjSetInv : st.objectIndexSet.table.invExt)
    (hStep : Architecture.vspaceLookup asid vaddr st = .ok (paddr, st')) :
    lowEquivalent_smp ctx observer st' st :=
  nonInterference_perCore ctx observer st st' hObjInv hIdxComplete hObjSetInv
    (.vspaceLookup asid vaddr paddr hStep)
    (vspaceLookup_confinedToCore st st' asid vaddr paddr bootCoreId hStep)

theorem nonInterference_perCore_cspaceCopy (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState) (src dst : CSpaceAddr)
    (hObjInv : st.objects.invExt) (hIdxComplete : objectIndexSetComplete st)
    (hObjSetInv : st.objectIndexSet.table.invExt)
    (hSrcHigh : objectObservable ctx observer src.cnode = false)
    (hDstHigh : objectObservable ctx observer dst.cnode = false)
    (hStep : SeLe4n.Kernel.cspaceCopy src dst st = .ok ((), st')) :
    lowEquivalent_smp ctx observer st' st :=
  nonInterference_perCore ctx observer st st' hObjInv hIdxComplete hObjSetInv
    (.cspaceCopy src dst hSrcHigh hDstHigh hStep)
    (cspaceCopy_confinedToCore st st' src dst bootCoreId hStep)

theorem nonInterference_perCore_cspaceMove (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState) (src dst : CSpaceAddr)
    (hObjInv : st.objects.invExt) (hIdxComplete : objectIndexSetComplete st)
    (hObjSetInv : st.objectIndexSet.table.invExt)
    (hSrcHigh : objectObservable ctx observer src.cnode = false)
    (hDstHigh : objectObservable ctx observer dst.cnode = false)
    (hStep : SeLe4n.Kernel.cspaceMove src dst st = .ok ((), st')) :
    lowEquivalent_smp ctx observer st' st :=
  nonInterference_perCore ctx observer st st' hObjInv hIdxComplete hObjSetInv
    (.cspaceMove src dst hSrcHigh hDstHigh hStep)
    (cspaceMove_confinedToCore st st' src dst bootCoreId hStep)

theorem nonInterference_perCore_cspaceDeleteSlot (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState) (addr : CSpaceAddr)
    (hObjInv : st.objects.invExt) (hIdxComplete : objectIndexSetComplete st)
    (hObjSetInv : st.objectIndexSet.table.invExt)
    (hAddrHigh : objectObservable ctx observer addr.cnode = false)
    (hStep : SeLe4n.Kernel.cspaceDeleteSlot addr st = .ok ((), st')) :
    lowEquivalent_smp ctx observer st' st :=
  nonInterference_perCore ctx observer st st' hObjInv hIdxComplete hObjSetInv
    (.cspaceDeleteSlot addr hAddrHigh hStep)
    (cspaceDeleteSlot_confinedToCore st st' addr bootCoreId hStep)

theorem nonInterference_perCore_endpointReply (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState) (replier target : SeLe4n.ThreadId) (msg : IpcMessage)
    (hObjInv : st.objects.invExt) (hIdxComplete : objectIndexSetComplete st)
    (hObjSetInv : st.objectIndexSet.table.invExt)
    (hTargetHigh : threadObservable ctx observer target = false)
    (hTargetObjHigh : objectObservable ctx observer target.toObjId = false)
    (hStep : endpointReply replier target msg st = .ok ((), st')) :
    lowEquivalent_smp ctx observer st' st :=
  nonInterference_perCore ctx observer st st' hObjInv hIdxComplete hObjSetInv
    (.endpointReply replier target msg hTargetHigh hTargetObjHigh hStep)
    (endpointReply_confinedToBootCore st st' replier target msg hStep)

theorem nonInterference_perCore_endpointReceiveDual (ctx : LabelingContext)
    (observer : IfObserver) (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver sender : SeLe4n.ThreadId) (replyId : Option SeLe4n.ReplyId)
    (hObjInv : st.objects.invExt) (hIdxComplete : objectIndexSetComplete st)
    (hObjSetInv : st.objectIndexSet.table.invExt)
    (hEndpointHigh : objectObservable ctx observer endpointId = false)
    (hReceiverHigh : threadObservable ctx observer receiver = false)
    (hReceiverObjHigh : objectObservable ctx observer receiver.toObjId = false)
    (hCoherent : ∀ tid : SeLe4n.ThreadId, threadObservable ctx observer tid = false →
      objectObservable ctx observer tid.toObjId = false)
    (hStep : endpointReceiveDual endpointId receiver replyId st = .ok (sender, st'))
    (hSendQueueHeadHigh : ∀ ep sender, st.objects[endpointId]? = some (.endpoint ep) →
      ep.sendQ.head = some sender → threadObservable ctx observer sender = false)
    (hSendQueueNextHigh : ∀ ep sender senderTcb nextTid,
      st.objects[endpointId]? = some (.endpoint ep) → ep.sendQ.head = some sender →
      st.objects[sender.toObjId]? = some (.tcb senderTcb) → senderTcb.queueNext = some nextTid →
      objectObservable ctx observer nextTid.toObjId = false)
    (hRecvQueueTailHigh : ∀ ep tailTid, st.objects[endpointId]? = some (.endpoint ep) →
      ep.receiveQ.tail = some tailTid → objectObservable ctx observer tailTid.toObjId = false) :
    lowEquivalent_smp ctx observer st' st :=
  nonInterference_perCore ctx observer st st' hObjInv hIdxComplete hObjSetInv
    (.endpointReceiveDualHigh endpointId receiver sender replyId hEndpointHigh hReceiverHigh
      hReceiverObjHigh hCoherent hStep hSendQueueHeadHigh hSendQueueNextHigh hRecvQueueTailHigh)
    (endpointReceiveDual_confinedToBootCore st st' endpointId receiver sender replyId hStep)

theorem nonInterference_perCore_endpointCall (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState) (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId)
    (msg : IpcMessage)
    (hObjInv : st.objects.invExt) (hIdxComplete : objectIndexSetComplete st)
    (hObjSetInv : st.objectIndexSet.table.invExt)
    (hEndpointHigh : objectObservable ctx observer endpointId = false)
    (hCallerHigh : threadObservable ctx observer caller = false)
    (hCallerObjHigh : objectObservable ctx observer caller.toObjId = false)
    (hCoherent : ∀ tid : SeLe4n.ThreadId, threadObservable ctx observer tid = false →
      objectObservable ctx observer tid.toObjId = false)
    (hStep : endpointCall endpointId caller msg st = .ok ((), st'))
    (hRecvQueueHeadHigh : ∀ ep receiver, st.objects[endpointId]? = some (.endpoint ep) →
      ep.receiveQ.head = some receiver → threadObservable ctx observer receiver = false)
    (hRecvQueueNextHigh : ∀ ep receiver recvTcb nextTid,
      st.objects[endpointId]? = some (.endpoint ep) → ep.receiveQ.head = some receiver →
      st.objects[receiver.toObjId]? = some (.tcb recvTcb) → recvTcb.queueNext = some nextTid →
      objectObservable ctx observer nextTid.toObjId = false)
    (hSendQueueTailHigh : ∀ ep tailTid, st.objects[endpointId]? = some (.endpoint ep) →
      ep.sendQ.tail = some tailTid → objectObservable ctx observer tailTid.toObjId = false) :
    lowEquivalent_smp ctx observer st' st :=
  nonInterference_perCore ctx observer st st' hObjInv hIdxComplete hObjSetInv
    (.endpointCallHigh endpointId caller msg hEndpointHigh hCallerHigh hCallerObjHigh hCoherent
      hStep hRecvQueueHeadHigh hRecvQueueNextHigh hSendQueueTailHigh)
    (endpointCall_confinedToBootCore st st' endpointId caller msg hStep)

theorem nonInterference_perCore_endpointReplyRecv (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (replierReceiver replyTarget : SeLe4n.ThreadId) (replyMsg : IpcMessage)
    (replyId : Option SeLe4n.ReplyId)
    (hObjInv : st.objects.invExt) (hIdxComplete : objectIndexSetComplete st)
    (hObjSetInv : st.objectIndexSet.table.invExt)
    (hEndpointHigh : objectObservable ctx observer endpointId = false)
    (hReceiverHigh : threadObservable ctx observer replierReceiver = false)
    (hReceiverObjHigh : objectObservable ctx observer replierReceiver.toObjId = false)
    (hReplyTargetHigh : threadObservable ctx observer replyTarget = false)
    (hReplyTargetObjHigh : objectObservable ctx observer replyTarget.toObjId = false)
    (hCoherent : ∀ tid : SeLe4n.ThreadId, threadObservable ctx observer tid = false →
      objectObservable ctx observer tid.toObjId = false)
    (hStep : endpointReplyRecv endpointId replierReceiver replyTarget replyMsg replyId st
      = .ok ((), st'))
    (hSendQueueHeadHigh : ∀ ep sender, st.objects[endpointId]? = some (.endpoint ep) →
      ep.sendQ.head = some sender → threadObservable ctx observer sender = false)
    (hSendQueueNextHigh : ∀ ep sender senderTcb nextTid,
      st.objects[endpointId]? = some (.endpoint ep) → ep.sendQ.head = some sender →
      st.objects[sender.toObjId]? = some (.tcb senderTcb) → senderTcb.queueNext = some nextTid →
      objectObservable ctx observer nextTid.toObjId = false)
    (hRecvQueueTailHigh : ∀ ep tailTid, st.objects[endpointId]? = some (.endpoint ep) →
      ep.receiveQ.tail = some tailTid → objectObservable ctx observer tailTid.toObjId = false) :
    lowEquivalent_smp ctx observer st' st :=
  nonInterference_perCore ctx observer st st' hObjInv hIdxComplete hObjSetInv
    (.endpointReplyRecvHigh endpointId replierReceiver replyTarget replyMsg replyId hEndpointHigh
      hReceiverHigh hReceiverObjHigh hReplyTargetHigh hReplyTargetObjHigh hCoherent hStep
      hSendQueueHeadHigh hSendQueueNextHigh hRecvQueueTailHigh)
    (endpointReplyRecv_confinedToBootCore st st' endpointId replierReceiver replyTarget replyMsg
      replyId hStep)

theorem nonInterference_perCore_storeObject (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState) (oid : SeLe4n.ObjId) (obj : KernelObject)
    (hObjInv : st.objects.invExt) (hIdxComplete : objectIndexSetComplete st)
    (hObjSetInv : st.objectIndexSet.table.invExt)
    (hOidHigh : objectObservable ctx observer oid = false)
    (hStep : storeObject oid obj st = .ok ((), st')) :
    lowEquivalent_smp ctx observer st' st :=
  nonInterference_perCore ctx observer st st' hObjInv hIdxComplete hObjSetInv
    (.storeObjectHigh oid obj hOidHigh hStep)
    (storeObject_confinedToCore st st' oid obj bootCoreId hStep)

theorem nonInterference_perCore_setCurrentThread (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState) (tid : Option SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt) (hIdxComplete : objectIndexSetComplete st)
    (hObjSetInv : st.objectIndexSet.table.invExt)
    (hTidHigh : ∀ t, tid = some t → threadObservable ctx observer t = false)
    (hCurrentHigh : ∀ t, st.scheduler.currentOnCore bootCoreId = some t →
      threadObservable ctx observer t = false)
    (hStep : setCurrentThread tid st = .ok ((), st')) :
    lowEquivalent_smp ctx observer st' st :=
  nonInterference_perCore ctx observer st st' hObjInv hIdxComplete hObjSetInv
    (.setCurrentThread tid hTidHigh hCurrentHigh hStep)
    (setCurrentThread_confinedToBootCore st st' tid hStep)

theorem nonInterference_perCore_ensureRunnable (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt) (hIdxComplete : objectIndexSetComplete st)
    (hObjSetInv : st.objectIndexSet.table.invExt)
    (hTidHigh : threadObservable ctx observer tid = false)
    (hEq : st' = ensureRunnable st tid) :
    lowEquivalent_smp ctx observer st' st :=
  nonInterference_perCore ctx observer st st' hObjInv hIdxComplete hObjSetInv
    (.ensureRunnableHigh tid hTidHigh hEq)
    (hEq ▸ ensureRunnable_confinedToBootCore st tid)

theorem nonInterference_perCore_removeRunnable (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt) (hIdxComplete : objectIndexSetComplete st)
    (hObjSetInv : st.objectIndexSet.table.invExt)
    (hTidHigh : threadObservable ctx observer tid = false)
    (hEq : st' = removeRunnable st tid) :
    lowEquivalent_smp ctx observer st' st :=
  nonInterference_perCore ctx observer st st' hObjInv hIdxComplete hObjSetInv
    (.removeRunnableHigh tid hTidHigh hEq)
    (hEq ▸ removeRunnable_confinedToBootCore st tid)

theorem nonInterference_perCore_storeTcbIpcStateAndMessage (ctx : LabelingContext)
    (observer : IfObserver) (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState) (msg : Option IpcMessage)
    (hObjInv : st.objects.invExt) (hIdxComplete : objectIndexSetComplete st)
    (hObjSetInv : st.objectIndexSet.table.invExt)
    (hTidObjHigh : objectObservable ctx observer tid.toObjId = false)
    (hStep : storeTcbIpcStateAndMessage st tid ipc msg = .ok st') :
    lowEquivalent_smp ctx observer st' st :=
  nonInterference_perCore ctx observer st st' hObjInv hIdxComplete hObjSetInv
    (.storeTcbIpcStateAndMessageHigh tid ipc msg hTidObjHigh hStep)
    (storeTcbIpcStateAndMessage_confinedToCore st st' tid ipc msg bootCoreId hStep)

theorem nonInterference_perCore_storeTcbQueueLinks (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (prev : Option SeLe4n.ThreadId)
    (pprev : Option QueuePPrev) (next : Option SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt) (hIdxComplete : objectIndexSetComplete st)
    (hObjSetInv : st.objectIndexSet.table.invExt)
    (hTidObjHigh : objectObservable ctx observer tid.toObjId = false)
    (hStep : storeTcbQueueLinks st tid prev pprev next = .ok st') :
    lowEquivalent_smp ctx observer st' st :=
  nonInterference_perCore ctx observer st st' hObjInv hIdxComplete hObjSetInv
    (.storeTcbQueueLinksHigh tid prev pprev next hTidObjHigh hStep)
    (storeTcbQueueLinks_confinedToCore st st' tid prev pprev next bootCoreId hStep)

theorem nonInterference_perCore_cspaceMutate (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState) (addr : CSpaceAddr) (rights : AccessRightSet)
    (badge : Option SeLe4n.Badge)
    (hObjInv : st.objects.invExt) (hIdxComplete : objectIndexSetComplete st)
    (hObjSetInv : st.objectIndexSet.table.invExt)
    (hAddrHigh : objectObservable ctx observer addr.cnode = false)
    (hStep : SeLe4n.Kernel.cspaceMutate addr rights badge st = .ok ((), st')) :
    lowEquivalent_smp ctx observer st' st :=
  nonInterference_perCore ctx observer st st' hObjInv hIdxComplete hObjSetInv
    (.cspaceMutateHigh addr rights badge hAddrHigh hStep)
    (cspaceMutate_confinedToCore st st' addr rights badge bootCoreId hStep)

theorem nonInterference_perCore_handleYield (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState)
    (hObjInv : st.objects.invExt) (hIdxComplete : objectIndexSetComplete st)
    (hObjSetInv : st.objectIndexSet.table.invExt)
    (hCurrentHigh : ∀ t, st.scheduler.currentOnCore bootCoreId = some t →
      threadObservable ctx observer t = false)
    (hAllRunnable : ∀ tid, tid ∈ st.scheduler.runnable →
      threadObservable ctx observer tid = false)
    (hStep : SeLe4n.Kernel.handleYield st = .ok ((), st')) :
    lowEquivalent_smp ctx observer st' st :=
  nonInterference_perCore ctx observer st st' hObjInv hIdxComplete hObjSetInv
    (.handleYield hCurrentHigh hAllRunnable hStep) (handleYield_confinedToBootCore st st' hStep)

theorem nonInterference_perCore_timerTick (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState)
    (hObjInv : st.objects.invExt) (hIdxComplete : objectIndexSetComplete st)
    (hObjSetInv : st.objectIndexSet.table.invExt)
    (hCurrentHigh : ∀ t, st.scheduler.currentOnCore bootCoreId = some t →
      threadObservable ctx observer t = false)
    (hCurrentObjHigh : ∀ t, st.scheduler.currentOnCore bootCoreId = some t →
      objectObservable ctx observer t.toObjId = false)
    (hAllRunnable : ∀ tid, tid ∈ st.scheduler.runnable →
      threadObservable ctx observer tid = false)
    (hStep : SeLe4n.Kernel.timerTick st = .ok ((), st')) :
    lowEquivalent_smp ctx observer st' st :=
  nonInterference_perCore ctx observer st st' hObjInv hIdxComplete hObjSetInv
    (.timerTick hCurrentHigh hCurrentObjHigh hAllRunnable hStep)
    (timerTick_confinedToBootCore st st' hStep)

theorem nonInterference_perCore_syscallDecodeError (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState)
    (hObjInv : st.objects.invExt) (hIdxComplete : objectIndexSetComplete st)
    (hObjSetInv : st.objectIndexSet.table.invExt)
    (hEq : st' = st) :
    lowEquivalent_smp ctx observer st' st :=
  nonInterference_perCore ctx observer st st' hObjInv hIdxComplete hObjSetInv
    (.syscallDecodeError hEq) (observableSlotsConfinedToCore_of_eq bootCoreId hEq)

theorem nonInterference_perCore_registerServiceChecked (ctx : LabelingContext)
    (observer : IfObserver) (st st' : SystemState) (caller : SeLe4n.ThreadId)
    (reg : ServiceRegistration)
    (hObjInv : st.objects.invExt) (hIdxComplete : objectIndexSetComplete st)
    (hObjSetInv : st.objectIndexSet.table.invExt)
    (hStep : registerServiceChecked ctx caller reg st = .ok ((), st')) :
    lowEquivalent_smp ctx observer st' st :=
  nonInterference_perCore ctx observer st st' hObjInv hIdxComplete hObjSetInv
    (.registerServiceChecked caller reg hStep)
    (registerServiceChecked_confinedToCore ctx st st' caller reg bootCoreId hStep)

/-! #### The four catch-all constructors

`syscallDispatchHigh`, `endpointCallWithDonationHigh`,
`endpointReplyWithReversionHigh` and `handleInterrupt` carry a whole-state
projection hypothesis instead of an operational one, so nothing about their
per-core write set can be derived — and under SMP the dispatch they stand for
genuinely writes a remote core (the cross-core wake).  Each therefore takes the
confinement premise; `nonInterference_perCore_catchAll_count` records that this
is exactly four of the thirty-five. -/

theorem nonInterference_perCore_syscallDispatch (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState)
    (hObjInv : st.objects.invExt) (hIdxComplete : objectIndexSetComplete st)
    (hObjSetInv : st.objectIndexSet.table.invExt)
    (hCurrentHigh : ∀ t, st.scheduler.currentOnCore bootCoreId = some t →
      threadObservable ctx observer t = false)
    (hProj : projectState ctx observer st' = projectState ctx observer st)
    (hConfined : observableSlotsConfinedToCore st st' bootCoreId) :
    lowEquivalent_smp ctx observer st' st :=
  nonInterference_perCore ctx observer st st' hObjInv hIdxComplete hObjSetInv
    (.syscallDispatchHigh hCurrentHigh hProj) hConfined

theorem nonInterference_perCore_endpointCallWithDonation (ctx : LabelingContext)
    (observer : IfObserver) (st st' : SystemState)
    (hObjInv : st.objects.invExt) (hIdxComplete : objectIndexSetComplete st)
    (hObjSetInv : st.objectIndexSet.table.invExt)
    (hCurrentHigh : ∀ t, st.scheduler.currentOnCore bootCoreId = some t →
      threadObservable ctx observer t = false)
    (hProj : projectState ctx observer st' = projectState ctx observer st)
    (hConfined : observableSlotsConfinedToCore st st' bootCoreId) :
    lowEquivalent_smp ctx observer st' st :=
  nonInterference_perCore ctx observer st st' hObjInv hIdxComplete hObjSetInv
    (.endpointCallWithDonationHigh hCurrentHigh hProj) hConfined

theorem nonInterference_perCore_endpointReplyWithReversion (ctx : LabelingContext)
    (observer : IfObserver) (st st' : SystemState)
    (hObjInv : st.objects.invExt) (hIdxComplete : objectIndexSetComplete st)
    (hObjSetInv : st.objectIndexSet.table.invExt)
    (hCurrentHigh : ∀ t, st.scheduler.currentOnCore bootCoreId = some t →
      threadObservable ctx observer t = false)
    (hProj : projectState ctx observer st' = projectState ctx observer st)
    (hConfined : observableSlotsConfinedToCore st st' bootCoreId) :
    lowEquivalent_smp ctx observer st' st :=
  nonInterference_perCore ctx observer st st' hObjInv hIdxComplete hObjSetInv
    (.endpointReplyWithReversionHigh hCurrentHigh hProj) hConfined

theorem nonInterference_perCore_handleInterrupt (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState)
    (hObjInv : st.objects.invExt) (hIdxComplete : objectIndexSetComplete st)
    (hObjSetInv : st.objectIndexSet.table.invExt)
    (hCurrentHigh : ∀ t, st.scheduler.currentOnCore bootCoreId = some t →
      threadObservable ctx observer t = false)
    (hCurrentObjHigh : ∀ t, st.scheduler.currentOnCore bootCoreId = some t →
      objectObservable ctx observer t.toObjId = false)
    (hAllRunnable : ∀ tid, tid ∈ st.scheduler.runnable →
      threadObservable ctx observer tid = false)
    (hProj : projectState ctx observer st' = projectState ctx observer st)
    (hConfined : observableSlotsConfinedToCore st st' bootCoreId) :
    lowEquivalent_smp ctx observer st' st :=
  nonInterference_perCore ctx observer st st' hObjInv hIdxComplete hObjSetInv
    (.handleInterrupt hCurrentHigh hCurrentObjHigh hAllRunnable hProj) hConfined

-- ============================================================================
-- §5  SM8.B.5 — per-core coverage of the operation taxonomy
-- ============================================================================

/-- SM8.B.5: a **compile-time-validated** theorem name.  Elaborates the
identifier and returns its spelling, so a table entry naming a theorem that does
not exist — or one that has since been renamed — is a build failure rather than
a silently stale string.

The same device as `pcist!` in `Scheduler/Invariant/PerCoreInvariantSuiteInventory`,
narrowed to the one thing needed here.  `let _ := @ident; "…"` zeta-reduces, so
the `rfl`/`decide` proofs over the table are unaffected. -/
syntax (name := perCoreNiTheoremNameMacro) "niName!" ident : term

macro_rules
  | `(niName! $ident:ident) => do
      let nameStxLit := Lean.Syntax.mkStrLit ident.getId.toString
      `(let _ := @$ident; $nameStxLit)

/-- SM8.B.5: the name of each `KernelOperation`'s **per-core** non-interference
theorem, in the idiom of `kernelOperationNiConstructor` (which names its
single-core `NonInterferenceStep` constructor).

Every entry goes through `niName!`, so the string and the declaration cannot
drift apart.

The match is exhaustive, so a new `KernelOperation` variant fails to compile
until it is given a per-core theorem — the same tripwire the single-core
mapping carries, one layer up.  `niStepCoverage_perCore_injective` and
`niStepCoverage_perCore_count` make the correspondence 1:1 and complete. -/
def kernelOperationPerCoreNiTheorem : KernelOperation → String
  | .chooseThread                   => niName! nonInterference_perCore_chooseThread
  | .endpointSendDual               => niName! nonInterference_perCore_endpointSendDual
  | .cspaceMint                     => niName! nonInterference_perCore_cspaceMint
  | .cspaceRevoke                   => niName! nonInterference_perCore_cspaceRevoke
  | .lifecycleRetype                => niName! nonInterference_perCore_lifecycleRetype
  | .lifecycleRevokeDeleteRetype    => niName! nonInterference_perCore_lifecycleRevokeDeleteRetype
  | .notificationSignal             => niName! nonInterference_perCore_notificationSignal
  | .notificationWait               => niName! nonInterference_perCore_notificationWait
  | .cspaceInsertSlot               => niName! nonInterference_perCore_cspaceInsertSlot
  | .schedule                       => niName! nonInterference_perCore_schedule
  | .vspaceMapPage                  => niName! nonInterference_perCore_vspaceMapPage
  | .vspaceUnmapPage                => niName! nonInterference_perCore_vspaceUnmapPage
  | .vspaceLookup                   => niName! nonInterference_perCore_vspaceLookup
  | .cspaceCopy                     => niName! nonInterference_perCore_cspaceCopy
  | .cspaceMove                     => niName! nonInterference_perCore_cspaceMove
  | .cspaceDeleteSlot               => niName! nonInterference_perCore_cspaceDeleteSlot
  | .endpointReply                  => niName! nonInterference_perCore_endpointReply
  | .endpointReceiveDualHigh        => niName! nonInterference_perCore_endpointReceiveDual
  | .endpointCallHigh               => niName! nonInterference_perCore_endpointCall
  | .endpointReplyRecvHigh          => niName! nonInterference_perCore_endpointReplyRecv
  | .storeObjectHigh                => niName! nonInterference_perCore_storeObject
  | .setCurrentThread               => niName! nonInterference_perCore_setCurrentThread
  | .ensureRunnableHigh             => niName! nonInterference_perCore_ensureRunnable
  | .removeRunnableHigh             => niName! nonInterference_perCore_removeRunnable
  | .storeTcbIpcStateAndMessageHigh => niName! nonInterference_perCore_storeTcbIpcStateAndMessage
  | .storeTcbQueueLinksHigh         => niName! nonInterference_perCore_storeTcbQueueLinks
  | .cspaceMutateHigh               => niName! nonInterference_perCore_cspaceMutate
  | .handleYield                    => niName! nonInterference_perCore_handleYield
  | .timerTick                      => niName! nonInterference_perCore_timerTick
  | .syscallDecodeError             => niName! nonInterference_perCore_syscallDecodeError
  | .syscallDispatchHigh            => niName! nonInterference_perCore_syscallDispatch
  | .registerServiceChecked         => niName! nonInterference_perCore_registerServiceChecked
  | .endpointCallWithDonationHigh   => niName! nonInterference_perCore_endpointCallWithDonation
  | .endpointReplyWithReversionHigh => niName! nonInterference_perCore_endpointReplyWithReversion
  | .handleInterrupt                => niName! nonInterference_perCore_handleInterrupt

/-- SM8.B.5: the per-core theorem names are pairwise distinct — the mapping is
1:1, so no two operations were given the same lift. -/
theorem niStepCoverage_perCore_injective :
    ∀ op₁ op₂ : KernelOperation,
      kernelOperationPerCoreNiTheorem op₁ = kernelOperationPerCoreNiTheorem op₂ → op₁ = op₂ := by
  intro op₁ op₂ hEq
  cases op₁ <;> cases op₂ <;> (first | rfl | simp [kernelOperationPerCoreNiTheorem] at hEq)

/-- SM8.B.5: thirty-five distinct per-core theorem names — the count the plan
re-anchored at the SM8.A cut (`kernelOperation_count` /
`niStepCoverage_count` are the authority). -/
theorem niStepCoverage_perCore_count :
    ([ kernelOperationPerCoreNiTheorem .chooseThread
     , kernelOperationPerCoreNiTheorem .endpointSendDual
     , kernelOperationPerCoreNiTheorem .cspaceMint
     , kernelOperationPerCoreNiTheorem .cspaceRevoke
     , kernelOperationPerCoreNiTheorem .lifecycleRetype
     , kernelOperationPerCoreNiTheorem .lifecycleRevokeDeleteRetype
     , kernelOperationPerCoreNiTheorem .notificationSignal
     , kernelOperationPerCoreNiTheorem .notificationWait
     , kernelOperationPerCoreNiTheorem .cspaceInsertSlot
     , kernelOperationPerCoreNiTheorem .schedule
     , kernelOperationPerCoreNiTheorem .vspaceMapPage
     , kernelOperationPerCoreNiTheorem .vspaceUnmapPage
     , kernelOperationPerCoreNiTheorem .vspaceLookup
     , kernelOperationPerCoreNiTheorem .cspaceCopy
     , kernelOperationPerCoreNiTheorem .cspaceMove
     , kernelOperationPerCoreNiTheorem .cspaceDeleteSlot
     , kernelOperationPerCoreNiTheorem .endpointReply
     , kernelOperationPerCoreNiTheorem .endpointReceiveDualHigh
     , kernelOperationPerCoreNiTheorem .endpointCallHigh
     , kernelOperationPerCoreNiTheorem .endpointReplyRecvHigh
     , kernelOperationPerCoreNiTheorem .storeObjectHigh
     , kernelOperationPerCoreNiTheorem .setCurrentThread
     , kernelOperationPerCoreNiTheorem .ensureRunnableHigh
     , kernelOperationPerCoreNiTheorem .removeRunnableHigh
     , kernelOperationPerCoreNiTheorem .storeTcbIpcStateAndMessageHigh
     , kernelOperationPerCoreNiTheorem .storeTcbQueueLinksHigh
     , kernelOperationPerCoreNiTheorem .cspaceMutateHigh
     , kernelOperationPerCoreNiTheorem .handleYield
     , kernelOperationPerCoreNiTheorem .timerTick
     , kernelOperationPerCoreNiTheorem .syscallDecodeError
     , kernelOperationPerCoreNiTheorem .syscallDispatchHigh
     , kernelOperationPerCoreNiTheorem .registerServiceChecked
     , kernelOperationPerCoreNiTheorem .endpointCallWithDonationHigh
     , kernelOperationPerCoreNiTheorem .endpointReplyWithReversionHigh
     , kernelOperationPerCoreNiTheorem .handleInterrupt
     ]).length = 35 := by rfl

/-- SM8.B.5: **whether the operation's own semantics establish the confinement
premise**, or whether the caller must supply it.

`false` exactly for the four constructors that carry a whole-state projection
hypothesis and no operational one.

**Enumerated, not wildcarded.**  An earlier form ended `| _ => true`, which
silently classified any future `KernelOperation` variant as "derived" — a
wildcard cannot be an exhaustiveness tripwire, and only
`perCoreConfinementDerived_count` breaking would have caught it, one step
removed from the cause.  Spelling all thirty-five arms out makes a new variant a
*compile* error here, at the table that would have mis-described it. -/
def perCoreConfinementDerived : KernelOperation → Bool
  | .syscallDispatchHigh | .endpointCallWithDonationHigh
  | .endpointReplyWithReversionHigh | .handleInterrupt => false
  | .chooseThread | .endpointSendDual | .cspaceMint | .cspaceRevoke
  | .lifecycleRetype | .lifecycleRevokeDeleteRetype | .notificationSignal
  | .notificationWait | .cspaceInsertSlot | .schedule | .vspaceMapPage
  | .vspaceUnmapPage | .vspaceLookup | .cspaceCopy | .cspaceMove
  | .cspaceDeleteSlot | .endpointReply | .endpointReceiveDualHigh
  | .endpointCallHigh | .endpointReplyRecvHigh | .storeObjectHigh
  | .setCurrentThread | .ensureRunnableHigh | .removeRunnableHigh
  | .storeTcbIpcStateAndMessageHigh | .storeTcbQueueLinksHigh
  | .cspaceMutateHigh | .handleYield | .timerTick | .syscallDecodeError
  | .registerServiceChecked => true

/-- SM8.B.5: thirty-one of the thirty-five operations discharge the confinement
premise from their own semantics; exactly four — the catch-alls — do not. -/
theorem perCoreConfinementDerived_count :
    (([ KernelOperation.chooseThread, .endpointSendDual, .cspaceMint,
        .cspaceRevoke, .lifecycleRetype, .lifecycleRevokeDeleteRetype,
        .notificationSignal, .notificationWait, .cspaceInsertSlot,
        .schedule, .vspaceMapPage, .vspaceUnmapPage, .vspaceLookup,
        .cspaceCopy, .cspaceMove, .cspaceDeleteSlot,
        .endpointReply, .endpointReceiveDualHigh, .endpointCallHigh,
        .endpointReplyRecvHigh, .storeObjectHigh, .setCurrentThread,
        .ensureRunnableHigh, .removeRunnableHigh,
        .storeTcbIpcStateAndMessageHigh, .storeTcbQueueLinksHigh,
        .cspaceMutateHigh, .handleYield, .timerTick,
        .syscallDecodeError, .syscallDispatchHigh,
        .registerServiceChecked,
        .endpointCallWithDonationHigh, .endpointReplyWithReversionHigh,
        .handleInterrupt ]).filter perCoreConfinementDerived).length = 31 := by decide

/-- SM8.B.5 (per-core coverage): every `KernelOperation` has a witnessing
per-core non-interference step — one that is boot-core-confined **and** whose
post-state is `lowEquivalent_smp` to the pre-state.

Like its single-core counterpart `niStepConstructorCoverage`, this witnesses
*discoverability* over the operation taxonomy, not per-op semantics: the
universal witness is the state-identity step.  The per-op semantic content is
§4b's thirty-five theorems, indexed by `kernelOperationPerCoreNiTheorem`.  The
exhaustive match is the tripwire — a new `KernelOperation` variant makes this
proof non-exhaustive and the build fails. -/
theorem niStepCoverage_perCore (ctx : LabelingContext) (observer : IfObserver)
    (st : SystemState) :
    ∀ _op : KernelOperation, ∃ st' : SystemState,
      NonInterferenceStep ctx observer st st' ∧
      observableSlotsConfinedToCore st st' bootCoreId ∧
      (st.objects.invExt → objectIndexSetComplete st → st.objectIndexSet.table.invExt →
        lowEquivalent_smp ctx observer st' st) := by
  intro
    | .chooseThread | .endpointSendDual | .cspaceMint | .cspaceRevoke
    | .lifecycleRetype | .lifecycleRevokeDeleteRetype | .notificationSignal
    | .notificationWait | .cspaceInsertSlot | .schedule | .vspaceMapPage
    | .vspaceUnmapPage | .vspaceLookup | .cspaceCopy | .cspaceMove
    | .cspaceDeleteSlot | .endpointReply | .endpointReceiveDualHigh
    | .endpointCallHigh | .endpointReplyRecvHigh | .storeObjectHigh
    | .setCurrentThread | .ensureRunnableHigh | .removeRunnableHigh
    | .storeTcbIpcStateAndMessageHigh | .storeTcbQueueLinksHigh
    | .cspaceMutateHigh | .handleYield | .timerTick
    | .syscallDecodeError | .syscallDispatchHigh
    | .registerServiceChecked
    | .endpointCallWithDonationHigh | .endpointReplyWithReversionHigh
    | .handleInterrupt
      => exact ⟨st, .syscallDecodeError rfl, observableSlotsConfinedToCore_refl st bootCoreId,
          fun hObjInv hIdx hSet =>
            nonInterference_perCore ctx observer st st hObjInv hIdx hSet
              (.syscallDecodeError rfl) (observableSlotsConfinedToCore_refl st bootCoreId)⟩

-- ============================================================================
-- §6  SM8.B.4 — non-interference under the per-object lock set
-- ============================================================================
--
-- The SM3 two-phase-locking bracket `withLockSet S core action s` acquires
-- every lock in `S`, runs `action`, and releases in reverse order.  Each
-- acquire/release rewrites the `lock : RwLockState` field of the object the
-- `LockId` names (or the table-level `objStoreLock`).
--
-- `RwLockState` carries `writerHeld : Option CoreId`, `readers : List CoreId`
-- and `waiters : List (CoreId × AccessMode)` — every field a core identity.  If
-- the projection carried it, an observer that can see an object would learn the
-- set of cores currently operating on that object, which is the *placement*
-- channel WS-SM SM5.B closed by stripping `TCB.cpuAffinity`, re-opened through
-- another field.  `projectKernelObject` therefore erases `lock` structurally
-- (see its `.endpoint` … `.untyped` arms), and the consequence is proved here:
-- the bracket is invisible **unconditionally** — no hypothesis about which
-- objects the lock set names, and none about whether the locks are contended.
--
-- That is what leaves CC-5 a *hardware timing* channel and nothing more (plan
-- Definition 3.4.1): the model carries no state flow through lock acquisition
-- at all, so a spinning core's only signal is wall-clock time.

/-- SM8.B.4: a lock-field update is invisible to the projection — the projected
object is literally the same, because `projectKernelObject` erases `lock` on
every arm. -/
@[simp] theorem projectKernelObject_updateLock (ctx : LabelingContext) (observer : IfObserver)
    (obj : KernelObject) (op : SeLe4n.Kernel.Concurrency.RwLockOp) :
    projectKernelObject ctx observer (obj.updateLock op) =
      projectKernelObject ctx observer obj := by
  cases obj <;> rfl

/-- SM8.B.4: `updateObjectAt` with a lock-only transform preserves the
observer's object projection at **every** id — including ids the observer can
see, which is the point. -/
theorem updateObjectAt_updateLock_preserves_projectObjects (ctx : LabelingContext)
    (observer : IfObserver) (s : SystemState) (oid : SeLe4n.ObjId)
    (op : SeLe4n.Kernel.Concurrency.RwLockOp) (hInv : s.objects.invExt) :
    projectObjects ctx observer
        (SeLe4n.Kernel.Concurrency.updateObjectAt s oid (fun obj => obj.updateLock op))
      = projectObjects ctx observer s := by
  unfold SeLe4n.Kernel.Concurrency.updateObjectAt
  cases hGet : s.objects.get? oid with
  | none => rfl
  | some obj =>
    funext o
    simp only [projectObjects]
    by_cases hObs : objectObservable ctx observer o = true
    · rw [if_pos hObs, if_pos hObs]
      simp only [RHTable_getElem?_eq_get?]
      rw [RHTable_getElem?_insert s.objects oid _ hInv o]
      by_cases hEq : (oid == o) = true
      · have hOid : oid = o := eq_of_beq hEq
        subst hOid
        rw [if_pos hEq, hGet]
        simp only [Option.map_some, Option.some.injEq]
        exact projectKernelObject_updateLock ctx observer obj op
      · rw [if_neg hEq]
    · simp only [Bool.not_eq_true] at hObs
      rw [if_neg (by simp [hObs]), if_neg (by simp [hObs])]

/-- SM8.B.4 (the assembly helper): a rewrite whose only projection-relevant
effect is on the object store — and there only in ways the observer's object
projection cannot see — preserves the whole projection.

Stated for a general pair of states rather than for one operation, because §6,
§7 and §8 all reach for it. -/
theorem projectState_eq_of_objects_projection_eq (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState)
    (hObjects : projectObjects ctx observer st' = projectObjects ctx observer st)
    (hSched : st'.scheduler = st.scheduler)
    (hServices : st'.services = st.services)
    (hIrq : st'.irqHandlers = st.irqHandlers)
    (hIndex : st'.objectIndex = st.objectIndex)
    (hMachine : st'.machine = st.machine) :
    projectState ctx observer st' = projectState ctx observer st := by
  simp only [projectState]
  congr 1 <;>
    first
      | exact hObjects
      | simp only [projectObjectIndex, hIndex]
      | simp [projectRunnable, projectCurrent, projectActiveDomain, projectDomainTimeRemaining,
              projectDomainSchedule, projectDomainScheduleIndex, projectMachineRegs, hSched,
              hMachine]
      | (funext sid; simp only [projectServicePresence, lookupService, hServices])
      | (funext irq; simp only [projectIrqHandlers, hIrq])
      | exact projectMemory_eq_of_memory_eq ctx observer st' st (by rw [hMachine])
      | exact projectServiceRegistry_eq_of_services_eq ctx observer st' st hServices

/-- The lock-only object rewrite frames the scheduler. -/
theorem updateObjectAt_updateLock_scheduler_eq (s : SystemState) (oid : SeLe4n.ObjId)
    (op : SeLe4n.Kernel.Concurrency.RwLockOp) :
    (SeLe4n.Kernel.Concurrency.updateObjectAt s oid (fun obj => obj.updateLock op)).scheduler
      = s.scheduler := by
  unfold SeLe4n.Kernel.Concurrency.updateObjectAt; split <;> rfl

/-- The lock-only object rewrite frames the machine. -/
theorem updateObjectAt_updateLock_machine_eq (s : SystemState) (oid : SeLe4n.ObjId)
    (op : SeLe4n.Kernel.Concurrency.RwLockOp) :
    (SeLe4n.Kernel.Concurrency.updateObjectAt s oid (fun obj => obj.updateLock op)).machine
      = s.machine := by
  unfold SeLe4n.Kernel.Concurrency.updateObjectAt; split <;> rfl

/-- The lock-only object rewrite frames the object index. -/
theorem updateObjectAt_updateLock_objectIndex_eq (s : SystemState) (oid : SeLe4n.ObjId)
    (op : SeLe4n.Kernel.Concurrency.RwLockOp) :
    (SeLe4n.Kernel.Concurrency.updateObjectAt s oid (fun obj => obj.updateLock op)).objectIndex
      = s.objectIndex := by
  unfold SeLe4n.Kernel.Concurrency.updateObjectAt; split <;> rfl

/-- The lock-only object rewrite frames the service store. -/
theorem updateObjectAt_updateLock_services_eq (s : SystemState) (oid : SeLe4n.ObjId)
    (op : SeLe4n.Kernel.Concurrency.RwLockOp) :
    (SeLe4n.Kernel.Concurrency.updateObjectAt s oid (fun obj => obj.updateLock op)).services
      = s.services := by
  unfold SeLe4n.Kernel.Concurrency.updateObjectAt; split <;> rfl

/-- The lock-only object rewrite frames the IRQ table. -/
theorem updateObjectAt_updateLock_irqHandlers_eq (s : SystemState) (oid : SeLe4n.ObjId)
    (op : SeLe4n.Kernel.Concurrency.RwLockOp) :
    (SeLe4n.Kernel.Concurrency.updateObjectAt s oid (fun obj => obj.updateLock op)).irqHandlers
      = s.irqHandlers := by
  unfold SeLe4n.Kernel.Concurrency.updateObjectAt; split <;> rfl

/-- SM8.B.4: the kind-checked lock update preserves the observer's projection —
**unconditionally**, with no hypothesis about which object the `LockId` names. -/
theorem updateObjectLockAt_preserves_projection (ctx : LabelingContext) (observer : IfObserver)
    (s : SystemState) (l : SeLe4n.Kernel.Concurrency.LockId)
    (op : SeLe4n.Kernel.Concurrency.RwLockOp) (hInv : s.objects.invExt) :
    projectState ctx observer (SeLe4n.Kernel.Concurrency.updateObjectLockAt s l op)
      = projectState ctx observer s := by
  unfold SeLe4n.Kernel.Concurrency.updateObjectLockAt
  split
  · refine projectState_eq_of_objects_projection_eq ctx observer s _
      (updateObjectAt_updateLock_preserves_projectObjects ctx observer s l.objId op hInv)
      (updateObjectAt_updateLock_scheduler_eq s l.objId op)
      (updateObjectAt_updateLock_services_eq s l.objId op)
      (updateObjectAt_updateLock_irqHandlers_eq s l.objId op)
      (updateObjectAt_updateLock_objectIndex_eq s l.objId op)
      (updateObjectAt_updateLock_machine_eq s l.objId op)
  · rfl

/-- SM8.B.4: `updateObjectAt` with a lock-only transform preserves the object
store's extensional invariant, so the fold below can keep applying the lemma
above. -/
theorem updateObjectAt_updateLock_preserves_objects_invExt (s : SystemState)
    (oid : SeLe4n.ObjId) (op : SeLe4n.Kernel.Concurrency.RwLockOp) (hInv : s.objects.invExt) :
    (SeLe4n.Kernel.Concurrency.updateObjectAt s oid (fun obj => obj.updateLock op)).objects.invExt := by
  unfold SeLe4n.Kernel.Concurrency.updateObjectAt
  cases hGet : s.objects.get? oid with
  | none => exact hInv
  | some obj => exact RHTable_insert_preserves_invExt s.objects oid _ hInv

theorem updateObjectLockAt_preserves_objects_invExt (s : SystemState)
    (l : SeLe4n.Kernel.Concurrency.LockId) (op : SeLe4n.Kernel.Concurrency.RwLockOp)
    (hInv : s.objects.invExt) :
    (SeLe4n.Kernel.Concurrency.updateObjectLockAt s l op).objects.invExt := by
  unfold SeLe4n.Kernel.Concurrency.updateObjectLockAt
  cases hLookup : SeLe4n.Model.LockId.lookup s l with
  | none => exact hInv
  | some _ => exact updateObjectAt_updateLock_preserves_objects_invExt s l.objId op hInv

/-- SM8.B.4: acquiring one per-object lock preserves the observer's projection. -/
theorem acquireLockOnObject_preserves_projection (ctx : LabelingContext) (observer : IfObserver)
    (s : SystemState) (core : CoreId) (l : SeLe4n.Kernel.Concurrency.LockId)
    (mode : SeLe4n.Kernel.Concurrency.AccessMode) (hInv : s.objects.invExt) :
    projectState ctx observer (SeLe4n.Kernel.Concurrency.acquireLockOnObject s core l mode)
      = projectState ctx observer s := by
  unfold SeLe4n.Kernel.Concurrency.acquireLockOnObject
  cases l.kind <;>
    first
      | rfl
      | exact updateObjectLockAt_preserves_projection ctx observer s l _ hInv

/-- SM8.B.4: releasing one per-object lock preserves the observer's projection. -/
theorem releaseLockOnObject_preserves_projection (ctx : LabelingContext) (observer : IfObserver)
    (s : SystemState) (core : CoreId) (l : SeLe4n.Kernel.Concurrency.LockId)
    (mode : SeLe4n.Kernel.Concurrency.AccessMode) (hInv : s.objects.invExt) :
    projectState ctx observer (SeLe4n.Kernel.Concurrency.releaseLockOnObject s core l mode)
      = projectState ctx observer s := by
  unfold SeLe4n.Kernel.Concurrency.releaseLockOnObject
  cases l.kind <;>
    first
      | rfl
      | exact updateObjectLockAt_preserves_projection ctx observer s l _ hInv

theorem acquireLockOnObject_preserves_objects_invExt (s : SystemState) (core : CoreId)
    (l : SeLe4n.Kernel.Concurrency.LockId) (mode : SeLe4n.Kernel.Concurrency.AccessMode)
    (hInv : s.objects.invExt) :
    (SeLe4n.Kernel.Concurrency.acquireLockOnObject s core l mode).objects.invExt := by
  unfold SeLe4n.Kernel.Concurrency.acquireLockOnObject
  cases l.kind <;>
    first
      | exact hInv
      | exact updateObjectLockAt_preserves_objects_invExt s l _ hInv

theorem releaseLockOnObject_preserves_objects_invExt (s : SystemState) (core : CoreId)
    (l : SeLe4n.Kernel.Concurrency.LockId) (mode : SeLe4n.Kernel.Concurrency.AccessMode)
    (hInv : s.objects.invExt) :
    (SeLe4n.Kernel.Concurrency.releaseLockOnObject s core l mode).objects.invExt := by
  unfold SeLe4n.Kernel.Concurrency.releaseLockOnObject
  cases l.kind <;>
    first
      | exact hInv
      | exact updateObjectLockAt_preserves_objects_invExt s l _ hInv

theorem updateObjectLockAt_scheduler_eq (s : SystemState) (l : SeLe4n.Kernel.Concurrency.LockId)
    (op : SeLe4n.Kernel.Concurrency.RwLockOp) :
    (SeLe4n.Kernel.Concurrency.updateObjectLockAt s l op).scheduler = s.scheduler := by
  unfold SeLe4n.Kernel.Concurrency.updateObjectLockAt
  split
  · exact updateObjectAt_updateLock_scheduler_eq s l.objId op
  · rfl

theorem updateObjectLockAt_machine_eq (s : SystemState) (l : SeLe4n.Kernel.Concurrency.LockId)
    (op : SeLe4n.Kernel.Concurrency.RwLockOp) :
    (SeLe4n.Kernel.Concurrency.updateObjectLockAt s l op).machine = s.machine := by
  unfold SeLe4n.Kernel.Concurrency.updateObjectLockAt
  split
  · exact updateObjectAt_updateLock_machine_eq s l.objId op
  · rfl

/-- SM8.B.4: acquiring one lock writes no scheduler slot and no register bank. -/
theorem acquireLockOnObject_confinedToCore (s : SystemState) (core : CoreId)
    (l : SeLe4n.Kernel.Concurrency.LockId) (mode : SeLe4n.Kernel.Concurrency.AccessMode) (c₀ : CoreId) :
    observableSlotsConfinedToCore s
      (SeLe4n.Kernel.Concurrency.acquireLockOnObject s core l mode) c₀ := by
  refine observableSlotsConfinedToCore_of_scheduler_machine_eq c₀ ?_ ?_ <;>
    (unfold SeLe4n.Kernel.Concurrency.acquireLockOnObject
     cases l.kind <;>
       first
         | rfl
         | exact updateObjectLockAt_scheduler_eq s l _
         | exact updateObjectLockAt_machine_eq s l _)

/-- SM8.B.4: releasing one lock writes no scheduler slot and no register bank. -/
theorem releaseLockOnObject_confinedToCore (s : SystemState) (core : CoreId)
    (l : SeLe4n.Kernel.Concurrency.LockId) (mode : SeLe4n.Kernel.Concurrency.AccessMode) (c₀ : CoreId) :
    observableSlotsConfinedToCore s
      (SeLe4n.Kernel.Concurrency.releaseLockOnObject s core l mode) c₀ := by
  refine observableSlotsConfinedToCore_of_scheduler_machine_eq c₀ ?_ ?_ <;>
    (unfold SeLe4n.Kernel.Concurrency.releaseLockOnObject
     cases l.kind <;>
       first
         | rfl
         | exact updateObjectLockAt_scheduler_eq s l _
         | exact updateObjectLockAt_machine_eq s l _)


/-! ### The 2PL folds and the bracket -/

theorem acquireAll_preserves_objects_invExt (core : CoreId)
    (pairs : List (SeLe4n.Kernel.Concurrency.LockId × SeLe4n.Kernel.Concurrency.AccessMode))
    (s : SystemState) (hInv : s.objects.invExt) :
    (SeLe4n.Kernel.Concurrency.acquireAll core pairs s).objects.invExt := by
  induction pairs generalizing s with
  | nil => exact hInv
  | cons p rest ih =>
    obtain ⟨l, m⟩ := p
    rw [SeLe4n.Kernel.Concurrency.acquireAll_cons]
    exact ih _ (acquireLockOnObject_preserves_objects_invExt s core l m hInv)

theorem releaseAll_preserves_objects_invExt (core : CoreId)
    (pairs : List (SeLe4n.Kernel.Concurrency.LockId × SeLe4n.Kernel.Concurrency.AccessMode))
    (s : SystemState) (hInv : s.objects.invExt) :
    (SeLe4n.Kernel.Concurrency.releaseAll core pairs s).objects.invExt := by
  induction pairs generalizing s with
  | nil => exact hInv
  | cons p rest ih =>
    obtain ⟨l, m⟩ := p
    rw [SeLe4n.Kernel.Concurrency.releaseAll_cons]
    exact ih _ (releaseLockOnObject_preserves_objects_invExt s core l m hInv)

/-- SM8.B.4: the growing phase of the 2PL bracket is invisible. -/
theorem acquireAll_preserves_projection (ctx : LabelingContext) (observer : IfObserver)
    (core : CoreId)
    (pairs : List (SeLe4n.Kernel.Concurrency.LockId × SeLe4n.Kernel.Concurrency.AccessMode))
    (s : SystemState) (hInv : s.objects.invExt) :
    projectState ctx observer (SeLe4n.Kernel.Concurrency.acquireAll core pairs s)
      = projectState ctx observer s := by
  induction pairs generalizing s with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨l, m⟩ := p
    rw [SeLe4n.Kernel.Concurrency.acquireAll_cons,
        ih _ (acquireLockOnObject_preserves_objects_invExt s core l m hInv)]
    exact acquireLockOnObject_preserves_projection ctx observer s core l m hInv

/-- SM8.B.4: the shrinking phase of the 2PL bracket is invisible. -/
theorem releaseAll_preserves_projection (ctx : LabelingContext) (observer : IfObserver)
    (core : CoreId)
    (pairs : List (SeLe4n.Kernel.Concurrency.LockId × SeLe4n.Kernel.Concurrency.AccessMode))
    (s : SystemState) (hInv : s.objects.invExt) :
    projectState ctx observer (SeLe4n.Kernel.Concurrency.releaseAll core pairs s)
      = projectState ctx observer s := by
  induction pairs generalizing s with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨l, m⟩ := p
    rw [SeLe4n.Kernel.Concurrency.releaseAll_cons,
        ih _ (releaseLockOnObject_preserves_objects_invExt s core l m hInv)]
    exact releaseLockOnObject_preserves_projection ctx observer s core l m hInv

theorem acquireAll_confinedToCore (core : CoreId)
    (pairs : List (SeLe4n.Kernel.Concurrency.LockId × SeLe4n.Kernel.Concurrency.AccessMode))
    (s : SystemState) (c₀ : CoreId) :
    observableSlotsConfinedToCore s (SeLe4n.Kernel.Concurrency.acquireAll core pairs s) c₀ := by
  induction pairs generalizing s with
  | nil => exact observableSlotsConfinedToCore_refl s c₀
  | cons p rest ih =>
    obtain ⟨l, m⟩ := p
    rw [SeLe4n.Kernel.Concurrency.acquireAll_cons]
    exact observableSlotsConfinedToCore_trans
      (acquireLockOnObject_confinedToCore s core l m c₀) (ih _)

theorem releaseAll_confinedToCore (core : CoreId)
    (pairs : List (SeLe4n.Kernel.Concurrency.LockId × SeLe4n.Kernel.Concurrency.AccessMode))
    (s : SystemState) (c₀ : CoreId) :
    observableSlotsConfinedToCore s (SeLe4n.Kernel.Concurrency.releaseAll core pairs s) c₀ := by
  induction pairs generalizing s with
  | nil => exact observableSlotsConfinedToCore_refl s c₀
  | cons p rest ih =>
    obtain ⟨l, m⟩ := p
    rw [SeLe4n.Kernel.Concurrency.releaseAll_cons]
    exact observableSlotsConfinedToCore_trans
      (releaseLockOnObject_confinedToCore s core l m c₀) (ih _)

/-- SM8.B.4 (headline): **the two-phase-locking bracket is non-interference
transparent.**  `withLockSet` preserves the observer's projection exactly when
its guarded action does — the acquire and release phases contribute nothing.

No hypothesis constrains the lock set: it may name objects the observer can
see, and the locks may be contended.  That is the whole point of erasing
`lock` from the projection; without the erasure this theorem would need
"every lock in `S` names a non-observable object", and the lock state of a
*visible* object would be a model-level flow rather than the pure timing
channel CC-5 is documented to be. -/
theorem withLockSet_preserves_projection {α : Type} (ctx : LabelingContext)
    (observer : IfObserver) (S : SeLe4n.Kernel.Concurrency.LockSet) (core : CoreId)
    (action : SystemState → SystemState × α) (s : SystemState)
    (hInv : s.objects.invExt)
    (hActionInv : ∀ s', s'.objects.invExt → ((action s').1).objects.invExt)
    (hAction : ∀ s', s'.objects.invExt →
      projectState ctx observer (action s').1 = projectState ctx observer s') :
    projectState ctx observer (SeLe4n.Kernel.Concurrency.withLockSet S core action s).1
      = projectState ctx observer s := by
  rw [SeLe4n.Kernel.Concurrency.withLockSet_fst]
  have hAcqInv := acquireAll_preserves_objects_invExt core S.lockAcquireSequence s hInv
  rw [releaseAll_preserves_projection ctx observer core _ _ (hActionInv _ hAcqInv),
      hAction _ hAcqInv,
      acquireAll_preserves_projection ctx observer core S.lockAcquireSequence s hInv]

/-- SM8.B.4: the bracket's own writes stay off every core's scheduler slots and
register banks, so confinement rides through it too. -/
theorem withLockSet_confinedToCore {α : Type} (S : SeLe4n.Kernel.Concurrency.LockSet)
    (core : CoreId) (action : SystemState → SystemState × α) (s : SystemState) (c₀ : CoreId)
    (hAction : ∀ s', observableSlotsConfinedToCore s' (action s').1 c₀) :
    observableSlotsConfinedToCore s
      (SeLe4n.Kernel.Concurrency.withLockSet S core action s).1 c₀ := by
  rw [SeLe4n.Kernel.Concurrency.withLockSet_fst]
  exact observableSlotsConfinedToCore_trans
    (acquireAll_confinedToCore core S.lockAcquireSequence s c₀)
    (observableSlotsConfinedToCore_trans (hAction _)
      (releaseAll_confinedToCore core _ _ c₀))

/-- SM8.B.4 (the per-core headline): **non-interference under the per-object
lock set.**  A 2PL-guarded transition is invisible to an observer on *every*
core exactly when the guarded action is invisible on the boot core and keeps
its per-core writes on the boot core. -/
theorem nonInterference_perCore_underLockSet {α : Type} (ctx : LabelingContext)
    (observer : IfObserver) (S : SeLe4n.Kernel.Concurrency.LockSet) (core : CoreId)
    (action : SystemState → SystemState × α) (s : SystemState)
    (hInv : s.objects.invExt)
    (hActionInv : ∀ s', s'.objects.invExt → ((action s').1).objects.invExt)
    (hActionProj : ∀ s', s'.objects.invExt →
      projectState ctx observer (action s').1 = projectState ctx observer s')
    (hActionConfined : ∀ s', observableSlotsConfinedToCore s' (action s').1 bootCoreId) :
    lowEquivalent_smp ctx observer
      (SeLe4n.Kernel.Concurrency.withLockSet S core action s).1 s :=
  lowEquivalent_smp_of_projection_and_confinement ctx observer
    (withLockSet_preserves_projection ctx observer S core action s hInv hActionInv hActionProj)
    (withLockSet_confinedToCore S core action s bootCoreId hActionConfined)

/-- SM8.B.4 (the plan's Corollary 2.1.11 route, as a bridge): a lock set whose
objects the observer cannot see gives the §2 shared-frame premise for free.

The plan discharges Theorem 3.3.1 from serializability — "c-observable state
writes happen only with c's locks held, which c' does not have".  This is that
argument's formal shape: **disjointness of the lock set from the observer's
visible objects implies the object-frame premise**, hence
`crossCoreNonInterference`.  It is stated for the *guarded action*, because the
bracket itself is already invisible unconditionally
(`withLockSet_preserves_projection`), so all the disjointness has to buy is the
action's frame. -/
theorem crossCoreNonInterference_of_disjoint_lockSet (ctx : LabelingContext)
    (observer : IfObserver) {st st' : SystemState} {c c' : CoreId}
    (writeSet : List SeLe4n.ObjId)
    (hne : c ≠ c')
    (hRuns : observableSlotsConfinedToCore st st' c')
    (hDisjoint : ∀ oid, oid ∈ writeSet → objectObservable ctx observer oid = false)
    (hWrites : ∀ oid, oid ∉ writeSet → st'.objects[oid]? = st.objects[oid]?)
    (hIndex : st'.objectIndex = st.objectIndex)
    (hServices : st'.services = st.services)
    (hIrq : st'.irqHandlers = st.irqHandlers)
    (hMemory : st'.machine.memory = st.machine.memory)
    (hDomSched : st'.scheduler.domainSchedule = st.scheduler.domainSchedule) :
    projectStateOnCore ctx observer st' c = projectStateOnCore ctx observer st c := by
  refine crossCoreNonInterference_of_state_frames ctx observer hne hRuns ?_ hIndex hServices
    hIrq hMemory hDomSched
  intro oid hObs
  by_cases hMem : oid ∈ writeSet
  · exact absurd hObs (by rw [hDisjoint oid hMem]; simp)
  · exact hWrites oid hMem

-- ============================================================================
-- §7  SM8.B.13 — `crossCoreLeakage_bounded`
-- ============================================================================

/-- SM8.B.13 (headline): **cross-core leakage is bounded by the shared
fragment.**

For an observer on core `c`, a transition confined to a different core `c'`
leaves core `c`'s per-core fragment *provably* untouched, and consequently the
observer's view moves **if and only if** the shared fragment moves.  So the
channel from core `c'` to the observer is exactly the seven label-filtered
shared components — six of the thirteen `ObservableState` components carry no
cross-core flow at all.

The `↔` is what makes this a bound rather than a remark: it says the shared
fragment is not merely *a* route but the *only* one. -/
theorem crossCoreLeakage_bounded (ctx : LabelingContext) (observer : IfObserver)
    {st st' : SystemState} {c c' : CoreId}
    (hne : c ≠ c')
    (hRuns : observableSlotsConfinedToCore st st' c') :
    (projectStateOnCore ctx observer st' c).perCoreFragment
        = (projectStateOnCore ctx observer st c).perCoreFragment ∧
      (projectStateOnCore ctx observer st' c = projectStateOnCore ctx observer st c ↔
        (projectStateOnCore ctx observer st' c).sharedFragment
          = (projectStateOnCore ctx observer st c).sharedFragment) := by
  have hPerCore : (projectStateOnCore ctx observer st' c).perCoreFragment
      = (projectStateOnCore ctx observer st c).perCoreFragment := by
    simp only [projectStateOnCore_perCoreFragment, PerCoreObservableFragment.mk.injEq]
    exact ⟨projectRunnableOnCore_frame _ _ (hRuns.runQueue c hne),
      projectCurrentOnCore_frame _ _ (hRuns.current c hne),
      projectActiveDomainOnCore_frame _ _ (hRuns.activeDomain c hne),
      projectDomainTimeRemainingOnCore_frame _ _ (hRuns.domainTimeRemaining c hne),
      projectDomainScheduleIndexOnCore_frame _ _ (hRuns.domainScheduleIndex c hne),
      projectMachineRegsOnCore_frame _ _ (hRuns.current c hne) (hRuns.regs c hne)⟩
  refine ⟨hPerCore, ?_, ?_⟩
  · exact fun h => congrArg ObservableState.sharedFragment h
  · exact fun hShared => ObservableState.ext_fragments hShared hPerCore

/-- SM8.B.13 (the reconstruction form): the observer's post-transition view is
literally rebuilt from the **new shared fragment** and its **own pre-transition
per-core fragment**.  Everything a remote core's transition can tell the
observer is therefore in the shared half; nothing at all flows into the
per-core half. -/
theorem crossCoreLeakage_bounded_reconstruction (ctx : LabelingContext) (observer : IfObserver)
    {st st' : SystemState} {c c' : CoreId}
    (hne : c ≠ c')
    (hRuns : observableSlotsConfinedToCore st st' c') :
    projectStateOnCore ctx observer st' c =
      ObservableState.ofFragments (projectStateOnCore ctx observer st' c).sharedFragment
        (projectStateOnCore ctx observer st c).perCoreFragment := by
  rw [← (crossCoreLeakage_bounded ctx observer hne hRuns).1]
  exact (ObservableState.ofFragments_eta _).symm

/-- SM8.B.13: the shared fragment is a function of the **global** projection
alone (SM8.A's `onCore_sharedFragment_eq_globalProjection`), so the bound above
says the whole cross-core channel is the single-core, label-filtered projection
the release-grade NI theorems already reason about.  A transition preserving
that projection leaks nothing to any remote observer — which is
`nonInterference_perCore` read backwards. -/
theorem crossCoreLeakage_bounded_by_globalProjection (ctx : LabelingContext)
    (observer : IfObserver) {st st' : SystemState} {c c' : CoreId}
    (hne : c ≠ c')
    (hRuns : observableSlotsConfinedToCore st st' c')
    (hProj : projectState ctx observer st' = projectState ctx observer st) :
    projectStateOnCore ctx observer st' c = projectStateOnCore ctx observer st c :=
  crossCoreNonInterference ctx observer hne hRuns
    (sharedViewUnchanged_of_globalProjection ctx observer hProj)

/-- SM8.B.2 (non-orphan bridge): every SM6 cross-core non-interference result is
stated in `lowEquivalent_smp` form, and SM8.A's
`lowEquivalent_smp_iff_forall_observer` says that form **is** "invisible to every
per-core observer at that clearance".  So `endpointCallOnCore_call_path_NI_smp`,
`notificationSignalOnCore_call_path_NI_smp` and their siblings are consumers of
this module's observer layer without needing to be restated. -/
theorem crossCoreTransition_invisible_to_every_observer (ctx : LabelingContext)
    (L : SecurityLabel) (st st' : SystemState)
    (h : lowEquivalent_smp ctx (IfObserver.ofLabel L) st' st) :
    ∀ c : CoreId, lowEquivalentForObserver ctx ⟨c, L⟩ st' st :=
  (lowEquivalent_smp_iff_forall_observer ctx L st' st).mp h


end SeLe4n.Kernel
