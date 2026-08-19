-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.InformationFlow.ProjectionPerCore

/-!
# WS-SM SM8.A — Per-core observable state

Plan `docs/planning/SMP_INFORMATION_FLOW_PLAN.md` §3.1–§3.2 / §5 sub-tasks
SM8.A.1 … SM8.A.6.  This module mounts the SMP *observer* — the pair
`(c, L)` of a core and a security label (plan Definition 3.1.1) — and the
observable state that observer sees (plan Definition 3.2.1), on top of the
SM4.D per-core projection functions in `ProjectionPerCore.lean`.

## What this layer adds over SM4.D

SM4.D lifted the six scheduler-reading IF-M1 projections to per-core forms
and aggregated them into `projectStateOnCore ctx observer st c`.  That is
already the (core, observer) projection in *function* form.  SM8.A supplies
the missing structure around it:

* **The observer itself** (§1).  `(c, L)` becomes a value
  (`PerCoreObserver`), not a convention spread across two argument
  positions, so SM8.B's `crossCoreNonInterference` and SM8.C's per-core
  declassification audit quantify over one thing.
* **The shared / per-core field partition** (§3).  `ObservableState`'s
  thirteen components split into seven that the observer sees identically
  from every core and six that are restricted to core `c`.  The partition
  is a **bijection**, not a convenient grouping:
  `ObservableState.ofFragments` reassembles a state from the pair and
  `ofFragments_eta` proves the round trip, so a fourteenth
  `ObservableState` field registered in neither fragment leaves
  `ofFragments` unable to supply it.  The plan §7 "per-core projection
  missing a field" risk is therefore a compile error as a *checked fact*,
  not as an argument about one.  The headline
  `onCore_isProjection_of_globalProjection` is the exact `iff` that
  follows: the observer learns the global projection's shared fragment
  paired with core `c`'s per-core fragment — all of it, and nothing beyond.
* **The decidable fragment** (§4).  Observable-state equality is *not*
  decidable — five components are functions over unbounded domains and the
  sixth (`machineRegs`) contains `RegisterFile.gpr`, whose structural `BEq`
  is provably not lawful (`RegisterFile.not_lawfulBEq`).  §4 carves out the
  fragment that *is* decidable, adds the finer register-aware check that
  carries the ARM64 structural comparison as far as computation allows,
  proves both sound refuters, and proves both **strict** so no caller can
  mistake either for full equality.
* **Per-core independence** (§5).  The read set of the per-core observable
  state is characterised exactly: the six shared state components
  (`objects`, `services`, `irqHandlers`, `objectIndex`,
  `scheduler.domainSchedule`, `machine.memory`) plus core `c`'s five
  scheduler slots and core `c`'s register bank — and *nothing else*, in
  particular no other core's slots.  Note this does not follow from
  `projectStateOnCore_congr`, whose `hBase` hypothesis is equality of the
  whole global projection and therefore drags the **boot** core's slots in;
  SM8.B needs the boot-core-free form.
* **Label monotonicity** (§6).  Raising the observer's clearance can only
  widen what it sees, over a `visibilityLe` preorder carrying one clause per
  `ObservableState` component, each as strong as the truth allows — the two
  list components by `Sublist`, so order is preserved; the four scheduling
  components (the accepted CC-1 channel, which passes through *unfiltered*)
  by equality; the remaining partial components by value; and `objects` by
  `objectVisibilityLe`, which is equality off the CNode arm and slot
  un-redaction on it.  `ObservableState.eq_of_visibilityLe_antisymm` is the
  completeness check on that clause list: mutual domination plus agreement on
  `objects` is equality, so a fourteenth component with no clause leaves a
  goal nothing can close.

## Relationship to the live surface

Every definition here is a conservative re-presentation of
`projectStateOnCore`, so `ObservableState.onCore ctx bootCoreId L s` is
*definitionally* the live single-core `projectState ctx ⟨L⟩ s` and the
existing non-interference surface is untouched.

Axiom-clean: every declaration depends only on the standard foundational
axioms (`propext` / `Quot.sound` / `Classical.choice`), checked exhaustively
rather than by sampling.

Two per-core hardware views this module proves *invisible* — the SM7.C
`perCoreTlb` and the SM7.D `perCoreICache` — are nonetheless registered as
**accepted covert channels CC-6 and CC-7** in the plan's §3.5 inventory, on
the CC-2 machine-timer precedent: excluding a field from the projection is a
statement about the model, and a real observer still measures cache and TLB
residency by timing its own accesses.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId bootCoreId)

-- ============================================================================
-- §1  The SMP observer (plan Definition 3.1.1)
-- ============================================================================

/-- SM8.A.1: the `IfObserver` carrying clearance `L`.

The label-filtered projections (`projectObjects`, `projectIrqHandlers`, …)
are indexed by an `IfObserver`; naming the injection keeps every SM8 site
from re-spelling the anonymous-constructor literal, so the observer's
clearance is threaded through one function rather than by convention. -/
def IfObserver.ofLabel (L : SecurityLabel) : IfObserver := { clearance := L }

@[simp] theorem IfObserver.ofLabel_clearance (L : SecurityLabel) :
    (IfObserver.ofLabel L).clearance = L := rfl

/-- SM8.A.1 (plan Definition 3.1.1): an SMP information-flow **observer** is a
pair `(c, L)` — an attacker thread with clearance `L` running on core `c`.

Per-core rather than per-thread (plan §4.1): a thread is bound to a core by
`cpuAffinity`, and every cross-core leakage path the SMP kernel opens
(scheduling decisions, lock contention, cross-core IPC) is a per-core
operation, so the core is the coarsest observer coordinate that still makes
each core's view a function of its own per-core state plus label-filtered
shared state. -/
structure PerCoreObserver where
  /-- The core the observer executes on. -/
  core : CoreId
  /-- The observer's security clearance. -/
  clearance : SecurityLabel
  deriving Repr, DecidableEq

/-- The label half of a per-core observer, as the `IfObserver` the
label-filtered (core-independent) projections consume. -/
def PerCoreObserver.toIfObserver (o : PerCoreObserver) : IfObserver :=
  IfObserver.ofLabel o.clearance

@[simp] theorem PerCoreObserver.toIfObserver_clearance (o : PerCoreObserver) :
    o.toIfObserver.clearance = o.clearance := rfl

/-- The boot-core observer at clearance `L` — the observer whose view is the
live single-core projection (see `onCore_bootCore`). -/
def PerCoreObserver.onBootCore (L : SecurityLabel) : PerCoreObserver :=
  { core := bootCoreId, clearance := L }

-- ============================================================================
-- §2  SM8.A.1 — `ObservableState.onCore` (plan Definition 3.2.1)
-- ============================================================================

/-- SM8.A.1 (plan Definition 3.2.1): the observable state at the observer
`(c, L)`.

The per-core components (`runnable`, `current`, `activeDomain`,
`domainTimeRemaining`, `domainScheduleIndex`, `machineRegs`) are read off
core `c`'s scheduler slots and register bank; the shared components
(`objects`, `services`, `irqHandlers`, `objectIndex`, `domainSchedule`,
`memory`, `serviceRegistry`) are label-filtered only.

Defined as the SM4.D `projectStateOnCore` at the observer `⟨L⟩` rather than
as a second structure literal: one projection function, so the per-core
observer and the SM4.D per-core invariant migration cannot drift apart. -/
def ObservableState.onCore (ctx : LabelingContext) (c : CoreId) (L : SecurityLabel)
    (s : SystemState) : ObservableState :=
  projectStateOnCore ctx (IfObserver.ofLabel L) s c

/-- SM8.A.1: the per-core observable state is the SM4.D per-core projection
(definition-pinning anchor — a divergence between the SM8 observer view and
the SM4.D projection layer is a compile error). -/
theorem onCore_eq_projectStateOnCore (ctx : LabelingContext) (c : CoreId)
    (L : SecurityLabel) (s : SystemState) :
    ObservableState.onCore ctx c L s = projectStateOnCore ctx (IfObserver.ofLabel L) s c := rfl

/-- SM8.A.1: at the boot core the per-core observable state is *definitionally*
the live single-core `projectState`.  This is the non-orphan connection to the
existing (single-core) non-interference surface: every SM8 theorem instantiated
at `bootCoreId` is a statement about the live projection. -/
theorem onCore_bootCore (ctx : LabelingContext) (L : SecurityLabel) (s : SystemState) :
    ObservableState.onCore ctx bootCoreId L s = projectState ctx (IfObserver.ofLabel L) s := rfl

/-- The view a per-core observer has of a state. -/
def PerCoreObserver.view (o : PerCoreObserver) (ctx : LabelingContext)
    (s : SystemState) : ObservableState :=
  ObservableState.onCore ctx o.core o.clearance s

/-- SM8.A.1: low-equivalence *at an observer* — the SM8.B non-interference
substrate.  Two states are indistinguishable to `(c, L)` when the observer's
views agree. -/
def lowEquivalentForObserver (ctx : LabelingContext) (o : PerCoreObserver)
    (s₁ s₂ : SystemState) : Prop :=
  o.view ctx s₁ = o.view ctx s₂

/-- The observer form and the SM4.D `(core, IfObserver)` form of per-core
low-equivalence are the same relation. -/
theorem lowEquivalentForObserver_iff_lowEquivalentOnCore
    (ctx : LabelingContext) (o : PerCoreObserver) (s₁ s₂ : SystemState) :
    lowEquivalentForObserver ctx o s₁ s₂ ↔
      lowEquivalentOnCore ctx o.toIfObserver s₁ s₂ o.core := Iff.rfl

/-- At the boot-core observer, observer low-equivalence is the live
single-core `lowEquivalent`. -/
theorem lowEquivalentForObserver_bootCore (ctx : LabelingContext) (L : SecurityLabel)
    (s₁ s₂ : SystemState) :
    lowEquivalentForObserver ctx (PerCoreObserver.onBootCore L) s₁ s₂ ↔
      lowEquivalent ctx (IfObserver.ofLabel L) s₁ s₂ := Iff.rfl

theorem lowEquivalentForObserver_refl (ctx : LabelingContext) (o : PerCoreObserver)
    (s : SystemState) : lowEquivalentForObserver ctx o s s := rfl

theorem lowEquivalentForObserver_symm {ctx : LabelingContext} {o : PerCoreObserver}
    {s₁ s₂ : SystemState} (h : lowEquivalentForObserver ctx o s₁ s₂) :
    lowEquivalentForObserver ctx o s₂ s₁ := h.symm

theorem lowEquivalentForObserver_trans {ctx : LabelingContext} {o : PerCoreObserver}
    {s₁ s₂ s₃ : SystemState}
    (h₁ : lowEquivalentForObserver ctx o s₁ s₂)
    (h₂ : lowEquivalentForObserver ctx o s₂ s₃) :
    lowEquivalentForObserver ctx o s₁ s₃ := h₁.trans h₂

/-- SM8.A.1: the SMP form — indistinguishable to *every* observer at
clearance `L`.  Definitionally the SM4.D `lowEquivalent_smp` at `⟨L⟩`, so the
SM6 cross-core non-interference theorems already stated in that form are
statements about all per-core observers at their label. -/
theorem lowEquivalent_smp_iff_forall_observer (ctx : LabelingContext) (L : SecurityLabel)
    (s₁ s₂ : SystemState) :
    lowEquivalent_smp ctx (IfObserver.ofLabel L) s₁ s₂ ↔
      ∀ c : CoreId, lowEquivalentForObserver ctx ⟨c, L⟩ s₁ s₂ := Iff.rfl

-- ============================================================================
-- §3  SM8.A.2 — the shared / per-core field partition
-- ============================================================================
--
-- `ObservableState` has thirteen components.  Under the per-core observer
-- they split into two groups:
--
--   * SHARED (7)   — objects, services, irqHandlers, objectIndex,
--                    domainSchedule, memory, serviceRegistry.  Filtered by
--                    the observer's label; read no per-core scheduler slot
--                    and no per-core register bank, hence identical from
--                    every core.  (`domainSchedule` is a system-wide
--                    `SchedulerState` field, not a per-core `Vector`.)
--   * PER-CORE (6) — runnable, current, activeDomain, domainTimeRemaining,
--                    domainScheduleIndex, machineRegs.  Restricted to core
--                    `c`'s slots / register bank.
--
-- `ObservableState.ext_fragments` below closes the partition: it rebuilds an
-- observable state from the two fragments, so a new `ObservableState` field
-- that is registered in neither fragment makes that theorem fail to
-- elaborate.  This is the structural form of the plan §7 risk "per-core
-- projection missing a field" — a build error, not a review checklist.

/-- SM8.A.2: the components of an observable state that are the same from
every core (they are filtered by the observer's *label* only). -/
structure SharedObservableFragment where
  objects : SeLe4n.ObjId → Option KernelObject
  services : ServiceId → Bool
  irqHandlers : SeLe4n.Irq → Option SeLe4n.ObjId
  objectIndex : List SeLe4n.ObjId
  domainSchedule : List DomainScheduleEntry
  memory : SeLe4n.PAddr → Option UInt8
  serviceRegistry : ServiceId → Option ServiceGraphEntry

/-- SM8.A.2: the components of an observable state that are restricted to the
observer's core. -/
structure PerCoreObservableFragment where
  runnable : List SeLe4n.ThreadId
  current : Option SeLe4n.ThreadId
  activeDomain : SeLe4n.DomainId
  domainTimeRemaining : Nat
  domainScheduleIndex : Nat
  machineRegs : Option RegisterFile

/-- The shared half of an observable state. -/
def ObservableState.sharedFragment (v : ObservableState) : SharedObservableFragment :=
  { objects := v.objects
    services := v.services
    irqHandlers := v.irqHandlers
    objectIndex := v.objectIndex
    domainSchedule := v.domainSchedule
    memory := v.memory
    serviceRegistry := v.serviceRegistry }

/-- The core-restricted half of an observable state. -/
def ObservableState.perCoreFragment (v : ObservableState) : PerCoreObservableFragment :=
  { runnable := v.runnable
    current := v.current
    activeDomain := v.activeDomain
    domainTimeRemaining := v.domainTimeRemaining
    domainScheduleIndex := v.domainScheduleIndex
    machineRegs := v.machineRegs }

/-- SM8.A.2 (partition totality): the two fragments **determine** the
observable state.

This is the field-coverage tripwire.  Adding a component to
`ObservableState` without assigning it to `SharedObservableFragment` or
`PerCoreObservableFragment` leaves this theorem unprovable, so the per-core
observer can never silently drop a security-relevant field. -/
theorem ObservableState.ext_fragments {v₁ v₂ : ObservableState}
    (hShared : v₁.sharedFragment = v₂.sharedFragment)
    (hPerCore : v₁.perCoreFragment = v₂.perCoreFragment) : v₁ = v₂ := by
  obtain ⟨o₁, r₁, cu₁, sv₁, ad₁, ih₁, oi₁, dtr₁, ds₁, dsi₁, mr₁, m₁, sr₁⟩ := v₁
  obtain ⟨o₂, r₂, cu₂, sv₂, ad₂, ih₂, oi₂, dtr₂, ds₂, dsi₂, mr₂, m₂, sr₂⟩ := v₂
  simp only [ObservableState.sharedFragment, ObservableState.perCoreFragment,
    SharedObservableFragment.mk.injEq, PerCoreObservableFragment.mk.injEq] at hShared hPerCore
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hShared
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hPerCore
  subst_vars
  rfl

/-- SM8.A.2: rebuild an observable state from its two fragments.

Together with `ofFragments_sharedFragment` / `ofFragments_perCoreFragment` /
`ofFragments_eta` below this makes the partition a **bijection**
`ObservableState ≃ SharedObservableFragment × PerCoreObservableFragment`, which
is what turns "a fourteenth field is a compile error" from an argument into a
checked fact: a new `ObservableState` component leaves this definition unable
to produce it. -/
def ObservableState.ofFragments (sh : SharedObservableFragment)
    (pc : PerCoreObservableFragment) : ObservableState :=
  { objects := sh.objects
    runnable := pc.runnable
    current := pc.current
    services := sh.services
    activeDomain := pc.activeDomain
    irqHandlers := sh.irqHandlers
    objectIndex := sh.objectIndex
    domainTimeRemaining := pc.domainTimeRemaining
    domainSchedule := sh.domainSchedule
    domainScheduleIndex := pc.domainScheduleIndex
    machineRegs := pc.machineRegs
    memory := sh.memory
    serviceRegistry := sh.serviceRegistry }

@[simp] theorem ObservableState.ofFragments_sharedFragment (sh : SharedObservableFragment)
    (pc : PerCoreObservableFragment) : (ObservableState.ofFragments sh pc).sharedFragment = sh := by
  cases sh; rfl

@[simp] theorem ObservableState.ofFragments_perCoreFragment (sh : SharedObservableFragment)
    (pc : PerCoreObservableFragment) : (ObservableState.ofFragments sh pc).perCoreFragment = pc := by
  cases pc; rfl

/-- SM8.A.2 (the load-bearing half of the tripwire): the two fragments carry
**all** of an observable state — reassembling them returns the original.

`ext_fragments` says the fragments determine the state; this says they
*constitute* it.  A component added to `ObservableState` and registered in
neither fragment makes `ofFragments` unable to supply it, so the definition
above stops compiling before this theorem is ever reached. -/
@[simp] theorem ObservableState.ofFragments_eta (v : ObservableState) :
    ObservableState.ofFragments v.sharedFragment v.perCoreFragment = v := by
  cases v; rfl

/-- SM8.A.2: the fragment pair is a faithful encoding — distinct observable
states have distinct fragment pairs. -/
theorem ObservableState.fragments_injective {v₁ v₂ : ObservableState}
    (h : (v₁.sharedFragment, v₁.perCoreFragment) = (v₂.sharedFragment, v₂.perCoreFragment)) :
    v₁ = v₂ :=
  ObservableState.ext_fragments (congrArg Prod.fst h) (congrArg Prod.snd h)

/-- SM8.A.2 (definition-pinning): the shared fragment of the per-core
observable state, spelled out.  Every component is a *label-only* projection —
no `…OnCore` accessor appears — which is what makes the fragment
core-independent below. -/
@[simp] theorem onCore_sharedFragment (ctx : LabelingContext) (c : CoreId)
    (L : SecurityLabel) (s : SystemState) :
    (ObservableState.onCore ctx c L s).sharedFragment =
      { objects := projectObjects ctx (IfObserver.ofLabel L) s
        services := projectServicePresence ctx (IfObserver.ofLabel L) s
        irqHandlers := projectIrqHandlers ctx (IfObserver.ofLabel L) s
        objectIndex := projectObjectIndex ctx (IfObserver.ofLabel L) s
        domainSchedule := projectDomainSchedule ctx (IfObserver.ofLabel L) s
        memory := projectMemory ctx (IfObserver.ofLabel L) s
        serviceRegistry := projectServiceRegistry ctx (IfObserver.ofLabel L) s } := rfl

/-- SM8.A.2 (definition-pinning): the per-core fragment of the per-core
observable state, spelled out.  Every component is an `…OnCore c` projection —
core `c` and no other. -/
@[simp] theorem onCore_perCoreFragment (ctx : LabelingContext) (c : CoreId)
    (L : SecurityLabel) (s : SystemState) :
    (ObservableState.onCore ctx c L s).perCoreFragment =
      { runnable := projectRunnableOnCore ctx (IfObserver.ofLabel L) s c
        current := projectCurrentOnCore ctx (IfObserver.ofLabel L) s c
        activeDomain := projectActiveDomainOnCore ctx (IfObserver.ofLabel L) s c
        domainTimeRemaining := projectDomainTimeRemainingOnCore ctx (IfObserver.ofLabel L) s c
        domainScheduleIndex := projectDomainScheduleIndexOnCore ctx (IfObserver.ofLabel L) s c
        machineRegs := projectMachineRegsOnCore ctx (IfObserver.ofLabel L) s c } := rfl

/-! ### Component accessors

One `@[simp]` lemma per `ObservableState` component, each `rfl`.  They are the
working form of the §3 decomposition — a proof about one observable component
rewrites straight to the projection that computes it — and, like the fragment
lemmas above, they pin the definition: re-pointing a component at a different
projection breaks the corresponding `rfl`. -/

@[simp] theorem onCore_objects (ctx : LabelingContext) (c : CoreId) (L : SecurityLabel)
    (s : SystemState) :
    (ObservableState.onCore ctx c L s).objects = projectObjects ctx (IfObserver.ofLabel L) s := rfl

@[simp] theorem onCore_services (ctx : LabelingContext) (c : CoreId) (L : SecurityLabel)
    (s : SystemState) :
    (ObservableState.onCore ctx c L s).services =
      projectServicePresence ctx (IfObserver.ofLabel L) s := rfl

@[simp] theorem onCore_irqHandlers (ctx : LabelingContext) (c : CoreId) (L : SecurityLabel)
    (s : SystemState) :
    (ObservableState.onCore ctx c L s).irqHandlers =
      projectIrqHandlers ctx (IfObserver.ofLabel L) s := rfl

@[simp] theorem onCore_objectIndex (ctx : LabelingContext) (c : CoreId) (L : SecurityLabel)
    (s : SystemState) :
    (ObservableState.onCore ctx c L s).objectIndex =
      projectObjectIndex ctx (IfObserver.ofLabel L) s := rfl

@[simp] theorem onCore_domainSchedule (ctx : LabelingContext) (c : CoreId) (L : SecurityLabel)
    (s : SystemState) :
    (ObservableState.onCore ctx c L s).domainSchedule =
      projectDomainSchedule ctx (IfObserver.ofLabel L) s := rfl

@[simp] theorem onCore_memory (ctx : LabelingContext) (c : CoreId) (L : SecurityLabel)
    (s : SystemState) :
    (ObservableState.onCore ctx c L s).memory = projectMemory ctx (IfObserver.ofLabel L) s := rfl

@[simp] theorem onCore_serviceRegistry (ctx : LabelingContext) (c : CoreId) (L : SecurityLabel)
    (s : SystemState) :
    (ObservableState.onCore ctx c L s).serviceRegistry =
      projectServiceRegistry ctx (IfObserver.ofLabel L) s := rfl

@[simp] theorem onCore_runnable (ctx : LabelingContext) (c : CoreId) (L : SecurityLabel)
    (s : SystemState) :
    (ObservableState.onCore ctx c L s).runnable =
      projectRunnableOnCore ctx (IfObserver.ofLabel L) s c := rfl

@[simp] theorem onCore_current (ctx : LabelingContext) (c : CoreId) (L : SecurityLabel)
    (s : SystemState) :
    (ObservableState.onCore ctx c L s).current =
      projectCurrentOnCore ctx (IfObserver.ofLabel L) s c := rfl

@[simp] theorem onCore_activeDomain (ctx : LabelingContext) (c : CoreId) (L : SecurityLabel)
    (s : SystemState) :
    (ObservableState.onCore ctx c L s).activeDomain =
      projectActiveDomainOnCore ctx (IfObserver.ofLabel L) s c := rfl

@[simp] theorem onCore_domainTimeRemaining (ctx : LabelingContext) (c : CoreId)
    (L : SecurityLabel) (s : SystemState) :
    (ObservableState.onCore ctx c L s).domainTimeRemaining =
      projectDomainTimeRemainingOnCore ctx (IfObserver.ofLabel L) s c := rfl

@[simp] theorem onCore_domainScheduleIndex (ctx : LabelingContext) (c : CoreId)
    (L : SecurityLabel) (s : SystemState) :
    (ObservableState.onCore ctx c L s).domainScheduleIndex =
      projectDomainScheduleIndexOnCore ctx (IfObserver.ofLabel L) s c := rfl

@[simp] theorem onCore_machineRegs (ctx : LabelingContext) (c : CoreId) (L : SecurityLabel)
    (s : SystemState) :
    (ObservableState.onCore ctx c L s).machineRegs =
      projectMachineRegsOnCore ctx (IfObserver.ofLabel L) s c := rfl

/-- SM8.A.2: the shared fragment of the per-core observable state **is** the
shared fragment of the global projection — the per-core observer adds no
shared-component content and removes none. -/
theorem onCore_sharedFragment_eq_globalProjection (ctx : LabelingContext) (c : CoreId)
    (L : SecurityLabel) (s : SystemState) :
    (ObservableState.onCore ctx c L s).sharedFragment =
      (projectState ctx (IfObserver.ofLabel L) s).sharedFragment := rfl

/-- SM8.A.2: consequently the shared fragment is a **function of the global
projection alone** — two states a global observer at `L` cannot distinguish
are indistinguishable on every shared component to a per-core observer at
`(c, L)`, for every core.  (The per-core-specific content is confined to the
six components of `PerCoreObservableFragment`; see
`onCore_perCore_independence` for the matching read-set bound.) -/
theorem onCore_sharedFragment_determined_by_globalProjection
    (ctx : LabelingContext) (c : CoreId) (L : SecurityLabel) {s₁ s₂ : SystemState}
    (h : projectState ctx (IfObserver.ofLabel L) s₁ = projectState ctx (IfObserver.ofLabel L) s₂) :
    (ObservableState.onCore ctx c L s₁).sharedFragment =
      (ObservableState.onCore ctx c L s₂).sharedFragment := by
  rw [onCore_sharedFragment_eq_globalProjection, onCore_sharedFragment_eq_globalProjection, h]

/-- SM8.A.2: the shared fragment is the **same on every core** — the core
coordinate of the observer touches only the six per-core components.  This is
the orthogonality of the two observer dimensions: the core selects scheduler
slots, the label selects entities.

Note what this does *not* say.  A shared component that read one fixed core's
slot would still be core-independent in this sense (every observer would see
that core's value), so this theorem alone would not catch it.  The theorem that
does is `onCore_perCore_independence`, whose hypotheses mention only shared
*state* components and the observer's own core: a shared projection reading
`bootCoreId`'s slot would leave it unprovable for `c ≠ bootCoreId`. -/
theorem onCore_sharedFragment_core_independent (ctx : LabelingContext)
    (L : SecurityLabel) (s : SystemState) (c c' : CoreId) :
    (ObservableState.onCore ctx c L s).sharedFragment =
      (ObservableState.onCore ctx c' L s).sharedFragment := rfl

/-- SM8.A.2: what the per-core observer at `(c, L)` actually holds — the shared
fragment of the **global** projection, paired with core `c`'s per-core
fragment. -/
def observableFactorOnCore (ctx : LabelingContext) (c : CoreId) (L : SecurityLabel)
    (s : SystemState) : SharedObservableFragment × PerCoreObservableFragment :=
  ((projectState ctx (IfObserver.ofLabel L) s).sharedFragment,
   (ObservableState.onCore ctx c L s).perCoreFragment)

/-- SM8.A.2 (headline): **the per-core observable state is exactly a projection
of the global projection.**

Two states are indistinguishable to the observer `(c, L)` **if and only if**
they agree on the shared fragment of the *global* projection at `L` and on core
`c`'s per-core fragment.  So `ObservableState.onCore` factors through

    s ↦ (global projection's shared part at L, core c's six slots)

and the factoring is *faithful*: the observer learns that pair, all of it and
nothing beyond it.

Both directions carry weight.  `→` is the completeness half — no observable
difference escapes the pair.  `←` is the soundness half, and it is the one the
SM4.D congruence could not give: it needs the §3 partition to be total
(`ext_fragments`), not merely a convenient grouping.  The state-level
convenience form is `onCore_congr_of_globalProjection` below; the
boot-core-free form SM8.B consumes is `onCore_perCore_independence` (§5). -/
theorem onCore_isProjection_of_globalProjection
    (ctx : LabelingContext) (c : CoreId) (L : SecurityLabel) (s₁ s₂ : SystemState) :
    ObservableState.onCore ctx c L s₁ = ObservableState.onCore ctx c L s₂ ↔
      observableFactorOnCore ctx c L s₁ = observableFactorOnCore ctx c L s₂ := by
  constructor
  · intro h
    have hS : (projectState ctx (IfObserver.ofLabel L) s₁).sharedFragment
        = (projectState ctx (IfObserver.ofLabel L) s₂).sharedFragment := by
      rw [← onCore_sharedFragment_eq_globalProjection ctx c L s₁,
          ← onCore_sharedFragment_eq_globalProjection ctx c L s₂]
      exact congrArg ObservableState.sharedFragment h
    have hP : (ObservableState.onCore ctx c L s₁).perCoreFragment
        = (ObservableState.onCore ctx c L s₂).perCoreFragment :=
      congrArg ObservableState.perCoreFragment h
    unfold observableFactorOnCore
    rw [hS, hP]
  · intro h
    refine ObservableState.ext_fragments ?_ (congrArg Prod.snd h)
    rw [onCore_sharedFragment_eq_globalProjection, onCore_sharedFragment_eq_globalProjection]
    exact congrArg Prod.fst h

/-- SM8.A.2 (state-level convenience form): equal global projections plus equal
core-`c` slots give equal per-core views.  A direct instance of the SM4.D
per-core congruence; the substantive statement is the `iff` above. -/
theorem onCore_congr_of_globalProjection
    (ctx : LabelingContext) (c : CoreId) (L : SecurityLabel) {s₁ s₂ : SystemState}
    (hGlobal : projectState ctx (IfObserver.ofLabel L) s₁
      = projectState ctx (IfObserver.ofLabel L) s₂)
    (hRQ : s₁.scheduler.runQueueOnCore c = s₂.scheduler.runQueueOnCore c)
    (hCur : s₁.scheduler.currentOnCore c = s₂.scheduler.currentOnCore c)
    (hAD : s₁.scheduler.activeDomainOnCore c = s₂.scheduler.activeDomainOnCore c)
    (hDTR : s₁.scheduler.domainTimeRemainingOnCore c = s₂.scheduler.domainTimeRemainingOnCore c)
    (hDSI : s₁.scheduler.domainScheduleIndexOnCore c = s₂.scheduler.domainScheduleIndexOnCore c)
    (hRegs : s₁.machine.regsOnCore c = s₂.machine.regsOnCore c) :
    ObservableState.onCore ctx c L s₁ = ObservableState.onCore ctx c L s₂ :=
  projectStateOnCore_congr ctx (IfObserver.ofLabel L) hGlobal hRQ hCur hAD hDTR hDSI hRegs

-- ============================================================================
-- §4  SM8.A.3 — the decidable fragment of the per-core observable state
-- ============================================================================
--
-- Equality of `ObservableState` values is **not** decidable, and no honest
-- instance can claim otherwise:
--
--   * five components are functions over unbounded domains — `objects`
--     (`ObjId → …`), `services` and `serviceRegistry` (`ServiceId → …`),
--     `irqHandlers` (`Irq → …`) and `memory` (`PAddr → …`);
--   * `machineRegs` carries a `RegisterFile`, whose `gpr : RegName →
--     RegValue` component makes even its structural `BEq` non-lawful — see
--     `RegisterFile.not_lawfulBEq`, which exhibits two register files that
--     compare equal yet differ.
--
-- What *is* decidable is the fragment below: the five per-core scheduler
-- components (all with `DecidableEq`) plus the register bank's
-- **observability**, which is a `Bool`.  The fragment is a sound refuter
-- (`lowEquivalentSliceOnCore_of_lowEquivalentOnCore`: equal views ⇒ equal
-- slices, so a slice mismatch is a genuine observable difference) and is
-- proven **strict** (`perCoreSlice_erases_register_content`,
-- `perCoreSlice_erases_shared_content`), so a `decide` on the slice can
-- never be mistaken for a decision about the observable state.

/-- SM8.A.3: the decidable fragment of the per-core observable state.

Carries the five `DecidableEq` per-core scheduler components verbatim and
replaces the register bank by the `Bool` recording whether it is observable
at all.  The register *content* is deliberately outside the fragment: see
the section note. -/
structure PerCoreObservableSlice where
  runnable : List SeLe4n.ThreadId
  current : Option SeLe4n.ThreadId
  activeDomain : SeLe4n.DomainId
  domainTimeRemaining : Nat
  domainScheduleIndex : Nat
  /-- Whether the observer sees core `c`'s register bank at all — `true`
      exactly when core `c`'s current thread is observable. -/
  registersObservable : Bool
  deriving Repr, DecidableEq

/-- The decidable slice of an observable state. -/
def ObservableState.perCoreSlice (v : ObservableState) : PerCoreObservableSlice :=
  { runnable := v.runnable
    current := v.current
    activeDomain := v.activeDomain
    domainTimeRemaining := v.domainTimeRemaining
    domainScheduleIndex := v.domainScheduleIndex
    registersObservable := v.machineRegs.isSome }

/-- SM8.A.3: the decidable slice observed at `(c, L)`. -/
def ObservableState.sliceOnCore (ctx : LabelingContext) (c : CoreId) (L : SecurityLabel)
    (s : SystemState) : PerCoreObservableSlice :=
  (ObservableState.onCore ctx c L s).perCoreSlice

/-- SM8.A.3: per-core low-equivalence **restricted to the decidable slice**.
Deliberately a distinct relation from `lowEquivalentOnCore`, so that a
`decide` can never be read as deciding observable-state equality. -/
def lowEquivalentSliceOnCore (ctx : LabelingContext) (c : CoreId) (L : SecurityLabel)
    (s₁ s₂ : SystemState) : Prop :=
  ObservableState.sliceOnCore ctx c L s₁ = ObservableState.sliceOnCore ctx c L s₂

/-- SM8.A.3 (the instance): slice-level per-core low-equivalence is decidable. -/
instance onCore_decidable (ctx : LabelingContext) (c : CoreId) (L : SecurityLabel)
    (s₁ s₂ : SystemState) : Decidable (lowEquivalentSliceOnCore ctx c L s₁ s₂) :=
  inferInstanceAs (Decidable (_ = _))

/-- SM8.A.3 (soundness as a refuter): observable equality at `(c, L)` implies
slice equality.  Contrapositively, a decided slice **mismatch** is a genuine
difference in what the observer sees — the decision procedure never reports a
leak that is not there. -/
theorem lowEquivalentSliceOnCore_of_lowEquivalentOnCore
    (ctx : LabelingContext) (c : CoreId) (L : SecurityLabel) {s₁ s₂ : SystemState}
    (h : lowEquivalentOnCore ctx (IfObserver.ofLabel L) s₁ s₂ c) :
    lowEquivalentSliceOnCore ctx c L s₁ s₂ :=
  congrArg ObservableState.perCoreSlice h

/-- SM8.A.3 (strictness, register half): the slice keeps only the register
bank's *observability*, not its content.  Two observable states whose register
files differ everywhere have the same slice, so slice equality is strictly
weaker than observable equality. -/
theorem perCoreSlice_erases_register_content :
    ∃ v₁ v₂ : ObservableState,
      v₁.perCoreSlice = v₂.perCoreSlice ∧ v₁.machineRegs ≠ v₂.machineRegs := by
  refine ⟨{ objects := fun _ => none, runnable := [], current := none,
            services := fun _ => false, activeDomain := ⟨0⟩, irqHandlers := fun _ => none,
            objectIndex := [], domainTimeRemaining := 0, domainSchedule := [],
            domainScheduleIndex := 0,
            machineRegs := some { pc := ⟨0⟩, sp := ⟨0⟩, gpr := fun _ => ⟨0⟩ },
            memory := fun _ => none, serviceRegistry := fun _ => none },
          { objects := fun _ => none, runnable := [], current := none,
            services := fun _ => false, activeDomain := ⟨0⟩, irqHandlers := fun _ => none,
            objectIndex := [], domainTimeRemaining := 0, domainSchedule := [],
            domainScheduleIndex := 0,
            machineRegs := some { pc := ⟨1⟩, sp := ⟨0⟩, gpr := fun _ => ⟨0⟩ },
            memory := fun _ => none, serviceRegistry := fun _ => none },
          rfl, ?_⟩
  intro h
  have hval : (0 : Nat) = 1 :=
    congrArg (fun (o : Option RegisterFile) =>
      match o with | some rf => rf.pc.val | none => 0) h
  exact absurd hval (by decide)

/-- SM8.A.3 (strictness, shared half): the slice carries no shared component,
so two observable states differing only in a shared component also have the
same slice.  Together with `perCoreSlice_erases_register_content` this pins
the decidable fragment as a **strict** sub-observation on both halves of the
§3 partition. -/
theorem perCoreSlice_erases_shared_content :
    ∃ v₁ v₂ : ObservableState, v₁.perCoreSlice = v₂.perCoreSlice ∧ v₁ ≠ v₂ := by
  refine ⟨{ objects := fun _ => none, runnable := [], current := none,
            services := fun _ => false, activeDomain := ⟨0⟩, irqHandlers := fun _ => none,
            objectIndex := [], domainTimeRemaining := 0, domainSchedule := [],
            domainScheduleIndex := 0, machineRegs := none,
            memory := fun _ => none, serviceRegistry := fun _ => none },
          { objects := fun _ => none, runnable := [], current := none,
            services := fun _ => false, activeDomain := ⟨0⟩, irqHandlers := fun _ => none,
            objectIndex := [SeLe4n.ObjId.ofNat 0], domainTimeRemaining := 0,
            domainSchedule := [], domainScheduleIndex := 0, machineRegs := none,
            memory := fun _ => none, serviceRegistry := fun _ => none },
          rfl, ?_⟩
  intro h
  have hidx : ([] : List SeLe4n.ObjId) = [SeLe4n.ObjId.ofNat 0] :=
    congrArg ObservableState.objectIndex h
  exact absurd hidx (by decide)

/-- SM8.A.3: the slice of the per-core observable state, spelled out — the
form the runtime suite decides on. -/
@[simp] theorem onCore_perCoreSlice (ctx : LabelingContext) (c : CoreId)
    (L : SecurityLabel) (s : SystemState) :
    ObservableState.sliceOnCore ctx c L s =
      { runnable := projectRunnableOnCore ctx (IfObserver.ofLabel L) s c
        current := projectCurrentOnCore ctx (IfObserver.ofLabel L) s c
        activeDomain := projectActiveDomainOnCore ctx (IfObserver.ofLabel L) s c
        domainTimeRemaining := projectDomainTimeRemainingOnCore ctx (IfObserver.ofLabel L) s c
        domainScheduleIndex := projectDomainScheduleIndexOnCore ctx (IfObserver.ofLabel L) s c
        registersObservable :=
          (projectMachineRegsOnCore ctx (IfObserver.ofLabel L) s c).isSome } := rfl

/-! ### The finer check: carrying the register bank's structural comparison

The slice keeps only whether the register bank is *observable*.  The bank's
content can still be compared — by `RegisterFile`'s structural `BEq` over `pc`,
`sp` and the 32 architectural GPRs, which is exactly what the model documents
that instance for.  The check below is therefore strictly finer than
`lowEquivalentSliceOnCore` while remaining computable.

It is **not** a decision procedure for observable equality, and cannot be made
one: `RegisterFile`'s `BEq` is not lawful (`RegisterFile.not_lawfulBEq`), so
`= true` does not imply the banks are equal, and the shared components are
still absent.  Its guarantee is one-directional and stated as such below. -/

/-- `Option RegisterFile`'s structural comparison is reflexive (it inherits
`RegisterFile.beq_self`), which is what makes the finer check sound. -/
theorem machineRegs_beq_self (o : Option RegisterFile) : (o == o) = true := by
  cases o with
  | none => rfl
  | some rf => exact RegisterFile.beq_self rf

/-- SM8.A.3 (finer check): the decidable slice **plus** the register bank's
structural comparison. -/
def lowEquivalentSliceOnCoreCheckWithRegs (ctx : LabelingContext) (c : CoreId)
    (L : SecurityLabel) (s₁ s₂ : SystemState) : Bool :=
  decide (lowEquivalentSliceOnCore ctx c L s₁ s₂) &&
    ((ObservableState.onCore ctx c L s₁).machineRegs
      == (ObservableState.onCore ctx c L s₂).machineRegs)

/-- SM8.A.3: the finer check is a sound refuter too — observable equality at
`(c, L)` implies it returns `true`, so a `false` is a genuine difference. -/
theorem lowEquivalentSliceOnCoreCheckWithRegs_of_lowEquivalentOnCore
    (ctx : LabelingContext) (c : CoreId) (L : SecurityLabel) {s₁ s₂ : SystemState}
    (h : lowEquivalentOnCore ctx (IfObserver.ofLabel L) s₁ s₂ c) :
    lowEquivalentSliceOnCoreCheckWithRegs ctx c L s₁ s₂ = true := by
  have hView : ObservableState.onCore ctx c L s₁ = ObservableState.onCore ctx c L s₂ := h
  simp only [lowEquivalentSliceOnCoreCheckWithRegs, hView, Bool.and_eq_true,
    decide_eq_true_eq, machineRegs_beq_self, and_true]
  exact lowEquivalentSliceOnCore_of_lowEquivalentOnCore ctx c L h

/-- SM8.A.3: the finer check refines the slice — it can only reject more. -/
theorem lowEquivalentSliceOnCoreCheckWithRegs_le_slice (ctx : LabelingContext) (c : CoreId)
    (L : SecurityLabel) (s₁ s₂ : SystemState)
    (h : lowEquivalentSliceOnCoreCheckWithRegs ctx c L s₁ s₂ = true) :
    lowEquivalentSliceOnCore ctx c L s₁ s₂ := by
  simp only [lowEquivalentSliceOnCoreCheckWithRegs, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

/-- SM8.A.3 (the finer check is still strict): `RegisterFile`'s comparison is
not lawful, so even the register-aware check accepts states whose banks differ.
Two banks agreeing on `pc`, `sp` and all 32 architectural GPRs but differing at
an out-of-range index compare equal — the same counterexample class as
`RegisterFile.not_lawfulBEq`.  No computable check can close this: the `gpr`
field is a function over an unbounded index type. -/
theorem machineRegs_beq_not_injective :
    ∃ rf₁ rf₂ : RegisterFile, (rf₁ == rf₂) = true ∧ rf₁ ≠ rf₂ := by
  refine ⟨{ pc := ⟨0⟩, sp := ⟨0⟩, gpr := fun _ => ⟨0⟩ },
          { pc := ⟨0⟩, sp := ⟨0⟩, gpr := fun r => if r.val = 32 then ⟨1⟩ else ⟨0⟩ },
          by decide, ?_⟩
  intro h
  have hgpr : (0 : Nat) = 1 :=
    congrArg (fun rf : RegisterFile => (rf.gpr ⟨32⟩).val) h
  exact absurd hgpr (by decide)

-- ============================================================================
-- §5  SM8.A.4 — per-core independence (the read set of the per-core view)
-- ============================================================================
--
-- `onCore_perCore_independence` states the **read set** of the per-core
-- observable state at `(c, L)`:
--
--   shared   : objects, services, irqHandlers, objectIndex,
--              scheduler.domainSchedule, machine.memory
--   core `c` : scheduler.{runQueue, current, activeDomain,
--              domainTimeRemaining, domainScheduleIndex}OnCore c,
--              machine.regsOnCore c
--
-- and nothing else — in particular no other core's scheduler slot or
-- register bank, which is the per-core observability locality the SMP
-- non-interference proofs consume.
--
-- This does **not** follow from the SM4.D `projectStateOnCore_congr`: that
-- lemma's `hBase` hypothesis is equality of the whole *global* projection,
-- which reads the boot core's five scheduler slots and the boot core's
-- register bank.  A cross-core transition on core `c'` generally breaks
-- `hBase` when `c' = bootCoreId`, so SM8.B needs the boot-core-free form
-- proven here.

/-- SM8.A.4 (headline): **the per-core observable state at `(c, L)` reads the
six shared state components and core `c`'s six slots — and nothing else.**

Every hypothesis below names either a shared component or core `c`; no other
core appears.  The `…_ne` corollaries that follow instantiate it against the
SM4.B per-core store/load algebra, giving the cross-core frames directly. -/
theorem onCore_perCore_independence
    (ctx : LabelingContext) (L : SecurityLabel) {s₁ s₂ : SystemState} {c : CoreId}
    (hObjects : s₁.objects = s₂.objects)
    (hServices : s₁.services = s₂.services)
    (hIrq : s₁.irqHandlers = s₂.irqHandlers)
    (hIndex : s₁.objectIndex = s₂.objectIndex)
    (hDomSched : s₁.scheduler.domainSchedule = s₂.scheduler.domainSchedule)
    (hMem : s₁.machine.memory = s₂.machine.memory)
    (hRQ : s₁.scheduler.runQueueOnCore c = s₂.scheduler.runQueueOnCore c)
    (hCur : s₁.scheduler.currentOnCore c = s₂.scheduler.currentOnCore c)
    (hAD : s₁.scheduler.activeDomainOnCore c = s₂.scheduler.activeDomainOnCore c)
    (hDTR : s₁.scheduler.domainTimeRemainingOnCore c = s₂.scheduler.domainTimeRemainingOnCore c)
    (hDSI : s₁.scheduler.domainScheduleIndexOnCore c = s₂.scheduler.domainScheduleIndexOnCore c)
    (hRegs : s₁.machine.regsOnCore c = s₂.machine.regsOnCore c) :
    ObservableState.onCore ctx c L s₁ = ObservableState.onCore ctx c L s₂ := by
  refine ObservableState.ext_fragments ?_ ?_
  · simp only [onCore_sharedFragment, SharedObservableFragment.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · funext oid; simp only [projectObjects]; rw [hObjects]
    · funext sid; simp only [projectServicePresence, lookupService]; rw [hServices]
    · funext irq; simp only [projectIrqHandlers]; rw [hIrq]
    · simp only [projectObjectIndex]; rw [hIndex]
    · simp only [projectDomainSchedule]; rw [hDomSched]
    · exact projectMemory_eq_of_memory_eq _ _ _ _ hMem
    · exact projectServiceRegistry_eq_of_services_eq _ _ _ _ hServices
  · simp only [onCore_perCoreFragment, PerCoreObservableFragment.mk.injEq]
    exact ⟨projectRunnableOnCore_frame _ _ hRQ, projectCurrentOnCore_frame _ _ hCur,
      projectActiveDomainOnCore_frame _ _ hAD, projectDomainTimeRemainingOnCore_frame _ _ hDTR,
      projectDomainScheduleIndexOnCore_frame _ _ hDSI,
      projectMachineRegsOnCore_frame _ _ hCur hRegs⟩

/-! ### Cross-core frames: a write to core `c'` is invisible on core `c ≠ c'` -/

/-- SM8.A.4: writing a *different* core's current-thread slot is invisible to
the observer on core `c`. -/
theorem onCore_setCurrentOnCore_ne (ctx : LabelingContext) (L : SecurityLabel)
    (s : SystemState) {c c' : CoreId} (hne : c ≠ c') (v : Option SeLe4n.ThreadId) :
    ObservableState.onCore ctx c L
        { s with scheduler := s.scheduler.setCurrentOnCore c' v }
      = ObservableState.onCore ctx c L s := by
  refine onCore_perCore_independence ctx L rfl rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_ ?_ rfl <;>
    simp [Ne.symm hne]

/-- SM8.A.4: writing a *different* core's run queue is invisible to the
observer on core `c`. -/
theorem onCore_setRunQueueOnCore_ne (ctx : LabelingContext) (L : SecurityLabel)
    (s : SystemState) {c c' : CoreId} (hne : c ≠ c') (v : SeLe4n.Kernel.RunQueue) :
    ObservableState.onCore ctx c L
        { s with scheduler := s.scheduler.setRunQueueOnCore c' v }
      = ObservableState.onCore ctx c L s := by
  refine onCore_perCore_independence ctx L rfl rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_ ?_ rfl <;>
    simp [Ne.symm hne]

/-- SM8.A.4: writing a *different* core's active domain is invisible to the
observer on core `c`.  (Scheduling transparency makes the *own* core's active
domain unconditionally visible — see `onCore_schedulingTransparency` — so the
per-core restriction is what keeps a remote domain switch out of the view.) -/
theorem onCore_setActiveDomainOnCore_ne (ctx : LabelingContext) (L : SecurityLabel)
    (s : SystemState) {c c' : CoreId} (hne : c ≠ c') (v : SeLe4n.DomainId) :
    ObservableState.onCore ctx c L
        { s with scheduler := s.scheduler.setActiveDomainOnCore c' v }
      = ObservableState.onCore ctx c L s := by
  refine onCore_perCore_independence ctx L rfl rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_ ?_ rfl <;>
    simp [Ne.symm hne]

/-- SM8.A.4: writing a *different* core's remaining domain ticks is invisible
to the observer on core `c`. -/
theorem onCore_setDomainTimeRemainingOnCore_ne (ctx : LabelingContext) (L : SecurityLabel)
    (s : SystemState) {c c' : CoreId} (hne : c ≠ c') (v : Nat) :
    ObservableState.onCore ctx c L
        { s with scheduler := s.scheduler.setDomainTimeRemainingOnCore c' v }
      = ObservableState.onCore ctx c L s := by
  refine onCore_perCore_independence ctx L rfl rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_ ?_ rfl <;>
    simp [Ne.symm hne]

/-- SM8.A.4: writing a *different* core's domain-schedule index is invisible
to the observer on core `c`. -/
theorem onCore_setDomainScheduleIndexOnCore_ne (ctx : LabelingContext) (L : SecurityLabel)
    (s : SystemState) {c c' : CoreId} (hne : c ≠ c') (v : Nat) :
    ObservableState.onCore ctx c L
        { s with scheduler := s.scheduler.setDomainScheduleIndexOnCore c' v }
      = ObservableState.onCore ctx c L s := by
  refine onCore_perCore_independence ctx L rfl rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_ ?_ rfl <;>
    simp [Ne.symm hne]

/-- SM8.A.4: writing a *different* core's register bank is invisible to the
observer on core `c`.  This is the SM5.I per-core register-bank half of the
locality property: a context switch on core `c'` does not change what core
`c`'s observer sees, even though both banks live in the same `MachineState`. -/
theorem onCore_setRegsOnCore_ne (ctx : LabelingContext) (L : SecurityLabel)
    (s : SystemState) {c c' : CoreId} (hne : c ≠ c') (v : RegisterFile) :
    ObservableState.onCore ctx c L { s with machine := s.machine.setRegsOnCore c' v }
      = ObservableState.onCore ctx c L s := by
  refine onCore_perCore_independence ctx L rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl ?_
  exact MachineState.regsOnCore_setRegsOnCore_ne _ _ _ _ (Ne.symm hne)

/-! ### Fields outside the read set: invisible on *every* core

Each of these is `onCore_perCore_independence` with every hypothesis `rfl`.
They are the negative half of read-set exactness — a component the per-core
observable state does not read at all, hence invisible even on the core that
owns it. -/

/-- SM8.A.4: the CBS replenishment queue is scheduler-internal ordering state
outside the observable projection — invisible on **any** core, including the
one written.  (Per-core form of `projectState_replenishQueue_eq`.) -/
theorem onCore_setReplenishQueueOnCore (ctx : LabelingContext) (L : SecurityLabel)
    (s : SystemState) (c c' : CoreId) (v : SeLe4n.Kernel.ReplenishQueue) :
    ObservableState.onCore ctx c L
        { s with scheduler := s.scheduler.setReplenishQueueOnCore c' v }
      = ObservableState.onCore ctx c L s := by
  refine onCore_perCore_independence ctx L rfl rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_ ?_ rfl <;> simp

/-- SM8.A.4: the diagnostic timeout-error log is invisible on any core. -/
theorem onCore_setLastTimeoutErrorsOnCore (ctx : LabelingContext) (L : SecurityLabel)
    (s : SystemState) (c c' : CoreId) (v : List (SeLe4n.ThreadId × KernelError)) :
    ObservableState.onCore ctx c L
        { s with scheduler := s.scheduler.setLastTimeoutErrorsOnCore c' v }
      = ObservableState.onCore ctx c L s := by
  refine onCore_perCore_independence ctx L rfl rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_ ?_ rfl <;> simp

/-- SM8.A.4: the SchedContext→threads performance index is invisible.
(Per-core form of `projectState_scThreadIndex_eq`.) -/
theorem onCore_scThreadIndex (ctx : LabelingContext) (L : SecurityLabel)
    (s : SystemState) (c : CoreId)
    (idx : SeLe4n.Kernel.RobinHood.RHTable SeLe4n.SchedContextId (List SeLe4n.ThreadId)) :
    ObservableState.onCore ctx c L { s with scThreadIndex := idx }
      = ObservableState.onCore ctx c L s :=
  onCore_perCore_independence ctx L rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

/-- SM8.A.4: the machine timer is invisible to every per-core observer.

This is the per-core restatement of the deliberate `ObservableState`
exclusion documented on the structure: projecting a monotonic counter would
hand every observer a timing channel.  Under SMP the exclusion has to hold on
each core separately, which is what this theorem says. -/
theorem onCore_machineTimer (ctx : LabelingContext) (L : SecurityLabel)
    (s : SystemState) (c : CoreId) (t : Nat) :
    ObservableState.onCore ctx c L { s with machine := { s.machine with timer := t } }
      = ObservableState.onCore ctx c L s :=
  onCore_perCore_independence ctx L rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

/-- SM8.A.4: the SM7.C per-core TLB view is invisible to every per-core
observer — a cached translation is a timing channel, kept out of the
projection for the same reason as the machine timer.  (Per-core-observer form
of the SM7.C `perCoreTlb_write_preserves_projection` witness.) -/
theorem onCore_perCoreTlb (ctx : LabelingContext) (L : SecurityLabel)
    (s : SystemState) (c : CoreId)
    (v : Vector TlbState SeLe4n.Kernel.Concurrency.numCores) :
    ObservableState.onCore ctx c L { s with perCoreTlb := v }
      = ObservableState.onCore ctx c L s :=
  onCore_perCore_independence ctx L rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

-- ============================================================================
-- §6  SM8.A.5 — label monotonicity
-- ============================================================================
--
-- Raising the observer's clearance can only widen what it sees.  The
-- observability gates are `securityFlowsTo (label of entity) (clearance)`, so
-- monotonicity is transitivity of the flow relation (`securityFlowsTo_trans`)
-- applied at each gate.
--
-- Note what monotonicity is *not*: it is a statement about **visibility**, not
-- about content.  A wider clearance can reveal *more* of an already-visible
-- CNode (its slot filter admits more targets), so the projected object at the
-- two clearances need not be equal — see `projectCNode_lookup_monotone` for
-- the slot-level refinement and `projectKernelObject_observer_independent_off_cnode`
-- for the (only) arm where equality does hold.
--
-- The four scheduling components move in neither direction: they are
-- unconditionally visible (accepted covert channel CC-1), which
-- `onCore_schedulingTransparency` restates per core.

/-! ### Gate monotonicity -/

/-- SM8.A.5: object observability is monotone in the observer's clearance. -/
theorem objectObservable_monotone (ctx : LabelingContext) {L₁ L₂ : SecurityLabel}
    (hFlow : securityFlowsTo L₁ L₂ = true) (oid : SeLe4n.ObjId)
    (h : objectObservable ctx (IfObserver.ofLabel L₁) oid = true) :
    objectObservable ctx (IfObserver.ofLabel L₂) oid = true :=
  securityFlowsTo_trans _ _ _ h hFlow

/-- SM8.A.5: thread observability is monotone in the observer's clearance. -/
theorem threadObservable_monotone (ctx : LabelingContext) {L₁ L₂ : SecurityLabel}
    (hFlow : securityFlowsTo L₁ L₂ = true) (tid : SeLe4n.ThreadId)
    (h : threadObservable ctx (IfObserver.ofLabel L₁) tid = true) :
    threadObservable ctx (IfObserver.ofLabel L₂) tid = true :=
  securityFlowsTo_trans _ _ _ h hFlow

/-- SM8.A.5: service observability is monotone in the observer's clearance. -/
theorem serviceObservable_monotone (ctx : LabelingContext) {L₁ L₂ : SecurityLabel}
    (hFlow : securityFlowsTo L₁ L₂ = true) (sid : ServiceId)
    (h : serviceObservable ctx (IfObserver.ofLabel L₁) sid = true) :
    serviceObservable ctx (IfObserver.ofLabel L₂) sid = true :=
  securityFlowsTo_trans _ _ _ h hFlow

/-- SM8.A.5: capability-target observability is monotone — every arm of
`capTargetObservable` reduces to an object-observability test. -/
theorem capTargetObservable_monotone (ctx : LabelingContext) {L₁ L₂ : SecurityLabel}
    (hFlow : securityFlowsTo L₁ L₂ = true) (target : CapTarget)
    (h : capTargetObservable ctx (IfObserver.ofLabel L₁) target = true) :
    capTargetObservable ctx (IfObserver.ofLabel L₂) target = true := by
  cases target with
  | object oid => exact objectObservable_monotone ctx hFlow oid h
  | cnodeSlot cnode _ => exact objectObservable_monotone ctx hFlow cnode h
  | replyCap rid => exact objectObservable_monotone ctx hFlow rid.toObjId h
  -- WS-SM SM9.A.9: an audit-trail capability names no object, so its
  -- observability is constant `true` and monotonicity is immediate.  The arm is
  -- listed rather than absorbed by a wildcard because the theorem's content is
  -- that *every* target arm reduces to an object-observability test or to a
  -- constant, and a wildcard would stop saying which.
  | auditTrail => exact h

/-- SM8.A.4: the SM7.D per-core instruction-cache view is invisible to every
per-core observer — the structural sibling of `perCoreTlb` above, and a timing
channel for the same reason (a resident line is evidence of a past fetch). -/
theorem onCore_perCoreICache (ctx : LabelingContext) (L : SecurityLabel)
    (s : SystemState) (c : CoreId)
    (v : Vector ICacheState SeLe4n.Kernel.Concurrency.numCores) :
    ObservableState.onCore ctx c L { s with perCoreICache := v }
      = ObservableState.onCore ctx c L s :=
  onCore_perCore_independence ctx L rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

/-- SM8.A.4: the SM7.D cache-maintenance emission ledger is invisible on every
core.  It is drained in the same atomic step that commits the transition, so it
never holds cross-core content across an observation point; the theorem states
the stronger fact that it is outside the read set regardless. -/
theorem onCore_pendingIcacheMaintenance (ctx : LabelingContext) (L : SecurityLabel)
    (s : SystemState) (c : CoreId)
    (v : List SeLe4n.Kernel.Architecture.ICacheInvalidation) :
    ObservableState.onCore ctx c L { s with pendingIcacheMaintenance := v }
      = ObservableState.onCore ctx c L s :=
  onCore_perCore_independence ctx L rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

/-- SM8.A.4: the SM7.A/B TLB-shootdown state (per-core pending queues +
acknowledgment vector + round generation) is invisible on every core. -/
theorem onCore_tlbShootdown (ctx : LabelingContext) (L : SecurityLabel)
    (s : SystemState) (c : CoreId)
    (v : SeLe4n.Kernel.Architecture.TlbShootdownState) :
    ObservableState.onCore ctx c L { s with tlbShootdown := v }
      = ObservableState.onCore ctx c L s :=
  onCore_perCore_independence ctx L rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

/-- SM8.C.8 / SM9.A: the mounted declassification audit trail is invisible on
every core.

The read-set half of `declassificationAuditLog_write_preserves_projection`,
lifted to the per-core observer.  Once SM9.A ships a reader this stops being
the whole story and becomes exactly half of it: the trail is outside
`ObservableState` — so an audited downgrade moves no per-core view — *and* it
is readable through a capability-gated, clearance-filtered syscall, which is
why SM9.A.4a states the reader's flow argument over
`auditObservationalEquivalence` rather than over `lowEquivalent`. -/
theorem onCore_declassificationAuditLog (ctx : LabelingContext) (L : SecurityLabel)
    (s : SystemState) (c : CoreId) (v : SeLe4n.Kernel.DeclassificationAuditLog) :
    ObservableState.onCore ctx c L { s with declassificationAuditLog := v }
      = ObservableState.onCore ctx c L s :=
  onCore_perCore_independence ctx L rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

/-- SM9.A.1a: the declassification audit **epoch** is invisible on every core.

Separate from the trail's own corollary because the argument is different: an
entry is content, and a cleared reader may see it; the epoch is a count of
entries the reader may *not* see.  Being outside the read set is what makes a
drain — the only writer that moves it — invisible to every per-core observer,
and it is why the epoch reaches only a caller holding the configured
audit-monitor clearance rather than every reader with an audit capability. -/
theorem onCore_declassificationAuditEpoch (ctx : LabelingContext) (L : SecurityLabel)
    (s : SystemState) (c : CoreId) (v : Nat) :
    ObservableState.onCore ctx c L { s with declassificationAuditEpoch := v }
      = ObservableState.onCore ctx c L s :=
  onCore_perCore_independence ctx L rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

/-- SM9.B.8: the mounted declassification **refusal ledger** is invisible on
every core.

The read-set half of `declassificationRefusals_write_preserves_projection`.
Both halves are needed and neither implies the other: being outside the
projection says the seam's refusal write moves no observer's view, and being
outside the per-core read set says the same on a core other than the one the
refused syscall executed on — which is the statement the cross-core
non-interference inventory consumes for a syscall that can be refused on any
core. -/
theorem onCore_declassificationRefusals (ctx : LabelingContext) (L : SecurityLabel)
    (s : SystemState) (c : CoreId) (v : SeLe4n.Kernel.RefusalLedger) :
    ObservableState.onCore ctx c L { s with declassificationRefusals := v }
      = ObservableState.onCore ctx c L s :=
  onCore_perCore_independence ctx L rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

/-- SM9.D.6: the mounted declassification **taint side table** is invisible on
every core.

The read-set half of `declassificationTaint_write_preserves_projection`.  Both
halves are needed and neither implies the other: being outside the projection
says the entry seam's propagation write moves no observer's view, and being
outside the per-core read set says the same on a core other than the one the
propagating syscall executed on — which is the statement the cross-core
non-interference inventory consumes for the content-moving arms, every one of
which can run on any core. -/
theorem onCore_declassificationTaint (ctx : LabelingContext) (L : SecurityLabel)
    (s : SystemState) (c : CoreId)
    (v : SeLe4n.Kernel.TaintTable) :
    ObservableState.onCore ctx c L { s with declassificationTaint := v }
      = ObservableState.onCore ctx c L s :=
  onCore_perCore_independence ctx L rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

/-- SM8.A.4: the pre-SMP scalar TLB view (the 9th `proofLayerInvariantBundle`
conjunct's subject) is invisible on every core, completing the sweep over the
memory-subsystem state the SM7 phases mounted. -/
theorem onCore_tlb (ctx : LabelingContext) (L : SecurityLabel)
    (s : SystemState) (c : CoreId) (v : TlbState) :
    ObservableState.onCore ctx c L { s with tlb := v }
      = ObservableState.onCore ctx c L s :=
  onCore_perCore_independence ctx L rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

/-- SM8.A.5: memory-address observability is monotone.  Vacuous when no
ownership model is configured (`memoryAddressObservable` is then constantly
`false`) or the address is unowned; otherwise the owning domain's label flows
transitively to the wider clearance. -/
theorem memoryAddressObservable_monotone (ctx : LabelingContext) {L₁ L₂ : SecurityLabel}
    (hFlow : securityFlowsTo L₁ L₂ = true) (pa : SeLe4n.PAddr)
    (h : memoryAddressObservable ctx (IfObserver.ofLabel L₁) pa = true) :
    memoryAddressObservable ctx (IfObserver.ofLabel L₂) pa = true := by
  -- `split at h` case-splits the ownership model and the region owner in both
  -- the hypothesis and the goal; the two absent cases contradict `h`, and the
  -- remaining case is transitivity of the flow relation at the region's label.
  unfold memoryAddressObservable at h ⊢
  split at h
  · simp at h
  · split at h
    · simp at h
    · exact securityFlowsTo_trans _ _ _ h hFlow

/-! ### Object-content refinement across clearances -/

/-- The observer-filtered CNode that `projectKernelObject` produces in its
`.cnode` arm, named so the slot-level lemmas below have a handle.

The `lock` erasure mirrors `projectKernelObject`'s (WS-SM SM8.B.4): an
`RwLockState` is a set of core identities, and carrying it into the projection
would re-open the placement channel SM5.B closed on `TCB.cpuAffinity`. -/
def projectCNode (ctx : LabelingContext) (observer : IfObserver) (cn : CNode) : CNode :=
  { cn with lock := SeLe4n.Kernel.Concurrency.RwLockState.unheld,
            slots := cn.slots.filter (fun _ cap => capTargetObservable ctx observer cap.target) }

/-- Definition-pinning: `projectKernelObject`'s `.cnode` arm **is**
`projectCNode`, so the slot lemmas below are statements about the live
projection rather than about a parallel copy of its filter. -/
theorem projectKernelObject_cnode (ctx : LabelingContext) (observer : IfObserver) (cn : CNode) :
    projectKernelObject ctx observer (.cnode cn) = .cnode (projectCNode ctx observer cn) := rfl

/-- SM8.A.5 (content refinement): a CNode slot visible to the narrower
clearance is visible, **with the same capability**, to the wider one.

This is the sense in which a higher-clearance observer sees "more" of an
object it can already see: `projectKernelObject` redacts CNode slots whose
target is not observable, and raising the clearance can only un-redact. -/
theorem projectCNode_lookup_monotone (ctx : LabelingContext) {L₁ L₂ : SecurityLabel}
    (hFlow : securityFlowsTo L₁ L₂ = true) (cn : CNode) (slot : SeLe4n.Slot) (cap : Capability)
    (h : (projectCNode ctx (IfObserver.ofLabel L₁) cn).lookup slot = some cap) :
    (projectCNode ctx (IfObserver.ofLabel L₂) cn).lookup slot = some cap := by
  have hInv : cn.slots.table.invExt := SeLe4n.Kernel.RobinHood.RHTable.invExtK_invExt cn.slots.hWF
  simp only [projectCNode, CNode.lookup, SeLe4n.UniqueSlotMap.get?,
    SeLe4n.UniqueSlotMap.table_filter] at h ⊢
  obtain ⟨hOrig, hPred⟩ :=
    (SeLe4n.Kernel.RobinHood.RHTable.filter_getElem?_iff _ _ _ _ hInv).mp h
  exact (SeLe4n.Kernel.RobinHood.RHTable.filter_getElem?_iff _ _ _ _ hInv).mpr
    ⟨hOrig, capTargetObservable_monotone ctx hFlow _ hPred⟩

/-- SM8.A.5: off the CNode arm, `projectKernelObject` does not read the
observer at all — the TCB / SchedContext / Reply erasures are structural and
every other object passes through unchanged.  So for a non-CNode object,
visibility is the *only* thing the clearance controls. -/
theorem projectKernelObject_observer_independent_off_cnode
    (ctx : LabelingContext) (o₁ o₂ : IfObserver) (obj : KernelObject)
    (hNotCNode : ∀ cn, obj ≠ .cnode cn) :
    projectKernelObject ctx o₁ obj = projectKernelObject ctx o₂ obj := by
  cases obj
  case cnode cn => exact absurd rfl (hNotCNode cn)
  all_goals rfl

/-! ### Object-content refinement

The `objects` component of `ObservableState.visibilityLe` is the only one whose
*content* may widen, so it needs a relation of its own rather than an `isSome`
implication.  Without one the order would let a wider clearance substitute an
unrelated object at an id it had already shown — the opposite of "sees at least
as much". -/

/-- SM8.A.5: the visibility order on a **projected CNode**.

`projectCNode` is `{ cn with slots := cn.slots.filter … }`, so raising the
clearance may re-admit redacted slots and may do nothing else.  This relation
says exactly that: the five non-slot fields are pinned, and every capability
the narrower observer can look up is still there — same slot, same capability
— for the wider one.  It may not be moved, altered, or dropped.

Named fields rather than a nested conjunction, so a consumer writes
`h.lookup` instead of a projection chain and `eq_of_cnodeVisibilityLe_of_slots_eq`
can state that the field list is exhaustive. -/
structure cnodeVisibilityLe (cn₁ cn₂ : CNode) : Prop where
  depth : cn₁.depth = cn₂.depth
  guardWidth : cn₁.guardWidth = cn₂.guardWidth
  guardValue : cn₁.guardValue = cn₂.guardValue
  radixWidth : cn₁.radixWidth = cn₂.radixWidth
  lock : cn₁.lock = cn₂.lock
  lookup : ∀ slot cap, cn₁.lookup slot = some cap → cn₂.lookup slot = some cap

theorem cnodeVisibilityLe_refl (cn : CNode) : cnodeVisibilityLe cn cn :=
  ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ h => h⟩

theorem cnodeVisibilityLe_trans {cn₁ cn₂ cn₃ : CNode}
    (h₁ : cnodeVisibilityLe cn₁ cn₂) (h₂ : cnodeVisibilityLe cn₂ cn₃) :
    cnodeVisibilityLe cn₁ cn₃ :=
  ⟨h₁.depth.trans h₂.depth, h₁.guardWidth.trans h₂.guardWidth,
   h₁.guardValue.trans h₂.guardValue, h₁.radixWidth.trans h₂.radixWidth,
   h₁.lock.trans h₂.lock, fun slot cap h => h₂.lookup slot cap (h₁.lookup slot cap h)⟩

/-- SM8.A.5: the field list of `cnodeVisibilityLe` is **exhaustive** — two
CNodes ordered by it whose slot maps agree are equal.  A sixth non-slot field
added to `CNode` makes this proof fail, which is how the relation learns it has
to grow. -/
theorem eq_of_cnodeVisibilityLe_of_slots_eq {cn₁ cn₂ : CNode}
    (h : cnodeVisibilityLe cn₁ cn₂) (hSlots : cn₁.slots = cn₂.slots) : cn₁ = cn₂ := by
  obtain ⟨d₁, gw₁, gv₁, rw₁, s₁, lk₁⟩ := cn₁
  obtain ⟨d₂, gw₂, gv₂, rw₂, s₂, lk₂⟩ := cn₂
  obtain ⟨hd, hgw, hgv, hrw, hlk, _⟩ := h
  simp_all

/-- SM8.A.5: the visibility order on a **projected kernel object**.

Off the CNode arm `projectKernelObject` does not read the observer at all
(`projectKernelObject_observer_independent_off_cnode`), so the only admissible
relation there is equality: a wider clearance may not substitute a different
endpoint, TCB, notification, VSpaceRoot, Untyped, SchedContext or Reply at an
id it already showed.  On the CNode arm it is `cnodeVisibilityLe` — slots may
be un-redacted, nothing else may move.  The arms are not interchangeable: a
CNode may not widen into a non-CNode, or the reverse. -/
def objectVisibilityLe (o₁ o₂ : KernelObject) : Prop :=
  match o₁ with
  | .cnode cn₁ =>
      match o₂ with
      | .cnode cn₂ => cnodeVisibilityLe cn₁ cn₂
      | _ => False
  | _ => o₁ = o₂

theorem objectVisibilityLe_refl (o : KernelObject) : objectVisibilityLe o o := by
  cases o <;> first | exact cnodeVisibilityLe_refl _ | rfl

theorem objectVisibilityLe_trans {o₁ o₂ o₃ : KernelObject}
    (h₁ : objectVisibilityLe o₁ o₂) (h₂ : objectVisibilityLe o₂ o₃) :
    objectVisibilityLe o₁ o₃ := by
  cases o₁
  case cnode cn₁ =>
    cases o₂
    case cnode cn₂ =>
      cases o₃
      case cnode cn₃ => exact cnodeVisibilityLe_trans h₁ h₂
      all_goals exact h₂.elim
    all_goals exact h₁.elim
  all_goals (cases h₁; exact h₂)

/-- SM8.A.5: off the CNode arm the object order **is** equality.  This is the
property a consumer needs in order to know that a visible endpoint or TCB
cannot be swapped for something else by a wider clearance — and, unlike
`onCore_objects_label_invariant_off_cnode`, it follows from a `visibilityLe`
hypothesis alone, with no access to the underlying state. -/
theorem eq_of_objectVisibilityLe_of_not_cnode {o₁ o₂ : KernelObject}
    (h : objectVisibilityLe o₁ o₂) (hNotCNode : ∀ cn, o₁ ≠ .cnode cn) : o₁ = o₂ := by
  cases o₁
  case cnode cn => exact absurd rfl (hNotCNode cn)
  all_goals exact h

/-- SM8.A.5: on the CNode arm, the wider side is a CNode too, related by
`cnodeVisibilityLe`. -/
theorem objectVisibilityLe_cnode {cn₁ : CNode} {o₂ : KernelObject}
    (h : objectVisibilityLe (.cnode cn₁) o₂) :
    ∃ cn₂, o₂ = .cnode cn₂ ∧ cnodeVisibilityLe cn₁ cn₂ := by
  cases o₂
  case cnode cn₂ => exact ⟨cn₂, rfl, h⟩
  all_goals exact h.elim

/-- SM8.A.5: `projectCNode` is monotone in the clearance **as a CNode** — not
merely slot by slot.  The shape is pinned because the projection rewrites only
`slots`. -/
theorem projectCNode_visibilityLe_monotone (ctx : LabelingContext) {L₁ L₂ : SecurityLabel}
    (hFlow : securityFlowsTo L₁ L₂ = true) (cn : CNode) :
    cnodeVisibilityLe (projectCNode ctx (IfObserver.ofLabel L₁) cn)
      (projectCNode ctx (IfObserver.ofLabel L₂) cn) :=
  ⟨rfl, rfl, rfl, rfl, rfl,
   fun slot cap h => projectCNode_lookup_monotone ctx hFlow cn slot cap h⟩

/-- SM8.A.5: the whole object projection is monotone in the clearance.  This is
the lemma the `objects` clause of `ObservableState.visibilityLe` is discharged
by, and it is what makes that clause a statement about content rather than
about mere presence. -/
theorem projectKernelObject_visibilityLe_monotone (ctx : LabelingContext)
    {L₁ L₂ : SecurityLabel} (hFlow : securityFlowsTo L₁ L₂ = true) (obj : KernelObject) :
    objectVisibilityLe (projectKernelObject ctx (IfObserver.ofLabel L₁) obj)
      (projectKernelObject ctx (IfObserver.ofLabel L₂) obj) := by
  cases obj
  case cnode cn =>
    simpa only [projectKernelObject_cnode] using projectCNode_visibilityLe_monotone ctx hFlow cn
  all_goals exact objectVisibilityLe_refl _

/-- A widening filter predicate yields a **sublist**, not merely a superset.

General `List` fact, kept local because SM8.A is its only consumer today; lift
it to `Prelude.lean` if a second one appears.  It is what lets the
`visibilityLe` list clauses below preserve *order* — the two projections filter
the *same* underlying list, so a wider clearance can only re-admit elements in
place, never reorder them.  Ordering is security-relevant here: a run queue's
order is its dispatch order. -/
theorem filter_sublist_filter_of_imp {α : Type} (l : List α) (p q : α → Bool)
    (h : ∀ a, p a = true → q a = true) : (l.filter p).Sublist (l.filter q) := by
  induction l with
  | nil => simp
  | cons a t ih =>
    cases hp : p a with
    | false =>
      cases hq : q a with
      | false => simpa [List.filter_cons, hp, hq] using ih
      | true => simpa [List.filter_cons, hp, hq] using ih.cons a
    | true =>
      have hq : q a = true := h a hp
      simpa [List.filter_cons, hp, hq] using ih.cons₂ a

/-- Mutual implication between two `Option`s at every value is equality.  Kept
private: it is the antisymmetry step for the six partial components of
`ObservableState.visibilityLe`, and nothing else needs it yet. -/
private theorem eq_of_option_imp {α : Type _} {x y : Option α}
    (h₁ : ∀ a, x = some a → y = some a) (h₂ : ∀ a, y = some a → x = some a) : x = y := by
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some a => exact h₂ a rfl
  | some a => exact (h₁ a rfl).symm

/-- The `Bool` companion of `eq_of_option_imp`, for the `services` component. -/
private theorem eq_of_bool_imp {a b : Bool}
    (h₁ : a = true → b = true) (h₂ : b = true → a = true) : a = b := by
  cases a <;> cases b <;> simp_all

/-! ### The per-core observable order -/

/-- SM8.A.5: `v₁` is observationally **below** `v₂` when everything visible in
`v₁` is visible in `v₂`, with the same value where the component carries one.

One field per `ObservableState` component, in declaration order, so the clause
list can be read off against the component list.  Every clause is as strong as
the truth allows:

* `objects` is the only component whose *content* may widen, and it widens only
  by CNode slot un-redaction: `objectVisibilityLe` pins equality on every other
  arm.  Stating it as an `isSome` implication — as this definition did before
  v0.33.4 — would have let a wider clearance replace a visible endpoint with an
  unrelated object.
* the two list components are compared by `List.Sublist`, not by membership:
  both are filters of the *same* underlying list, so a wider clearance re-admits
  elements in place and the order is preserved — and a run queue's order is its
  dispatch order, so a membership-only clause would discard security-relevant
  structure.
* the four scheduling components pass through **unfiltered** (accepted covert
  channel CC-1, restated by `onCore_schedulingTransparency`), so the truth about
  them is equality, not visibility.  Omitting them — as this definition did
  before v0.33.4 — left two states with different `activeDomain` dominating each
  other in both directions.
* every remaining partial component is compared by value.

`ObservableState.eq_of_visibilityLe_antisymm` is the completeness check on this
list: a fourteenth component with no clause here makes that proof fail. -/
structure ObservableState.visibilityLe (v₁ v₂ : ObservableState) : Prop where
  objects : ∀ oid obj₁, v₁.objects oid = some obj₁ →
    ∃ obj₂, v₂.objects oid = some obj₂ ∧ objectVisibilityLe obj₁ obj₂
  runnable : v₁.runnable.Sublist v₂.runnable
  current : ∀ t, v₁.current = some t → v₂.current = some t
  services : ∀ sid, v₁.services sid = true → v₂.services sid = true
  activeDomain : v₁.activeDomain = v₂.activeDomain
  irqHandlers : ∀ irq oid, v₁.irqHandlers irq = some oid → v₂.irqHandlers irq = some oid
  objectIndex : v₁.objectIndex.Sublist v₂.objectIndex
  domainTimeRemaining : v₁.domainTimeRemaining = v₂.domainTimeRemaining
  domainSchedule : v₁.domainSchedule = v₂.domainSchedule
  domainScheduleIndex : v₁.domainScheduleIndex = v₂.domainScheduleIndex
  machineRegs : ∀ rf, v₁.machineRegs = some rf → v₂.machineRegs = some rf
  memory : ∀ pa b, v₁.memory pa = some b → v₂.memory pa = some b
  serviceRegistry : ∀ sid e, v₁.serviceRegistry sid = some e → v₂.serviceRegistry sid = some e

theorem ObservableState.visibilityLe_refl (v : ObservableState) : v.visibilityLe v where
  objects := fun _ obj₁ h => ⟨obj₁, h, objectVisibilityLe_refl obj₁⟩
  runnable := List.Sublist.refl _
  current := fun _ h => h
  services := fun _ h => h
  activeDomain := rfl
  irqHandlers := fun _ _ h => h
  objectIndex := List.Sublist.refl _
  domainTimeRemaining := rfl
  domainSchedule := rfl
  domainScheduleIndex := rfl
  machineRegs := fun _ h => h
  memory := fun _ _ h => h
  serviceRegistry := fun _ _ h => h

theorem ObservableState.visibilityLe_trans {v₁ v₂ v₃ : ObservableState}
    (h₁ : v₁.visibilityLe v₂) (h₂ : v₂.visibilityLe v₃) : v₁.visibilityLe v₃ where
  objects := by
    intro oid obj₁ hGet
    obtain ⟨obj₂, hGet₂, hLe₂⟩ := h₁.objects oid obj₁ hGet
    obtain ⟨obj₃, hGet₃, hLe₃⟩ := h₂.objects oid obj₂ hGet₂
    exact ⟨obj₃, hGet₃, objectVisibilityLe_trans hLe₂ hLe₃⟩
  runnable := h₁.runnable.trans h₂.runnable
  current := fun t h => h₂.current t (h₁.current t h)
  services := fun sid h => h₂.services sid (h₁.services sid h)
  activeDomain := h₁.activeDomain.trans h₂.activeDomain
  irqHandlers := fun irq oid h => h₂.irqHandlers irq oid (h₁.irqHandlers irq oid h)
  objectIndex := h₁.objectIndex.trans h₂.objectIndex
  domainTimeRemaining := h₁.domainTimeRemaining.trans h₂.domainTimeRemaining
  domainSchedule := h₁.domainSchedule.trans h₂.domainSchedule
  domainScheduleIndex := h₁.domainScheduleIndex.trans h₂.domainScheduleIndex
  machineRegs := fun rf h => h₂.machineRegs rf (h₁.machineRegs rf h)
  memory := fun pa b h => h₂.memory pa b (h₁.memory pa b h)
  serviceRegistry := fun sid e h => h₂.serviceRegistry sid e (h₁.serviceRegistry sid e h)

/-- SM8.A.5: the membership consequence of the `runnable` sublist clause — the
form most consumers want, derived so the stronger clause costs nothing. -/
theorem ObservableState.visibilityLe_mem_runnable {v₁ v₂ : ObservableState}
    (h : v₁.visibilityLe v₂) {t : SeLe4n.ThreadId} (ht : t ∈ v₁.runnable) : t ∈ v₂.runnable :=
  h.runnable.subset ht

/-- SM8.A.5: the membership consequence of the `objectIndex` sublist clause. -/
theorem ObservableState.visibilityLe_mem_objectIndex {v₁ v₂ : ObservableState}
    (h : v₁.visibilityLe v₂) {oid : SeLe4n.ObjId} (ho : oid ∈ v₁.objectIndex) :
    oid ∈ v₂.objectIndex :=
  h.objectIndex.subset ho

/-- SM8.A.5: the presence consequence of the `objects` clause — the weakest
form, kept because it is the shape most consumers reach for first. -/
theorem ObservableState.visibilityLe_objects_isSome {v₁ v₂ : ObservableState}
    (h : v₁.visibilityLe v₂) {oid : SeLe4n.ObjId}
    (hSome : (v₁.objects oid).isSome = true) : (v₂.objects oid).isSome = true := by
  cases hGet : v₁.objects oid with
  | none => rw [hGet] at hSome; simp at hSome
  | some obj₁ =>
    obtain ⟨_, hGet₂, _⟩ := h.objects oid obj₁ hGet
    simp [hGet₂]

/-- SM8.A.5: from the order **alone**, a visible non-CNode object keeps its
value.  The state-level `onCore_objects_label_invariant_off_cnode` says the same
thing about the two projections of one state; this says it about any two states
in the order, which is what an SM8.B consumer holding only `visibilityLe` has. -/
theorem ObservableState.visibilityLe_objects_eq_of_not_cnode {v₁ v₂ : ObservableState}
    (h : v₁.visibilityLe v₂) {oid : SeLe4n.ObjId} {obj : KernelObject}
    (hGet : v₁.objects oid = some obj) (hNotCNode : ∀ cn, obj ≠ .cnode cn) :
    v₂.objects oid = some obj := by
  obtain ⟨obj₂, hGet₂, hLe⟩ := h.objects oid obj hGet
  rw [hGet₂, eq_of_objectVisibilityLe_of_not_cnode hLe hNotCNode]

/-- SM8.A.5: from the order **alone**, a visible CNode slot keeps its
capability.  The `visibilityLe`-hypothesis form of
`onCore_objects_cnode_slot_monotone`. -/
theorem ObservableState.visibilityLe_cnode_lookup {v₁ v₂ : ObservableState}
    (h : v₁.visibilityLe v₂) {oid : SeLe4n.ObjId} {cn₁ : CNode}
    {slot : SeLe4n.Slot} {cap : Capability}
    (hGet : v₁.objects oid = some (.cnode cn₁)) (hLookup : cn₁.lookup slot = some cap) :
    ∃ cn₂, v₂.objects oid = some (.cnode cn₂) ∧ cn₂.lookup slot = some cap := by
  obtain ⟨obj₂, hGet₂, hLe⟩ := h.objects oid _ hGet
  obtain ⟨cn₂, hEq, hCn⟩ := objectVisibilityLe_cnode hLe
  exact ⟨cn₂, hEq ▸ hGet₂, hCn.lookup slot cap hLookup⟩

/-- SM8.A.5 (**the completeness check on the clause list**): two states that
dominate each other and agree on `objects` are **equal**.

`objects` is a hypothesis rather than a conclusion because it is the one
component the order deliberately lets widen, and mutual domination on it yields
equal *lookups* rather than equal slot maps — a `UniqueSlotMap` is a hash table,
and two tables with the same contents may differ in probe order.

Every other component is a conclusion, and that is the point.  The proof
discharges one goal per `ObservableState` field, so a fourteenth component with
no clause in `visibilityLe` leaves a goal nothing can close — the same
compile-error discipline `ObservableState.ofFragments_eta` applies to the field
partition.  It is also the statement that fails for the pre-v0.33.4 definition:
the four scheduling components had no clause, so two states differing in
`activeDomain` dominated each other and this theorem was false. -/
theorem ObservableState.eq_of_visibilityLe_antisymm {v₁ v₂ : ObservableState}
    (h₁ : v₁.visibilityLe v₂) (h₂ : v₂.visibilityLe v₁)
    (hObjects : v₁.objects = v₂.objects) : v₁ = v₂ := by
  have hRunnable : v₁.runnable = v₂.runnable :=
    h₁.runnable.eq_of_length (Nat.le_antisymm h₁.runnable.length_le h₂.runnable.length_le)
  have hObjectIndex : v₁.objectIndex = v₂.objectIndex :=
    h₁.objectIndex.eq_of_length
      (Nat.le_antisymm h₁.objectIndex.length_le h₂.objectIndex.length_le)
  have hCurrent : v₁.current = v₂.current := eq_of_option_imp h₁.current h₂.current
  have hServices : v₁.services = v₂.services :=
    funext fun sid => eq_of_bool_imp (h₁.services sid) (h₂.services sid)
  have hIrq : v₁.irqHandlers = v₂.irqHandlers :=
    funext fun irq => eq_of_option_imp (h₁.irqHandlers irq) (h₂.irqHandlers irq)
  have hRegs : v₁.machineRegs = v₂.machineRegs := eq_of_option_imp h₁.machineRegs h₂.machineRegs
  have hMemory : v₁.memory = v₂.memory :=
    funext fun pa => eq_of_option_imp (h₁.memory pa) (h₂.memory pa)
  have hRegistry : v₁.serviceRegistry = v₂.serviceRegistry :=
    funext fun sid => eq_of_option_imp (h₁.serviceRegistry sid) (h₂.serviceRegistry sid)
  have hDomain := h₁.activeDomain
  have hRemaining := h₁.domainTimeRemaining
  have hSchedule := h₁.domainSchedule
  have hIndex := h₁.domainScheduleIndex
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _⟩ := v₁
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _⟩ := v₂
  simp only [ObservableState.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> assumption

/-- SM8.A.5 (headline): **the per-core observable state is monotone in the
observer's clearance.**  On any fixed core, an observer whose clearance
dominates another's sees at least as much.

Proved gate by gate from `securityFlowsTo_trans`; the core coordinate plays no
role, which is the label half of the §3 orthogonality (the core selects
scheduler slots, the label selects entities). -/
theorem onCore_label_monotone (ctx : LabelingContext) (c : CoreId) {L₁ L₂ : SecurityLabel}
    (hFlow : securityFlowsTo L₁ L₂ = true) (s : SystemState) :
    (ObservableState.onCore ctx c L₁ s).visibilityLe (ObservableState.onCore ctx c L₂ s) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- objects: visibility widens, and the projected *content* widens only by
    -- CNode slot un-redaction (`projectKernelObject_visibilityLe_monotone`)
    intro oid obj₁ hGet
    simp only [onCore_objects, projectObjects] at hGet ⊢
    by_cases hObs : objectObservable ctx (IfObserver.ofLabel L₁) oid = true
    · rw [if_pos hObs] at hGet
      cases hLook : s.objects[oid]? with
      | none => rw [hLook] at hGet; simp at hGet
      | some obj =>
        rw [hLook] at hGet
        simp only [Option.map_some, Option.some.injEq] at hGet
        subst hGet
        refine ⟨projectKernelObject ctx (IfObserver.ofLabel L₂) obj, ?_,
          projectKernelObject_visibilityLe_monotone ctx hFlow obj⟩
        -- `cases hLook :` already substituted `some obj` into the goal
        rw [if_pos (objectObservable_monotone ctx hFlow oid hObs), Option.map_some]
    · rw [if_neg hObs] at hGet; simp at hGet
  · -- runnable: the SAME core-c run queue under a widening filter, so the
    -- wider view is a sublist — order preserved, not merely a superset
    simp only [onCore_runnable, projectRunnableOnCore]
    exact filter_sublist_filter_of_imp _ _ _ (fun t ht => threadObservable_monotone ctx hFlow t ht)
  · -- current
    intro t ht
    simp only [onCore_current, projectCurrentOnCore] at ht ⊢
    cases hCur : s.scheduler.currentOnCore c with
    | none => rw [hCur] at ht; simp at ht
    | some tid =>
      rw [hCur] at ht
      by_cases hObs : threadObservable ctx (IfObserver.ofLabel L₁) tid = true
      · have hEq : tid = t := by simpa [hObs] using ht
        subst hEq
        simp [threadObservable_monotone ctx hFlow _ hObs]
      · simp [hObs] at ht
  · -- services
    intro sid hs
    simp only [onCore_services, projectServicePresence] at hs ⊢
    by_cases hObs : serviceObservable ctx (IfObserver.ofLabel L₁) sid = true
    · simpa [serviceObservable_monotone ctx hFlow sid hObs, hObs] using hs
    · simp [hObs] at hs
  · -- activeDomain: unfiltered (CC-1), so equal rather than merely visible
    rfl
  · -- irqHandlers
    intro irq oid hIrq
    simp only [onCore_irqHandlers, projectIrqHandlers] at hIrq ⊢
    cases hLook : s.irqHandlers[irq]? with
    | none => rw [hLook] at hIrq; simp at hIrq
    | some oid' =>
      rw [hLook] at hIrq
      by_cases hObs : objectObservable ctx (IfObserver.ofLabel L₁) oid' = true
      · have hEq : oid' = oid := by simpa [hObs] using hIrq
        subst hEq
        simp [objectObservable_monotone ctx hFlow _ hObs]
      · simp [hObs] at hIrq
  · -- objectIndex: likewise a sublist of the same underlying index
    simp only [onCore_objectIndex, projectObjectIndex]
    exact filter_sublist_filter_of_imp _ _ _
      (fun oid hoid => objectObservable_monotone ctx hFlow oid hoid)
  · -- domainTimeRemaining: unfiltered (CC-1)
    rfl
  · -- domainSchedule: unfiltered (CC-1)
    rfl
  · -- domainScheduleIndex: unfiltered (CC-1)
    rfl
  · -- machineRegs: exact — both clearances return core `c`'s own bank
    intro rf hr
    simp only [onCore_machineRegs, projectMachineRegsOnCore] at hr ⊢
    cases hCur : s.scheduler.currentOnCore c with
    | none => rw [hCur] at hr; simp at hr
    | some tid =>
      rw [hCur] at hr
      by_cases hObs : threadObservable ctx (IfObserver.ofLabel L₁) tid = true
      · simpa [threadObservable_monotone ctx hFlow _ hObs, hObs] using hr
      · simp [hObs] at hr
  · -- memory
    intro pa b hm
    simp only [onCore_memory, projectMemory] at hm ⊢
    by_cases hObs : memoryAddressObservable ctx (IfObserver.ofLabel L₁) pa = true
    · simpa [memoryAddressObservable_monotone ctx hFlow pa hObs, hObs] using hm
    · simp [hObs] at hm
  · -- serviceRegistry: exact, not merely visible — both clearances return the
    -- same `lookupService` result once the service is observable at all
    intro sid e hs
    simp only [onCore_serviceRegistry, projectServiceRegistry] at hs ⊢
    by_cases hObs : serviceObservable ctx (IfObserver.ofLabel L₁) sid = true
    · simpa [serviceObservable_monotone ctx hFlow sid hObs, hObs] using hs
    · simp [hObs] at hs

/-- SM8.A.5 (the `objects` component, exactly): off the CNode arm, an object
visible at the narrower clearance projects to the **same value** at the wider
one.  Together with `projectCNode_lookup_monotone` (the CNode arm, where the
projection genuinely widens) this bounds the one component of
`ObservableState.visibilityLe` that is stated by visibility rather than by
value: the widening is confined to CNode slot redaction. -/
theorem onCore_objects_label_invariant_off_cnode (ctx : LabelingContext) (c : CoreId)
    {L₁ L₂ : SecurityLabel} (hFlow : securityFlowsTo L₁ L₂ = true) (s : SystemState)
    (oid : SeLe4n.ObjId) (obj : KernelObject)
    (hGet : s.objects[oid]? = some obj)
    (hNotCNode : ∀ cn, obj ≠ .cnode cn)
    (hVisible : ((ObservableState.onCore ctx c L₁ s).objects oid).isSome = true) :
    (ObservableState.onCore ctx c L₂ s).objects oid
      = (ObservableState.onCore ctx c L₁ s).objects oid := by
  have hSome := hVisible
  simp only [onCore_objects, projectObjects] at hSome ⊢
  by_cases hObs : objectObservable ctx (IfObserver.ofLabel L₁) oid = true
  · rw [objectObservable_monotone ctx hFlow oid hObs]
    simp only [hObs, if_pos, hGet, Option.map_some]
    rw [projectKernelObject_observer_independent_off_cnode ctx (IfObserver.ofLabel L₂)
      (IfObserver.ofLabel L₁) obj hNotCNode]
  · simp [hObs] at hSome

/-- SM8.A.5: the SMP form of the visibility order — the wider clearance
dominates on **every** core.  Mirrors the SM4.D `lowEquivalent_smp` idiom, so
SM8.B can quantify over observers uniformly. -/
def visibilityLe_smp (ctx : LabelingContext) (L₁ L₂ : SecurityLabel) (s : SystemState) : Prop :=
  ∀ c : CoreId, (ObservableState.onCore ctx c L₁ s).visibilityLe
    (ObservableState.onCore ctx c L₂ s)

theorem visibilityLe_smp_at (ctx : LabelingContext) (L₁ L₂ : SecurityLabel) (s : SystemState)
    (c : CoreId) (h : visibilityLe_smp ctx L₁ L₂ s) :
    (ObservableState.onCore ctx c L₁ s).visibilityLe (ObservableState.onCore ctx c L₂ s) := h c

/-- SM8.A.5 (SMP headline): clearance monotonicity holds on every core at once. -/
theorem onCore_label_monotone_smp (ctx : LabelingContext) {L₁ L₂ : SecurityLabel}
    (hFlow : securityFlowsTo L₁ L₂ = true) (s : SystemState) :
    visibilityLe_smp ctx L₁ L₂ s :=
  fun c => onCore_label_monotone ctx c hFlow s

/-- SM8.A.5 (observer form): monotonicity for two observers on the same core
whose clearances are ordered. -/
theorem observerView_label_monotone (ctx : LabelingContext) {o₁ o₂ : PerCoreObserver}
    (hCore : o₁.core = o₂.core) (hFlow : securityFlowsTo o₁.clearance o₂.clearance = true)
    (s : SystemState) :
    (o₁.view ctx s).visibilityLe (o₂.view ctx s) := by
  obtain ⟨c₁, l₁⟩ := o₁
  obtain ⟨c₂, l₂⟩ := o₂
  cases hCore
  exact onCore_label_monotone ctx c₁ hFlow s

/-- SM8.A.5: the per-core observable object at an **observable CNode** is the
observer-filtered CNode.  The bridge that carries `projectCNode_lookup_monotone`
up to the layer SM8.A is about. -/
theorem onCore_objects_cnode (ctx : LabelingContext) (c : CoreId) (L : SecurityLabel)
    (s : SystemState) (oid : SeLe4n.ObjId) (cn : CNode)
    (hGet : s.objects[oid]? = some (.cnode cn))
    (hObs : objectObservable ctx (IfObserver.ofLabel L) oid = true) :
    (ObservableState.onCore ctx c L s).objects oid
      = some (.cnode (projectCNode ctx (IfObserver.ofLabel L) cn)) := by
  simp only [onCore_objects, projectObjects, hObs, if_true, hGet, Option.map_some,
    projectKernelObject_cnode]

/-- SM8.A.5 (object-content refinement, at the observable-state layer): a CNode
slot the narrower observer can see is still there, **with the same capability**,
for the wider one.

This is the `objects` clause of `ObservableState.visibilityLe` sharpened from
"the object stays visible" to "the object's visible content only grows", which
is the precise sense in which a higher clearance sees more of an object it can
already see. -/
theorem onCore_objects_cnode_slot_monotone (ctx : LabelingContext) (c : CoreId)
    {L₁ L₂ : SecurityLabel} (hFlow : securityFlowsTo L₁ L₂ = true) (s : SystemState)
    (oid : SeLe4n.ObjId) (cn : CNode) (slot : SeLe4n.Slot) (cap : Capability)
    (hGet : s.objects[oid]? = some (.cnode cn))
    (hObs : objectObservable ctx (IfObserver.ofLabel L₁) oid = true)
    (hSlot : ∀ cn₁, (ObservableState.onCore ctx c L₁ s).objects oid = some (.cnode cn₁) →
      cn₁.lookup slot = some cap) :
    ∃ cn₂, (ObservableState.onCore ctx c L₂ s).objects oid = some (.cnode cn₂) ∧
      cn₂.lookup slot = some cap := by
  refine ⟨projectCNode ctx (IfObserver.ofLabel L₂) cn,
    onCore_objects_cnode ctx c L₂ s oid cn hGet (objectObservable_monotone ctx hFlow oid hObs),
    ?_⟩
  exact projectCNode_lookup_monotone ctx hFlow cn slot cap
    (hSlot _ (onCore_objects_cnode ctx c L₁ s oid cn hGet hObs))

/-- SM8.A.5 (the non-monotone components): the four scheduling components pass
through **unfiltered** — the observer reads core `c`'s raw scheduler state, with
no label gate anywhere in the path.

Stated against the state rather than as an equality between two clearances
(which would be true of any constant function): this says *what* the observer
gets, so it is evidence about the channel's content and not merely that some
filter is label-blind.  The two-clearance form is the corollary below.

This is the per-core restatement of the accepted covert channel CC-1
(`acceptedCovertChannel_scheduling`, mirroring the single-core
`schedulingCovertChannel_bounded_width` — which, despite its name, proves
transparency rather than a capacity bound): under SMP each core carries its own
`activeDomain` / `domainTimeRemaining` / `domainScheduleIndex`, so the channel
exists **once per core**, while the system-wide `domainSchedule` is shared. -/
theorem onCore_schedulingTransparency (ctx : LabelingContext) (c : CoreId)
    (L : SecurityLabel) (s : SystemState) :
    (ObservableState.onCore ctx c L s).activeDomain = s.scheduler.activeDomainOnCore c ∧
      (ObservableState.onCore ctx c L s).domainTimeRemaining =
        s.scheduler.domainTimeRemainingOnCore c ∧
      (ObservableState.onCore ctx c L s).domainSchedule = s.scheduler.domainSchedule ∧
      (ObservableState.onCore ctx c L s).domainScheduleIndex =
        s.scheduler.domainScheduleIndexOnCore c :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- SM8.A.5: the label-invariance that follows — an immediate corollary of the
unfiltered reads above, and the form a two-observer argument uses. -/
theorem onCore_schedulingTransparency_label_invariant (ctx : LabelingContext) (c : CoreId)
    (L₁ L₂ : SecurityLabel) (s : SystemState) :
    (ObservableState.onCore ctx c L₁ s).activeDomain =
        (ObservableState.onCore ctx c L₂ s).activeDomain ∧
      (ObservableState.onCore ctx c L₁ s).domainTimeRemaining =
        (ObservableState.onCore ctx c L₂ s).domainTimeRemaining ∧
      (ObservableState.onCore ctx c L₁ s).domainSchedule =
        (ObservableState.onCore ctx c L₂ s).domainSchedule ∧
      (ObservableState.onCore ctx c L₁ s).domainScheduleIndex =
        (ObservableState.onCore ctx c L₂ s).domainScheduleIndex := by
  obtain ⟨a₁, b₁, c₁, d₁⟩ := onCore_schedulingTransparency ctx c L₁ s
  obtain ⟨a₂, b₂, c₂, d₂⟩ := onCore_schedulingTransparency ctx c L₂ s
  exact ⟨a₁.trans a₂.symm, b₁.trans b₂.symm, c₁.trans c₂.symm, d₁.trans d₂.symm⟩

/-- SM8.A.5 (non-vacuity): monotonicity is **strict** under a non-trivial
labeling.  Under `testLabelingContext`, object 0 carries `kernelTrusted`; a
`publicLabel` observer cannot see it and a `kernelTrusted` observer can, while
`publicLabel` does flow to `kernelTrusted`.  So `visibilityLe` is a genuine
order, not an equality in disguise — and, dually, `defaultLabelingContext`
would make every such witness vacuous (`defaultLabelingContext_insecure`). -/
theorem onCore_label_monotone_strict :
    securityFlowsTo SecurityLabel.publicLabel SecurityLabel.kernelTrusted = true ∧
      objectObservable testLabelingContext
        (IfObserver.ofLabel SecurityLabel.publicLabel) (SeLe4n.ObjId.ofNat 0) = false ∧
      objectObservable testLabelingContext
        (IfObserver.ofLabel SecurityLabel.kernelTrusted) (SeLe4n.ObjId.ofNat 0) = true := by
  decide

end SeLe4n.Kernel
