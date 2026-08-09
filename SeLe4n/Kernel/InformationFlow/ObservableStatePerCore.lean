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
  from every core and six that are restricted to core `c`.
  `ObservableState.ext_fragments` makes the partition **total**: a
  fourteenth `ObservableState` field that is registered in neither
  fragment fails to compile, so the plan §7 "per-core projection missing a
  field" risk is a build error rather than a silent gap.
* **The decidable fragment** (§4).  Observable-state equality is *not*
  decidable — five components are functions over unbounded domains and the
  sixth (`machineRegs`) contains `RegisterFile.gpr`, whose structural `BEq`
  is provably not lawful (`RegisterFile.not_lawfulBEq`).  §4 carves out the
  fragment that *is* decidable, proves it a sound refuter, and proves it a
  **strict** fragment so no caller can mistake it for full equality.
* **Per-core independence** (§5).  The read set of the per-core observable
  state is characterised exactly: the seven shared state components plus
  core `c`'s five scheduler slots and core `c`'s register bank — and
  *nothing else*, in particular no other core's slots.  Note this does not
  follow from `projectStateOnCore_congr`, whose `hBase` hypothesis is
  equality of the whole global projection and therefore drags the **boot**
  core's slots in; SM8.B needs the boot-core-free form.
* **Label monotonicity** (§6).  Raising the observer's clearance can only
  widen what it sees.  The scheduling components are label-*invariant*
  (the accepted CC-1 channel, restated per core).

## Relationship to the live surface

Every definition here is a conservative re-presentation of
`projectStateOnCore`, so `ObservableState.onCore ctx bootCoreId L s` is
*definitionally* the live single-core `projectState ctx ⟨L⟩ s` and the
existing non-interference surface is untouched.

Axiom-clean: every theorem depends only on the standard foundational
axioms (`propext` / `Quot.sound` / `Classical.choice`).
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

/-- SM8.A.2 (headline): **the per-core observable state is a projection of the
global projection.**

Two states that the global observer at `L` cannot tell apart, and whose core
`c` scheduler slots and register bank agree, are indistinguishable to the
per-core observer `(c, L)`.  Equivalently: `ObservableState.onCore` factors as

    (global projection at L, core c's six slots) ↦ per-core view

so the per-core observer learns exactly the global projection plus core `c`'s
scheduler state — no more.

Contrast `onCore_perCore_independence` (§5), which replaces the
global-projection hypothesis by the *state-level* reads it depends on and is
therefore free of any reference to the boot core. -/
theorem onCore_isProjection_of_globalProjection
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
`.cnode` arm, named so the slot-level lemmas below have a handle. -/
def projectCNode (ctx : LabelingContext) (observer : IfObserver) (cn : CNode) : CNode :=
  { cn with slots := cn.slots.filter (fun _ cap => capTargetObservable ctx observer cap.target) }

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

/-! ### The per-core observable order -/

/-- SM8.A.5: `v₁` is observationally **below** `v₂` when everything visible in
`v₁` is visible in `v₂`, with the same value where the component carries one.

Every component that *can* be compared by value is: only `objects` is compared
by `isSome`, because a wider clearance may legitimately reveal more of a
visible CNode (see `projectCNode_lookup_monotone` for the refinement, and
`onCore_objects_label_invariant_off_cnode` for the arms where equality does
hold).  Weakening any other clause to `isSome` would understate what is
actually proved. -/
def ObservableState.visibilityLe (v₁ v₂ : ObservableState) : Prop :=
  (∀ oid, (v₁.objects oid).isSome = true → (v₂.objects oid).isSome = true) ∧
  (∀ t, t ∈ v₁.runnable → t ∈ v₂.runnable) ∧
  (∀ t, v₁.current = some t → v₂.current = some t) ∧
  (∀ sid, v₁.services sid = true → v₂.services sid = true) ∧
  (∀ irq oid, v₁.irqHandlers irq = some oid → v₂.irqHandlers irq = some oid) ∧
  (∀ oid, oid ∈ v₁.objectIndex → oid ∈ v₂.objectIndex) ∧
  (∀ pa b, v₁.memory pa = some b → v₂.memory pa = some b) ∧
  (∀ sid e, v₁.serviceRegistry sid = some e → v₂.serviceRegistry sid = some e) ∧
  (∀ rf, v₁.machineRegs = some rf → v₂.machineRegs = some rf)

theorem ObservableState.visibilityLe_refl (v : ObservableState) : v.visibilityLe v :=
  ⟨fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h, fun _ _ h => h,
   fun _ h => h, fun _ _ h => h, fun _ _ h => h, fun _ h => h⟩

theorem ObservableState.visibilityLe_trans {v₁ v₂ v₃ : ObservableState}
    (h₁ : v₁.visibilityLe v₂) (h₂ : v₂.visibilityLe v₃) : v₁.visibilityLe v₃ :=
  ⟨fun oid h => h₂.1 oid (h₁.1 oid h),
   fun t h => h₂.2.1 t (h₁.2.1 t h),
   fun t h => h₂.2.2.1 t (h₁.2.2.1 t h),
   fun sid h => h₂.2.2.2.1 sid (h₁.2.2.2.1 sid h),
   fun irq oid h => h₂.2.2.2.2.1 irq oid (h₁.2.2.2.2.1 irq oid h),
   fun oid h => h₂.2.2.2.2.2.1 oid (h₁.2.2.2.2.2.1 oid h),
   fun pa b h => h₂.2.2.2.2.2.2.1 pa b (h₁.2.2.2.2.2.2.1 pa b h),
   fun sid e h => h₂.2.2.2.2.2.2.2.1 sid e (h₁.2.2.2.2.2.2.2.1 sid e h),
   fun rf h => h₂.2.2.2.2.2.2.2.2 rf (h₁.2.2.2.2.2.2.2.2 rf h)⟩

/-- SM8.A.5 (headline): **the per-core observable state is monotone in the
observer's clearance.**  On any fixed core, an observer whose clearance
dominates another's sees at least as much.

Proved gate by gate from `securityFlowsTo_trans`; the core coordinate plays no
role, which is the label half of the §3 orthogonality (the core selects
scheduler slots, the label selects entities). -/
theorem onCore_label_monotone (ctx : LabelingContext) (c : CoreId) {L₁ L₂ : SecurityLabel}
    (hFlow : securityFlowsTo L₁ L₂ = true) (s : SystemState) :
    (ObservableState.onCore ctx c L₁ s).visibilityLe (ObservableState.onCore ctx c L₂ s) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- objects: visibility widens; the projected content may widen too (CNodes)
    intro oid hSome
    simp only [onCore_objects, projectObjects] at hSome ⊢
    by_cases hObs : objectObservable ctx (IfObserver.ofLabel L₁) oid = true
    · simpa [objectObservable_monotone ctx hFlow oid hObs, hObs] using hSome
    · simp [hObs] at hSome
  · -- runnable: same core-c run queue, wider filter predicate
    intro t ht
    simp only [onCore_runnable, projectRunnableOnCore, List.mem_filter] at ht ⊢
    exact ⟨ht.1, threadObservable_monotone ctx hFlow t ht.2⟩
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
  · -- objectIndex
    intro oid hoid
    simp only [onCore_objectIndex, projectObjectIndex, List.mem_filter] at hoid ⊢
    exact ⟨hoid.1, objectObservable_monotone ctx hFlow oid hoid.2⟩
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

/-- SM8.A.5 (the non-monotone components): the four scheduling components are
label-**invariant**, not merely monotone — they are visible to every observer
under scheduling transparency.

This is the per-core restatement of the accepted covert channel CC-1
(`acceptedCovertChannel_scheduling`): under SMP each core carries its own
`activeDomain` / `domainTimeRemaining` / `domainScheduleIndex`, so the channel
exists once per core, and the system-wide `domainSchedule` is shared. -/
theorem onCore_schedulingTransparency (ctx : LabelingContext) (c : CoreId)
    (L₁ L₂ : SecurityLabel) (s : SystemState) :
    (ObservableState.onCore ctx c L₁ s).activeDomain =
        (ObservableState.onCore ctx c L₂ s).activeDomain ∧
      (ObservableState.onCore ctx c L₁ s).domainTimeRemaining =
        (ObservableState.onCore ctx c L₂ s).domainTimeRemaining ∧
      (ObservableState.onCore ctx c L₁ s).domainSchedule =
        (ObservableState.onCore ctx c L₂ s).domainSchedule ∧
      (ObservableState.onCore ctx c L₁ s).domainScheduleIndex =
        (ObservableState.onCore ctx c L₂ s).domainScheduleIndex :=
  ⟨rfl, rfl, rfl, rfl⟩

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
