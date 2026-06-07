-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.InformationFlow.Projection

/-!
# WS-SM SM4.D — Per-core information-flow projections

This module is the InformationFlow slice of the SM4.D cross-subsystem
migration (plan `docs/planning/SMP_PER_CORE_STATE_PLAN.md` §5.4,
sub-tasks SM4.D.12 / SM4.D.13 / SM4.D.14).  It lifts the six
scheduler-reading IF-M1 projection functions defined in
`InformationFlow/Projection.lean` from the single-core forms (pinned to
`bootCoreId` after SM4.B) to per-core forms parameterised by an explicit
`(c : CoreId)`, plus the aggregate `projectStateOnCore`.

The non-scheduler projections (`projectObjects`, `projectServicePresence`,
`projectIrqHandlers`, `projectObjectIndex`, `projectDomainSchedule`,
`projectMemory`, `projectServiceRegistry`) read no per-core scheduler
field, so they are unchanged; only the six scheduler-reading projections
(`projectRunnable`, `projectCurrent`, `projectActiveDomain`,
`projectDomainTimeRemaining`, `projectDomainScheduleIndex`,
`projectMachineRegs`) gain `…OnCore` forms.

The migration is additive and soundness-preserving: each `…OnCore` form
at `bootCoreId` is *definitionally* its single-core counterpart (because
`SchedulerState.runnable` is the `abbrev`
`(runQueueOnCore bootCoreId).toList`), so the boot-core bridges close by
`rfl` and the live non-interference surface (built on `projectState`) is
untouched.  The frame lemmas are the substantive SM5 content: a write to
core `c'`'s scheduler slot leaves core `c`'s projection unchanged for
`c ≠ c'`, which is exactly the per-core observability locality the SMP
non-interference proofs require.

The InformationFlow Invariant files (`Invariant/Composition.lean`,
`Invariant/Helpers.lean`, `Invariant/Operations.lean`, SM4.D.14) define no
predicate that reads a scheduler accessor *directly* — they consume the
projections — so no per-core predicate migration is needed there; their
SMP lift is the per-core projection frame lemmas below.

Axiom-clean: every theorem depends only on the standard foundational
axioms (`propext` / `Quot.sound` / `Classical.choice`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId bootCoreId)

-- ============================================================================
-- §1  Per-core projection forms (plan §3.4 migration pattern)
-- ============================================================================

/-- SM4.D: per-core form of `projectRunnable` — core `c`'s observable
runnable threads. -/
def projectRunnableOnCore (ctx : LabelingContext) (observer : IfObserver)
    (st : SystemState) (c : CoreId) : List SeLe4n.ThreadId :=
  (st.scheduler.runQueueOnCore c).toList.filter (threadObservable ctx observer)

/-- SM4.D: per-core form of `projectCurrent` — core `c`'s observable
current thread. -/
def projectCurrentOnCore (ctx : LabelingContext) (observer : IfObserver)
    (st : SystemState) (c : CoreId) : Option SeLe4n.ThreadId :=
  match (st.scheduler.currentOnCore c) with
  | some tid => if threadObservable ctx observer tid then some tid else none
  | none => none

/-- SM4.D: per-core form of `projectActiveDomain` — core `c`'s active
scheduling domain (always visible; scheduling transparency). -/
def projectActiveDomainOnCore (_ctx : LabelingContext) (_observer : IfObserver)
    (st : SystemState) (c : CoreId) : SeLe4n.DomainId :=
  (st.scheduler.activeDomainOnCore c)

/-- SM4.D: per-core form of `projectDomainTimeRemaining`. -/
def projectDomainTimeRemainingOnCore (_ctx : LabelingContext) (_observer : IfObserver)
    (st : SystemState) (c : CoreId) : Nat :=
  (st.scheduler.domainTimeRemainingOnCore c)

/-- SM4.D: per-core form of `projectDomainScheduleIndex`. -/
def projectDomainScheduleIndexOnCore (_ctx : LabelingContext) (_observer : IfObserver)
    (st : SystemState) (c : CoreId) : Nat :=
  (st.scheduler.domainScheduleIndexOnCore c)

/-- SM4.D: per-core form of `projectMachineRegs` — core `c`'s machine
register file, visible only when core `c`'s current thread is observable.
WS-SM SM5.I (per-core banks, now live): reads core `c`'s **own** register bank
(`regsOnCore c`), so for a non-boot core the projection exposes that core's
registers rather than the boot core's — the SMP-correct information-flow
observation. -/
def projectMachineRegsOnCore (ctx : LabelingContext) (observer : IfObserver)
    (st : SystemState) (c : CoreId) : Option RegisterFile :=
  match (st.scheduler.currentOnCore c) with
  | some tid => if threadObservable ctx observer tid then some (st.machine.regsOnCore c) else none
  | none => none

/-- SM4.D: per-core form of `projectState` — the IF-M1 observable state
projected at core `c`.  Only the six scheduler-reading components are
per-core; every other component is shared (read off `projectState`). -/
def projectStateOnCore (ctx : LabelingContext) (observer : IfObserver)
    (st : SystemState) (c : CoreId) : ObservableState :=
  { projectState ctx observer st with
    runnable := projectRunnableOnCore ctx observer st c
    current := projectCurrentOnCore ctx observer st c
    activeDomain := projectActiveDomainOnCore ctx observer st c
    domainTimeRemaining := projectDomainTimeRemainingOnCore ctx observer st c
    domainScheduleIndex := projectDomainScheduleIndexOnCore ctx observer st c
    machineRegs := projectMachineRegsOnCore ctx observer st c }

-- ============================================================================
-- §2  Boot-core bridges (the non-orphan connection to the live surface)
-- ============================================================================

theorem projectRunnableOnCore_bootCore (ctx : LabelingContext) (observer : IfObserver)
    (st : SystemState) :
    projectRunnableOnCore ctx observer st bootCoreId = projectRunnable ctx observer st := rfl

theorem projectCurrentOnCore_bootCore (ctx : LabelingContext) (observer : IfObserver)
    (st : SystemState) :
    projectCurrentOnCore ctx observer st bootCoreId = projectCurrent ctx observer st := rfl

theorem projectActiveDomainOnCore_bootCore (ctx : LabelingContext) (observer : IfObserver)
    (st : SystemState) :
    projectActiveDomainOnCore ctx observer st bootCoreId = projectActiveDomain ctx observer st :=
  rfl

theorem projectDomainTimeRemainingOnCore_bootCore (ctx : LabelingContext)
    (observer : IfObserver) (st : SystemState) :
    projectDomainTimeRemainingOnCore ctx observer st bootCoreId =
      projectDomainTimeRemaining ctx observer st := rfl

theorem projectDomainScheduleIndexOnCore_bootCore (ctx : LabelingContext)
    (observer : IfObserver) (st : SystemState) :
    projectDomainScheduleIndexOnCore ctx observer st bootCoreId =
      projectDomainScheduleIndex ctx observer st := rfl

theorem projectMachineRegsOnCore_bootCore (ctx : LabelingContext) (observer : IfObserver)
    (st : SystemState) :
    projectMachineRegsOnCore ctx observer st bootCoreId = projectMachineRegs ctx observer st :=
  rfl

theorem projectStateOnCore_bootCore (ctx : LabelingContext) (observer : IfObserver)
    (st : SystemState) :
    projectStateOnCore ctx observer st bootCoreId = projectState ctx observer st := rfl

-- ============================================================================
-- §3  Frame lemmas (per-core observability locality — the SM5 NI content)
-- ============================================================================
--
-- Each per-core projection at core `c` reads only core `c`'s relevant
-- scheduler slot (`projectMachineRegsOnCore` additionally reads core `c`'s
-- own register bank `regsOnCore c`).  Hence a write to a *different* core's
-- scheduler slot (or a different core's register bank)
-- leaves core `c`'s projection unchanged — the per-core observability
-- locality the SMP non-interference proofs require.  SM5 discharges the
-- per-slot equality hypotheses from the SM4.B `set…OnCore_…OnCore_ne`
-- cross-core independence algebra.

theorem projectRunnableOnCore_frame (ctx : LabelingContext) (observer : IfObserver)
    {st st' : SystemState} {c : CoreId}
    (hRQ : st'.scheduler.runQueueOnCore c = st.scheduler.runQueueOnCore c) :
    projectRunnableOnCore ctx observer st' c = projectRunnableOnCore ctx observer st c := by
  unfold projectRunnableOnCore; rw [hRQ]

theorem projectCurrentOnCore_frame (ctx : LabelingContext) (observer : IfObserver)
    {st st' : SystemState} {c : CoreId}
    (hCur : st'.scheduler.currentOnCore c = st.scheduler.currentOnCore c) :
    projectCurrentOnCore ctx observer st' c = projectCurrentOnCore ctx observer st c := by
  unfold projectCurrentOnCore; rw [hCur]

theorem projectActiveDomainOnCore_frame (ctx : LabelingContext) (observer : IfObserver)
    {st st' : SystemState} {c : CoreId}
    (hAD : st'.scheduler.activeDomainOnCore c = st.scheduler.activeDomainOnCore c) :
    projectActiveDomainOnCore ctx observer st' c = projectActiveDomainOnCore ctx observer st c := by
  unfold projectActiveDomainOnCore; rw [hAD]

theorem projectDomainTimeRemainingOnCore_frame (ctx : LabelingContext) (observer : IfObserver)
    {st st' : SystemState} {c : CoreId}
    (hDTR : st'.scheduler.domainTimeRemainingOnCore c = st.scheduler.domainTimeRemainingOnCore c) :
    projectDomainTimeRemainingOnCore ctx observer st' c =
      projectDomainTimeRemainingOnCore ctx observer st c := by
  unfold projectDomainTimeRemainingOnCore; rw [hDTR]

theorem projectDomainScheduleIndexOnCore_frame (ctx : LabelingContext) (observer : IfObserver)
    {st st' : SystemState} {c : CoreId}
    (hDSI : st'.scheduler.domainScheduleIndexOnCore c = st.scheduler.domainScheduleIndexOnCore c) :
    projectDomainScheduleIndexOnCore ctx observer st' c =
      projectDomainScheduleIndexOnCore ctx observer st c := by
  unfold projectDomainScheduleIndexOnCore; rw [hDSI]

theorem projectMachineRegsOnCore_frame (ctx : LabelingContext) (observer : IfObserver)
    {st st' : SystemState} {c : CoreId}
    (hCur : st'.scheduler.currentOnCore c = st.scheduler.currentOnCore c)
    (hRegs : st'.machine.regsOnCore c = st.machine.regsOnCore c) :
    projectMachineRegsOnCore ctx observer st' c = projectMachineRegsOnCore ctx observer st c := by
  unfold projectMachineRegsOnCore; rw [hCur, hRegs]

/-- SM4.D: per-core observable-state congruence.  When the shared
(non-scheduler) projection components agree and core `c`'s six
scheduler slots agree, the per-core projected state agrees.  This is the
aggregate frame the SMP non-interference preservation proofs compose
from the per-component frames above plus the existing `projectState_*`
shared-component lemmas. -/
theorem projectStateOnCore_congr (ctx : LabelingContext) (observer : IfObserver)
    {st st' : SystemState} {c : CoreId}
    (hBase : projectState ctx observer st' = projectState ctx observer st)
    (hRQ : st'.scheduler.runQueueOnCore c = st.scheduler.runQueueOnCore c)
    (hCur : st'.scheduler.currentOnCore c = st.scheduler.currentOnCore c)
    (hAD : st'.scheduler.activeDomainOnCore c = st.scheduler.activeDomainOnCore c)
    (hDTR : st'.scheduler.domainTimeRemainingOnCore c = st.scheduler.domainTimeRemainingOnCore c)
    (hDSI : st'.scheduler.domainScheduleIndexOnCore c = st.scheduler.domainScheduleIndexOnCore c)
    (hRegs : st'.machine.regsOnCore c = st.machine.regsOnCore c) :
    projectStateOnCore ctx observer st' c = projectStateOnCore ctx observer st c := by
  unfold projectStateOnCore
  rw [hBase,
      projectRunnableOnCore_frame ctx observer hRQ,
      projectCurrentOnCore_frame ctx observer hCur,
      projectActiveDomainOnCore_frame ctx observer hAD,
      projectDomainTimeRemainingOnCore_frame ctx observer hDTR,
      projectDomainScheduleIndexOnCore_frame ctx observer hDSI,
      projectMachineRegsOnCore_frame ctx observer hCur hRegs]

-- ============================================================================
-- §4  Per-core low-equivalence (the SM4.D.13 NI substrate)
-- ============================================================================
--
-- `lowEquivalent` (also in `Projection.lean`) reads scheduler state
-- *transitively* through `projectState`, so it is part of the SM4.D.13
-- migration surface.  Its per-core form compares the per-core observable
-- projections; the boot-core bridge connects it to the live single-core
-- `lowEquivalent`, and the `∀ c` SMP form is the per-core observable-state
-- equivalence the SM6 info-flow phase consumes.

/-- SM4.D: per-core form of `lowEquivalent` — two states are low-equivalent
on core `c` when their per-core observer projections agree. -/
def lowEquivalentOnCore (ctx : LabelingContext) (observer : IfObserver)
    (s₁ s₂ : SystemState) (c : CoreId) : Prop :=
  projectStateOnCore ctx observer s₁ c = projectStateOnCore ctx observer s₂ c

theorem lowEquivalentOnCore_bootCore (ctx : LabelingContext) (observer : IfObserver)
    (s₁ s₂ : SystemState) :
    lowEquivalentOnCore ctx observer s₁ s₂ bootCoreId ↔ lowEquivalent ctx observer s₁ s₂ :=
  Iff.rfl

theorem lowEquivalentOnCore_refl (ctx : LabelingContext) (observer : IfObserver)
    (st : SystemState) (c : CoreId) :
    lowEquivalentOnCore ctx observer st st c := rfl

theorem lowEquivalentOnCore_symm {ctx : LabelingContext} {observer : IfObserver}
    {s₁ s₂ : SystemState} {c : CoreId}
    (h : lowEquivalentOnCore ctx observer s₁ s₂ c) :
    lowEquivalentOnCore ctx observer s₂ s₁ c := h.symm

theorem lowEquivalentOnCore_trans {ctx : LabelingContext} {observer : IfObserver}
    {s₁ s₂ s₃ : SystemState} {c : CoreId}
    (h₁ : lowEquivalentOnCore ctx observer s₁ s₂ c)
    (h₂ : lowEquivalentOnCore ctx observer s₂ s₃ c) :
    lowEquivalentOnCore ctx observer s₁ s₃ c := h₁.trans h₂

/-- SM4.D: system-wide SMP form of low-equivalence — the observable states
agree on every core. -/
def lowEquivalent_smp (ctx : LabelingContext) (observer : IfObserver)
    (s₁ s₂ : SystemState) : Prop :=
  ∀ c : CoreId, lowEquivalentOnCore ctx observer s₁ s₂ c

theorem lowEquivalent_smp_aggregateForall (ctx : LabelingContext) (observer : IfObserver)
    (s₁ s₂ : SystemState) :
    (∀ c : CoreId, lowEquivalentOnCore ctx observer s₁ s₂ c) ↔
      lowEquivalent_smp ctx observer s₁ s₂ := Iff.rfl

theorem lowEquivalent_smp_at (ctx : LabelingContext) (observer : IfObserver)
    (s₁ s₂ : SystemState) (c : CoreId)
    (h : lowEquivalent_smp ctx observer s₁ s₂) :
    lowEquivalentOnCore ctx observer s₁ s₂ c := h c

/-- SM4.D: the SMP low-equivalence implies the live single-core
`lowEquivalent` (instantiate at `bootCoreId` + bridge). -/
theorem lowEquivalent_smp_to_singleCore (ctx : LabelingContext) (observer : IfObserver)
    (s₁ s₂ : SystemState) (h : lowEquivalent_smp ctx observer s₁ s₂) :
    lowEquivalent ctx observer s₁ s₂ :=
  (lowEquivalentOnCore_bootCore ctx observer s₁ s₂).mp (h bootCoreId)

end SeLe4n.Kernel
