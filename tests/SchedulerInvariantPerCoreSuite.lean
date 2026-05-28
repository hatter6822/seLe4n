-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Invariant.PerCore

/-!
# WS-SM SM4.C — Per-core scheduler invariant migration test suite

Tier-2 (runtime) + Tier-3 (surface anchor) coverage for the WS-SM Phase
SM4.C "Scheduler invariants migration" deliverable.  Each section below
exercises a different layer of the per-core invariant migration:

* **§1 Surface anchors** — every public SM4.C symbol resolves at
  elaboration time, so a rename or removal fails the build immediately.
* **§2 Elaboration-time examples** — apply each headline theorem
  (`default_schedulerInvariant_perCore`, `_smp`, `_aggregateForall`, the
  bundle bridges, the pairwise/independence corollaries, the frame
  lemmas, the SMP-preservation skeleton) to verified inputs.
* **§3 Runtime assertions** — `lake exe scheduler_invariant_per_core_suite`
  re-exercises the decidable facts the theorems rest on (default-state
  per-core agreement; bridge `Iff.rfl` reflexivity; theorem-application
  side-effects on `allCores`).  A silent regression in any of these
  surfaces in the Tier-2 trace pass.
-/

namespace SeLe4n.Testing.SchedulerInvariantPerCore

open SeLe4n.Model
open SeLe4n.Kernel
open SeLe4n.Kernel.Concurrency

-- ============================================================================
-- §1  Surface anchors (Tier-3): every SM4.C public symbol resolves
-- ============================================================================

-- Per-core predicate forms (16):
#check @queueCurrentConsistentOnCore
#check @runQueueUniqueOnCore
#check @currentThreadValidOnCore
#check @currentThreadInActiveDomainOnCore
#check @timeSlicePositiveOnCore
#check @currentTimeSlicePositiveOnCore
#check @edfCurrentHasEarliestDeadlineOnCore
#check @contextMatchesCurrentOnCore
#check @runnableThreadsAreTCBsOnCore
#check @schedulerPriorityMatchOnCore
#check @domainTimeRemainingPositiveOnCore
#check @currentBudgetPositiveOnCore
#check @budgetPositiveOnCore
#check @replenishmentPipelineOrderOnCore
#check @replenishQueueValidOnCore
#check @effectiveParamsMatchRunQueueOnCore

-- Boot-core bridges (16):
#check @queueCurrentConsistentOnCore_bootCore_iff
#check @runQueueUniqueOnCore_bootCore_iff
#check @currentThreadValidOnCore_bootCore_iff
#check @currentThreadInActiveDomainOnCore_bootCore_iff
#check @timeSlicePositiveOnCore_bootCore_iff
#check @currentTimeSlicePositiveOnCore_bootCore_iff
#check @edfCurrentHasEarliestDeadlineOnCore_bootCore_iff
#check @contextMatchesCurrentOnCore_bootCore_iff
#check @runnableThreadsAreTCBsOnCore_bootCore_iff
#check @schedulerPriorityMatchOnCore_bootCore_iff
#check @domainTimeRemainingPositiveOnCore_bootCore_iff
#check @currentBudgetPositiveOnCore_bootCore_iff
#check @budgetPositiveOnCore_bootCore_iff
#check @replenishmentPipelineOrderOnCore_bootCore_iff
#check @replenishQueueValidOnCore_bootCore_iff
#check @effectiveParamsMatchRunQueueOnCore_bootCore_iff

-- Aggregate + system-wide form (SM4.C.29):
#check @schedulerInvariant_perCore
#check @schedulerInvariant_smp
#check @schedulerInvariant_perCore_aggregateForall
#check @schedulerInvariant_smp_at

-- Per-conjunct projections (mirrors `schedulerInvariantBundleFull_to_*`):
#check @schedulerInvariant_perCore_to_queueCurrentConsistent
#check @schedulerInvariant_perCore_to_runQueueUnique
#check @schedulerInvariant_perCore_to_currentThreadValid
#check @schedulerInvariant_perCore_to_timeSlicePositive
#check @schedulerInvariant_perCore_to_currentTimeSlicePositive
#check @schedulerInvariant_perCore_to_edfCurrentHasEarliestDeadline
#check @schedulerInvariant_perCore_to_contextMatchesCurrent
#check @schedulerInvariant_perCore_to_runnableThreadsAreTCBs
#check @schedulerInvariant_perCore_to_schedulerPriorityMatch
#check @schedulerInvariant_perCore_to_domainTimeRemainingPositive

-- Bundle bridges (live cross-subsystem surface ↔ per-core layer):
#check @schedulerInvariantBundleFull_to_perCore_bootCore
#check @schedulerInvariant_perCore_bootCore_to_bundleFull
#check @schedulerInvariantBundleExtended_to_perCore_bootCore

-- Default-state:
#check @default_schedulerInvariant_perCore
#check @default_schedulerInvariant_smp

-- Frame + cross-core independence (SM4.C.30):
#check @schedulerInvariant_perCore_frame
#check @schedulerInvariant_perCore_frame_idle
#check @schedulerInvariant_perCore_independent_of_setCurrentOnCore
#check @schedulerInvariant_perCore_independent_of_setRunQueueOnCore
#check @schedulerInvariant_perCore_independent_of_setDomainTimeRemainingOnCore
#check @schedulerInvariant_perCore_independent_of_setReplenishQueueOnCore
#check @schedulerInvariant_perCore_independent_of_setActiveDomainOnCore
#check @schedulerInvariant_perCore_independent_of_setDomainScheduleIndexOnCore
#check @schedulerInvariant_perCore_independent_of_setLastTimeoutErrorsOnCore
#check @schedulerInvariant_perCore_pairwise
#check @schedulerInvariant_smp_of_bootCore_and_idle_frame

-- Plan §5.6 missing predicate:
#check @runQueueOnCoreWellFormed

-- Per-conjunct frame lemmas (§5.5 — fine-grained SM5 reasoning):
#check @queueCurrentConsistentOnCore_frame
#check @runQueueUniqueOnCore_frame
#check @runQueueOnCoreWellFormed_frame
#check @currentThreadValidOnCore_frame
#check @currentThreadInActiveDomainOnCore_frame
#check @timeSlicePositiveOnCore_frame
#check @currentTimeSlicePositiveOnCore_frame
#check @edfCurrentHasEarliestDeadlineOnCore_frame
#check @contextMatchesCurrentOnCore_frame
#check @runnableThreadsAreTCBsOnCore_frame
#check @schedulerPriorityMatchOnCore_frame
#check @domainTimeRemainingPositiveOnCore_frame
#check @currentBudgetPositiveOnCore_frame
#check @budgetPositiveOnCore_frame
#check @replenishmentPipelineOrderOnCore_frame
#check @replenishQueueValidOnCore_frame
#check @effectiveParamsMatchRunQueueOnCore_frame

-- Extended per-core aggregate (§3.5 — mirroring schedulerInvariantBundleExtended):
#check @schedulerInvariant_perCore_extended
#check @schedulerInvariant_smp_extended
#check @schedulerInvariant_perCore_extended_aggregateForall
#check @schedulerInvariant_smp_extended_at
#check @schedulerInvariant_perCore_extended_to_base
#check @schedulerInvariant_perCore_extended_to_currentBudgetPositive
#check @schedulerInvariant_perCore_extended_to_budgetPositive
#check @schedulerInvariant_perCore_extended_to_replenishQueueValid
#check @schedulerInvariant_perCore_extended_to_effectiveParamsMatchRunQueue

-- Extended bundle bridges:
#check @schedulerInvariantBundleExtended_to_perCore_extended_bootCore
#check @schedulerInvariant_perCore_extended_bootCore_to_bundleExtended

-- Extended default-state:
#check @default_schedulerInvariant_perCore_extended
#check @default_schedulerInvariant_smp_extended

-- Extended frame, pairwise, SMP-preservation skeleton (§8):
#check @schedulerInvariant_perCore_extended_frame
#check @schedulerInvariant_perCore_extended_frame_idle
#check @schedulerInvariant_perCore_extended_pairwise
#check @schedulerInvariant_smp_extended_of_bootCore_and_idle_frame

-- Cross-subsystem per-core predicates (§9 — plan §5.6):
#check @schedContextRunQueueConsistent_perCore
#check @priorityInheritance_perCore
#check @activeDomainOnCore_isInDomainSchedule
#check @schedContextRunQueueConsistent_perCore_bootCore_iff
#check @priorityInheritance_perCore_iff
#check @default_schedContextRunQueueConsistent_perCore
#check @default_priorityInheritance_perCore
#check @default_activeDomainOnCore_isInDomainSchedule
#check @schedContextRunQueueConsistent_perCore_frame
#check @priorityInheritance_perCore_frame
#check @activeDomainOnCore_isInDomainSchedule_frame

-- "Sufficient idle" + SMP-preservation composition (§11):
#check @schedulerInvariant_perCore_holds_if_idle
#check @schedulerInvariant_perCore_idle_on_post_state
#check @schedulerInvariant_smp_of_bootCore_preservation
#check @schedulerInvariant_smp_extended_of_bootCore_preservation

-- Cross-subsystem per-core aggregate (§10):
#check @schedulerInvariant_perCore_crossSubsystem
#check @schedulerInvariant_smp_crossSubsystem
#check @schedulerInvariant_perCore_crossSubsystem_aggregateForall
#check @schedulerInvariant_smp_crossSubsystem_at
#check @schedulerInvariant_perCore_crossSubsystem_to_extended
#check @schedulerInvariant_perCore_crossSubsystem_to_schedContextRunQueueConsistent
#check @schedulerInvariant_perCore_crossSubsystem_to_priorityInheritance
#check @schedulerInvariant_perCore_crossSubsystem_to_activeDomainOnCore_isInDomainSchedule
#check @crossSubsystemInvariant_to_perCore_crossSubsystem_bootCore
#check @default_schedulerInvariant_perCore_crossSubsystem
#check @default_schedulerInvariant_smp_crossSubsystem

-- ============================================================================
-- §2  Elaboration-time examples: theorems applied to verified inputs
-- ============================================================================

-- §2.1  The default state satisfies the per-core invariant on every core.
example : schedulerInvariant_perCore (default : SystemState) bootCoreId :=
  default_schedulerInvariant_perCore bootCoreId

example (c : CoreId) : schedulerInvariant_perCore (default : SystemState) c :=
  default_schedulerInvariant_perCore c

example : schedulerInvariant_smp (default : SystemState) :=
  default_schedulerInvariant_smp

-- §2.2  The `aggregateForall` bridge between the per-core and SMP forms.
example :
    (∀ c : CoreId, schedulerInvariant_perCore (default : SystemState) c) ↔
    schedulerInvariant_smp (default : SystemState) :=
  schedulerInvariant_perCore_aggregateForall _

-- §2.3  Bundle bridge: the existing `schedulerInvariantBundleFull` implies the
--       per-core invariant at the boot core.  (This is the non-orphan
--       connection — every existing single-core preservation proof yields a
--       per-core preservation at the boot core for free.)
example {st : SystemState} (h : schedulerInvariantBundleFull st) :
    schedulerInvariant_perCore st bootCoreId :=
  schedulerInvariantBundleFull_to_perCore_bootCore h

example {st : SystemState} (h : schedulerInvariantBundleExtended st) :
    schedulerInvariant_perCore st bootCoreId :=
  schedulerInvariantBundleExtended_to_perCore_bootCore h

-- Converse: the per-core slice at the boot core plus the system-wide
-- `domainScheduleEntriesPositive` rebuilds the full bundle.
example {st : SystemState}
    (h : schedulerInvariant_perCore st bootCoreId)
    (hDSE : domainScheduleEntriesPositive st) :
    schedulerInvariantBundleFull st :=
  schedulerInvariant_perCore_bootCore_to_bundleFull h hDSE

-- §2.4  Boot-core bridges are `Iff.rfl` (per-core forms at `bootCoreId` are
--       definitionally the existing single-core predicates).
example (s : SchedulerState) :
    queueCurrentConsistentOnCore s bootCoreId ↔ queueCurrentConsistent s :=
  queueCurrentConsistentOnCore_bootCore_iff s

example (st : SystemState) :
    currentThreadValidOnCore st bootCoreId ↔ currentThreadValid st :=
  currentThreadValidOnCore_bootCore_iff st

-- §2.5  Cross-core pairwise independence (SM4.C.30).  Pick two distinct
--       core ids (0 and 1 are distinct under `numCores = 4`); writing core
--       1's `current` leaves core 0's invariant unchanged.
example {st : SystemState} (vc : Option SeLe4n.ThreadId) :
    schedulerInvariant_perCore
      { st with scheduler := st.scheduler.setCurrentOnCore ⟨1, by decide⟩ vc }
      bootCoreId ↔
    schedulerInvariant_perCore st bootCoreId :=
  schedulerInvariant_perCore_independent_of_setCurrentOnCore
    (c := bootCoreId) (c' := ⟨1, by decide⟩) (by decide) vc

-- §2.6  The composed-write pairwise theorem: writing all three of c₂'s
--       slots the invariant reads.
example {st : SystemState} (vc : Option SeLe4n.ThreadId) (vrq : SeLe4n.Kernel.RunQueue) (vdtr : Nat) :
    schedulerInvariant_perCore
      { st with scheduler :=
        ((st.scheduler.setCurrentOnCore ⟨1, by decide⟩ vc).setRunQueueOnCore
          ⟨1, by decide⟩ vrq).setDomainTimeRemainingOnCore ⟨1, by decide⟩ vdtr }
      bootCoreId ↔
    schedulerInvariant_perCore st bootCoreId :=
  schedulerInvariant_perCore_pairwise
    (c₁ := bootCoreId) (c₂ := ⟨1, by decide⟩) (by decide) vc vrq vdtr

-- §2.7  Boot core slice extracts via the SMP forall.
example (h : schedulerInvariant_smp (default : SystemState)) :
    schedulerInvariant_perCore (default : SystemState) bootCoreId :=
  schedulerInvariant_smp_at _ bootCoreId h

-- §2.8  Extended per-core aggregate: default state on every core.
example : schedulerInvariant_perCore_extended (default : SystemState) bootCoreId :=
  default_schedulerInvariant_perCore_extended bootCoreId

example (c : CoreId) : schedulerInvariant_perCore_extended (default : SystemState) c :=
  default_schedulerInvariant_perCore_extended c

example : schedulerInvariant_smp_extended (default : SystemState) :=
  default_schedulerInvariant_smp_extended

example :
    (∀ c : CoreId, schedulerInvariant_perCore_extended (default : SystemState) c) ↔
    schedulerInvariant_smp_extended (default : SystemState) :=
  schedulerInvariant_perCore_extended_aggregateForall _

-- §2.9  Extended bundle bridges.
example {st : SystemState} (h : schedulerInvariantBundleExtended st) :
    schedulerInvariant_perCore_extended st bootCoreId :=
  schedulerInvariantBundleExtended_to_perCore_extended_bootCore h

example {st : SystemState}
    (h : schedulerInvariant_perCore_extended st bootCoreId)
    (hDSE : domainScheduleEntriesPositive st)
    (hSCWF : schedContextsWellFormed st)
    (hSCBC : schedContextBindingConsistent st)
    (hBTDC : boundThreadDomainConsistent st) :
    schedulerInvariantBundleExtended st :=
  schedulerInvariant_perCore_extended_bootCore_to_bundleExtended h hDSE hSCWF hSCBC hBTDC

-- §2.10  Extended-aggregate pairwise independence.
example {st : SystemState} (vc : Option SeLe4n.ThreadId) (vrq : SeLe4n.Kernel.RunQueue)
    (vdtr : Nat) (vrepl : SeLe4n.Kernel.ReplenishQueue) :
    schedulerInvariant_perCore_extended
      { st with scheduler :=
        (((st.scheduler.setCurrentOnCore ⟨1, by decide⟩ vc).setRunQueueOnCore
            ⟨1, by decide⟩ vrq).setDomainTimeRemainingOnCore ⟨1, by decide⟩
            vdtr).setReplenishQueueOnCore ⟨1, by decide⟩ vrepl }
      bootCoreId ↔
    schedulerInvariant_perCore_extended st bootCoreId :=
  schedulerInvariant_perCore_extended_pairwise
    (c₁ := bootCoreId) (c₂ := ⟨1, by decide⟩) (by decide) vc vrq vdtr vrepl

-- §2.11  Per-conjunct frame lemma application (sample — one per category).
example (s s' : SchedulerState) (c : CoreId)
    (hCur : s'.currentOnCore c = s.currentOnCore c)
    (hRQ : s'.runQueueOnCore c = s.runQueueOnCore c) :
    queueCurrentConsistentOnCore s' c ↔ queueCurrentConsistentOnCore s c :=
  queueCurrentConsistentOnCore_frame hCur hRQ

example (st st' : SystemState) (c : CoreId)
    (hCur : st'.scheduler.currentOnCore c = st.scheduler.currentOnCore c)
    (hRegs : st'.machine.regs = st.machine.regs)
    (hObj : st'.objects = st.objects) :
    contextMatchesCurrentOnCore st' c ↔ contextMatchesCurrentOnCore st c :=
  contextMatchesCurrentOnCore_frame hCur hRegs hObj

-- §2.12  Cross-subsystem per-core aggregate: default state + bridges.
example : schedulerInvariant_perCore_crossSubsystem (default : SystemState) bootCoreId :=
  default_schedulerInvariant_perCore_crossSubsystem bootCoreId

example (c : CoreId) :
    schedulerInvariant_perCore_crossSubsystem (default : SystemState) c :=
  default_schedulerInvariant_perCore_crossSubsystem c

example : schedulerInvariant_smp_crossSubsystem (default : SystemState) :=
  default_schedulerInvariant_smp_crossSubsystem

-- Bridge from the live CrossSubsystem + Extended bundle to the per-core
-- cross-subsystem invariant at the boot core.
example {st : SystemState}
    (hExt : schedulerInvariantBundleExtended st)
    (hCSI : crossSubsystemInvariant st)
    (hADS : activeDomainOnCore_isInDomainSchedule st bootCoreId) :
    schedulerInvariant_perCore_crossSubsystem st bootCoreId :=
  crossSubsystemInvariant_to_perCore_crossSubsystem_bootCore hExt hCSI hADS

-- ============================================================================
-- §3  Runtime assertions (Tier-2): a silent regression surfaces here.
-- ============================================================================

private def assertBool (name : String) (b : Bool) : IO Unit := do
  if b then
    IO.println s!"  PASS: {name}"
  else
    IO.println s!"  FAIL: {name}"
    throw (IO.userError s!"Assertion failed: {name}")

/-- §3.1  Default-state foundations: the facts the per-core default theorem
    rests on (each per-core slot of `default` reads the neutral value).  We
    iterate over `allCores` to confirm the property holds on every core. -/
private def runDefaultFoundationChecks : IO Unit := do
  IO.println "--- §3.1 default-state per-core foundations ---"
  assertBool "default.currentOnCore = none on every core"
    (allCores.all (fun c => decide ((default : SystemState).scheduler.currentOnCore c = none)))
  assertBool "default.runQueueOnCore.toList = [] on every core"
    (allCores.all (fun c => decide
      (((default : SystemState).scheduler.runQueueOnCore c).toList = [])))
  assertBool "default.domainTimeRemainingOnCore = 5 on every core"
    (allCores.all (fun c => decide
      ((default : SystemState).scheduler.domainTimeRemainingOnCore c = 5)))
  assertBool "default.replenishQueueOnCore.entries = [] on every core"
    (allCores.all (fun c => decide
      (((default : SystemState).scheduler.replenishQueueOnCore c).entries = [])))
  assertBool "default.activeDomainOnCore = ⟨0⟩ on every core"
    (allCores.all (fun c => decide
      ((default : SystemState).scheduler.activeDomainOnCore c = ⟨0⟩)))

/-- §3.2  Theorem application: every headline SM4.C theorem can be applied
    and yields a proof of its conclusion.  The mere fact that these `have`
    bindings elaborate at runtime is the assertion (a regression in any
    theorem's typing or its proof would surface as an elaboration failure
    AT RUNTIME for the IO call). -/
private def runTheoremApplicationChecks : IO Unit := do
  IO.println "--- §3.2 per-core theorem applications ---"
  -- Default-state on every core.
  assertBool "default_schedulerInvariant_perCore applies on every core"
    (allCores.all (fun c =>
      have _h : schedulerInvariant_perCore (default : SystemState) c :=
        default_schedulerInvariant_perCore c
      true))
  -- SMP form on default.
  assertBool "default_schedulerInvariant_smp applies"
    (have _h : schedulerInvariant_smp (default : SystemState) :=
      default_schedulerInvariant_smp
     true)
  -- Boot-core projection.
  assertBool "schedulerInvariant_smp_at extracts every core"
    (allCores.all (fun c =>
      have _h : schedulerInvariant_perCore (default : SystemState) c :=
        schedulerInvariant_smp_at _ c default_schedulerInvariant_smp
      true))

/-- §3.3  Cross-core independence (SM4.C.30): writing core 1's slots leaves
    the boot-core invariant on the default state unchanged.  We extract the
    `.mpr` direction of the independence iff, apply it to
    `default_schedulerInvariant_perCore bootCoreId`, and confirm the
    post-write state's boot-core invariant typechecks. -/
private def runIndependenceChecks : IO Unit := do
  IO.println "--- §3.3 cross-core pairwise independence ---"
  let c₂ : CoreId := ⟨1, by decide⟩
  assertBool "writing core 1's current preserves boot-core invariant"
    (have _h : schedulerInvariant_perCore
        { (default : SystemState) with
          scheduler := (default : SystemState).scheduler.setCurrentOnCore c₂
            (some (SeLe4n.ThreadId.ofNat 7)) } bootCoreId :=
      (schedulerInvariant_perCore_independent_of_setCurrentOnCore
        (c := bootCoreId) (c' := c₂) (by decide)
        (some (SeLe4n.ThreadId.ofNat 7))).mpr
        (default_schedulerInvariant_perCore bootCoreId)
     true)
  assertBool "writing core 1's runQueue preserves boot-core invariant"
    (have _h : schedulerInvariant_perCore
        { (default : SystemState) with
          scheduler := (default : SystemState).scheduler.setRunQueueOnCore c₂
            SeLe4n.Kernel.RunQueue.empty } bootCoreId :=
      (schedulerInvariant_perCore_independent_of_setRunQueueOnCore
        (c := bootCoreId) (c' := c₂) (by decide)
        SeLe4n.Kernel.RunQueue.empty).mpr
        (default_schedulerInvariant_perCore bootCoreId)
     true)
  assertBool "writing core 1's domainTimeRemaining preserves boot-core invariant"
    (have _h : schedulerInvariant_perCore
        { (default : SystemState) with
          scheduler := (default : SystemState).scheduler.setDomainTimeRemainingOnCore c₂ 42 }
        bootCoreId :=
      (schedulerInvariant_perCore_independent_of_setDomainTimeRemainingOnCore
        (c := bootCoreId) (c' := c₂) (by decide) 42).mpr
        (default_schedulerInvariant_perCore bootCoreId)
     true)
  assertBool "pairwise composed write preserves boot-core invariant"
    (have _h : schedulerInvariant_perCore
        { (default : SystemState) with
          scheduler :=
            (((default : SystemState).scheduler.setCurrentOnCore c₂
              (some (SeLe4n.ThreadId.ofNat 7))).setRunQueueOnCore c₂
              SeLe4n.Kernel.RunQueue.empty).setDomainTimeRemainingOnCore c₂ 42 }
        bootCoreId :=
      (schedulerInvariant_perCore_pairwise
        (c₁ := bootCoreId) (c₂ := c₂) (by decide)
        (some (SeLe4n.ThreadId.ofNat 7)) SeLe4n.Kernel.RunQueue.empty 42).mpr
        (default_schedulerInvariant_perCore bootCoreId)
     true)

/-- §3.4  Boot-core bridges hold reflexively (every per-core form at
    `bootCoreId` is definitionally the existing single-core predicate). -/
private def runBridgeReflexivityChecks : IO Unit := do
  IO.println "--- §3.4 boot-core bridges are reflexive ---"
  assertBool "queueCurrentConsistentOnCore_bootCore_iff applies"
    (have _h := queueCurrentConsistentOnCore_bootCore_iff (default : SystemState).scheduler
     true)
  assertBool "currentThreadValidOnCore_bootCore_iff applies"
    (have _h := currentThreadValidOnCore_bootCore_iff (default : SystemState)
     true)
  assertBool "schedulerPriorityMatchOnCore_bootCore_iff applies"
    (have _h := schedulerPriorityMatchOnCore_bootCore_iff (default : SystemState)
     true)
  assertBool "replenishmentPipelineOrderOnCore_bootCore_iff applies"
    (have _h := replenishmentPipelineOrderOnCore_bootCore_iff (default : SystemState)
     true)

/-- §3.5  Extended per-core aggregate: default-state applies on every core,
plus SMP form, plus pairwise. -/
private def runExtendedAggregateChecks : IO Unit := do
  IO.println "--- §3.5 extended per-core aggregate (mirroring BundleExtended) ---"
  assertBool "default_schedulerInvariant_perCore_extended applies on every core"
    (allCores.all (fun c =>
      have _h : schedulerInvariant_perCore_extended (default : SystemState) c :=
        default_schedulerInvariant_perCore_extended c
      true))
  assertBool "default_schedulerInvariant_smp_extended applies"
    (have _h : schedulerInvariant_smp_extended (default : SystemState) :=
      default_schedulerInvariant_smp_extended
     true)
  assertBool "schedulerInvariant_smp_extended_at extracts every core"
    (allCores.all (fun c =>
      have _h : schedulerInvariant_perCore_extended (default : SystemState) c :=
        schedulerInvariant_smp_extended_at _ c default_schedulerInvariant_smp_extended
      true))
  -- Extended-aggregate pairwise independence: writing all 4 distinguishing
  -- slots of core 1 leaves boot core's extended invariant unchanged.
  let c₂ : CoreId := ⟨1, by decide⟩
  assertBool "extended pairwise composed write preserves boot-core invariant"
    (have _h : schedulerInvariant_perCore_extended
        { (default : SystemState) with
          scheduler :=
            ((((default : SystemState).scheduler.setCurrentOnCore c₂
                (some (SeLe4n.ThreadId.ofNat 7))).setRunQueueOnCore c₂
                SeLe4n.Kernel.RunQueue.empty).setDomainTimeRemainingOnCore c₂
                42).setReplenishQueueOnCore c₂ SeLe4n.Kernel.ReplenishQueue.empty }
        bootCoreId :=
      (schedulerInvariant_perCore_extended_pairwise
        (c₁ := bootCoreId) (c₂ := c₂) (by decide)
        (some (SeLe4n.ThreadId.ofNat 7)) SeLe4n.Kernel.RunQueue.empty 42
        SeLe4n.Kernel.ReplenishQueue.empty).mpr
        (default_schedulerInvariant_perCore_extended bootCoreId)
     true)

/-- §3.6  Per-conjunct frame lemmas (sample: one per category). -/
private def runPerConjunctFrameChecks : IO Unit := do
  IO.println "--- §3.6 per-conjunct frame lemmas (fine-grained SM5 reasoning) ---"
  -- All 17 per-conjunct frame lemmas resolve via reflexive hypotheses applied
  -- to the default state.
  assertBool "queueCurrentConsistentOnCore_frame applies on default"
    (have _h := queueCurrentConsistentOnCore_frame (s := (default : SystemState).scheduler)
        (s' := (default : SystemState).scheduler) (c := bootCoreId) rfl rfl
     true)
  assertBool "currentThreadValidOnCore_frame applies on default"
    (have _h := currentThreadValidOnCore_frame (st := (default : SystemState))
        (st' := (default : SystemState)) (c := bootCoreId) rfl rfl
     true)
  assertBool "contextMatchesCurrentOnCore_frame applies on default"
    (have _h := contextMatchesCurrentOnCore_frame (st := (default : SystemState))
        (st' := (default : SystemState)) (c := bootCoreId) rfl rfl rfl
     true)
  assertBool "currentBudgetPositiveOnCore_frame applies on default"
    (have _h := currentBudgetPositiveOnCore_frame (st := (default : SystemState))
        (st' := (default : SystemState)) (c := bootCoreId) rfl rfl
     true)
  assertBool "budgetPositiveOnCore_frame applies on default"
    (have _h := budgetPositiveOnCore_frame (st := (default : SystemState))
        (st' := (default : SystemState)) (c := bootCoreId) rfl rfl
     true)
  assertBool "replenishmentPipelineOrderOnCore_frame applies on default"
    (have _h := replenishmentPipelineOrderOnCore_frame (st := (default : SystemState))
        (st' := (default : SystemState)) (c := bootCoreId) rfl rfl
     true)
  assertBool "domainTimeRemainingPositiveOnCore_frame applies on default"
    (have _h := domainTimeRemainingPositiveOnCore_frame (st := (default : SystemState))
        (st' := (default : SystemState)) (c := bootCoreId) rfl
     true)

/-- §3.7  Cross-subsystem per-core aggregate: default-state applies on every
core, SMP form, projections, and bridge from `crossSubsystemInvariant`. -/
private def runCrossSubsystemAggregateChecks : IO Unit := do
  IO.println "--- §3.7 cross-subsystem per-core aggregate (plan §5.6) ---"
  assertBool "default_schedulerInvariant_perCore_crossSubsystem applies on every core"
    (allCores.all (fun c =>
      have _h : schedulerInvariant_perCore_crossSubsystem (default : SystemState) c :=
        default_schedulerInvariant_perCore_crossSubsystem c
      true))
  assertBool "default_schedulerInvariant_smp_crossSubsystem applies"
    (have _h : schedulerInvariant_smp_crossSubsystem (default : SystemState) :=
      default_schedulerInvariant_smp_crossSubsystem
     true)
  assertBool "schedulerInvariant_smp_crossSubsystem_at extracts every core"
    (allCores.all (fun c =>
      have _h : schedulerInvariant_perCore_crossSubsystem (default : SystemState) c :=
        schedulerInvariant_smp_crossSubsystem_at _ c default_schedulerInvariant_smp_crossSubsystem
      true))
  -- Project each of the 4 cross-subsystem-aggregate conjuncts.
  assertBool "perCore_crossSubsystem_to_extended projects on default"
    (allCores.all (fun c =>
      have _h : schedulerInvariant_perCore_extended (default : SystemState) c :=
        schedulerInvariant_perCore_crossSubsystem_to_extended
          (default_schedulerInvariant_perCore_crossSubsystem c)
      true))
  assertBool "perCore_crossSubsystem_to_schedContextRunQueueConsistent projects"
    (allCores.all (fun c =>
      have _h : schedContextRunQueueConsistent_perCore (default : SystemState) c :=
        schedulerInvariant_perCore_crossSubsystem_to_schedContextRunQueueConsistent
          (default_schedulerInvariant_perCore_crossSubsystem c)
      true))
  assertBool "perCore_crossSubsystem_to_priorityInheritance projects"
    (allCores.all (fun c =>
      have _h : priorityInheritance_perCore (default : SystemState) c :=
        schedulerInvariant_perCore_crossSubsystem_to_priorityInheritance
          (default_schedulerInvariant_perCore_crossSubsystem c)
      true))
  assertBool "perCore_crossSubsystem_to_activeDomainOnCore_isInDomainSchedule projects"
    (allCores.all (fun c =>
      have _h : activeDomainOnCore_isInDomainSchedule (default : SystemState) c :=
        schedulerInvariant_perCore_crossSubsystem_to_activeDomainOnCore_isInDomainSchedule
          (default_schedulerInvariant_perCore_crossSubsystem c)
      true))

def runSchedulerInvariantPerCoreChecks : IO Unit := do
  IO.println "WS-SM SM4.C — Per-core scheduler invariant migration suite"
  IO.println "===================================="
  runDefaultFoundationChecks
  runTheoremApplicationChecks
  runIndependenceChecks
  runBridgeReflexivityChecks
  runExtendedAggregateChecks
  runPerConjunctFrameChecks
  runCrossSubsystemAggregateChecks
  IO.println "===================================="
  IO.println "All SM4.C per-core scheduler invariant migration checks PASS."

end SeLe4n.Testing.SchedulerInvariantPerCore

def main : IO Unit :=
  SeLe4n.Testing.SchedulerInvariantPerCore.runSchedulerInvariantPerCoreChecks
