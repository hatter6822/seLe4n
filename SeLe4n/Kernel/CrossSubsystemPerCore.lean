-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.Invariant.PerCore
import SeLe4n.Kernel.Capability.Invariant.PerCore
import SeLe4n.Kernel.Architecture.InvariantPerCore
import SeLe4n.Kernel.InformationFlow.ProjectionPerCore
import SeLe4n.Kernel.Scheduler.Invariant.PerCore

/-!
# WS-SM SM4.D — Cross-subsystem per-core invariant capstone

This module is the capstone of the SM4.D cross-subsystem migration (plan
`docs/planning/SMP_PER_CORE_STATE_PLAN.md` §5.4, sub-task SM4.D.19).  It
imports the per-subsystem per-core invariant slices landed by SM4.D
(IPC, Capability, Architecture, InformationFlow) plus the SM4.C scheduler
per-core layer, and assembles:

1. **`crossSubsystemInvariant_perCore`** — the per-core form of the
   master 12-conjunct `crossSubsystemInvariant` (`CrossSubsystem.lean`).
   Only its ninth conjunct (`schedContextRunQueueConsistent`) reads
   scheduler state; SM4.C already migrated it to
   `schedContextRunQueueConsistent_perCore`, so the per-core master
   invariant replaces exactly that conjunct, leaving the eleven
   core-independent conjuncts shared.  Boot-core bridge connects it to
   the live `crossSubsystemInvariant`.

2. **`crossSubsystemSchedulerContract_perCore`** — the SM4.D bundle of
   *every* cross-subsystem scheduler-reading invariant in per-core form:
   the IPC scheduler contract + dequeue coherence + passive-server
   idleness (`IPC.Invariant.PerCore`), the architecture register-decode
   consistency (`Architecture.InvariantPerCore`), and the SchedContext↔
   run-queue consistency (`Scheduler.Invariant.PerCore`).  Together with
   the `∀ c` SMP form and the boot-core bridge it is the single per-core
   surface SM5's per-core scheduler consumes for cross-subsystem
   coherence.

Both come with `∀ c` SMP aggregates, boot-core bridges to the live
single-core surface, per-conjunct projections, and default-state
witnesses.  The migration is additive and soundness-preserving: the live
`crossSubsystemInvariant` / IPC / architecture invariant surfaces are
untouched and stay green.

Axiom-clean: every theorem depends only on the standard foundational
axioms (`propext` / `Quot.sound` / `Classical.choice`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId bootCoreId)

-- ============================================================================
-- §1  Per-core master cross-subsystem invariant
-- ============================================================================

/-- SM4.D: per-core form of `crossSubsystemInvariant`.  Eleven conjuncts
are core-independent and unchanged; the ninth (`schedContextRunQueueConsistent`)
is replaced by the SM4.C per-core form `schedContextRunQueueConsistent_perCore`. -/
def crossSubsystemInvariant_perCore (st : SystemState) (c : CoreId) : Prop :=
  registryEndpointValid st ∧
  registryInterfaceValid st ∧
  registryDependencyConsistent st ∧
  noStaleEndpointQueueReferences st ∧
  noStaleNotificationWaitReferences st ∧
  serviceGraphInvariant st ∧
  schedContextStoreConsistent st ∧
  schedContextNotDualBound st ∧
  schedContextRunQueueConsistent_perCore st c ∧
  PriorityInheritance.blockingAcyclic st ∧
  lifecycleObjectTypeLockstep st ∧
  untypedRegionsDisjoint st

/-- SM4.D: the per-core master invariant at `bootCoreId` is the live
single-core `crossSubsystemInvariant` (the ninth conjunct bridges via
the SM4.C `schedContextRunQueueConsistent_perCore_bootCore_iff`). -/
theorem crossSubsystemInvariant_perCore_bootCore_iff (st : SystemState) :
    crossSubsystemInvariant_perCore st bootCoreId ↔ crossSubsystemInvariant st := by
  unfold crossSubsystemInvariant_perCore crossSubsystemInvariant
  rw [schedContextRunQueueConsistent_perCore_bootCore_iff]

/-- SM4.D: system-wide SMP form of the master cross-subsystem invariant. -/
def crossSubsystemInvariant_smp (st : SystemState) : Prop :=
  ∀ c : CoreId, crossSubsystemInvariant_perCore st c

theorem crossSubsystemInvariant_smp_aggregateForall (st : SystemState) :
    (∀ c : CoreId, crossSubsystemInvariant_perCore st c) ↔
      crossSubsystemInvariant_smp st := Iff.rfl

theorem crossSubsystemInvariant_smp_at (st : SystemState) (c : CoreId)
    (h : crossSubsystemInvariant_smp st) : crossSubsystemInvariant_perCore st c := h c

theorem crossSubsystemInvariant_smp_to_singleCore (st : SystemState)
    (h : crossSubsystemInvariant_smp st) : crossSubsystemInvariant st :=
  (crossSubsystemInvariant_perCore_bootCore_iff st).mp (h bootCoreId)

/-- SM4.D: extract the per-core SchedContext↔run-queue conjunct from the
per-core master invariant. -/
theorem crossSubsystemInvariant_perCore_to_schedContextRunQueueConsistent
    {st : SystemState} {c : CoreId} (h : crossSubsystemInvariant_perCore st c) :
    schedContextRunQueueConsistent_perCore st c := h.2.2.2.2.2.2.2.2.1

theorem default_crossSubsystemInvariant_perCore (c : CoreId) :
    crossSubsystemInvariant_perCore (default : SystemState) c := by
  have h := default_crossSubsystemInvariant
  unfold crossSubsystemInvariant at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, _h9, h10, h11, h12⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8,
    default_schedContextRunQueueConsistent_perCore c, h10, h11, h12⟩

theorem default_crossSubsystemInvariant_smp :
    crossSubsystemInvariant_smp (default : SystemState) :=
  fun c => default_crossSubsystemInvariant_perCore c

-- ============================================================================
-- §2  Cross-subsystem scheduler-contract capstone (the SM4.D bundle)
-- ============================================================================
--
-- Bundles every cross-subsystem scheduler-reading invariant in per-core
-- form: the IPC scheduler contract, dequeue-on-dispatch coherence, and
-- passive-server idleness (SM4.D, IPC); architecture register-decode
-- consistency (SM4.D, Architecture); and SchedContext↔run-queue
-- consistency (SM4.C, Scheduler).  This is the single per-core surface
-- SM5's per-core scheduler consumes for cross-subsystem coherence.

/-- SM4.D: the cross-subsystem scheduler-contract bundle on core `c`. -/
def crossSubsystemSchedulerContract_perCore (st : SystemState) (c : CoreId) : Prop :=
  ipcSchedulerContractPredicates_perCore st c ∧
  currentThreadDequeueCoherent_perCore st c ∧
  passiveServerIdle_perCore st c ∧
  Architecture.registerDecodeConsistent_perCore st c ∧
  schedContextRunQueueConsistent_perCore st c

/-- SM4.D: the contract bundle at `bootCoreId` is the conjunction of the
five live single-core invariants (each conjunct via its boot-core bridge). -/
theorem crossSubsystemSchedulerContract_perCore_bootCore_iff (st : SystemState) :
    crossSubsystemSchedulerContract_perCore st bootCoreId ↔
      (ipcSchedulerContractPredicates st ∧ currentThreadDequeueCoherent st ∧
       passiveServerIdle st ∧ Architecture.registerDecodeConsistent st ∧
       schedContextRunQueueConsistent st) := by
  unfold crossSubsystemSchedulerContract_perCore
  exact and_congr (ipcSchedulerContractPredicates_perCore_bootCore_iff st)
    (and_congr (currentThreadDequeueCoherent_perCore_bootCore_iff st)
      (and_congr (passiveServerIdle_perCore_bootCore_iff st)
        (and_congr (Architecture.registerDecodeConsistent_perCore_bootCore_iff st)
          (schedContextRunQueueConsistent_perCore_bootCore_iff st))))

/-- SM4.D: system-wide SMP form of the cross-subsystem scheduler contract. -/
def crossSubsystemSchedulerContract_smp (st : SystemState) : Prop :=
  ∀ c : CoreId, crossSubsystemSchedulerContract_perCore st c

theorem crossSubsystemSchedulerContract_smp_aggregateForall (st : SystemState) :
    (∀ c : CoreId, crossSubsystemSchedulerContract_perCore st c) ↔
      crossSubsystemSchedulerContract_smp st := Iff.rfl

theorem crossSubsystemSchedulerContract_smp_at (st : SystemState) (c : CoreId)
    (h : crossSubsystemSchedulerContract_smp st) :
    crossSubsystemSchedulerContract_perCore st c := h c

-- Per-conjunct projections (cheap accessors).

theorem crossSubsystemSchedulerContract_perCore_to_ipcSchedulerContractPredicates
    {st : SystemState} {c : CoreId} (h : crossSubsystemSchedulerContract_perCore st c) :
    ipcSchedulerContractPredicates_perCore st c := h.1

theorem crossSubsystemSchedulerContract_perCore_to_currentThreadDequeueCoherent
    {st : SystemState} {c : CoreId} (h : crossSubsystemSchedulerContract_perCore st c) :
    currentThreadDequeueCoherent_perCore st c := h.2.1

theorem crossSubsystemSchedulerContract_perCore_to_passiveServerIdle
    {st : SystemState} {c : CoreId} (h : crossSubsystemSchedulerContract_perCore st c) :
    passiveServerIdle_perCore st c := h.2.2.1

theorem crossSubsystemSchedulerContract_perCore_to_registerDecodeConsistent
    {st : SystemState} {c : CoreId} (h : crossSubsystemSchedulerContract_perCore st c) :
    Architecture.registerDecodeConsistent_perCore st c := h.2.2.2.1

theorem crossSubsystemSchedulerContract_perCore_to_schedContextRunQueueConsistent
    {st : SystemState} {c : CoreId} (h : crossSubsystemSchedulerContract_perCore st c) :
    schedContextRunQueueConsistent_perCore st c := h.2.2.2.2

theorem default_crossSubsystemSchedulerContract_perCore (c : CoreId) :
    crossSubsystemSchedulerContract_perCore (default : SystemState) c :=
  ⟨default_ipcSchedulerContractPredicates_perCore c,
   default_currentThreadDequeueCoherent_perCore c,
   default_passiveServerIdle_perCore c,
   Architecture.default_registerDecodeConsistent_perCore c,
   default_schedContextRunQueueConsistent_perCore c⟩

theorem default_crossSubsystemSchedulerContract_smp :
    crossSubsystemSchedulerContract_smp (default : SystemState) :=
  fun c => default_crossSubsystemSchedulerContract_perCore c

end SeLe4n.Kernel
