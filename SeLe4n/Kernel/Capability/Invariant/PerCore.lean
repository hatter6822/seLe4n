-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Capability.Invariant.Defs

/-!
# WS-SM SM4.D — Per-core capability↔scheduler coherence invariants

This module is the Capability slice of the SM4.D cross-subsystem
migration (plan `docs/planning/SMP_PER_CORE_STATE_PLAN.md` §5.4,
sub-tasks SM4.D.3 / SM4.D.4).  The single scheduler-reading capability
predicate is `cleanupHookDischarged` (`Capability/Invariant/Defs.lean`),
whose second conjunct asserts that the cleanup target's TCB carries no
stale scheduler-queue reference (`tcb.tid ∉ (runQueueOnCore bootCoreId).flat`).

Per the implement-the-improvement rule, the per-core migration delivers
the genuine SMP semantics: a retyped object's TCB must not be runnable
on **any** core (`cleanupNoStaleSchedRef_smp`).  This is strictly
stronger than the single-core form (which only checks the boot core) and
is the correct precondition for retyping an object on an SMP system.

The migration is additive and soundness-preserving: the per-core form at
`bootCoreId` is *definitionally* the single-core predicate, so the
boot-core bridge closes by `Iff.rfl` and the live capability invariant
surface is untouched.

`cleanupHookDischarged`'s other two conjuncts — the lifecycle
object-type-metadata match (conjunct 1) and the opaque `ScrubToken`
witness (conjunct 3) — are core-independent, so the full per-core form
parameterises only the scheduler conjunct.  Default-state and frame
lemmas are provided for the **scheduler conjunct** only: conjunct 3
(`ScrubToken`, an opaque structural witness that cleanup observably ran)
is not trivially inhabited on the empty default state, so no full default
is claimed (matching the absence of a single-core `default_cleanupHookDischarged`).

Axiom-clean: every theorem depends only on the standard foundational
axioms (`propext` / `Quot.sound` / `Classical.choice`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId bootCoreId)

-- ============================================================================
-- §1  Per-core predicate forms
-- ============================================================================

/-- SM4.D: per-core form of the scheduler-reading conjunct of
`cleanupHookDischarged`: the cleanup target's TCB (if any) is not in core
`c`'s run queue. -/
def cleanupNoStaleSchedRef_perCore (st : SystemState) (target : SeLe4n.ObjId)
    (c : CoreId) : Prop :=
  ∀ tcb, st.objects[target]? = some (.tcb tcb) →
    ¬ (tcb.tid ∈ (st.scheduler.runQueueOnCore c).flat)

/-- SM4.D: per-core form of `cleanupHookDischarged`.  The lifecycle
object-type-metadata conjunct and the `ScrubToken` witness are
core-independent; only the no-stale-scheduler-reference conjunct is
parameterised by `c`. -/
def cleanupHookDischarged_perCore (st : SystemState) (target : SeLe4n.ObjId)
    (c : CoreId) : Prop :=
  (∀ obj, st.objects[target]? = some obj →
    SystemState.lookupObjectTypeMeta st target = some obj.objectType)
  ∧ cleanupNoStaleSchedRef_perCore st target c
  ∧ SeLe4n.Kernel.ScrubToken st target

-- ============================================================================
-- §2  Boot-core bridges (the non-orphan connection to the live surface)
-- ============================================================================

theorem cleanupNoStaleSchedRef_perCore_bootCore_iff (st : SystemState)
    (target : SeLe4n.ObjId) :
    cleanupNoStaleSchedRef_perCore st target bootCoreId ↔
      (∀ tcb, st.objects[target]? = some (.tcb tcb) →
        ¬ (tcb.tid ∈ (st.scheduler.runQueueOnCore bootCoreId).flat)) := Iff.rfl

theorem cleanupHookDischarged_perCore_bootCore_iff (st : SystemState)
    (target : SeLe4n.ObjId) :
    cleanupHookDischarged_perCore st target bootCoreId ↔
      cleanupHookDischarged st target := Iff.rfl

-- ============================================================================
-- §3  Frame lemma for the scheduler conjunct
-- ============================================================================

theorem cleanupNoStaleSchedRef_perCore_frame {st st' : SystemState}
    {target : SeLe4n.ObjId} {c : CoreId}
    (hObj : st'.objects = st.objects)
    (hRQ : st'.scheduler.runQueueOnCore c = st.scheduler.runQueueOnCore c) :
    cleanupNoStaleSchedRef_perCore st' target c ↔
      cleanupNoStaleSchedRef_perCore st target c := by
  unfold cleanupNoStaleSchedRef_perCore; rw [hObj, hRQ]

-- ============================================================================
-- §4  Default-state for the scheduler conjunct
-- ============================================================================

/-- SM4.D: on the freshly-booted (empty) system, no cleanup target carries
a stale scheduler reference on any core — vacuous, since the object store
is empty.  (No full `default_cleanupHookDischarged_perCore` is claimed:
its `ScrubToken` conjunct is an opaque cleanup-ran witness, not inhabited
on the default state.) -/
theorem default_cleanupNoStaleSchedRef_perCore (target : SeLe4n.ObjId) (c : CoreId) :
    cleanupNoStaleSchedRef_perCore (default : SystemState) target c := by
  intro tcb hObj
  have hNone : (default : SystemState).objects[target]? = none := by
    simp only [RHTable_getElem?_eq_get?]
    exact SeLe4n.Kernel.RobinHood.RHTable.getElem?_empty 16 (by omega) target
  rw [hNone] at hObj; exact absurd hObj (by simp)

-- ============================================================================
-- §5  System-wide SMP form (∀ c) — the genuine SMP generalisation
-- ============================================================================

/-- SM4.D: a cleanup target's TCB is not runnable on **any** core.  This is
the SMP-correct precondition for retyping: the boot-core-only single-core
check (`cleanupHookDischarged`'s conjunct 2) is too weak when more than one
core can schedule the target's TCB. -/
def cleanupNoStaleSchedRef_smp (st : SystemState) (target : SeLe4n.ObjId) : Prop :=
  ∀ c : CoreId, cleanupNoStaleSchedRef_perCore st target c

theorem cleanupNoStaleSchedRef_smp_aggregateForall (st : SystemState)
    (target : SeLe4n.ObjId) :
    (∀ c : CoreId, cleanupNoStaleSchedRef_perCore st target c) ↔
      cleanupNoStaleSchedRef_smp st target := Iff.rfl

theorem cleanupNoStaleSchedRef_smp_at (st : SystemState) (target : SeLe4n.ObjId)
    (c : CoreId) (h : cleanupNoStaleSchedRef_smp st target) :
    cleanupNoStaleSchedRef_perCore st target c := h c

/-- SM4.D: the SMP no-stale-reference form implies the live single-core
conjunct (instantiate at `bootCoreId` + bridge). -/
theorem cleanupNoStaleSchedRef_smp_to_singleCore (st : SystemState)
    (target : SeLe4n.ObjId) (h : cleanupNoStaleSchedRef_smp st target) :
    ∀ tcb, st.objects[target]? = some (.tcb tcb) →
      ¬ (tcb.tid ∈ (st.scheduler.runQueueOnCore bootCoreId).flat) :=
  (cleanupNoStaleSchedRef_perCore_bootCore_iff st target).mp (h bootCoreId)

theorem default_cleanupNoStaleSchedRef_smp (target : SeLe4n.ObjId) :
    cleanupNoStaleSchedRef_smp (default : SystemState) target :=
  fun c => default_cleanupNoStaleSchedRef_perCore target c

-- ============================================================================
-- §6  Full cleanup-hook SMP form (the SMP retype precondition)
-- ============================================================================

/-- SM4.D: the SMP form of `cleanupHookDischarged` — the lifecycle
object-type-metadata match (core-independent), the SMP no-stale-scheduler-
reference conjunct (`∀ c`, the implement-the-improvement strengthening),
and the opaque `ScrubToken` cleanup-ran witness (core-independent).  This
is the precondition an SMP-aware retype entry point requires: a retyped
object's TCB must not be runnable on **any** core. -/
def cleanupHookDischarged_smp (st : SystemState) (target : SeLe4n.ObjId) : Prop :=
  (∀ obj, st.objects[target]? = some obj →
    SystemState.lookupObjectTypeMeta st target = some obj.objectType)
  ∧ cleanupNoStaleSchedRef_smp st target
  ∧ SeLe4n.Kernel.ScrubToken st target

/-- SM4.D: the SMP cleanup-hook form implies the live single-core
`cleanupHookDischarged` (the no-stale-ref conjunct narrows from all cores
to the boot core via the bridge; the other two conjuncts are shared). -/
theorem cleanupHookDischarged_smp_to_singleCore (st : SystemState)
    (target : SeLe4n.ObjId) (h : cleanupHookDischarged_smp st target) :
    cleanupHookDischarged st target :=
  ⟨h.1, cleanupNoStaleSchedRef_smp_to_singleCore st target h.2.1, h.2.2⟩

/-- SM4.D: extract the SMP no-stale-reference conjunct from the full SMP
cleanup-hook form. -/
theorem cleanupHookDischarged_smp_to_noStaleSchedRef (st : SystemState)
    (target : SeLe4n.ObjId) (h : cleanupHookDischarged_smp st target) :
    cleanupNoStaleSchedRef_smp st target := h.2.1

end SeLe4n.Kernel
