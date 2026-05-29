-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Architecture.Invariant

/-!
# WS-SM SM4.D — Per-core architecture↔scheduler coherence invariant

This module is the Architecture slice of the SM4.D cross-subsystem
migration (plan `docs/planning/SMP_PER_CORE_STATE_PLAN.md` §5.4,
sub-task SM4.D.9).  The single scheduler-reading architecture predicate
is `registerDecodeConsistent` (`Architecture/Invariant.lean`): whenever a
core has a current thread, that thread resolves to a TCB in the object
store (so register-decode at syscall entry has a TCB to read).

The migration lifts it to the per-core form `registerDecodeConsistent_perCore`
parameterised by an explicit `(c : CoreId)` (plan §3.4 Pattern 1), with a
boot-core bridge (`Iff.rfl`), a frame lemma, a default-state witness, and
the `∀ c` system-wide SMP aggregate.  The migration is additive and
soundness-preserving: the live `Architecture/Invariant.lean` surface is
untouched and stays green.

This module is a *sibling* of `Architecture/Invariant.lean` (rather than
an in-file extension) so it can be staged-only — the per-core layer is
not reachable from production until SM5's per-core scheduler consumes it.
`Architecture/ExceptionModel.lean` and `Architecture/InterruptDispatch.lean`
(SM4.D.10 / SM4.D.11) define no scheduler-reading predicates, so they
require no per-core migration; ditto `Architecture/VSpace.lean` and
`Architecture/SyscallEntry.lean` (SM4.D.21 / SM4.D.22).

Axiom-clean: every theorem depends only on the standard foundational
axioms (`propext` / `Quot.sound` / `Classical.choice`).
-/

namespace SeLe4n.Kernel.Architecture

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId bootCoreId)
open SeLe4n.Kernel

/-- Local helper: if two `SystemState`s agree on `objects`, every `getTcb?`
query agrees too (mirrors the SM4.C private helper of the same name).  Used
by the frame lemma to thread the `objects` hypothesis through the typed
accessor. -/
private theorem getTcb?_congr_objects
    {st st' : SystemState} (h : st'.objects = st.objects)
    (tid : SeLe4n.ThreadId) : st'.getTcb? tid = st.getTcb? tid := by
  unfold SystemState.getTcb?; rw [h]

-- ============================================================================
-- §1  Per-core predicate form
-- ============================================================================

/-- SM4.D: per-core form of `registerDecodeConsistent`.  When core `c` has
a current thread `tid`, `tid` resolves to a TCB in the object store.  Uses
the typed `getTcb?` accessor (AK7 discipline; adds no `tid.toObjId` raw
lookup site). -/
def registerDecodeConsistent_perCore (st : SystemState) (c : CoreId) : Prop :=
  ∀ tid, (st.scheduler.currentOnCore c) = some tid →
    ∃ tcb, st.getTcb? tid = some tcb

-- ============================================================================
-- §2  Boot-core bridge
-- ============================================================================

theorem registerDecodeConsistent_perCore_bootCore_iff (st : SystemState) :
    registerDecodeConsistent_perCore st bootCoreId ↔ registerDecodeConsistent st := by
  unfold registerDecodeConsistent_perCore registerDecodeConsistent
  simp only [SystemState.getTcb?_eq_some_iff]

-- ============================================================================
-- §3  Frame lemma
-- ============================================================================

theorem registerDecodeConsistent_perCore_frame {st st' : SystemState} {c : CoreId}
    (hObj : st'.objects = st.objects)
    (hCur : st'.scheduler.currentOnCore c = st.scheduler.currentOnCore c) :
    registerDecodeConsistent_perCore st' c ↔ registerDecodeConsistent_perCore st c := by
  unfold registerDecodeConsistent_perCore
  simp only [hCur, getTcb?_congr_objects hObj]

-- ============================================================================
-- §4  Default-state
-- ============================================================================

/-- SM4.D: on the freshly-booted system, register-decode consistency holds
on every core — vacuous, since each core's `current` is `none`. -/
theorem default_registerDecodeConsistent_perCore (c : CoreId) :
    registerDecodeConsistent_perCore (default : SystemState) c := by
  intro tid hCur
  have hNone : (default : SystemState).scheduler.currentOnCore c = none :=
    (default_state_perCoreInitialized c).1
  rw [hNone] at hCur; exact absurd hCur (by simp)

-- ============================================================================
-- §5  System-wide SMP aggregate (∀ c)
-- ============================================================================

/-- SM4.D: system-wide SMP form of `registerDecodeConsistent` — every
core's current thread resolves to a TCB. -/
def registerDecodeConsistent_smp (st : SystemState) : Prop :=
  ∀ c : CoreId, registerDecodeConsistent_perCore st c

theorem registerDecodeConsistent_smp_aggregateForall (st : SystemState) :
    (∀ c : CoreId, registerDecodeConsistent_perCore st c) ↔
      registerDecodeConsistent_smp st := Iff.rfl

theorem registerDecodeConsistent_smp_at (st : SystemState) (c : CoreId)
    (h : registerDecodeConsistent_smp st) : registerDecodeConsistent_perCore st c := h c

theorem registerDecodeConsistent_smp_to_singleCore (st : SystemState)
    (h : registerDecodeConsistent_smp st) : registerDecodeConsistent st :=
  (registerDecodeConsistent_perCore_bootCore_iff st).mp (h bootCoreId)

theorem default_registerDecodeConsistent_smp :
    registerDecodeConsistent_smp (default : SystemState) :=
  fun c => default_registerDecodeConsistent_perCore c

end SeLe4n.Kernel.Architecture
