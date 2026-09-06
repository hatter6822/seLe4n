-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- WS-RR RR7.39: PRODUCTION.  The declared-footprint bracket the three live
-- per-core scheduler entries run.  `SeLe4n/Kernel/PerCoreTimerEntry.lean`,
-- `PerCoreRescheduleEntry.lean` and `SecondaryEntry.lean` are the consumers.

import SeLe4n.Kernel.Scheduler.Operations.SchedLockSet
import SeLe4n.Kernel.Concurrency.Runtime
import SeLe4n.Kernel.Scheduler.Operations.PerCoreRunLoop

/-!
# WS-RR RR7.39 — the declared footprint, at the per-core scheduler entries

RR7.12 put the live syscall seam inside the footprint its own decode declares.
The three per-core scheduler entries — the timer tick, the `.reschedule` SGI
receiver and the secondary bring-up entry — committed run-queue and
replenish-queue state under the SM5.I global entry lock and nothing else, which
is what `PerCoreTimerEntry`'s docstring called "the SM3.C combinator's
cross-domain extension (tracked SM5.I closure target)".

(`UncoveredLockDomain`'s own entry recorded the *syscall* half of the same
domain — it names `suspendThreadOnCoreSchedLockSet`, a syscall footprint — and
RR7.39 narrowed it to `syscallSeamSchedulerDomain` rather than deleting it, since
`lockSetForSyscall` still returns a `LockSet` whose `LockId` cannot name a
run-queue lock.)

This module is that extension's consumer.  Three pieces, in the order the entries
run them.

## 1.  The footprints, resolved from the entry's own argument

An entry's only argument is a raw `coreId : UInt64`, and the verified step decodes
it fail-closed through `Concurrency.coreIdOfUInt64?`.  The footprint is resolved
from **that same decode** — so a footprint is declared exactly when the step will
run, and an out-of-range id declares nothing and acquires nothing
(`…_invalid_core`).

Unlike the ABI seam's, these footprints do not read the state at all: a scheduler
entry's footprint is a function of the executing core, where a syscall's is a
function of a capability the pre-state resolves.  That makes the bracket's
revalidation *trivially* satisfied here (`…_state_independent`) — which is worth
saying out loud rather than leaving a reader to assume the guard is doing work it
is not.  What the guard still decides, and what no footprint-level theorem can,
is whether the growing phase **granted** the set or merely queued on it.

## 2.  The bracket

`runBracketed` at `schedulerLockBracketDomain` — the *same* definition the ABI
seam runs (`SeLe4n/Kernel/SyscallLockBracket.lean`), differing only in which
domain record supplies the five primitives.  RR7.39 made it shared precisely so
that "what does a revalidating 2PL bracket do" has one answer.

## 3.  The write-set containment

A declared footprint that does not cover a write is a *false* footprint, and the
2PL argument would then rest on exclusion the runtime never established.
`schedFootprintCoversWrites` states the obligation as data — for every lock the
footprint does **not** name, the state it guards is unchanged — and §4 discharges
it for both live steps.

For the timer tick the obligation reduces to one fact, because RR7.39 widened its
footprint to every core's run-queue lock (see
`timerTickOnCoreTimeoutDynamicLockSet`, and the finding that prompted it): the
tick must not touch a replenish queue other than its own core's.  For the
reschedule step it reduces to two: no sibling core's scheduling slots, and no
core's replenish queue.

## What this does *not* change

The granularity that matters for concurrency is still the granularity of the
**commit**, and `Platform.FFI.modifyGetKernelState` is one global
read-modify-write over a single `SystemState`.  So the SM5.I kernel-entry ticket
lock stays, and live WCRT is still the global lock's.  What this buys is the
model-level property the SM5 footprints were always about, now true of the three
entries as well as the syscall seam: the transition the kernel runs runs inside
its declared footprint.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId SgiKind AccessMode bootCoreId numCores
  LockBracketOutcome runBracketed coreIdOfUInt64?)

-- ============================================================================
-- §1  The footprints, resolved from the entry's own decode
-- ============================================================================

/-- **WS-RR RR7.39**: the footprint the live per-core timer entry declares.

`timerTickOnCoreCompleteLockSet` at the core the entry's own argument decodes to
— the object-store table write lock, every core's run-queue write lock (the tick's
wakes are target-aware) and that core's replenish-queue write lock.

`none` for an id the model has no core for, which is the same condition on which
`perCoreTimerTickStep` commits nothing: a footprint is declared exactly when there
is a step to bracket. -/
def declaredSchedLockSetForTimerTick (coreId : UInt64) :
    SystemState → Option SchedLockSet :=
  fun _ => (coreIdOfUInt64? coreId).bind
    (fun c => SchedLockSet.ofList? (timerTickOnCoreCompleteLockSet c))

/-- **WS-RR RR7.39**: the footprint the live `.reschedule` SGI receiver — and,
definitionally, the secondary bring-up entry — declares.

`handleRescheduleSgiOnCoreLockSet`, which SM5.C.5 already established *is*
`switchToThreadOnCoreLockSet`: the object-store table write lock and the executing
core's run-queue write lock.  The selection's reads and the
`candidateOutranksCurrentOnCore` comparison are on the same two domains, so the
switch's footprint subsumes them. -/
def declaredSchedLockSetForReschedule (coreId : UInt64) :
    SystemState → Option SchedLockSet :=
  fun _ => (coreIdOfUInt64? coreId).bind
    (fun c => SchedLockSet.ofList? (handleRescheduleSgiOnCoreLockSet c))

/-- **WS-RR RR7.39**: a valid core id declares the tick's complete footprint —
the footprint type's `Nodup` obligation is discharged by
`timerTickOnCoreCompleteLockSet_keys_nodup`, so the fail-closed constructor never
refuses a footprint this kernel actually declares. -/
theorem declaredSchedLockSetForTimerTick_resolves (coreId : UInt64) (st : SystemState)
    (h : coreId.toNat < numCores) :
    declaredSchedLockSetForTimerTick coreId st
      = some ⟨timerTickOnCoreCompleteLockSet ⟨coreId.toNat, h⟩,
              timerTickOnCoreCompleteLockSet_keys_nodup _⟩ := by
  unfold declaredSchedLockSetForTimerTick
  rw [Concurrency.coreIdOfUInt64?_eq_some coreId h]
  simp only [Option.bind_some]
  exact SchedLockSet.ofList?_isSome_of_nodup _

/-- **WS-RR RR7.39**: an out-of-range core id declares no footprint, so the
bracket takes its undeclared arm and acquires nothing — the same fail-closed
condition `perCoreTimerTickStep_invalid_core` reports on the step. -/
theorem declaredSchedLockSetForTimerTick_invalid_core (coreId : UInt64) (st : SystemState)
    (h : ¬ coreId.toNat < numCores) :
    declaredSchedLockSetForTimerTick coreId st = none := by
  unfold declaredSchedLockSetForTimerTick coreIdOfUInt64?
  rw [dif_neg h]
  rfl

/-- **WS-RR RR7.39**: the reschedule footprint resolves for a valid core id. -/
theorem declaredSchedLockSetForReschedule_resolves (coreId : UInt64) (st : SystemState)
    (h : coreId.toNat < numCores) :
    declaredSchedLockSetForReschedule coreId st
      = some ⟨handleRescheduleSgiOnCoreLockSet ⟨coreId.toNat, h⟩,
              switchToThreadOnCoreLockSet_keys_nodup _⟩ := by
  unfold declaredSchedLockSetForReschedule
  rw [Concurrency.coreIdOfUInt64?_eq_some coreId h]
  simp only [Option.bind_some]
  exact SchedLockSet.ofList?_isSome_of_nodup _

/-- **WS-RR RR7.39**: an out-of-range core id declares no reschedule footprint. -/
theorem declaredSchedLockSetForReschedule_invalid_core (coreId : UInt64) (st : SystemState)
    (h : ¬ coreId.toNat < numCores) :
    declaredSchedLockSetForReschedule coreId st = none := by
  unfold declaredSchedLockSetForReschedule coreIdOfUInt64?
  rw [dif_neg h]
  rfl

/-- **WS-RR RR7.39 (the revalidation is trivial here, and that is a theorem)**:
a scheduler entry's footprint does not depend on the state.

Stated rather than left implicit, because the bracket's guard has two conjuncts
and a reader is entitled to know which one is doing the work.  A syscall's
footprint is resolved through a capability the pre-state holds, so its
re-resolution can genuinely differ; a scheduler entry's is a function of the
executing core alone, so the growing phase cannot move it.  What the guard
decides here is the *other* conjunct — whether the footprint was granted or the
growing phase merely queued on a contended member. -/
theorem declaredSchedLockSetForTimerTick_state_independent (coreId : UInt64)
    (st₁ st₂ : SystemState) :
    declaredSchedLockSetForTimerTick coreId st₁
      = declaredSchedLockSetForTimerTick coreId st₂ := rfl

/-- **WS-RR RR7.39**: likewise for the reschedule footprint. -/
theorem declaredSchedLockSetForReschedule_state_independent (coreId : UInt64)
    (st₁ st₂ : SystemState) :
    declaredSchedLockSetForReschedule coreId st₁
      = declaredSchedLockSetForReschedule coreId st₂ := rfl

-- ============================================================================
-- §2  The brackets
-- ============================================================================

/-- **WS-RR RR7.39**: the core a scheduler entry acquires on behalf of.

The executing core, where the argument names one.  The `bootCoreId` fall-back is
provably never used to acquire anything: on an out-of-range id the footprint is
`none` and the bracket takes its undeclared arm
(`timerTickUnderDeclaredLockSet_invalid_core`), so the default is discharged by a
theorem rather than trusted as a convention. -/
@[inline] def schedEntryLockCore (coreId : UInt64) : CoreId :=
  (coreIdOfUInt64? coreId).getD bootCoreId

/-- **WS-RR RR7.39**: the per-core timer tick, inside its declared footprint. -/
def timerTickUnderDeclaredLockSet (coreId : UInt64) (st : SystemState) :
    LockBracketOutcome (List (CoreId × SgiKind) × Bool) :=
  runBracketed schedulerLockBracketDomain (declaredSchedLockSetForTimerTick coreId)
    (schedEntryLockCore coreId)
    (fun s => perCoreTimerTickStepWithClockAdvance s coreId) st

/-- **WS-RR RR7.39**: the per-core reschedule step, inside its declared
footprint. -/
def rescheduleUnderDeclaredLockSet (coreId : UInt64) (st : SystemState) :
    LockBracketOutcome Unit :=
  runBracketed schedulerLockBracketDomain (declaredSchedLockSetForReschedule coreId)
    (schedEntryLockCore coreId)
    (fun s => ((), perCoreRescheduleStep s coreId)) st

/-- **WS-RR RR7.39**: on an out-of-range core id the tick bracket is the bare
step — no lock is written, and the `schedEntryLockCore` fall-back is therefore
never used to acquire.  Composed with `perCoreTimerTickStep_invalid_core`, such
an entry commits nothing at all. -/
theorem timerTickUnderDeclaredLockSet_invalid_core (coreId : UInt64) (st : SystemState)
    (h : ¬ coreId.toNat < numCores) :
    timerTickUnderDeclaredLockSet coreId st
      = .undeclared (perCoreTimerTickStepWithClockAdvance st coreId) :=
  Concurrency.runBracketed_undeclared _ _ _ _ st
    (declaredSchedLockSetForTimerTick_invalid_core coreId st h)

/-- **WS-RR RR7.39**: likewise for the reschedule bracket. -/
theorem rescheduleUnderDeclaredLockSet_invalid_core (coreId : UInt64) (st : SystemState)
    (h : ¬ coreId.toNat < numCores) :
    rescheduleUnderDeclaredLockSet coreId st
      = .undeclared ((), perCoreRescheduleStep st coreId) :=
  Concurrency.runBracketed_undeclared _ _ _ _ st
    (declaredSchedLockSetForReschedule_invalid_core coreId st h)

/-- **WS-RR RR7.39 (a refused tick commits nothing)**: where the guard refuses,
the bracket produces no value, so the entry advances neither the HAL's shadow
clock nor any cross-core SGI.

The load-bearing negative at this seam.  A refusal that still reported a
`(sgis, clockAdvanced)` pair would have the entry poke remote cores and advance a
clock for a tick that never ran. -/
@[simp] theorem timerTickUnderDeclaredLockSet_refused_value (unwound : SystemState) :
    (LockBracketOutcome.refused (α := List (CoreId × SgiKind) × Bool) unwound).value?
      = none := rfl

-- ============================================================================
-- §3  What the footprint must cover
-- ============================================================================

/-- **WS-RR RR7.39**: the write-set obligation a declared scheduler footprint
carries — for every lock the footprint does **not** name, the state that lock
guards is unchanged.

Quantified over every core rather than over the cores the author had in mind, so
an under-declared footprint makes the statement false rather than vacuous — the
same shape as `preservesFieldsOutside` (RR7.19), which is what turned six
`_modifiedFields` comments into six proof obligations and immediately found two
omissions.

The three clauses partition the state the scheduler domain guards: the object
store under the table lock, core `d`'s scheduling slots under its run-queue lock,
and core `d`'s replenishment queue under its replenish-queue lock. -/
def schedFootprintCoversWrites (S : SchedLockSet) (st st' : SystemState) : Prop :=
  ((SchedLockId.object schedObjStoreLockId, AccessMode.write) ∉ S.pairs →
      st'.objects = st.objects) ∧
  (∀ d : CoreId, (SchedLockId.runQueue ⟨d⟩, AccessMode.write) ∉ S.pairs →
      st'.scheduler.runQueueOnCore d = st.scheduler.runQueueOnCore d ∧
      st'.scheduler.currentOnCore d = st.scheduler.currentOnCore d ∧
      st'.scheduler.activeDomainOnCore d = st.scheduler.activeDomainOnCore d) ∧
  (∀ d : CoreId, (SchedLockId.replenishQueue ⟨d⟩, AccessMode.write) ∉ S.pairs →
      st'.scheduler.replenishQueueOnCore d = st.scheduler.replenishQueueOnCore d)

/-- **WS-RR RR7.39**: a footprint covers a step that changes nothing. -/
theorem schedFootprintCoversWrites_refl (S : SchedLockSet) (st : SystemState) :
    schedFootprintCoversWrites S st st :=
  ⟨fun _ => rfl, fun _ _ => ⟨rfl, rfl, rfl⟩, fun _ _ => rfl⟩

-- ============================================================================
-- §4  The reschedule step's writes are inside its footprint
-- ============================================================================

/-- **WS-RR RR7.39**: the reschedule footprint names core `d`'s run-queue lock
exactly when `d` is the executing core.

The membership fact the containment proof turns into a frame hypothesis: a lock
the footprint does *not* name is a core the step must not have touched. -/
theorem mem_handleRescheduleSgiOnCoreLockSet_runQueue_iff (c d : CoreId) :
    (SchedLockId.runQueue ⟨d⟩, AccessMode.write) ∈ handleRescheduleSgiOnCoreLockSet c
      ↔ d = c := by
  simp only [handleRescheduleSgiOnCoreLockSet, switchToThreadOnCoreLockSet,
    List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq, and_true]
  constructor
  · rintro (h | h)
    · exact absurd h (by simp)
    · exact congrArg RunQueueLockId.core (SchedLockId.runQueue.inj h)
  · rintro rfl; exact Or.inr rfl

/-- **WS-RR RR7.39**: the reschedule footprint names no replenish-queue lock —
the step touches no replenishment at all. -/
theorem not_mem_handleRescheduleSgiOnCoreLockSet_replenishQueue (c d : CoreId) :
    (SchedLockId.replenishQueue ⟨d⟩, AccessMode.write)
      ∉ handleRescheduleSgiOnCoreLockSet c := by
  simp only [handleRescheduleSgiOnCoreLockSet, switchToThreadOnCoreLockSet,
    List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq, and_true]
  rintro (h | h) <;> exact absurd h (by simp)

/-- **WS-RR RR7.39**: the reschedule step is the identity or one switch on the
decoded core.

`handleRescheduleSgiOnCore` returns `.ok st` on three of its four arms (selector
error propagates, no candidate, candidate does not outrank) and
`switchToThreadOnCore` on the fourth, and `perCoreRescheduleStep` swallows the
error arm.  Naming the disjunction once is what lets every frame below be an
instance of the switch's own frames rather than a re-derivation. -/
theorem perCoreRescheduleStep_id_or_switch (st : SystemState) (coreId : UInt64)
    (h : coreId.toNat < numCores) :
    perCoreRescheduleStep st coreId = st ∨
      ∃ tid st', switchToThreadOnCore st ⟨coreId.toNat, h⟩ tid = .ok st' ∧
        perCoreRescheduleStep st coreId = st' := by
  unfold perCoreRescheduleStep
  rw [dif_pos h]
  unfold handleRescheduleSgiOnCore
  cases hCh : chooseThreadEffectiveOnCore st ⟨coreId.toNat, h⟩ with
  | error e => exact Or.inl rfl
  | ok cand =>
    cases cand with
    | none => exact Or.inl rfl
    | some tid =>
      simp only
      by_cases hOut : candidateOutranksCurrentOnCore st ⟨coreId.toNat, h⟩ tid
      · rw [if_pos hOut]
        cases hSw : switchToThreadOnCore st ⟨coreId.toNat, h⟩ tid with
        | error e => exact Or.inl rfl
        | ok st' => exact Or.inr ⟨tid, st', hSw, rfl⟩
      · rw [if_neg hOut]; exact Or.inl rfl

/-- **WS-RR RR7.39 (the payoff for the reschedule seam)**: the verified
reschedule step's writes are inside the footprint the entry declares.

Every clause is discharged from the switch's own frames — sibling cores'
scheduling slots (`switchToThreadOnCore_independent_of_other_core`), every core's
active domain (`_activeDomainOnCore_eq`) and every core's replenish queue
(`_replenishQueueOnCore`) — and the identity arm is trivial.  So the footprint the
bracket acquires is not a *false* footprint: the exclusion the 2PL argument rests
on is exclusion the entry actually established. -/
theorem perCoreRescheduleStep_coversWrites (st : SystemState) (coreId : UInt64)
    (h : coreId.toNat < numCores) :
    schedFootprintCoversWrites
      ⟨handleRescheduleSgiOnCoreLockSet ⟨coreId.toNat, h⟩,
        switchToThreadOnCoreLockSet_keys_nodup _⟩
      st (perCoreRescheduleStep st coreId) := by
  rcases perCoreRescheduleStep_id_or_switch st coreId h with hId | ⟨tid, st', hSw, hEq⟩
  · rw [hId]; exact schedFootprintCoversWrites_refl _ _
  · rw [hEq]
    refine ⟨?_, ?_, ?_⟩
    · -- the object lock IS declared, so this clause has no content
      intro hNot
      exact absurd (List.mem_cons_self) hNot
    · intro d hNot
      have hne : d ≠ ⟨coreId.toNat, h⟩ := fun hEqCore =>
        hNot ((mem_handleRescheduleSgiOnCoreLockSet_runQueue_iff _ d).mpr hEqCore)
      obtain ⟨hCur, hRq⟩ :=
        switchToThreadOnCore_independent_of_other_core st ⟨coreId.toNat, h⟩ d tid st'
          (fun hc => hne hc.symm) hSw
      exact ⟨hRq, hCur,
        switchToThreadOnCore_activeDomainOnCore_eq st ⟨coreId.toNat, h⟩ tid st' d hSw⟩
    · intro d _
      exact switchToThreadOnCore_replenishQueueOnCore st ⟨coreId.toNat, h⟩ tid st' d hSw

end SeLe4n.Kernel
