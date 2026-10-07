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

import SeLe4n.Kernel.Scheduler.Operations.PerCoreChooseThread
import SeLe4n.Kernel.Concurrency.Locks.LockBracket
import SeLe4n.Kernel.Concurrency.Locks.BracketSpec
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
domain — it names `suspendThreadOnCoreLockSet`, a syscall footprint — and
RR7.39 narrowed it to `syscallSeamSchedulerDomain` rather than deleting it, since
`lockSetForSyscall` still returned a `LockSet` whose `LockId` cannot name a
run-queue lock.  WS-RR RR8.12 Cut C6h, `v0.35.181`, deleted it: the syscall seam
brackets on this domain now, over one unified footprint spanning both — see
`declaredUnifiedLockSetForAbiEntry`.)

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

`runBracketed` at `objectLockBracketDomain` — the *same* definition the ABI
seam runs (`SeLe4n/Kernel/SyscallLockBracket.lean`), differing only in which
domain record supplies the five primitives.  RR7.39 made it shared precisely so
that "what does a revalidating 2PL bracket do" has one answer.

## 3.  The write-set containment

A declared footprint that does not cover a write is a *false* footprint, and the
2PL argument would then rest on exclusion the runtime never established.
`footprintCoversWrites` states the obligation as data — for every lock the
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
  LockBracketOutcome runBracketed coreIdOfUInt64?
  LockKey LockSet objectLockBracketDomain)

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
def declaredLockSetForTimerTick (coreId : UInt64) :
    SystemState → Option LockSet :=
  fun _ => (coreIdOfUInt64? coreId).bind
    (fun c => LockSet.ofList? (timerTickOnCoreCompleteLockSet c))

/-- **WS-RR RR7.39**: the footprint the live `.reschedule` SGI receiver — and,
definitionally, the secondary bring-up entry — declares.

`handleRescheduleSgiOnCoreLockSet`, which SM5.C.5 already established *is*
`switchToThreadOnCoreLockSet`: the object-store table write lock and the executing
core's run-queue write lock.  The selection's reads and the
`candidateOutranksCurrentOnCore` comparison are on the same two domains, so the
switch's footprint subsumes them. -/
def declaredLockSetForReschedule (coreId : UInt64) :
    SystemState → Option LockSet :=
  fun _ => (coreIdOfUInt64? coreId).bind
    (fun c => LockSet.ofList? (handleRescheduleSgiOnCoreLockSet c))

/-- **WS-RR RR7.39**: a valid core id declares the tick's complete footprint —
the footprint type's `Nodup` obligation is discharged by
`timerTickOnCoreCompleteLockSet_keys_nodup`, so the fail-closed constructor never
refuses a footprint this kernel actually declares. -/
theorem declaredLockSetForTimerTick_resolves (coreId : UInt64) (st : SystemState)
    (h : coreId.toNat < numCores) :
    declaredLockSetForTimerTick coreId st
      = some ⟨timerTickOnCoreCompleteLockSet ⟨coreId.toNat, h⟩,
              timerTickOnCoreCompleteLockSet_keys_nodup _⟩ := by
  unfold declaredLockSetForTimerTick
  rw [Concurrency.coreIdOfUInt64?_eq_some coreId h]
  simp only [Option.bind_some]
  exact LockSet.ofList?_isSome_of_nodup _

/-- **WS-RR RR7.39**: an out-of-range core id declares no footprint, so the
bracket takes its undeclared arm and acquires nothing — the same fail-closed
condition `perCoreTimerTickStep_invalid_core` reports on the step. -/
theorem declaredLockSetForTimerTick_invalid_core (coreId : UInt64) (st : SystemState)
    (h : ¬ coreId.toNat < numCores) :
    declaredLockSetForTimerTick coreId st = none := by
  unfold declaredLockSetForTimerTick coreIdOfUInt64?
  rw [dif_neg h]
  rfl

/-- **WS-RR RR7.39**: the reschedule footprint resolves for a valid core id. -/
theorem declaredLockSetForReschedule_resolves (coreId : UInt64) (st : SystemState)
    (h : coreId.toNat < numCores) :
    declaredLockSetForReschedule coreId st
      = some ⟨handleRescheduleSgiOnCoreLockSet ⟨coreId.toNat, h⟩,
              switchToThreadOnCoreLockSet_keys_nodup _⟩ := by
  unfold declaredLockSetForReschedule
  rw [Concurrency.coreIdOfUInt64?_eq_some coreId h]
  simp only [Option.bind_some]
  exact LockSet.ofList?_isSome_of_nodup _

/-- **WS-RR RR7.39**: an out-of-range core id declares no reschedule footprint. -/
theorem declaredLockSetForReschedule_invalid_core (coreId : UInt64) (st : SystemState)
    (h : ¬ coreId.toNat < numCores) :
    declaredLockSetForReschedule coreId st = none := by
  unfold declaredLockSetForReschedule coreIdOfUInt64?
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
theorem declaredLockSetForTimerTick_state_independent (coreId : UInt64)
    (st₁ st₂ : SystemState) :
    declaredLockSetForTimerTick coreId st₁
      = declaredLockSetForTimerTick coreId st₂ := rfl

/-- **WS-RR RR7.39**: likewise for the reschedule footprint. -/
theorem declaredLockSetForReschedule_state_independent (coreId : UInt64)
    (st₁ st₂ : SystemState) :
    declaredLockSetForReschedule coreId st₁
      = declaredLockSetForReschedule coreId st₂ := rfl

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
  runBracketed objectLockBracketDomain (declaredLockSetForTimerTick coreId)
    (schedEntryLockCore coreId)
    (fun s => perCoreTimerTickStepWithClockAdvance s coreId) st

/-- **WS-RR RR7.39**: the per-core reschedule step, inside its declared
footprint. -/
def rescheduleUnderDeclaredLockSet (coreId : UInt64) (st : SystemState) :
    LockBracketOutcome Unit :=
  runBracketed objectLockBracketDomain (declaredLockSetForReschedule coreId)
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
    (declaredLockSetForTimerTick_invalid_core coreId st h)

/-- **WS-RR RR7.39**: likewise for the reschedule bracket. -/
theorem rescheduleUnderDeclaredLockSet_invalid_core (coreId : UInt64) (st : SystemState)
    (h : ¬ coreId.toNat < numCores) :
    rescheduleUnderDeclaredLockSet coreId st
      = .undeclared ((), perCoreRescheduleStep st coreId) :=
  Concurrency.runBracketed_undeclared _ _ _ _ st
    (declaredLockSetForReschedule_invalid_core coreId st h)

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
-- `footprintCoversWrites` and its `_refl` / `_clearReschedulePendingOnCore` /
-- `_mono` lemmas moved to `Concurrency/Locks/BracketSpec.lean` at **WS-LS
-- LS2.1** (they are the obligation every `BracketSpec` carries, scheduler-domain
-- or not); `footprintCoversWrites_of_cores` stays here because it is stated
-- over `schedFootprintOfCores`.

/-- **WS-RR RR8.12 Cut C6a**: a canonical footprint covers a step confined to
its own two core lists.

The one bridge every declared syscall arm's coverage proof is an instance of.
`footprintCoversWrites`'s three clauses are discharged in three different
ways and only one of them is per-arm work:

* the **object** clause is vacuous, because `schedFootprintOfCores` always names
  the object-store table write lock (`schedFootprintOfCores_contains_objStore_write`)
  — a scheduler-domain footprint is a footprint of an operation that stores;
* the **run-queue** clause is the arm's own SM8.B confinement result, read
  through `mem_schedFootprintOfCores_runQueue_iff`: a lock the footprint does not
  name is a core outside the write set, which is exactly what confinement says
  the step did not touch;
* the **replenish** clause is the arm's own replenish frame, which SM8.B's
  confinement does *not* supply — `observableSlotsConfinedToCores` covers six
  per-core slots and the replenish queue is not one of them, which is why every
  donating arm carries a frame of its own.

Stated over the two core lists rather than over a `LockSet`, with the
footprint's `pairs` given by hypothesis, so it applies to a footprint however it
was constructed — and `SchedFootprintCensus` is what makes "however it was
constructed" mean "the canonical ladder" for every member of the family. -/
theorem footprintCoversWrites_of_cores (S : LockSet)
    (runCores replenishCores : List CoreId) (st st' : SystemState)
    (hS : S.pairs = schedFootprintOfCores runCores replenishCores)
    (hRun : ∀ d : CoreId, d ∉ runCores →
      st'.scheduler.runQueueOnCore d = st.scheduler.runQueueOnCore d ∧
      st'.scheduler.currentOnCore d = st.scheduler.currentOnCore d ∧
      st'.scheduler.activeDomainOnCore d = st.scheduler.activeDomainOnCore d)
    (hRepl : ∀ d : CoreId, d ∉ replenishCores →
      st'.scheduler.replenishQueueOnCore d = st.scheduler.replenishQueueOnCore d) :
    footprintCoversWrites S st st' := by
  refine ⟨?_, ?_, ?_⟩
  · intro hAbsent
    exact absurd (hS ▸ schedFootprintOfCores_contains_objStore_write runCores replenishCores)
      hAbsent
  · intro d hd
    refine hRun d ?_
    intro hMem
    exact hd (hS ▸ (mem_schedFootprintOfCores_runQueue_iff runCores replenishCores d).mpr hMem)
  · intro d hd
    refine hRepl d ?_
    intro hMem
    exact hd
      (hS ▸ (mem_schedFootprintOfCores_replenishQueue_iff runCores replenishCores d).mpr hMem)

-- ============================================================================
-- §4  The reschedule step's writes are inside its footprint
-- ============================================================================

/-- **WS-RR RR7.39**: the reschedule footprint names core `d`'s run-queue lock
exactly when `d` is the executing core.

The membership fact the containment proof turns into a frame hypothesis: a lock
the footprint does *not* name is a core the step must not have touched. -/
theorem mem_handleRescheduleSgiOnCoreLockSet_runQueue_iff (c d : CoreId) :
    (LockKey.runQueue d, AccessMode.write) ∈ handleRescheduleSgiOnCoreLockSet c
      ↔ d = c := by
  simp only [handleRescheduleSgiOnCoreLockSet, switchToThreadOnCoreLockSet,
    List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq, and_true]
  constructor
  · rintro (h | h)
    · exact absurd h (by simp)
    · exact LockKey.runQueue.inj h
  · rintro rfl; exact Or.inr rfl

/-- **WS-RR RR7.39**: the reschedule footprint names no replenish-queue lock —
the step touches no replenishment at all. -/
theorem not_mem_handleRescheduleSgiOnCoreLockSet_replenishQueue (c d : CoreId) :
    (LockKey.replenishQueue d, AccessMode.write)
      ∉ handleRescheduleSgiOnCoreLockSet c := by
  simp only [handleRescheduleSgiOnCoreLockSet, switchToThreadOnCoreLockSet,
    List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq, and_true]
  rintro (h | h) <;> exact absurd h (by simp)

/-- **WS-RR RR7.39**: the reschedule step is the identity, the core's own
reschedule-pending clear, one switch (then that clear), or the drop of an
out-of-domain incumbent (then that clear) on the decoded core.

`handleRescheduleSgiOnCore` propagates the selector's error, returns the
decoded core's flag clear (the KSC-1 accumulator's scheduling-point write) when
there is no candidate or the candidate does not outrank, and the switch followed
by that clear otherwise; `perCoreRescheduleStep` swallows the error arms.  Naming
the disjunction once is what lets every frame below be an instance of the
switch's own frames rather than a re-derivation. -/
theorem perCoreRescheduleStep_id_or_switch (st : SystemState) (coreId : UInt64)
    (h : coreId.toNat < numCores) :
    perCoreRescheduleStep st coreId = st ∨
      perCoreRescheduleStep st coreId = st.clearReschedulePendingOnCore ⟨coreId.toNat, h⟩ ∨
      (∃ tid st', switchToThreadOnCore st ⟨coreId.toNat, h⟩ tid = .ok st' ∧
        perCoreRescheduleStep st coreId
          = st'.clearReschedulePendingOnCore ⟨coreId.toNat, h⟩) ∨
      perCoreRescheduleStep st coreId
        = (dropCurrentOnCore st ⟨coreId.toNat, h⟩).clearReschedulePendingOnCore
            ⟨coreId.toNat, h⟩ := by
  unfold perCoreRescheduleStep
  rw [dif_pos h]
  unfold handleRescheduleSgiOnCore
  cases hCh : chooseThreadEffectiveOnCore st ⟨coreId.toNat, h⟩ with
  | error e => exact Or.inl rfl
  | ok cand =>
    cases cand with
    | none =>
      simp only
      by_cases hDrop : currentOutsideActiveDomainOnCore st ⟨coreId.toNat, h⟩ = true
      · rw [if_pos hDrop]; exact Or.inr (Or.inr (Or.inr rfl))
      · rw [if_neg hDrop]; exact Or.inr (Or.inl rfl)
    | some tid =>
      simp only
      by_cases hOut : (currentOutsideActiveDomainOnCore st ⟨coreId.toNat, h⟩ ||
          candidateOutranksCurrentOnCore st ⟨coreId.toNat, h⟩ tid) = true
      · rw [if_pos hOut]
        cases hSw : switchToThreadOnCore st ⟨coreId.toNat, h⟩ tid with
        | error e => exact Or.inl rfl
        | ok st' => exact Or.inr (Or.inr (Or.inl ⟨tid, st', hSw, rfl⟩))
      · rw [if_neg hOut]; exact Or.inr (Or.inl rfl)

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
    footprintCoversWrites
      ⟨handleRescheduleSgiOnCoreLockSet ⟨coreId.toNat, h⟩,
        switchToThreadOnCoreLockSet_keys_nodup _⟩
      st (perCoreRescheduleStep st coreId) := by
  rcases perCoreRescheduleStep_id_or_switch st coreId h with
    hId | hClr | ⟨tid, st', hSw, hEq⟩ | hDrop
  · rw [hId]; exact footprintCoversWrites_refl _ _
  · rw [hClr]; exact footprintCoversWrites_clearReschedulePendingOnCore _ _ _
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
  · rw [hDrop]
    refine ⟨?_, ?_, ?_⟩
    · intro hNot
      exact absurd (List.mem_cons_self) hNot
    · intro d hNot
      have hne : d ≠ ⟨coreId.toNat, h⟩ := fun hEqCore =>
        hNot ((mem_handleRescheduleSgiOnCoreLockSet_runQueue_iff _ d).mpr hEqCore)
      refine ⟨?_, ?_, ?_⟩
      · simp only [SystemState.clearReschedulePendingOnCore_scheduler,
          SchedulerState.clearReschedulePendingOnCore_runQueueOnCore,
          dropCurrentOnCore_runQueueOnCore]
        exact preemptCurrentOnCore_runQueueOnCore_ne st _ _ d (fun hc => hne hc.symm)
      · simp only [SystemState.clearReschedulePendingOnCore_scheduler,
          SchedulerState.clearReschedulePendingOnCore_currentOnCore]
        exact dropCurrentOnCore_currentOnCore_ne st _ d (fun hc => hne hc.symm)
      · simp [dropCurrentOnCore, preemptCurrentOnCore_activeDomainOnCore]
    · intro d _
      simp

end SeLe4n.Kernel
