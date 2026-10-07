-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- WS-RR RR7.39 / WS-LS LS2.2: PRODUCTION.  The declared footprints, their
-- write-set containment and the `BracketSpec`s the three live per-core
-- scheduler entries run.  `SeLe4n/Kernel/PerCoreTimerEntry.lean`,
-- `PerCoreRescheduleEntry.lean` and `SecondaryEntry.lean` are the consumers.
-- The timer tick's containment chain (`PerCoreCbs`,
-- `PerCoreTickCbsPreservation`) entered the production closure with it at
-- LS2.2: a bracket record cannot be built without its coverage proof, and the
-- record is what the entry runs.

import SeLe4n.Kernel.Scheduler.Operations.PerCoreChooseThread
import SeLe4n.Kernel.Concurrency.Locks.BracketSpec
import SeLe4n.Kernel.Concurrency.Runtime
import SeLe4n.Kernel.Scheduler.Operations.PerCoreRunLoop
import SeLe4n.Kernel.Scheduler.Operations.PerCoreTickCbsPreservation

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

A `BracketSpec` per seam (§6): the declared footprint, the step, and the proof
that the footprint covers the step's writes, as one record.  The entry runs
`BracketSpec.run`, which is the step and nothing else — since WS-LS LS2.2 the
growing and shrinking phases live on the ghost lock table
(`Concurrency/Locks/BracketSpec.lean`), where `runGhost_kernel` says the
executed path is the kernel projection of the proven one.  The former
revalidating bracket (`runBracketed`) still runs at the two syscall seams
until their seam-level coverage lands (plan rows LS2.3 and LS2.4).

## 3.  The write-set containment

A declared footprint that does not cover a write is a *false* footprint, and the
2PL argument would then rest on exclusion the runtime never established.
`footprintCoversWrites` states the obligation as data — for every lock the
footprint does **not** name, the state it guards is unchanged — and §4–§5 discharge
it for both live steps (§4 the reschedule step, §5 the timer tick, the latter
moved here from the former `Scheduler/Operations/SchedLockTimerContainment.lean`
at LS2.2 so that the record and its proof field sit in one module).

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
  coreIdOfUInt64? LockKey LockSet BracketSpec)

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

-- ============================================================================
-- §5  The timer step's writes are inside its footprint
-- ============================================================================
-- Moved from `Scheduler/Operations/SchedLockTimerContainment.lean` at **WS-LS
-- LS2.2**.  `timerTickOnCoreCompleteLockSet c` names the object-store table
-- write lock, **every** core's run-queue write lock, and core `c`'s
-- replenish-queue write lock, so `footprintCoversWrites` has content in exactly
-- one clause: no core's replenish queue other than `c`'s may move.  The chain,
-- one link per composed transition: `tickClockedState` writes `machine` only;
-- `setLastTimeoutErrorsOnCore` writes a diagnostic slot;
-- `processReplenishmentsDueOnCore` pops core `c`'s queue and its wakes touch
-- only run queues; `timerTickBudgetOnCore` inserts through
-- `replenishOnCore … c`; `scheduleEffectiveOnCore`, `handleRescheduleSgiOnCore`
-- and `scheduleDomainOnCore` frame every replenish queue.

/-- **WS-RR RR7.39 (frame)**: `timerTickOnCore` writes no replenish queue but its
own core's.

Every arm is a composition of transitions that either frame every replenish queue
or write core `c`'s slot; the `hne` hypothesis discharges the latter. -/
theorem timerTickOnCore_replenishQueueOnCore_ne (st : SystemState) (c : CoreId)
    (res : SystemState × List (CoreId × SgiKind)) (c' : CoreId) (hne : c ≠ c')
    (hTick : timerTickOnCore st c = .ok res) :
    res.1.scheduler.replenishQueueOnCore c' = st.scheduler.replenishQueueOnCore c' := by
  rw [timerTickOnCore_eq_prepared] at hTick
  -- the prepared state — the diagnostic clear composed with the drain — frames `c'`
  have hPrep : (timerTickOnCorePrepared st c).1.scheduler.replenishQueueOnCore c'
      = st.scheduler.replenishQueueOnCore c' := by
    simp only [timerTickOnCorePrepared]
    rw [processReplenishmentsDueOnCore_replenishQueueOnCore_ne _ c _ c' hne]
    simp [SchedulerState.setLastTimeoutErrorsOnCore_replenishQueueOnCore]
  split at hTick
  · -- idle core: either the local-wake reschedule, or the prepared state verbatim
    split at hTick
    · split at hTick
      · simp at hTick
      · rename_i st2 hSgi
        simp only [Except.ok.injEq] at hTick
        subst hTick
        rw [show ((st2, (timerTickOnCorePrepared st c).2.1) :
          SystemState × List (CoreId × SgiKind)).1 = st2 from rfl,
          handleRescheduleSgiOnCore_replenishQueueOnCore _ c st2 c' hSgi, hPrep]
    · simp only [Except.ok.injEq] at hTick
      subst hTick
      exact hPrep
  · -- a current thread: the budget charge, then at most one re-dispatch
    split at hTick
    · simp at hTick
    · rename_i st3 preempted timeoutSgis hBudget
      obtain ⟨tcb, hTcb, hBudget⟩ := timerTickChargeCurrentOnCore_ok hBudget
      have hSt3 : st3.scheduler.replenishQueueOnCore c'
          = st.scheduler.replenishQueueOnCore c' := by
        rw [timerTickBudgetOnCore_replenishQueueOnCore_ne _ c _ tcb st3 preempted c' hne
          hBudget, hPrep]
      split at hTick
      · split at hTick
        · simp at hTick
        · rename_i st4 hSched
          simp only [Except.ok.injEq] at hTick
          subst hTick
          rw [show ((st4, (timerTickOnCorePrepared st c).2.1 ++ timeoutSgis) :
            SystemState × List (CoreId × SgiKind)).1 = st4 from rfl,
            scheduleEffectiveOnCore_replenishQueueOnCore st3 c st4 c' hSched, hSt3]
      · split at hTick
        · split at hTick
          · simp at hTick
          · rename_i st4 hSgi
            simp only [Except.ok.injEq] at hTick
            subst hTick
            rw [show ((st4, (timerTickOnCorePrepared st c).2.1 ++ timeoutSgis) :
              SystemState × List (CoreId × SgiKind)).1 = st4 from rfl,
              handleRescheduleSgiOnCore_replenishQueueOnCore st3 c st4 c' hSgi, hSt3]
        · simp only [Except.ok.injEq] at hTick
          subst hTick
          exact hSt3

/-- **WS-RR RR7.39 (frame)**: the run-loop step writes no replenish queue but its
own core's — the tick's frame carried through the fail-closed core decode and the
domain transition. -/
theorem perCoreTimerTickStep_replenishQueueOnCore_ne (st : SystemState) (coreId : UInt64)
    (c' : CoreId) (h : coreId.toNat < numCores)
    (hne : (⟨coreId.toNat, h⟩ : CoreId) ≠ c') :
    (perCoreTimerTickStep st coreId).1.scheduler.replenishQueueOnCore c'
      = st.scheduler.replenishQueueOnCore c' := by
  unfold perCoreTimerTickStep
  rw [dif_pos h]
  cases hTick : timerTickOnCore (tickClockedState st ⟨coreId.toNat, h⟩) ⟨coreId.toNat, h⟩ with
  | error e => rfl
  | ok res =>
    simp only
    cases hDom : scheduleDomainOnCore res.1 ⟨coreId.toNat, h⟩ with
    | error e => rfl
    | ok st2 =>
      simp only
      rw [scheduleDomainOnCore_replenishQueueOnCore res.1 _ st2 c' hDom,
        timerTickOnCore_replenishQueueOnCore_ne _ _ res c' hne hTick,
        tickClockedState_scheduler]

/-- **WS-RR RR7.39 (the payoff for the timer seam)**: the verified tick step's
writes are inside the footprint the entry declares.

Two of the three clauses are vacuous by the footprint's own width — it names the
object-store table lock and every core's run-queue lock — and the third is
`perCoreTimerTickStep_replenishQueueOnCore_ne`.  So the footprint the bracket
acquires is not a *false* footprint. -/
theorem perCoreTimerTickStep_coversWrites (st : SystemState) (coreId : UInt64)
    (h : coreId.toNat < numCores) :
    footprintCoversWrites
      ⟨timerTickOnCoreCompleteLockSet ⟨coreId.toNat, h⟩,
        timerTickOnCoreCompleteLockSet_keys_nodup _⟩
      st (perCoreTimerTickStep st coreId).1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro hNot
    exact absurd List.mem_cons_self hNot
  · intro d hNot
    exact absurd
      (List.mem_cons_of_mem _ (List.mem_append_left _ (mem_allCoreRunQueueLockSegment d))) hNot
  · intro d hNot
    have hne : (⟨coreId.toNat, h⟩ : CoreId) ≠ d := by
      rintro rfl
      exact hNot (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_singleton.mpr rfl)))
    exact perCoreTimerTickStep_replenishQueueOnCore_ne st coreId d h hne

/-- **WS-RR RR7.39**: the clock-advance-flagged step commits the plain step's
state, so its containment is the plain step's. -/
theorem perCoreTimerTickStepWithClockAdvance_coversWrites (st : SystemState)
    (coreId : UInt64) (h : coreId.toNat < numCores) :
    footprintCoversWrites
      ⟨timerTickOnCoreCompleteLockSet ⟨coreId.toNat, h⟩,
        timerTickOnCoreCompleteLockSet_keys_nodup _⟩
      st (perCoreTimerTickStepWithClockAdvance st coreId).2 :=
  perCoreTimerTickStep_coversWrites st coreId h

-- ============================================================================
-- §6  The brackets: one `BracketSpec` per scheduler seam
-- ============================================================================

/-- **WS-LS LS2.2**: the per-core timer tick's bracket.

The footprint is `declaredLockSetForTimerTick` (§1), the step is the run-loop
step with its clock-advance flag, and the proof field is
`perCoreTimerTickStepWithClockAdvance_coversWrites` (§5) at the footprint the
decode resolves — so the record cannot be built for a footprint the step
writes outside of.  The entry runs `BracketSpec.run`, which is the step and
nothing else; the growing and shrinking phases exist on the ghost table
(`BracketSpec.runGhost`) alone, and `runGhost_kernel` says the executed path
is the kernel projection of the proven one.

No core argument: the executed bracket acquires nothing, so it names no
acquirer.  The former `schedEntryLockCore` fall-back — whose only use was an
acquire the undeclared arm never performed — is gone with the acquire. -/
def timerTickBracket (coreId : UInt64) :
    BracketSpec (List (CoreId × SgiKind) × Bool) where
  declared := declaredLockSetForTimerTick coreId
  step := fun s => perCoreTimerTickStepWithClockAdvance s coreId
  covers := by
    intro st S hS
    by_cases h : coreId.toNat < numCores
    · rw [declaredLockSetForTimerTick_resolves coreId st h] at hS
      rw [← Option.some.inj hS]
      exact perCoreTimerTickStepWithClockAdvance_coversWrites st coreId h
    · rw [declaredLockSetForTimerTick_invalid_core coreId st h] at hS
      cases hS

/-- **WS-LS LS2.2**: the per-core reschedule step's bracket — and, through
`secondaryKernelMain_eq_perCoreRescheduleEntry`, the secondary bring-up
entry's.  The proof field is `perCoreRescheduleStep_coversWrites` (§4). -/
def rescheduleBracket (coreId : UInt64) : BracketSpec Unit where
  declared := declaredLockSetForReschedule coreId
  step := fun s => ((), perCoreRescheduleStep s coreId)
  covers := by
    intro st S hS
    by_cases h : coreId.toNat < numCores
    · rw [declaredLockSetForReschedule_resolves coreId st h] at hS
      rw [← Option.some.inj hS]
      exact perCoreRescheduleStep_coversWrites st coreId h
    · rw [declaredLockSetForReschedule_invalid_core coreId st h] at hS
      cases hS

/-- **WS-LS LS2.2**: what the timer entry executes is the verified step —
`rfl`, because `BracketSpec.run` is the step.  The old bracket's three arms
(undeclared / committed / refused) are gone with the lock words it wrote;
`timerTickUnderDeclaredLockSet_invalid_core` and the refused-value negative
are subsumed by this equation holding on every core id. -/
theorem timerTickBracket_run (coreId : UInt64) (st : SystemState) :
    (timerTickBracket coreId).run st = perCoreTimerTickStepWithClockAdvance st coreId := rfl

/-- **WS-LS LS2.2**: likewise for the reschedule entry. -/
theorem rescheduleBracket_run (coreId : UInt64) (st : SystemState) :
    (rescheduleBracket coreId).run st = ((), perCoreRescheduleStep st coreId) := rfl

/-- **WS-LS LS2.2**: on the proven path a valid core's tick advances the ghost
table by the complete timer footprint and hands it back — the whole trace of
the bracket, with the step's kernel half unchanged by it. -/
theorem timerTickBracket_runGhost_locks (coreId : UInt64) (c : CoreId)
    (s : Concurrency.LockedSystemState) (h : coreId.toNat < numCores) :
    ((timerTickBracket coreId).runGhost c s).2.locks =
      Concurrency.LockState.bracket c
        ⟨timerTickOnCoreCompleteLockSet ⟨coreId.toNat, h⟩,
          timerTickOnCoreCompleteLockSet_keys_nodup _⟩ s.locks := by
  rw [BracketSpec.runGhost_locks]
  show Concurrency.LockState.bracketDeclared c (declaredLockSetForTimerTick coreId s.kernel)
    s.locks = _
  rw [declaredLockSetForTimerTick_resolves coreId s.kernel h,
    Concurrency.LockState.bracketDeclared_some]

/-- **WS-LS LS2.2**: an out-of-range core id declares nothing, so the proven
path leaves the ghost table alone — the fail-closed condition
`perCoreTimerTickStep_invalid_core` reports on the step, read at the table. -/
theorem timerTickBracket_runGhost_locks_invalid_core (coreId : UInt64) (c : CoreId)
    (s : Concurrency.LockedSystemState) (h : ¬ coreId.toNat < numCores) :
    ((timerTickBracket coreId).runGhost c s).2.locks = s.locks := by
  rw [BracketSpec.runGhost_locks]
  show Concurrency.LockState.bracketDeclared c (declaredLockSetForTimerTick coreId s.kernel)
    s.locks = _
  rw [declaredLockSetForTimerTick_invalid_core coreId s.kernel h,
    Concurrency.LockState.bracketDeclared_none]

end SeLe4n.Kernel
