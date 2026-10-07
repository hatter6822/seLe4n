-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/
import SeLe4n.Kernel.Concurrency.Locks.LockState

/-!
# WS-LS LS2.1 — the bracket as a specification over the ghost lock state

`docs/planning/LOCK_STATE_SEPARATION_PLAN.md` §3.2.  A bracketed kernel
transition is a `BracketSpec`: the footprint it declares, the step it runs,
and the proof that the footprint covers every write the step makes.  Its
executed form, `BracketSpec.run`, is the step and nothing else; its proven
form, `BracketSpec.runGhost`, runs the same step beside the ghost lock table
and advances the table by the bracket's lock trace.  The two agree on the
kernel state by `rfl` (`runGhost_kernel`, obligation O1): the executed path
is the kernel projection of the proven one, and no lock word is ever written
into a kernel object on the executed path.

## What is here

* `LockedSystemState` — the kernel state paired with the ghost table.
  Transitions stay typed over `SystemState`; only brackets see the pair.
* `footprintCoversWrites` — what a footprint has to cover, moved here from
  `SchedLockBracket.lean` (where it was `footprintCoversWrites`) because
  it is the obligation every spec carries, scheduler-domain or not.
* `LockState.bracket` / `LockState.bracketDeclared` — the lock trace a
  bracket applies to the table: the growing phase over the sorted footprint,
  the shrinking phase in reverse.  Stated once so `withLockSetGhost` and
  `runGhost` have one answer.
* `withLockSetGhost` — the ghost form of `withLockSet`: the same shape with
  the lock trace applied to the table instead of to the objects.  The
  word-level `withLockSet` stays until LS2.2 switches the seams (it is still
  executed at `SyscallDispatchEntry.lean`'s suspend seam); LS3.1 renames
  this one to `withLockSet` with its anchors.
* `BracketSpec`, `run`, `runGhost`, `runGhost_kernel` (O1),
  `runGhost_locks_of_unheld` (O3), `guard` (O4, Track D's hypothesis).

Nothing executes against the ghost table here: LS2.2 switches the seams.
-/

namespace SeLe4n.Kernel

open SeLe4n
open SeLe4n.Model
open Concurrency

-- ============================================================================
-- §1  What a footprint covers
-- ============================================================================

/-- **WS-RR RR7.39 / RR8.12 Cut C6a** (moved from `SchedLockBracket.lean` by
**WS-LS LS2.1**): what *covering* means — the frame condition a declared
footprint carries.  For every lock the footprint does **not** name, the state
that lock guards is unchanged.

Quantified over every core rather than over the cores the author had in mind,
so an under-declared footprint makes the statement false rather than vacuous —
the same shape as `preservesFieldsOutside` (RR7.19), which is what turned six
`_modifiedFields` comments into six proof obligations and immediately found
two omissions.

The three clauses partition the state the brackets guard: the object store,
core `d`'s scheduling slots under its run-queue lock, and core `d`'s
replenishment queue under its replenish-queue lock.

The object clause is stated at **two** granularities because footprints come
at two.  A scheduler entry declares the object-store *table* write lock, which
covers every key at once; the RR7.40 PIP chain declares each visited thread's
own `.tcb` lock instead, and nothing table-wide.  So the clause is discharged
by either — the table lock present makes it vacuous, and otherwise every key
whose own lock is absent must be unchanged.  Writing it as
`st'.objects = st.objects` under the table lock alone (its RR7.39 form) would
have been *false* of a per-object footprint rather than merely silent about
it, so the generalisation is what lets one predicate serve both and keeps
"what does covering mean" a single question.

Every `BracketSpec` carries this as its `covers` field; the object-domain
members' by-membership statements (`LockSetForSyscall.lean`) are lemmas
feeding it. -/
def footprintCoversWrites (S : LockSet) (st st' : SystemState) : Prop :=
  ((LockKey.objStore, AccessMode.write) ∉ S.pairs →
      ∀ oid : SeLe4n.ObjId,
        (LockKey.object ⟨Concurrency.LockKind.tcb, oid⟩, AccessMode.write) ∉ S.pairs →
        st'.objects[oid]? = st.objects[oid]?) ∧
  (∀ d : CoreId, (LockKey.runQueue d, AccessMode.write) ∉ S.pairs →
      st'.scheduler.runQueueOnCore d = st.scheduler.runQueueOnCore d ∧
      st'.scheduler.currentOnCore d = st.scheduler.currentOnCore d ∧
      st'.scheduler.activeDomainOnCore d = st.scheduler.activeDomainOnCore d) ∧
  (∀ d : CoreId, (LockKey.replenishQueue d, AccessMode.write) ∉ S.pairs →
      st'.scheduler.replenishQueueOnCore d = st.scheduler.replenishQueueOnCore d)

/-- **WS-RR RR7.39**: a footprint covers a step that changes nothing. -/
theorem footprintCoversWrites_refl (S : LockSet) (st : SystemState) :
    footprintCoversWrites S st st :=
  ⟨fun _ _ _ => rfl, fun _ _ => ⟨rfl, rfl, rfl⟩, fun _ _ => rfl⟩

/-- A footprint covers a step that writes only a core's reschedule-pending flag
(the KSC-1 accumulator): no clause of the coverage reads it. -/
theorem footprintCoversWrites_clearReschedulePendingOnCore (S : LockSet)
    (st : SystemState) (c : CoreId) :
    footprintCoversWrites S st (st.clearReschedulePendingOnCore c) :=
  ⟨fun _ _ _ => rfl, fun _ _ => ⟨rfl, rfl, rfl⟩, fun _ _ => rfl⟩

/-- **WS-RR RR8.12 Cut C6h**: coverage is MONOTONE in the footprint.

A footprint that names more locks covers at least what a smaller one covers,
because every clause of `footprintCoversWrites` is of the form *"a lock the
footprint does **not** name guards state the step did not change"* — so
widening the footprint only ever discharges more of those antecedents.

This is what lets a per-arm coverage theorem, stated over the arm's own
scheduler footprint, reach the **unified** footprint the syscall seam actually
acquires (`unifiedLockSetForSyscall`, which merges the object domain's members
in).  Without it the family would have to be restated at the unified
footprint, which is one question with two answers.  **WS-LS LS1.2**: the
inclusion is over the **write** members, because a merge keeps a write a write
but may raise a read, and the write members are all the predicate reads.

Over-declaring is the safe direction for coverage and **not** free in general:
lock contention is an observable channel (SM8.D's CC-5), which is why the
footprints themselves are narrowed per arm rather than widened to `allCores`.
What this theorem says is only that the *proof obligation* travels upward, not
that a wider footprint is a better one. -/
theorem footprintCoversWrites_mono (S U : LockSet) (st st' : SystemState)
    (hSub : ∀ l, (l, AccessMode.write) ∈ S.pairs → (l, AccessMode.write) ∈ U.pairs)
    (h : footprintCoversWrites S st st') :
    footprintCoversWrites U st st' := by
  obtain ⟨hObj, hRun, hRepl⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro hTable oid hTcb
    exact hObj (fun hMem => hTable (hSub _ hMem)) oid (fun hMem => hTcb (hSub _ hMem))
  · intro d hd
    exact hRun d (fun hMem => hd (hSub _ hMem))
  · intro d hd
    exact hRepl d (fun hMem => hd (hSub _ hMem))

namespace Concurrency

-- ============================================================================
-- §2  The pair, and the lock trace a bracket applies
-- ============================================================================

/-- **WS-LS LS2.1**: the kernel state beside the ghost lock table.

Transitions stay typed over `SystemState`; a bracket is the only thing that
sees both halves, and it changes `locks` by the bracket's trace and `kernel`
by its step.  After LS3 nothing typed over `SystemState` can name a lock word,
because none exists there. -/
structure LockedSystemState where
  /-- The kernel state the transitions are typed over. -/
  kernel : SystemState
  /-- The ghost lock table (`LockState`): one `RwLockState` per key. -/
  locks  : LockState

namespace LockState

/-- The lock trace one bracket over footprint `S` applies in core `c`'s name:
the growing phase over the sorted acquisition sequence, then the shrinking
phase (withdraw, then release) over its reverse.  `withLockSetGhost` and
`BracketSpec.runGhost` both advance the table by exactly this, so "what does a
bracket do to the locks" has one answer. -/
def bracket (c : CoreId) (S : LockSet) (L : LockState) : LockState :=
  unwindAll c S.lockAcquireSequence.reverse (acquireAll c S.lockAcquireSequence L)

/-- The trace a bracket applies given what it declared: nothing when nothing
was declared, `bracket` otherwise. -/
def bracketDeclared (c : CoreId) : Option LockSet → LockState → LockState
  | none,   L => L
  | some S, L => bracket c S L

@[simp] theorem bracketDeclared_none (c : CoreId) (L : LockState) :
    bracketDeclared c none L = L := rfl

@[simp] theorem bracketDeclared_some (c : CoreId) (S : LockSet) (L : LockState) :
    bracketDeclared c (some S) L = bracket c S L := rfl

/-- The empty footprint's bracket leaves the table alone. -/
@[simp] theorem bracket_empty (c : CoreId) (L : LockState) :
    bracket c LockSet.empty L = L := by
  simp [bracket, LockSet.lockAcquireSequence_empty, acquireAll, unwindAll, cancelAll,
    releaseAll]

/-- **WS-LS LS2.1 (obligation O3, second half, at the footprint)**: a bracket
from the all-free table returns to the all-free table.  `LockSet`'s own
key-uniqueness witness supplies the `Nodup` the LS1.1 round trip needs, so
nothing about the footprint has to be assumed. -/
theorem bracket_unheld (c : CoreId) (S : LockSet) : bracket c S unheld = unheld :=
  acquireAll_unwindAll_unheld c S.lockAcquireSequence
    (Concurrency.lockAcquireSequence_nodup_keys S.pairs S.hUniqueKeys)

/-- `bracketDeclared` from the all-free table returns to it, declared or not. -/
theorem bracketDeclared_unheld (c : CoreId) (d : Option LockSet) :
    bracketDeclared c d unheld = unheld := by
  cases d with
  | none => rfl
  | some S => exact bracket_unheld c S

/-- **WS-LS LS2.1 (obligation O3, first half, at the footprint)**: from the
all-free table the growing phase holds every declared member at its declared
mode — the ghost `acquireAll_establishes_lockSetHeld`, with no object-presence
hypothesis because a ghost lock exists for every key. -/
theorem acquireAll_unheld_heldAll_pairs (c : CoreId) (S : LockSet) :
    (acquireAll c S.lockAcquireSequence unheld).heldAll c S.pairs := by
  intro p hp
  exact acquireAll_unheld_held c S.lockAcquireSequence
    (Concurrency.lockAcquireSequence_nodup_keys S.pairs S.hUniqueKeys) p
    ((Concurrency.mem_lockAcquireSequence S.pairs p).mpr hp)

end LockState

-- ============================================================================
-- §3  `withLockSet` over the pair
-- ============================================================================

/-- **WS-LS LS2.1**: the ghost form of `withLockSet` — the same three-phase
shape, with the lock trace applied to the ghost table instead of to the
objects.  The action runs on `s.kernel`: the growing phase changes only
`locks`, by type, which is the fact the word-level bracket's re-resolution
guarded by computation.

The word-level `withLockSet` stays beside this until LS2.2 switches the seams
(the suspend seam still executes it); LS3.1 renames this one to `withLockSet`
with its anchors.  Every theorem the 2PL, serializability and observer files
state over the word-level bracket is restated over this one in LS2.1, with
the lock-write-invisibility hypotheses gone: here the kernel half of the
result *is* the action's, by `rfl`. -/
def withLockSetGhost {α : Type} (S : LockSet) (core : CoreId)
    (action : SystemState → SystemState × α) (s : LockedSystemState) :
    LockedSystemState × α :=
  let (postAction, result) := action s.kernel
  (⟨postAction, LockState.bracket core S s.locks⟩, result)

/-- The result of `withLockSetGhost`, decomposed: the action's kernel state,
the bracket's lock trace, the action's value. -/
theorem withLockSetGhost_eq_decomposition {α : Type} (S : LockSet) (core : CoreId)
    (action : SystemState → SystemState × α) (s : LockedSystemState) :
    withLockSetGhost S core action s =
      (⟨(action s.kernel).1, LockState.bracket core S s.locks⟩, (action s.kernel).2) := rfl

/-- The kernel half of the bracket's result is the action's. -/
@[simp] theorem withLockSetGhost_fst_kernel {α : Type} (S : LockSet) (core : CoreId)
    (action : SystemState → SystemState × α) (s : LockedSystemState) :
    (withLockSetGhost S core action s).1.kernel = (action s.kernel).1 := rfl

/-- The lock half of the bracket's result is the bracket's trace, whatever the
action did. -/
@[simp] theorem withLockSetGhost_fst_locks {α : Type} (S : LockSet) (core : CoreId)
    (action : SystemState → SystemState × α) (s : LockedSystemState) :
    (withLockSetGhost S core action s).1.locks = LockState.bracket core S s.locks := rfl

/-- The value the bracket returns is the action's. -/
@[simp] theorem withLockSetGhost_snd {α : Type} (S : LockSet) (core : CoreId)
    (action : SystemState → SystemState × α) (s : LockedSystemState) :
    (withLockSetGhost S core action s).2 = (action s.kernel).2 := rfl

/-- WS-SM SM3.C.1 over the pair: the empty footprint's bracket is the action
on the kernel half with the table untouched. -/
@[simp] theorem withLockSetGhost_empty {α : Type} (core : CoreId)
    (action : SystemState → SystemState × α) (s : LockedSystemState) :
    withLockSetGhost LockSet.empty core action s =
      (⟨(action s.kernel).1, s.locks⟩, (action s.kernel).2) := by
  rw [withLockSetGhost_eq_decomposition, LockState.bracket_empty]

/-- **O3 at `withLockSetGhost`**: from the all-free table a bracket returns
to the all-free table. -/
theorem withLockSetGhost_locks_of_unheld {α : Type} (S : LockSet) (core : CoreId)
    (action : SystemState → SystemState × α) (s : LockedSystemState)
    (hL : s.locks = LockState.unheld) :
    (withLockSetGhost S core action s).1.locks = LockState.unheld := by
  rw [withLockSetGhost_fst_locks, hL, LockState.bracket_unheld]

-- ============================================================================
-- §4  The bracket specification
-- ============================================================================

/-- **WS-LS LS2.1**: a bracketed kernel transition — what it declares, what it
does, and the proof that the declaration covers the doing.

`declared` resolves the footprint from the pre-state (`none` when the entry
declares nothing, which the executed path runs unbracketed and the ghost path
runs with the table untouched); `step` is the transition; `covers` is the
obligation every seam's spec discharges with its own coverage theorem
(`unifiedLockSetForSyscall_coversWrites`, `perCoreTimerTickStep_coversWrites`,
`perCoreRescheduleStep_coversWrites`, the suspend frames).  LS2.2 builds one
per committing seam and points the exported bodies at `run`. -/
structure BracketSpec (α : Type) where
  /-- The footprint the entry declares for a pre-state, if any. -/
  declared : SystemState → Option LockSet
  /-- The transition. -/
  step     : SystemState → α × SystemState
  /-- The declared footprint covers every write the step makes. -/
  covers   : ∀ st S, declared st = some S → footprintCoversWrites S st (step st).2

namespace BracketSpec

variable {α : Type}

/-- The executed bracket: the step, and nothing else.  No lock word exists on
this path to be written; exclusion is the HAL's (Track D), under the guard
`BracketSpec.guard` states. -/
@[inline] def run (b : BracketSpec α) : SystemState → α × SystemState := b.step

/-- The proven bracket: the same step beside the ghost table, which advances
by the bracket's lock trace (`LockState.bracketDeclared`).  The trace sits in
the `locks` field alone, so the kernel projection is the step by `rfl`. -/
def runGhost (b : BracketSpec α) (c : CoreId) (s : LockedSystemState) :
    α × LockedSystemState :=
  let (v, k) := b.step s.kernel
  (v, ⟨k, LockState.bracketDeclared c (b.declared s.kernel) s.locks⟩)

/-- **Obligation O1**: the executed path is the kernel projection of the
proven one.  `rfl`. -/
theorem runGhost_kernel (b : BracketSpec α) (c : CoreId) (s : LockedSystemState) :
    (b.runGhost c s).2.kernel = (b.run s.kernel).2 := rfl

/-- The value the proven bracket returns is the executed one's.  `rfl`. -/
theorem runGhost_fst (b : BracketSpec α) (c : CoreId) (s : LockedSystemState) :
    (b.runGhost c s).1 = (b.run s.kernel).1 := rfl

/-- The lock half of the proven bracket's result is the declared trace. -/
theorem runGhost_locks (b : BracketSpec α) (c : CoreId) (s : LockedSystemState) :
    (b.runGhost c s).2.locks = LockState.bracketDeclared c (b.declared s.kernel) s.locks := rfl

/-- An undeclared entry leaves the table alone. -/
theorem runGhost_undeclared (b : BracketSpec α) (c : CoreId) (s : LockedSystemState)
    (h : b.declared s.kernel = none) :
    b.runGhost c s = ((b.step s.kernel).1, ⟨(b.step s.kernel).2, s.locks⟩) := by
  show ((b.step s.kernel).1, (⟨(b.step s.kernel).2,
    LockState.bracketDeclared c (b.declared s.kernel) s.locks⟩ : LockedSystemState)) = _
  rw [h, LockState.bracketDeclared_none]

/-- A declared entry advances the table by its footprint's bracket. -/
theorem runGhost_declared (b : BracketSpec α) (c : CoreId) (s : LockedSystemState)
    (S : LockSet) (h : b.declared s.kernel = some S) :
    b.runGhost c s =
      ((b.step s.kernel).1, ⟨(b.step s.kernel).2, LockState.bracket c S s.locks⟩) := by
  show ((b.step s.kernel).1, (⟨(b.step s.kernel).2,
    LockState.bracketDeclared c (b.declared s.kernel) s.locks⟩ : LockedSystemState)) = _
  rw [h, LockState.bracketDeclared_some]

/-- A declared entry's proven bracket is `withLockSetGhost` at its footprint,
up to the order of the pair: `withLockSet` is `runGhost` of a spec whose
`declared` is constant. -/
theorem runGhost_eq_withLockSetGhost (b : BracketSpec α) (c : CoreId) (s : LockedSystemState)
    (S : LockSet) (h : b.declared s.kernel = some S) :
    b.runGhost c s =
      ((withLockSetGhost S c (fun st => ((b.step st).2, (b.step st).1)) s).2,
       (withLockSetGhost S c (fun st => ((b.step st).2, (b.step st).1)) s).1) := by
  rw [runGhost_declared b c s S h]
  rfl

/-- **Obligation O3**: under the entry lock every table starts all-free and
ends all-free — the refusal arm's replacement.  The step ran with every
declared member held (`guard_of_unheld`). -/
theorem runGhost_locks_of_unheld (b : BracketSpec α) (c : CoreId) (s : LockedSystemState)
    (hL : s.locks = LockState.unheld) :
    (b.runGhost c s).2.locks = LockState.unheld := by
  rw [runGhost_locks, hL, LockState.bracketDeclared_unheld]

/-- The spec's coverage, read at the executed path. -/
theorem run_covers (b : BracketSpec α) (st : SystemState) (S : LockSet)
    (h : b.declared st = some S) :
    footprintCoversWrites S st (b.run st).2 :=
  b.covers st S h

end BracketSpec

-- ============================================================================
-- §5  The guard (obligation O4): what Track D must establish
-- ============================================================================

/-- An acquire on a lock another core holds for writing is enqueued, not
granted — the per-key fact behind `BracketSpec.not_guard_of_contended`.  The
acquirer must not already be a reader, because `coreHolds c .read` admits a
reader beside a writer (a state `wf` excludes but the lemma does not assume). -/
theorem RwLockState.acquire_not_grants_of_writerHeld (s : RwLockState) (c holder : CoreId)
    (m : AccessMode) (hNe : holder ≠ c) (hW : s.writerHeld = some holder)
    (hR : c ∉ s.readers) :
    ¬ (s.applyOp (m.toAcquireOp c)).coreHolds c m := by
  have hWc : s.writerHeld ≠ some c := by
    rw [hW]; intro h; exact hNe (Option.some.inj h)
  have hSome : s.writerHeld.isSome = true := by rw [hW]; rfl
  cases m with
  | read =>
    show ¬ (s.applyOp (.tryAcquireRead c)).coreHolds c .read
    simp only [RwLockState.applyOp, RwLockState.coreHolds]
    by_cases hInv : s.coreInvolved c
    · rw [if_pos hInv]
      intro h
      rcases h with h | h
      · exact hR h
      · exact hWc h
    · rw [if_neg hInv, if_pos (Or.inl hSome)]
      intro h
      rcases h with h | h
      · exact hR h
      · exact hWc h
  | write =>
    show ¬ (s.applyOp (.tryAcquireWrite c)).coreHolds c .write
    simp only [RwLockState.applyOp, RwLockState.coreHolds]
    by_cases hInv : s.coreInvolved c
    · rw [if_pos hInv]; exact hWc
    · rw [if_neg hInv, if_pos (Or.inl hSome)]; exact hWc

namespace BracketSpec

variable {α : Type}

/-- **Obligation O4 — the ghost bracket's guard.**  When the entry declares a
footprint, the growing phase holds every member at its declared mode when
the step runs.  This is what the HAL's resolve–acquire–re-resolve loop must
establish (Track D); stated once here, consumed by no kernel code, and
discharged under the entry lock by `guard_of_unheld`.  Vacuous for an
undeclared entry, which runs no bracket. -/
def guard (b : BracketSpec α) (c : CoreId) (s : LockedSystemState) : Prop :=
  ∀ S, b.declared s.kernel = some S →
    (LockState.acquireAll c S.lockAcquireSequence s.locks).heldAll c S.pairs

/-- **O3 meets O4**: from the all-free table the guard holds — under the
entry lock, every bracket runs its step held. -/
theorem guard_of_unheld (b : BracketSpec α) (c : CoreId) (s : LockedSystemState)
    (hL : s.locks = LockState.unheld) : b.guard c s := by
  intro S _
  rw [hL]
  exact LockState.acquireAll_unheld_heldAll_pairs c S

/-- **The load-bearing negative** (SM8.D.5's
`lockSetAcquiredState_does_not_grant_when_contended`, at the ghost table):
when another core holds a declared member for writing, the growing phase
enqueues the acquirer and the guard is **false** — the proven bracket runs
its step regardless, because a pure total function cannot block, so what
makes the step exclusive is the HAL establishing the guard, not the
bracket.  Stated for any declared mode: a reader is refused beside a writer
as much as a writer is. -/
theorem not_guard_of_contended (b : BracketSpec α) (c holder : CoreId) (s : LockedSystemState)
    (S : LockSet) (k : LockKey) (m : AccessMode)
    (hDecl : b.declared s.kernel = some S) (hMem : (k, m) ∈ S.pairs) (hNe : holder ≠ c)
    (hHeld : s.locks k = { writerHeld := some holder, readers := [], waiters := [] }) :
    ¬ b.guard c s := by
  intro hGuard
  have hOne := hGuard S hDecl (k, m) hMem
  change ((LockState.acquireAll c S.lockAcquireSequence s.locks) k).coreHolds c m at hOne
  unfold LockSet.lockAcquireSequence at hOne
  rw [LockState.acquireAll_eq_applySeq, LockState.applySeq_key,
    LockState.keyOps_acquireOps_of_nodup c
      (Concurrency.lockAcquireSequence_nodup_keys S.pairs S.hUniqueKeys)
      ((Concurrency.mem_lockAcquireSequence S.pairs (k, m)).mpr hMem),
    List.foldl_cons, List.foldl_nil, hHeld] at hOne
  exact RwLockState.acquire_not_grants_of_writerHeld _ c holder m hNe rfl
    (List.not_mem_nil) hOne

end BracketSpec

end Concurrency

end SeLe4n.Kernel
