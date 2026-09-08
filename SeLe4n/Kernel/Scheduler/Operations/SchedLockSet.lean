-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- WS-RR RR7.39: PRODUCTION.  The scheduler lock domain's runtime — the
-- primitives that advance the words `SchedLockId` names, the footprint type
-- that carries key-uniqueness, and the `LockBracketDomain` instance the per-core
-- scheduler entries bracket through (`SeLe4n/Kernel/SchedLockBracket.lean`).

import SeLe4n.Kernel.Scheduler.Operations.PerCoreChooseThread
import SeLe4n.Kernel.Concurrency.Locks.LockBracket

/-!
# WS-RR RR7.39 — the scheduler lock domain, with a runtime

SM5.A.2 gave the per-core scheduler its cross-domain lock identifier —
`SchedLockId`, totally ordered `object < runQueue < replenishQueue` — and SM5.B
through SM5.G declared a footprint over it for every per-core transition.  What
none of that had was a **runtime**: `LockSet`'s primitives route `.objStore` to
`SystemState.objStoreLock` and a modeled kind to the object's own `lock` field,
and neither is a per-core scheduler word, because no such word existed.  A
bracket over `chooseThreadOnCoreLockSet` could sort the list, walk it, and change
nothing.

`SystemState.schedulerLocks` (RR7.39) is the state half; this module is the
operational half.  Three pieces:

## 1.  The primitives

`schedAcquireLock` / `schedReleaseLock` / `schedCancelLock` dispatch on the
`SchedLockId` constructor.  The `.object` arm **calls SM3.C's own primitive**
rather than re-deriving what acquiring an object lock does: that question has one
answer, `acquireLockOnObject`, and a second implementation here would be free to
disagree with it about the fail-closed kind check, the `.page` no-op, or the
table-lock singleton.  The two scheduler arms advance the per-core words through
the framing setters, so an acquisition is visible in exactly one lock word.

## 2.  The footprint type

`SchedLockSet` mirrors `LockSet` field for field: a list of
`(SchedLockId × AccessMode)` pairs carrying `Nodup` on the projected keys.  The
invariant is not decoration — a footprint that named the same lock twice would
have the growing phase acquire it twice, and a read-acquire counted twice is a
reader the shrinking phase never removes.  The declared model footprints are all
duplicate-free by construction, and `ofList?` is the fail-closed constructor that
*checks*: a list it cannot accept yields `none`, hence no footprint, hence the
bracket's undeclared fallback, which is always sound.

## 3.  The domain instance

`schedulerLockBracketDomain` is the `LockBracketDomain` the RR7.39 bracket runs.
It supplies five primitives and no more; the acquire / re-resolve / refuse /
commit / unwind discipline itself is `runBracketed`, shared with the ABI seam.

## What this does *not* claim

Nothing here says a transition's writes stay inside its footprint — that is a
statement about the *transition*, proved where the transition lives
(`SeLe4n/Kernel/SchedLockBracket.lean` §4 for the three live entries).  And as at
the ABI seam, the granularity that matters for concurrency is still the
granularity of the commit, which `Platform.FFI.modifyGetKernelState` keeps
global.  What this buys is the model-level property the SM5 footprints were
always about: the transition the kernel runs runs inside its declared footprint.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (numCores CoreId bootCoreId AccessMode RwLockState
  LockBracketDomain acquireLockOnObject releaseLockOnObject cancelLockOnObject
  lockHeld)

-- ============================================================================
-- §1  The per-lock primitives
-- ============================================================================

/-- **WS-RR RR7.39**: advance the word a `SchedLockId` names by an acquire of
`mode` on behalf of `core`.

The `.object` arm is SM3.C's `acquireLockOnObject` verbatim — including its
fail-closed kind check and its `.page` no-op — because "what does acquiring an
object lock do" is a question the object domain already answers, and answering
it twice is how two answers drift.  The two scheduler arms advance the per-core
word through the framing setter, so nothing else in the state moves. -/
def schedAcquireLock (s : SystemState) (core : CoreId) (l : SchedLockId)
    (mode : AccessMode) : SystemState :=
  match l with
  | .object lid => acquireLockOnObject s core lid mode
  | .runQueue r =>
      s.setRunQueueLockOnCore r.core
        ((s.runQueueLockOnCore r.core).applyOp (mode.toAcquireOp core))
  | .replenishQueue r =>
      s.setReplenishQueueLockOnCore r.core
        ((s.replenishQueueLockOnCore r.core).applyOp (mode.toAcquireOp core))

/-- **WS-RR RR7.39**: the release primitive — symmetric to `schedAcquireLock`,
routing the object arm to SM3.C's own release. -/
def schedReleaseLock (s : SystemState) (core : CoreId) (l : SchedLockId)
    (mode : AccessMode) : SystemState :=
  match l with
  | .object lid => releaseLockOnObject s core lid mode
  | .runQueue r =>
      s.setRunQueueLockOnCore r.core
        ((s.runQueueLockOnCore r.core).applyOp (mode.toReleaseOp core))
  | .replenishQueue r =>
      s.setReplenishQueueLockOnCore r.core
        ((s.replenishQueueLockOnCore r.core).applyOp (mode.toReleaseOp core))

/-- **WS-RR RR7.39**: the **withdrawal** primitive (WS-LC LC4's third sibling).

Withdrawing is what a release cannot do: both release arms guard on holdership
and are the identity for a core that is not a holder, so where the growing phase
found a member contended — `tryAcquire*` enqueues rather than granting — only a
withdrawal removes the request it left behind. -/
def schedCancelLock (s : SystemState) (core : CoreId) (l : SchedLockId)
    (mode : AccessMode) : SystemState :=
  match l with
  | .object lid => cancelLockOnObject s core lid mode
  | .runQueue r =>
      s.setRunQueueLockOnCore r.core
        ((s.runQueueLockOnCore r.core).applyOp (mode.toCancelOp core))
  | .replenishQueue r =>
      s.setReplenishQueueLockOnCore r.core
        ((s.replenishQueueLockOnCore r.core).applyOp (mode.toCancelOp core))

/-- **WS-RR RR7.39**: core `c` holds the lock a `SchedLockId` names, at `mode`.

The `.object` arm is SM3.C.4's `lockHeld` — again, one answer — and the two
scheduler arms read the per-core word through `RwLockState.coreHolds`, the same
predicate the object domain reads. -/
def schedLockHeld (c : CoreId) (l : SchedLockId) (mode : AccessMode)
    (s : SystemState) : Prop :=
  match l with
  | .object lid => lockHeld c lid mode s
  | .runQueue r => (s.runQueueLockOnCore r.core).coreHolds c mode
  | .replenishQueue r => (s.replenishQueueLockOnCore r.core).coreHolds c mode

instance schedLockHeld_decidable (c : CoreId) (l : SchedLockId) (mode : AccessMode)
    (s : SystemState) : Decidable (schedLockHeld c l mode s) := by
  unfold schedLockHeld
  cases l <;> exact inferInstance

/-- **WS-RR RR7.39 (the object arm is the object domain's)**: acquiring a
`.object`-constructed scheduler lock **is** SM3.C's per-object acquire.

Definitional, and stated so a cut that gave the scheduler domain its own object
handling would have to delete this theorem to do it. -/
@[simp] theorem schedAcquireLock_object (s : SystemState) (core : CoreId)
    (lid : Concurrency.LockId) (mode : AccessMode) :
    schedAcquireLock s core (.object lid) mode = acquireLockOnObject s core lid mode := rfl

/-- **WS-RR RR7.39**: the release arm likewise. -/
@[simp] theorem schedReleaseLock_object (s : SystemState) (core : CoreId)
    (lid : Concurrency.LockId) (mode : AccessMode) :
    schedReleaseLock s core (.object lid) mode = releaseLockOnObject s core lid mode := rfl

/-- **WS-RR RR7.39**: the withdrawal arm likewise. -/
@[simp] theorem schedCancelLock_object (s : SystemState) (core : CoreId)
    (lid : Concurrency.LockId) (mode : AccessMode) :
    schedCancelLock s core (.object lid) mode = cancelLockOnObject s core lid mode := rfl

/-- **WS-RR RR7.39**: the held predicate's object arm is SM3.C.4's. -/
@[simp] theorem schedLockHeld_object (c : CoreId) (lid : Concurrency.LockId)
    (mode : AccessMode) (s : SystemState) :
    schedLockHeld c (.object lid) mode s = lockHeld c lid mode s := rfl

-- ============================================================================
-- §2  The folds
-- ============================================================================

/-- **WS-RR RR7.39**: the growing phase — fold `schedAcquireLock` over a
sequence, in the order the caller supplies (which, from a footprint, is
`SchedLockId`-ascending). -/
def schedAcquireAll (core : CoreId) (pairs : List (SchedLockId × AccessMode))
    (s : SystemState) : SystemState :=
  pairs.foldl (init := s) (fun st p => schedAcquireLock st core p.fst p.snd)

/-- **WS-RR RR7.39**: the release half of the shrinking phase. -/
def schedReleaseAll (core : CoreId) (pairs : List (SchedLockId × AccessMode))
    (s : SystemState) : SystemState :=
  pairs.foldl (init := s) (fun st p => schedReleaseLock st core p.fst p.snd)

/-- **WS-RR RR7.39**: the withdrawal half of the shrinking phase. -/
def schedCancelAll (core : CoreId) (pairs : List (SchedLockId × AccessMode))
    (s : SystemState) : SystemState :=
  pairs.foldl (init := s) (fun st p => schedCancelLock st core p.fst p.snd)

/-- **WS-RR RR7.39**: the 2PL **shrinking phase** — withdraw, then release.

Withdraw-then-release, in that order, for WS-LC LC4's reason: the release arms
promote **from** `waiters`, so a core still queued when its own release runs can
be promoted into a holder slot the withdrawal already passed.  Withdrawing first
removes the request before any promotion can see it, and no release arm ever
enqueues, so the payoff needs no distinctness hypothesis on the footprint. -/
def schedUnwindAll (core : CoreId) (pairs : List (SchedLockId × AccessMode))
    (s : SystemState) : SystemState :=
  schedReleaseAll core pairs (schedCancelAll core pairs s)

@[simp] theorem schedAcquireAll_nil (core : CoreId) (s : SystemState) :
    schedAcquireAll core [] s = s := rfl

@[simp] theorem schedReleaseAll_nil (core : CoreId) (s : SystemState) :
    schedReleaseAll core [] s = s := rfl

@[simp] theorem schedCancelAll_nil (core : CoreId) (s : SystemState) :
    schedCancelAll core [] s = s := rfl

@[simp] theorem schedUnwindAll_nil (core : CoreId) (s : SystemState) :
    schedUnwindAll core [] s = s := rfl

@[simp] theorem schedAcquireAll_cons (core : CoreId) (l : SchedLockId) (m : AccessMode)
    (rest : List (SchedLockId × AccessMode)) (s : SystemState) :
    schedAcquireAll core ((l, m) :: rest) s
      = schedAcquireAll core rest (schedAcquireLock s core l m) := rfl

@[simp] theorem schedReleaseAll_cons (core : CoreId) (l : SchedLockId) (m : AccessMode)
    (rest : List (SchedLockId × AccessMode)) (s : SystemState) :
    schedReleaseAll core ((l, m) :: rest) s
      = schedReleaseAll core rest (schedReleaseLock s core l m) := rfl

@[simp] theorem schedCancelAll_cons (core : CoreId) (l : SchedLockId) (m : AccessMode)
    (rest : List (SchedLockId × AccessMode)) (s : SystemState) :
    schedCancelAll core ((l, m) :: rest) s
      = schedCancelAll core rest (schedCancelLock s core l m) := rfl

-- ============================================================================
-- §3  The footprint type
-- ============================================================================

/-- **WS-RR RR7.39**: a scheduler-domain footprint — a list of
`(SchedLockId × AccessMode)` declarations whose projected keys are pairwise
distinct.

Mirrors `LockSet` field for field, and for the same reason: key-uniqueness is
what makes "the growing phase acquires each declared lock once" true.  A
footprint naming one lock twice would have a read-acquire counted twice, leaving
a reader the symmetric shrinking phase never removes — a leak that no
footprint-level theorem about ordering or size would catch.

The `Nodup` witness is a `Prop`, so two `SchedLockSet`s with the same `pairs` are
equal, which is what lets the bracket's revalidation compare re-resolved
footprints by their pairs alone. -/
structure SchedLockSet where
  /-- The declarations, in whatever order the footprint was resolved in.

  **Not** an acquisition order (PR #892 review round 5).  This field's comment
  used to say "in `SchedLockId`-ascending acquisition order", which nothing
  enforced and which one resolver violated: `pipChainVisited` follows
  `blockingServer` down a blocking chain, and a chain descends in `ObjId`
  whenever a higher-numbered thread blocks on a lower-numbered one.  The
  acquisition order is `lockAcquireSequence`, which sorts — the same answer
  `objectLockBracketDomain` gives, rather than a second one that has to be
  maintained by every construction site. -/
  pairs : List (SchedLockId × AccessMode)
  /-- Each `SchedLockId` key appears at most once. -/
  hUniqueKeys : (pairs.map (·.fst)).Nodup

namespace SchedLockSet

instance : Repr SchedLockSet where
  reprPrec s n := reprPrec s.pairs n

instance : DecidableEq SchedLockSet := fun s₁ s₂ =>
  if h : s₁.pairs = s₂.pairs then
    .isTrue (by
      obtain ⟨p₁, h₁⟩ := s₁
      obtain ⟨p₂, _h₂⟩ := s₂
      subst h
      rfl)
  else
    .isFalse (fun heq => h (heq ▸ rfl))

/-- **WS-RR RR7.39 (the fail-closed constructor)**: build a footprint from a
declared list, refusing one whose keys repeat.

`none` is the honest answer for a list this domain cannot acquire correctly, and
it is *safe*: the bracket's undeclared arm runs the step exactly as an
unbracketed seam would, under whatever coarser serialisation the caller already
has.  Accepting a duplicated list and acquiring it anyway would be the one shape
this must not take — a declared footprint whose shrinking phase does not undo its
growing phase. -/
def ofList? (pairs : List (SchedLockId × AccessMode)) : Option SchedLockSet :=
  if h : (pairs.map (·.fst)).Nodup then some ⟨pairs, h⟩ else none

/-- **WS-RR RR7.39**: an accepted footprint carries exactly the list it was
built from — the resolver declares what the transition declared, unchanged. -/
theorem ofList?_pairs {pairs : List (SchedLockId × AccessMode)} {S : SchedLockSet}
    (h : ofList? pairs = some S) : S.pairs = pairs := by
  unfold ofList? at h
  by_cases hN : (pairs.map (·.fst)).Nodup
  · rw [dif_pos hN] at h
    exact (Option.some.inj h) ▸ rfl
  · rw [dif_neg hN] at h; exact absurd h (by simp)

/-- **WS-RR RR7.39**: a list with duplicate keys yields no footprint. -/
theorem ofList?_none_of_dup {pairs : List (SchedLockId × AccessMode)}
    (h : ¬ (pairs.map (·.fst)).Nodup) : ofList? pairs = none := by
  unfold ofList?; rw [dif_neg h]

/-- **WS-RR RR7.39**: a duplicate-free list always yields a footprint — the
positive direction, so a caller can see the refusal is about duplicates and
nothing else. -/
theorem ofList?_isSome_of_nodup {pairs : List (SchedLockId × AccessMode)}
    (h : (pairs.map (·.fst)).Nodup) : ofList? pairs = some ⟨pairs, h⟩ := by
  unfold ofList?; rw [dif_pos h]

/-- **WS-RR RR7.39**: membership reduces to membership in the pairs. -/
def Mem (S : SchedLockSet) (p : SchedLockId × AccessMode) : Prop := p ∈ S.pairs

instance : Membership (SchedLockId × AccessMode) SchedLockSet := ⟨Mem⟩

@[simp] theorem mem_def (p : SchedLockId × AccessMode) (S : SchedLockSet) :
    p ∈ S ↔ p ∈ S.pairs := Iff.rfl

/-- **WS-RR RR7.39**: the footprint's size — the number of locks the growing
phase acquires. -/
def size (S : SchedLockSet) : Nat := S.pairs.length

@[simp] theorem size_def (S : SchedLockSet) : S.size = S.pairs.length := rfl

/-- **PR #892 review round 5**: the order the growing phase acquires this
footprint in — the `SchedLockId`-ascending permutation of its declarations.

The object domain has answered "in what order does a bracket acquire a
footprint?" since SM3.B: `LockSet.lockAcquireSequence`, a `mergeSort` on the
key, so a footprint resolved in any order is still acquired along the SM0.I
ladder.  This domain answered it a second way — the declared list, verbatim —
and rested on each footprint being declared ascending.  That held for the
statically declared footprints, each of which carries its own `_pairwise_le`;
it did not hold for the one footprint resolved from the **state**.
`pipChainVisited` follows `blockingServer` with no ascending guard, so a
chain in which thread 10 blocks on thread 5 declared `[tcb 10, tcb 5]`, and
`SchedLockSet.ofList?` accepted it because it checks key-uniqueness and
nothing else.  Acquiring that walks the ladder **backwards**, against another
core acquiring 5 then 10 — a lock-order inversion, which is a deadlock.

So the two domains give one answer.  For the declared footprints this changes
nothing at all: an already-ascending list is its own `mergeSort`
(`lockAcquireSequence_eq_pairs_of_pairwise_le`), so their acquisition is the
list they always declared. -/
def lockAcquireSequence (S : SchedLockSet) : List (SchedLockId × AccessMode) :=
  S.pairs.mergeSort (fun p₁ p₂ => decide (p₁.fst ≤ p₂.fst))

/-- The comparator is transitive, from `SchedLockId.le_trans`. -/
private theorem leSchedLockId_bool_trans (a b c : SchedLockId × AccessMode) :
    decide (a.fst ≤ b.fst) = true →
    decide (b.fst ≤ c.fst) = true →
    decide (a.fst ≤ c.fst) = true := by
  intro hab hbc
  exact decide_eq_true (SchedLockId.le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc))

/-- The comparator is total, from `SchedLockId.le_total`. -/
private theorem leSchedLockId_bool_total (a b : SchedLockId × AccessMode) :
    (decide (a.fst ≤ b.fst) || decide (b.fst ≤ a.fst)) = true := by
  rcases SchedLockId.le_total a.fst b.fst with h | h
  · simp [decide_eq_true h]
  · simp [decide_eq_true h]

/-- **PR #892 review round 5**: the acquisition sequence is `SchedLockId`-ascending
— *unconditionally*, for every footprint, however it was resolved.

This is the property the domain's docstring used to assert of the declared
list.  It is now a theorem about the sequence the bracket actually folds over,
so the ladder holds for a footprint resolved from the state as much as for one
written down in a transition. -/
theorem lockAcquireSequence_ordered (S : SchedLockSet) :
    (lockAcquireSequence S).Pairwise (fun p₁ p₂ => p₁.fst ≤ p₂.fst) := by
  have hPairBool : List.Pairwise
      (fun p₁ p₂ => decide (p₁.fst ≤ p₂.fst) = true)
      (lockAcquireSequence S) :=
    List.pairwise_mergeSort
      (le := fun p₁ p₂ => decide (p₁.fst ≤ p₂.fst))
      leSchedLockId_bool_trans leSchedLockId_bool_total S.pairs
  exact hPairBool.imp (fun h => of_decide_eq_true h)

/-- **PR #892 review round 5**: the sort is a permutation of the declarations —
so the bracket acquires exactly the declared locks, no more and no fewer. -/
theorem lockAcquireSequence_perm (S : SchedLockSet) :
    (lockAcquireSequence S).Perm S.pairs :=
  List.mergeSort_perm S.pairs _

/-- **PR #892 review round 5**: membership is unchanged by the sort. -/
@[simp] theorem mem_lockAcquireSequence (S : SchedLockSet)
    (p : SchedLockId × AccessMode) : p ∈ lockAcquireSequence S ↔ p ∈ S.pairs := by
  simp only [lockAcquireSequence, List.mem_mergeSort]

/-- **PR #892 review round 5**: the sort preserves length, so a footprint's
size still counts what the growing phase acquires. -/
@[simp] theorem lockAcquireSequence_length (S : SchedLockSet) :
    (lockAcquireSequence S).length = S.size :=
  (lockAcquireSequence_perm S).length_eq

/-- **PR #892 review round 5**: a footprint already declared in ascending order
is acquired in exactly the order it declared.

This is what makes the change transparent for every statically declared
footprint: each carries a `_pairwise_le` theorem, so its acquisition sequence
is definitionally the list SM5 wrote down.  Only a footprint resolved out of
ladder order — the PIP chain — acquires in a different order than it lists,
which is the defect. -/
theorem lockAcquireSequence_eq_pairs_of_pairwise_le (S : SchedLockSet)
    (h : (S.pairs.map (·.fst)).Pairwise (· ≤ ·)) :
    lockAcquireSequence S = S.pairs := by
  refine List.mergeSort_of_pairwise ?_
  exact (List.pairwise_map.mp h).imp (fun hle => decide_eq_true hle)

end SchedLockSet

/-- **WS-RR RR7.39**: core `c` holds every lock the footprint declares, at the
declared mode — the scheduler domain's `lockSetHeld`. -/
def schedLockSetHeld (c : CoreId) (S : SchedLockSet) (s : SystemState) : Prop :=
  ∀ p ∈ S.pairs, schedLockHeld c p.fst p.snd s

instance schedLockSetHeld_decidable (c : CoreId) (S : SchedLockSet) (s : SystemState) :
    Decidable (schedLockSetHeld c S s) := by
  unfold schedLockSetHeld
  exact List.decidableBAll (fun p => schedLockHeld c p.fst p.snd s) S.pairs

-- ============================================================================
-- §4  The bracket domain
-- ============================================================================

/-- **WS-RR RR7.39**: the scheduler lock domain as a bracket domain.

Five primitives, and every one of them the domain's own: the sequence is the
footprint's **canonical** acquisition order (`SchedLockSet.lockAcquireSequence`,
a sort on the key — the same answer `objectLockBracketDomain` gives, for the
same reason), the folds are §2's, and the held predicate is §3's.  Everything
else about a revalidating bracket — resolve, acquire, re-resolve, refuse,
commit, unwind — comes from `runBracketed`, the *same* definition the ABI seam
runs.

**PR #892 review round 5**: the sequence used to be the declared list verbatim,
resting on "each model footprint carries its `_pairwise_le`".  That is true of
the footprints a *transition* declares and false of the one resolved from the
state: a PIP chain descends in `ObjId` whenever a higher-numbered thread blocks
on a lower-numbered one, and acquiring it verbatim walks the SM0.I ladder
backwards.  Sorting here fixes it for every footprint at once and costs the
declared ones nothing — an ascending list is its own sort. -/
def schedulerLockBracketDomain : LockBracketDomain where
  Footprint := SchedLockSet
  Key := SchedLockId × AccessMode
  decEqFootprint := inferInstance
  sequence := SchedLockSet.lockAcquireSequence
  acquire := schedAcquireAll
  unwind := schedUnwindAll
  held := schedLockSetHeld
  heldDec := fun c S s => schedLockSetHeld_decidable c S s

@[simp] theorem schedulerLockBracketDomain_sequence (S : SchedLockSet) :
    schedulerLockBracketDomain.sequence S = S.lockAcquireSequence := rfl

/-- **PR #892 review round 5**: the domain acquires in `SchedLockId`-ascending
order, whatever order the footprint was resolved in — the SM0.I ladder, held by
the domain rather than by a convention every resolver has to remember. -/
theorem schedulerLockBracketDomain_sequence_ordered (S : SchedLockSet) :
    (schedulerLockBracketDomain.sequence S).Pairwise (fun p₁ p₂ => p₁.fst ≤ p₂.fst) :=
  SchedLockSet.lockAcquireSequence_ordered S

/-- **PR #892 review round 5**: a footprint declared in ascending order — every
one a transition declares — is acquired exactly as it lists, so no SM5 result
about the declared sequence changes. -/
theorem schedulerLockBracketDomain_sequence_eq_pairs (S : SchedLockSet)
    (h : (S.pairs.map (·.fst)).Pairwise (· ≤ ·)) :
    schedulerLockBracketDomain.sequence S = S.pairs :=
  SchedLockSet.lockAcquireSequence_eq_pairs_of_pairwise_le S h

@[simp] theorem schedulerLockBracketDomain_acquire (c : CoreId)
    (pairs : List (SchedLockId × AccessMode)) (s : SystemState) :
    schedulerLockBracketDomain.acquire c pairs s = schedAcquireAll c pairs s := rfl

@[simp] theorem schedulerLockBracketDomain_unwind (c : CoreId)
    (pairs : List (SchedLockId × AccessMode)) (s : SystemState) :
    schedulerLockBracketDomain.unwind c pairs s = schedUnwindAll c pairs s := rfl

@[simp] theorem schedulerLockBracketDomain_held (c : CoreId) (S : SchedLockSet)
    (s : SystemState) :
    schedulerLockBracketDomain.held c S s = schedLockSetHeld c S s := rfl

end SeLe4n.Kernel
