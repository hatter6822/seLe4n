-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/
import SeLe4n.Kernel.Concurrency.Locks.LockKey
import SeLe4n.Kernel.Concurrency.Locks.RwLock

/-!
# WS-LS LS1.1 — the ghost lock state

One key type for every lock the kernel's brackets declare, one order over it,
and one table of `RwLockState`s indexed by it, held **beside** the kernel
state rather than inside it.

Until WS-LS LS3.1 a lock was a word *in* a kernel object (`KernelObject.lock`),
in the object store's own header (`SystemState.objStoreLock`), or in a per-core
scheduler record (`SystemState.schedulerLocks`), and the bracket that took a
footprint rewrote those objects — the lock model's share of a syscall's heap
allocations, which `docs/planning/LOCK_STATE_SEPARATION_PLAN.md` §1 measures
at about two thirds.  `LockState` is the same specification with the words
taken out of the state: a total function from `LockKey` to `RwLockState`,
advanced by the same `RwLockState.applyOp` the per-object words were.  Every
2PL, serializability and deadlock theorem is about the sequence of lock
operations a bracket applies, and that sequence is what this module keeps.
The kernel state carries no lock word since LS3.1; the only lock state is
this table.

## What is here

* `LockKey` and its order are `Locks/LockKey.lean` (they key `LockSet` too);
  `LockKey.ofLockId` is the one spelling of the table lock: every
  `.objStore`-kind `LockId` names the same word today, and here the same key.
* `LockState` — the ghost table, its per-key `acquire` / `release` / `cancel`
  through `RwLockState.applyOp`, and the folds `acquireAll` / `releaseAll` /
  `cancelAll` / `unwindAll` a bracket runs.  `applySeq` is their common form:
  a list of `(key, op)` pairs applied in order, and `applySeq_key` reads any
  one key's trace out of it (`keyOps`), which is the lift the per-lock
  refinement chain needs.
* The theorems the per-object layer once proved under object-presence
  hypotheses, in their ghost form: `acquireAll_unheld_held` (no object has to
  be present for a ghost lock to exist), `unwindAll_not_queued` (no `invExt`),
  `acquireAll_unwindAll_unheld` (the bracket's round trip, which
  `BracketSpec.runGhost` consumes), and `lockAcquireSequence_ordered` over
  `LockKey`.
* The refinement lift, `LockState.applySeq_unheld_key_refines`, lives in
  `Locks/Refinement.lean` with the bridges it lifts (that file is staged with
  them; nothing here depends on it): the trace a bracket applies to one key is
  an `RwLockOp` list, and `queuedRwLock_refines_rwLockSpec` already covers
  every such list, so the deployed `QueuedRwLock` refines the ghost key by key
  with no change to that file.

Every seam runs `BracketSpec.run` over this table (LS2), and LS3.1 deleted the
words and the per-object primitives that advanced them.
-/

namespace SeLe4n.Kernel.Concurrency

-- ============================================================================
-- §3  The ghost table
-- ============================================================================

/-- **WS-LS LS1.1**: the lock state — one `RwLockState` per key, total.

A function rather than a finite map because every key *has* a lock: the
object-presence hypotheses the per-object layer carried
(`acquireAll_establishes_lockSetHeld`'s `hEach`) existed only because a lock
lived in an object that could be absent.  Computable, so the Tier 2 suites
execute it; nothing in the kernel's export surface reaches it (LS2.2's
census). -/
def LockState : Type := LockKey → RwLockState

namespace LockState

/-- Every lock free: the state every entry starts in and ends in. -/
def unheld : LockState := fun _ => RwLockState.unheld

@[simp] theorem unheld_apply (k : LockKey) : unheld k = RwLockState.unheld := rfl

/-- Point update. -/
def update (L : LockState) (k : LockKey) (f : RwLockState → RwLockState) : LockState :=
  fun k' => if k' = k then f (L k) else L k'

@[simp] theorem update_self (L : LockState) (k : LockKey) (f : RwLockState → RwLockState) :
    L.update k f k = f (L k) := by
  unfold update; rw [if_pos rfl]

@[simp] theorem update_ne (L : LockState) {k k' : LockKey} (f : RwLockState → RwLockState)
    (h : k' ≠ k) : L.update k f k' = L k' := by
  unfold update; rw [if_neg h]

/-- Advance one key by one `RwLockOp` — the ghost's only primitive. -/
def applyOp (L : LockState) (k : LockKey) (op : RwLockOp) : LockState :=
  L.update k (·.applyOp op)

@[simp] theorem applyOp_self (L : LockState) (k : LockKey) (op : RwLockOp) :
    L.applyOp k op k = (L k).applyOp op := update_self L k _

@[simp] theorem applyOp_ne (L : LockState) {k k' : LockKey} (op : RwLockOp) (h : k' ≠ k) :
    L.applyOp k op k' = L k' := update_ne L _ h

/-- Acquire key `k` in mode `m` on behalf of core `c`. -/
def acquire (L : LockState) (c : CoreId) (k : LockKey) (m : AccessMode) : LockState :=
  L.applyOp k (m.toAcquireOp c)

/-- Release it. -/
def release (L : LockState) (c : CoreId) (k : LockKey) (m : AccessMode) : LockState :=
  L.applyOp k (m.toReleaseOp c)

/-- Withdraw a queued request for it. -/
def cancel (L : LockState) (c : CoreId) (k : LockKey) (m : AccessMode) : LockState :=
  L.applyOp k (m.toCancelOp c)

/-- Core `c` holds key `k` in mode `m`. -/
def held (L : LockState) (c : CoreId) (k : LockKey) (m : AccessMode) : Prop :=
  (L k).coreHolds c m

instance (L : LockState) (c : CoreId) (k : LockKey) (m : AccessMode) : Decidable (L.held c k m) :=
  inferInstanceAs (Decidable ((L k).coreHolds c m))

/-- Core `c` has a request queued at key `k`. -/
def queued (L : LockState) (c : CoreId) (k : LockKey) : Prop :=
  c ∈ (L k).waiters.map Prod.fst

instance (L : LockState) (c : CoreId) (k : LockKey) : Decidable (L.queued c k) :=
  inferInstanceAs (Decidable (c ∈ (L k).waiters.map Prod.fst))

/-- Core `c` holds every member of a footprint at its declared mode — the
ghost `lockSetHeld`.  Over the pair list; LS1.2 states it over `LockSet`. -/
def heldAll (L : LockState) (c : CoreId) (pairs : List (LockKey × AccessMode)) : Prop :=
  ∀ p ∈ pairs, L.held c p.fst p.snd

instance (L : LockState) (c : CoreId) (pairs : List (LockKey × AccessMode)) :
    Decidable (L.heldAll c pairs) := by
  unfold heldAll; exact inferInstance

-- ============================================================================
-- §4  The folds, and one key's trace through them
-- ============================================================================

/-- Apply a sequence of `(key, op)` pairs in order: the common form of every
fold below, and the one `applySeq_key` reads a single key's trace out of. -/
def applySeq (L : LockState) (ops : List (LockKey × RwLockOp)) : LockState :=
  ops.foldl (fun L p => L.applyOp p.fst p.snd) L

@[simp] theorem applySeq_nil (L : LockState) : L.applySeq [] = L := rfl

@[simp] theorem applySeq_cons (L : LockState) (p : LockKey × RwLockOp)
    (ops : List (LockKey × RwLockOp)) :
    L.applySeq (p :: ops) = (L.applyOp p.fst p.snd).applySeq ops := rfl

theorem applySeq_append (L : LockState) (ops₁ ops₂ : List (LockKey × RwLockOp)) :
    L.applySeq (ops₁ ++ ops₂) = (L.applySeq ops₁).applySeq ops₂ := by
  simp only [applySeq, List.foldl_append]

/-- The ops a footprint's growing phase applies. -/
def acquireOps (c : CoreId) (pairs : List (LockKey × AccessMode)) : List (LockKey × RwLockOp) :=
  pairs.map fun p => (p.fst, p.snd.toAcquireOp c)

/-- The ops its release half applies. -/
def releaseOps (c : CoreId) (pairs : List (LockKey × AccessMode)) : List (LockKey × RwLockOp) :=
  pairs.map fun p => (p.fst, p.snd.toReleaseOp c)

/-- The ops its withdrawal half applies. -/
def cancelOps (c : CoreId) (pairs : List (LockKey × AccessMode)) : List (LockKey × RwLockOp) :=
  pairs.map fun p => (p.fst, p.snd.toCancelOp c)

/-- The 2PL growing phase: acquire in input order (the caller passes
`lockAcquireSequence`). -/
def acquireAll (c : CoreId) (pairs : List (LockKey × AccessMode)) (L : LockState) : LockState :=
  pairs.foldl (fun L p => L.acquire c p.fst p.snd) L

/-- The release half of the shrinking phase (the caller passes the sequence
reversed). -/
def releaseAll (c : CoreId) (pairs : List (LockKey × AccessMode)) (L : LockState) : LockState :=
  pairs.foldl (fun L p => L.release c p.fst p.snd) L

/-- The withdrawal half. -/
def cancelAll (c : CoreId) (pairs : List (LockKey × AccessMode)) (L : LockState) : LockState :=
  pairs.foldl (fun L p => L.cancel c p.fst p.snd) L

/-- The shrinking phase: withdraw, then release, so a withdrawal lands before
any promotion a release triggers can see the withdrawn request. -/
def unwindAll (c : CoreId) (pairs : List (LockKey × AccessMode)) (L : LockState) : LockState :=
  releaseAll c pairs (cancelAll c pairs L)

@[simp] theorem acquireAll_nil (c : CoreId) (L : LockState) : acquireAll c [] L = L := rfl
@[simp] theorem releaseAll_nil (c : CoreId) (L : LockState) : releaseAll c [] L = L := rfl
@[simp] theorem cancelAll_nil (c : CoreId) (L : LockState) : cancelAll c [] L = L := rfl

@[simp] theorem acquireAll_cons (c : CoreId) (p : LockKey × AccessMode)
    (pairs : List (LockKey × AccessMode)) (L : LockState) :
    acquireAll c (p :: pairs) L = acquireAll c pairs (L.acquire c p.fst p.snd) := rfl
@[simp] theorem releaseAll_cons (c : CoreId) (p : LockKey × AccessMode)
    (pairs : List (LockKey × AccessMode)) (L : LockState) :
    releaseAll c (p :: pairs) L = releaseAll c pairs (L.release c p.fst p.snd) := rfl
@[simp] theorem cancelAll_cons (c : CoreId) (p : LockKey × AccessMode)
    (pairs : List (LockKey × AccessMode)) (L : LockState) :
    cancelAll c (p :: pairs) L = cancelAll c pairs (L.cancel c p.fst p.snd) := rfl

/-- Each fold is `applySeq` of its op list. -/
theorem acquireAll_eq_applySeq (c : CoreId) (pairs : List (LockKey × AccessMode)) (L : LockState) :
    acquireAll c pairs L = L.applySeq (acquireOps c pairs) := by
  induction pairs generalizing L with
  | nil => rfl
  | cons p rest ih => simp only [acquireAll_cons, acquireOps, List.map_cons, applySeq_cons]; exact ih _

theorem releaseAll_eq_applySeq (c : CoreId) (pairs : List (LockKey × AccessMode)) (L : LockState) :
    releaseAll c pairs L = L.applySeq (releaseOps c pairs) := by
  induction pairs generalizing L with
  | nil => rfl
  | cons p rest ih => simp only [releaseAll_cons, releaseOps, List.map_cons, applySeq_cons]; exact ih _

theorem cancelAll_eq_applySeq (c : CoreId) (pairs : List (LockKey × AccessMode)) (L : LockState) :
    cancelAll c pairs L = L.applySeq (cancelOps c pairs) := by
  induction pairs generalizing L with
  | nil => rfl
  | cons p rest ih => simp only [cancelAll_cons, cancelOps, List.map_cons, applySeq_cons]; exact ih _

/-- The whole bracket, as one op sequence: grow, withdraw in reverse, release
in reverse. -/
def bracketOps (c : CoreId) (seq : List (LockKey × AccessMode)) : List (LockKey × RwLockOp) :=
  acquireOps c seq ++ cancelOps c seq.reverse ++ releaseOps c seq.reverse

theorem unwindAll_acquireAll_eq_applySeq (c : CoreId) (seq : List (LockKey × AccessMode))
    (L : LockState) :
    unwindAll c seq.reverse (acquireAll c seq L) = L.applySeq (bracketOps c seq) := by
  simp only [unwindAll, bracketOps, releaseAll_eq_applySeq, cancelAll_eq_applySeq,
    acquireAll_eq_applySeq, applySeq_append]

/-- The ops of a sequence that address key `k`, in order: one key's trace. -/
def keyOps (k : LockKey) (ops : List (LockKey × RwLockOp)) : List RwLockOp :=
  (ops.filter fun p => decide (p.fst = k)).map (·.snd)

@[simp] theorem keyOps_nil (k : LockKey) : keyOps k [] = [] := rfl

theorem keyOps_cons_self (k : LockKey) (op : RwLockOp) (ops : List (LockKey × RwLockOp)) :
    keyOps k ((k, op) :: ops) = op :: keyOps k ops := by
  simp [keyOps]

theorem keyOps_cons_ne {k k' : LockKey} (h : k' ≠ k) (op : RwLockOp)
    (ops : List (LockKey × RwLockOp)) :
    keyOps k ((k', op) :: ops) = keyOps k ops := by
  simp [keyOps, h]

theorem keyOps_append (k : LockKey) (ops₁ ops₂ : List (LockKey × RwLockOp)) :
    keyOps k (ops₁ ++ ops₂) = keyOps k ops₁ ++ keyOps k ops₂ := by
  simp [keyOps, List.filter_append]

/-- **LS1.1 (the per-key reading)**: what a sequence does to one key is the
fold of that key's own ops over that key's own cell.  Keys are independent
cells, so every other op is a frame.  This is the lemma the refinement lift
and every held / queued theorem below go through. -/
theorem applySeq_key (L : LockState) (ops : List (LockKey × RwLockOp)) (k : LockKey) :
    L.applySeq ops k = (keyOps k ops).foldl RwLockState.applyOp (L k) := by
  induction ops generalizing L with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨k', op⟩ := p
    by_cases h : k' = k
    · subst h
      rw [applySeq_cons, ih, keyOps_cons_self, List.foldl_cons, applyOp_self]
    · rw [applySeq_cons, ih, keyOps_cons_ne h, applyOp_ne L op (Ne.symm h)]

/-- A key no op addresses is untouched. -/
theorem applySeq_of_not_mem (L : LockState) (ops : List (LockKey × RwLockOp)) (k : LockKey)
    (h : k ∉ ops.map (·.fst)) : L.applySeq ops k = L k := by
  rw [applySeq_key]
  have : keyOps k ops = [] := by
    simp only [keyOps, List.map_eq_nil_iff, List.filter_eq_nil_iff, decide_eq_true_eq]
    intro p hp hEq
    exact h (List.mem_map.mpr ⟨p, hp, hEq⟩)
  rw [this]; rfl

-- ============================================================================
-- §5  What the folds establish — the ghost forms of the per-object theorems
-- ============================================================================

/-- One key's trace through a mapped footprint: its ops are exactly the images
of its own declarations. -/
theorem mem_keyOps_map (k : LockKey) (pairs : List (LockKey × AccessMode))
    (f : AccessMode → RwLockOp) (op : RwLockOp) :
    op ∈ keyOps k (pairs.map fun p => (p.fst, f p.snd)) ↔ ∃ m, (k, m) ∈ pairs ∧ op = f m := by
  simp only [keyOps, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨k', op'⟩, ⟨⟨⟨k₀, m⟩, hp, hEq⟩, hk⟩, hop⟩
    simp only [Prod.mk.injEq] at hEq hk
    obtain ⟨rfl, rfl⟩ := hEq
    subst hk
    exact ⟨m, hp, hop.symm⟩
  · rintro ⟨m, hp, rfl⟩
    exact ⟨(k, f m), ⟨⟨(k, m), hp, rfl⟩, rfl⟩, rfl⟩

/-- A duplicate-free footprint's trace at a member is that member's one op. -/
theorem keyOps_map_of_nodup {k : LockKey} {m : AccessMode} {pairs : List (LockKey × AccessMode)}
    (hnd : (pairs.map (·.fst)).Nodup) (hmem : (k, m) ∈ pairs) (f : AccessMode → RwLockOp) :
    keyOps k (pairs.map fun p => (p.fst, f p.snd)) = [f m] := by
  induction pairs with
  | nil => exact absurd hmem (List.not_mem_nil)
  | cons p rest ih =>
    obtain ⟨k', m'⟩ := p
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hnot, hrest⟩ := hnd
    rw [List.map_cons]
    rcases List.mem_cons.mp hmem with hEq | hTail
    · simp only [Prod.mk.injEq] at hEq
      obtain ⟨rfl, rfl⟩ := hEq
      rw [keyOps_cons_self]
      have hNil : keyOps k (rest.map fun p => (p.fst, f p.snd)) = [] := by
        simp only [keyOps, List.map_eq_nil_iff, List.filter_eq_nil_iff, decide_eq_true_eq]
        rintro ⟨k₀, op⟩ hq hEq
        obtain ⟨⟨k₁, m₁⟩, hq₁, hEq₁⟩ := List.mem_map.mp hq
        simp only [Prod.mk.injEq] at hEq₁ hEq
        subst hEq
        exact hnot (List.mem_map.mpr ⟨(k₁, m₁), hq₁, hEq₁.1⟩)
      rw [hNil]
    · have hne : k' ≠ k := fun h => by
        subst h
        exact hnot (List.mem_map.mpr ⟨(k', m), hTail, rfl⟩)
      rw [keyOps_cons_ne hne]
      exact ih hrest hTail

/-- A key the footprint does not name has no trace. -/
theorem keyOps_map_of_not_mem {k : LockKey} {pairs : List (LockKey × AccessMode)}
    (h : k ∉ pairs.map (·.fst)) (f : AccessMode → RwLockOp) :
    keyOps k (pairs.map fun p => (p.fst, f p.snd)) = [] := by
  simp only [keyOps, List.map_eq_nil_iff, List.filter_eq_nil_iff, decide_eq_true_eq]
  rintro ⟨k₀, op⟩ hq hEq
  obtain ⟨⟨k₁, m₁⟩, hq₁, hEq₁⟩ := List.mem_map.mp hq
  simp only [Prod.mk.injEq] at hEq₁ hEq
  subst hEq
  exact h (List.mem_map.mpr ⟨(k₁, m₁), hq₁, hEq₁.1⟩)

/-- The three op lists, read at one key of a duplicate-free footprint. -/
theorem keyOps_acquireOps_of_nodup {k : LockKey} {m : AccessMode} {pairs : List (LockKey × AccessMode)}
    (c : CoreId) (hnd : (pairs.map (·.fst)).Nodup) (hmem : (k, m) ∈ pairs) :
    keyOps k (acquireOps c pairs) = [m.toAcquireOp c] :=
  keyOps_map_of_nodup hnd hmem (f := fun m => m.toAcquireOp c)

theorem keyOps_cancelOps_of_nodup {k : LockKey} {m : AccessMode} {pairs : List (LockKey × AccessMode)}
    (c : CoreId) (hnd : (pairs.map (·.fst)).Nodup) (hmem : (k, m) ∈ pairs) :
    keyOps k (cancelOps c pairs) = [RwLockOp.cancel c] :=
  keyOps_map_of_nodup hnd hmem (f := fun m => m.toCancelOp c)

theorem keyOps_releaseOps_of_nodup {k : LockKey} {m : AccessMode} {pairs : List (LockKey × AccessMode)}
    (c : CoreId) (hnd : (pairs.map (·.fst)).Nodup) (hmem : (k, m) ∈ pairs) :
    keyOps k (releaseOps c pairs) = [m.toReleaseOp c] :=
  keyOps_map_of_nodup hnd hmem (f := fun m => m.toReleaseOp c)

/-- And at a key the footprint does not name. -/
theorem keyOps_acquireOps_of_not_mem {k : LockKey} {pairs : List (LockKey × AccessMode)}
    (c : CoreId) (h : k ∉ pairs.map (·.fst)) : keyOps k (acquireOps c pairs) = [] :=
  keyOps_map_of_not_mem h (f := fun m => m.toAcquireOp c)

theorem keyOps_cancelOps_of_not_mem {k : LockKey} {pairs : List (LockKey × AccessMode)}
    (c : CoreId) (h : k ∉ pairs.map (·.fst)) : keyOps k (cancelOps c pairs) = [] :=
  keyOps_map_of_not_mem h (f := fun m => m.toCancelOp c)

theorem keyOps_releaseOps_of_not_mem {k : LockKey} {pairs : List (LockKey × AccessMode)}
    (c : CoreId) (h : k ∉ pairs.map (·.fst)) : keyOps k (releaseOps c pairs) = [] :=
  keyOps_map_of_not_mem h (f := fun m => m.toReleaseOp c)

/-- Membership in one key's trace, per op list. -/
theorem mem_keyOps_cancelOps (c : CoreId) (k : LockKey) (pairs : List (LockKey × AccessMode))
    (op : RwLockOp) :
    op ∈ keyOps k (cancelOps c pairs) ↔ ∃ m, (k, m) ∈ pairs ∧ op = RwLockOp.cancel c :=
  mem_keyOps_map k pairs (fun m => m.toCancelOp c) op

theorem mem_keyOps_releaseOps (c : CoreId) (k : LockKey) (pairs : List (LockKey × AccessMode))
    (op : RwLockOp) :
    op ∈ keyOps k (releaseOps c pairs) ↔ ∃ m, (k, m) ∈ pairs ∧ op = m.toReleaseOp c :=
  mem_keyOps_map k pairs (fun m => m.toReleaseOp c) op

/-- **LS1.1 (`acquireAll_establishes_lockSetHeld`, ghost form)**: the growing
phase over a duplicate-free footprint whose members are free leaves the core
holding every member at its declared mode.

The per-object theorem needed `objects.invExt` and a present object of the
right kind at every member; here a lock exists for every key, so only the
footprint's own well-formedness and the members' freedom remain. -/
theorem acquireAll_held_of_free (c : CoreId) (pairs : List (LockKey × AccessMode))
    (L : LockState) (hnd : (pairs.map (·.fst)).Nodup)
    (hFree : ∀ p ∈ pairs, L p.fst = RwLockState.unheld) :
    (acquireAll c pairs L).heldAll c pairs := by
  intro p hp
  obtain ⟨k, m⟩ := p
  show ((acquireAll c pairs L) k).coreHolds c m
  rw [acquireAll_eq_applySeq, applySeq_key, keyOps_acquireOps_of_nodup c hnd hp,
    List.foldl_cons, List.foldl_nil, hFree (k, m) hp]
  exact RwLockState.unheld_acquire_grants c m

/-- **LS1.1 (obligation O3, first half)**: from the all-free state, the growing
phase holds the footprint. -/
theorem acquireAll_unheld_held (c : CoreId) (pairs : List (LockKey × AccessMode))
    (hnd : (pairs.map (·.fst)).Nodup) :
    (acquireAll c pairs unheld).heldAll c pairs :=
  acquireAll_held_of_free c pairs unheld hnd (fun _ _ => rfl)

/-- A fold of withdrawals by `c`, at least one of them, leaves `c` unqueued. -/
private theorem foldl_cancel_not_queued (c : CoreId) (ops : List RwLockOp) (s : RwLockState)
    (hAll : ∀ op ∈ ops, op = RwLockOp.cancel c) (hNe : ops ≠ []) :
    c ∉ (ops.foldl RwLockState.applyOp s).waiters.map Prod.fst := by
  induction ops generalizing s with
  | nil => exact absurd rfl hNe
  | cons op rest ih =>
    have hop : op = RwLockOp.cancel c := hAll op (List.mem_cons_self ..)
    subst hop
    rw [List.foldl_cons]
    cases rest with
    | nil => exact rwLock_cancel_not_queued s c
    | cons op' rest' =>
      exact ih _ (fun o ho => hAll o (List.mem_cons_of_mem _ ho)) (List.cons_ne_nil _ _)

/-- A fold of releases by `c` never enqueues `c`. -/
private theorem foldl_release_preserves_not_queued (c : CoreId) (ops : List RwLockOp)
    (s : RwLockState) (hAll : ∀ op ∈ ops, ∃ m : AccessMode, op = m.toReleaseOp c)
    (h : c ∉ s.waiters.map Prod.fst) :
    c ∉ (ops.foldl RwLockState.applyOp s).waiters.map Prod.fst := by
  induction ops generalizing s with
  | nil => exact h
  | cons op rest ih =>
    obtain ⟨m, hm⟩ := hAll op (List.mem_cons_self ..)
    subst hm
    rw [List.foldl_cons]
    exact ih _ (fun o ho => hAll o (List.mem_cons_of_mem _ ho))
      (rwLock_release_preserves_not_queued s c c m h)

/-- **LS1.1 (`cancelAll_leaves_no_queued_request`, ghost form)**: the
withdrawal half leaves `c` unqueued at every member — with no hypothesis. -/
theorem cancelAll_not_queued (c : CoreId) (pairs : List (LockKey × AccessMode)) (L : LockState) :
    ∀ p ∈ pairs, ¬ (cancelAll c pairs L).queued c p.fst := by
  intro p hp
  obtain ⟨k, m⟩ := p
  show c ∉ ((cancelAll c pairs L) k).waiters.map Prod.fst
  rw [cancelAll_eq_applySeq, applySeq_key]
  apply foldl_cancel_not_queued
  · intro op hop
    obtain ⟨m', _, hEq⟩ := (mem_keyOps_cancelOps c k pairs op).mp hop
    exact hEq
  · intro hNil
    have : (RwLockOp.cancel c) ∈ keyOps k (cancelOps c pairs) :=
      (mem_keyOps_cancelOps c k pairs _).mpr ⟨m, hp, rfl⟩
    rw [hNil] at this
    exact List.not_mem_nil this

/-- **LS1.1 (`releaseAll_preserves_not_queued`, ghost form)**: the release
half cannot enqueue, at any key. -/
theorem releaseAll_preserves_not_queued (c : CoreId) (pairs : List (LockKey × AccessMode))
    (L : LockState) (k : LockKey) (h : ¬ L.queued c k) :
    ¬ (releaseAll c pairs L).queued c k := by
  show c ∉ ((releaseAll c pairs L) k).waiters.map Prod.fst
  rw [releaseAll_eq_applySeq, applySeq_key]
  apply foldl_release_preserves_not_queued c _ _ _ h
  intro op hop
  obtain ⟨m', _, hEq⟩ := (mem_keyOps_releaseOps c k pairs op).mp hop
  exact ⟨m', hEq⟩

/-- **LS1.1 (`unwindAll_leaves_no_queued_request`, ghost form)**: the shrinking
phase leaves the unwinding core with no queued request at any member of the
footprint.  The per-object theorem needed `objects.invExt`; this needs
nothing: a ghost lock exists at every key, the withdrawal fold establishes
absence at every member, and no release arm enqueues. -/
theorem unwindAll_not_queued (c : CoreId) (pairs : List (LockKey × AccessMode)) (L : LockState) :
    ∀ p ∈ pairs, ¬ (unwindAll c pairs L).queued c p.fst := fun p hp =>
  releaseAll_preserves_not_queued c pairs _ p.fst (cancelAll_not_queued c pairs L p hp)

/-- One key's full bracket trace from free: granted, withdrawn (a no-op on a
holder), released — back to free. -/
private theorem bracket_key_roundtrip (c : CoreId) (m : AccessMode) :
    ((RwLockState.unheld.applyOp (m.toAcquireOp c)).applyOp (RwLockOp.cancel c)).applyOp
      (m.toReleaseOp c) = RwLockState.unheld := by
  have hNoQ : c ∉ (RwLockState.unheld.applyOp (m.toAcquireOp c)).waiters.map Prod.fst := by
    cases m <;> simp [RwLockState.applyOp, RwLockState.coreInvolved, RwLockState.unheld,
      AccessMode.toAcquireOp]
  rw [RwLockState.applyOp_cancel_of_not_queued _ c hNoQ]
  exact RwLockState.unheld_acquire_release_roundtrip c m

/-- **LS1.1 (obligation O3, second half)**: a bracket over a duplicate-free
footprint, from the all-free state, returns to the all-free state — the
growing phase is granted at every member (nothing is held or queued, so no
acquire enqueues), the withdrawal finds nothing queued, and the release
returns each member to `unheld`.  LS2's `runGhost_locks_of_unheld` is this
theorem at the sorted sequence. -/
theorem acquireAll_unwindAll_unheld (c : CoreId) (seq : List (LockKey × AccessMode))
    (hnd : (seq.map (·.fst)).Nodup) :
    unwindAll c seq.reverse (acquireAll c seq unheld) = unheld := by
  rw [unwindAll_acquireAll_eq_applySeq]
  funext k
  rw [applySeq_key, bracketOps, keyOps_append, keyOps_append, unheld_apply]
  have hndRev : (seq.reverse.map (·.fst)).Nodup :=
    ((List.reverse_perm seq).map (·.fst)).nodup_iff.mpr hnd
  by_cases hk : k ∈ seq.map (·.fst)
  · obtain ⟨⟨k₀, m⟩, hp, hEq⟩ := List.mem_map.mp hk
    simp only at hEq
    subst hEq
    have hpRev : (k₀, m) ∈ seq.reverse := List.mem_reverse.mpr hp
    rw [keyOps_acquireOps_of_nodup c hnd hp, keyOps_cancelOps_of_nodup c hndRev hpRev,
      keyOps_releaseOps_of_nodup c hndRev hpRev]
    simp only [List.cons_append, List.nil_append, List.foldl_cons, List.foldl_nil]
    exact bracket_key_roundtrip c m
  · have hkRev : k ∉ seq.reverse.map (·.fst) := by
      rw [List.map_reverse, List.mem_reverse]; exact hk
    rw [keyOps_acquireOps_of_not_mem c hk, keyOps_cancelOps_of_not_mem c hkRev,
      keyOps_releaseOps_of_not_mem c hkRev]
    rfl

end LockState

end SeLe4n.Kernel.Concurrency
