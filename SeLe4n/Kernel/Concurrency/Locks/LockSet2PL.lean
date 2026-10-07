-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Model.State
import SeLe4n.Kernel.Concurrency.Locks.Kind
import SeLe4n.Kernel.Concurrency.Locks.LockSet
import SeLe4n.Kernel.Concurrency.Locks.LockIdProjection
import SeLe4n.Kernel.Concurrency.Locks.LockSetTransitions
import SeLe4n.Kernel.Concurrency.Locks.WithLockSet
import SeLe4n.Kernel.Concurrency.Locks.LockSetHeld
import SeLe4n.Kernel.Concurrency.Locks.BracketSpec

/-!
# WS-SM SM3.C.5 / C.6 / C.7 / C.8 — Two-phase-locking discipline theorems

The four substantive theorems for SM3.C, stated since **WS-LS LS2.1** over the
pair `LockedSystemState` and the ghost bracket `withLockSetGhost`
(`Locks/BracketSpec.lean`), which LS3.1 renames to `withLockSet`:

* **SM3.C.5** `lockSet_acquired_in_order`: every lock acquisition
  via the bracket happens in `LockKey` ascending order.  Follows
  from `lockAcquireSequence_ordered` (SM3.B.6) and the structural
  shape of `acquireAll` (sequential fold over the sorted list).

* **SM3.C.6** `lockSet_released_in_reverse`: every lock release
  via the bracket happens in `LockKey` *descending* order.
  Follows from the same SM3.B.6 lemma applied to
  `lockAcquireSequence.reverse`.

* **SM3.C.7** `lockSet_atomic_under_2pl`: the visible state
  transitions during the bracket form an atomic span — every
  external observer sees either the pre-acquire state or the
  post-release state, never an intermediate.  Over the pair this is
  `rfl`: the phases write the lock table, the action writes the kernel
  state, and `lockSet_observer_atomic` holds for every observer with no
  hypothesis.

* **SM3.C.8** `withLockSet_invariant_preserved` (plan §3.9 Corollary
  2.1.11): a kernel invariant the bare action preserves is preserved by
  the bracketed action.  This is the operational form of the
  architectural lever that keeps WS-SM's proof cost tractable: every
  existing single-core kernel-transition theorem lifts to the SMP form
  with its own proof.

## Strict-2PL discipline

The 2PL discipline is *strict* in seLe4n: locks are not released
until ALL of the action's mutations are complete.  This is what
makes the serializability theorem (SM3.E.3) immediate: the
commit-time of every transaction is unambiguously the
post-action moment, so the conflict graph is a strict total
order.

## What LS2.1 retired here

Before LS2.1 the bracket wrote lock words into kernel objects, so
"atomic from observer view" needed an observer that could not see those
writes: `AcquireInsensitive` / `UnwindInsensitive`, their `invExt`-guarded
`On` forms, the per-fold invisibility lemmas, the two guarded capstones and
an acquire-fold invariant form (`lockSet_invariant_preserved`) with its
worked instantiation on the table lock's well-formedness.  Over the pair the
kernel half of the bracket's result *is* the action's, by `rfl`, so that
machinery has nothing left to prove and is deleted; the theorems it fed keep
their names with the hypotheses dropped (a strengthening, recorded in
`docs/planning/LOCK_STATE_SEPARATION_PLAN.md` §5 O6).  §5b keeps the
word-level growing-phase facts (`acquireAll_establishes_lockSetHeld` and its
feeders) beside the word-level `withLockSet` until LS3.1 deletes the words;
their ghost forms are `LockState.acquireAll_unheld_heldAll_pairs` and
`LockState.bracket_unheld`.
-/

namespace SeLe4n.Kernel.Concurrency

open SeLe4n
open SeLe4n.Model

-- ============================================================================
-- §1 — `acquireOrder` / `releaseOrder` projection helpers
-- ============================================================================

/-- WS-SM SM3.C.5 helper: extract the LockId-ordered acquisition
sequence from a `LockSet`.  This is the *order* in which
`withLockSet` invokes `acquireLockOnObject`, separated from the
state-update fold so the ordering theorem can target it directly. -/
def acquireOrder (S : LockSet) : List LockKey :=
  S.lockAcquireSequence.map Prod.fst

/-- WS-SM SM3.C.6 helper: extract the LockId-ordered release
sequence — the reverse of the acquisition sequence. -/
def releaseOrder (S : LockSet) : List LockKey :=
  acquireOrder S |>.reverse

/-- WS-SM SM3.C.5 / C.6: round-trip — the release order is the
reverse of the acquire order. -/
@[simp] theorem releaseOrder_eq_acquireOrder_reverse (S : LockSet) :
    releaseOrder S = (acquireOrder S).reverse := rfl

-- ============================================================================
-- §2 — SM3.C.5 — `lockSet_acquired_in_order`
-- ============================================================================

/-- WS-SM SM3.C.5 (plan §5.3): every acquisition via `withLockSet`
happens in `LockId` ascending order.

The acquire order — `acquireOrder S` — is the projection of
`lockAcquireSequence S` onto its `fst` components.  Since
`lockAcquireSequence` is canonically sorted by `LockId` ascending
(SM3.B.6), the projection inherits the ordering.

This is the cornerstone witness for SM3.D's deadlock-freedom
theorem: any cycle in the wait-graph would require some core to
acquire a *lower* LockId than one it already holds, contradicting
this lemma. -/
theorem lockSet_acquired_in_order (S : LockSet) :
    (acquireOrder S).Pairwise (· ≤ ·) := by
  unfold acquireOrder
  -- `lockAcquireSequence` is Pairwise (· ≤ ·) on the fst projection.
  have h := S.lockAcquireSequence_ordered
  -- Lift the Pairwise on pairs (with fst-comparator) to Pairwise on the fst list.
  exact List.Pairwise.map _ (fun a b h => h) h

-- ============================================================================
-- §3 — SM3.C.6 — `lockSet_released_in_reverse`
-- ============================================================================

/-- WS-SM SM3.C.6 (plan §5.3): every release via `withLockSet`
happens in `LockId` descending order (i.e., the reverse of the
acquire order).

Follows from SM3.C.5's ordering by reversing the list: the
reverse of an ascending list is descending.  Combined with
`releaseOrder_eq_acquireOrder_reverse`, this gives the strict-2PL
LIFO release discipline. -/
theorem lockSet_released_in_reverse (S : LockSet) :
    (releaseOrder S).Pairwise (· ≥ ·) := by
  unfold releaseOrder
  -- The reverse of an ascending list is descending.
  rw [List.pairwise_reverse]
  -- Goal: (acquireOrder S).Pairwise (fun a b => b ≤ a) — but ≥ flips it.
  exact lockSet_acquired_in_order S

-- ============================================================================
-- §4 — SM3.C.7 — `lockSet_atomic_under_2pl`
-- ============================================================================

/-- WS-SM SM3.C.7 helper (**WS-LS LS2.1**: over the pair): the ghost bracket
factors into three sequentially-composed phases — the growing phase on the
lock table, the action on the kernel state, the shrinking phase on the table.

This is a definitional unfolding witness; SM3.E's serializability
proof appeals to it to argue that no external observer can
interleave with the action phase. -/
theorem withLockSet_three_phase_decomposition {α : Type} (S : LockSet)
    (core : CoreId) (action : SystemState → SystemState × α)
    (s : LockedSystemState) :
    let acquired := LockState.acquireAll core S.lockAcquireSequence s.locks
    let (postAction, result) := action s.kernel
    let unwound := LockState.unwindAll core S.lockAcquireSequence.reverse acquired
    withLockSetGhost S core action s = (⟨postAction, unwound⟩, result) := by
  rfl

/-- WS-SM SM3.C.7 (plan §5.3 Theorem 2.1.10 operational form; **WS-LS LS2.1**:
over the pair): the bracket yields an atomic-from-observer-view state
transition.

"Atomic from observer view" means: the kernel half of the bracket's result
is the post-state of `action` with all the action's mutations and nothing
else, and the lock half is the bracket's trace, which no kernel state
carries.  No external observer can see an intermediate state where some of
the action's mutations have applied but others haven't, because the action
is the only phase that touches the kernel half — the growing and shrinking
phases change the table alone, by type.  Before LS2.1 the phases wrote lock
words into kernel objects and this needed a lock-insensitive observer; over
the pair it is `rfl`. -/
theorem lockSet_atomic_under_2pl {α : Type} (S : LockSet) (core : CoreId)
    (action : SystemState → SystemState × α) (s : LockedSystemState) :
    let (postAction, result) := action s.kernel
    withLockSetGhost S core action s =
      (⟨postAction, LockState.bracket core S s.locks⟩, result) := by
  rfl

-- ============================================================================
-- §4b — SM3.C.7 — Observational atomicity
-- ============================================================================

/-- WS-SM SM3.C.7 (plan §5.3 Theorem 2.1.10, observer-atomicity capstone;
**WS-LS LS2.1**: over the pair, hypothesis-free): for **every** observer `π`
of the kernel state the bracket is invisible — the post-bracket projection is
the action's projection of the pre-state.  From the observer's view the
transition is atomic: it sees `π s.kernel` before and the action's `π`-image
after, never a partial state arising from the lock phases, because the
phases touch only `locks`.

Before LS2.1 this took the observer's acquire- and unwind-insensitivity, and
two guarded forms (`lockSet_observer_atomic_on`,
`lockSet_observer_atomic_of_objectStoreObserver`) threaded an `invExt` guard
through the folds for observers of the object store; both collapse into this
one statement, which is what the IPC capstones (`endpointCallOnCore_observer_atomic`
and its siblings) now instantiate. -/
theorem lockSet_observer_atomic {α β : Type} (S : LockSet) (core : CoreId)
    (action : SystemState → SystemState × α) (s : LockedSystemState)
    (π : SystemState → β) :
    π (withLockSetGhost S core action s).1.kernel = π (action s.kernel).1 := rfl

-- ---------------------------------------------------------------------------
-- WS-RR RR7.4: the two shared decisive observers of the IPC surface
--
-- Register §4 finding 7: every `_atomic_under_lockSet` theorem is a `rfl`
-- instance of the body-agnostic `lockSet_atomic_under_2pl`, and the
-- *substantive* observer form is instantiated by the seven SM6 transitions —
-- `endpointCall`, `endpointReply`, `endpointReplyRecv`, `notificationSignal`,
-- `notificationWait` and the two cancellations — every one of which watches
-- either a thread's IPC state or a notification's delivery state.  Two
-- observers, declared once, rather than seven copies of each.  (Before
-- WS-LS LS2.1 each observer also carried two insensitivity facts; over the
-- pair there is nothing for an observer to be insensitive to.)
--
-- Parameterised by an arbitrary thread / notification rather than by "the"
-- decisive one: the capstones then hold for *every* choice, which is strictly
-- stronger than picking the receiver, and removes the judgement call about
-- which participant a composite transition's decisive observable is.
-- ---------------------------------------------------------------------------

/-- **WS-RR RR7.4**: a thread's IPC state — the field every IPC rendezvous
writes and the one a partially-locked intermediate would expose. -/
def threadIpcStateObserver (tid : SeLe4n.ThreadId) : SystemState → Option ThreadIpcState :=
  fun s => (s.getTcb? tid).map TCB.ipcState

/-- **WS-RR RR7.4**: a notification's delivery state — its `state` (which
carries the pending badge) and its waiter list, as one projection so a caller
cannot watch half of the rendezvous. -/
def notificationDeliveryObserver (nid : SeLe4n.ObjId) :
    SystemState → Option (NotificationState × SeLe4n.NoDupList SeLe4n.ThreadId) :=
  fun s => (s.getNotification? nid).map (fun n => (n.state, n.waitingThreads))

-- ============================================================================
-- §5 — SM3.C.8 — `withLockSet_invariant_preserved` (Corollary 2.1.11)
-- ============================================================================

/-- WS-SM SM3.C.8 (plan §3.9 Corollary 2.1.11; **WS-LS LS2.1**: over the pair,
strengthened): the SMP-migration metatheorem.  A kernel invariant `post` the
bare action preserves is preserved by the bracketed action, because the
bracket's phases do not touch the kernel half.

Before LS2.1 this took three lock-insensitivity hypotheses (`post` survives a
single acquire, release and withdrawal at any key) and a separate acquire-fold
form, `lockSet_invariant_preserved`, carried the growing phase; both existed
because the word-level phases rewrote kernel objects.  Over the pair the three
hypotheses are dropped and the acquire-fold form has no state to be about (the
action runs on `s.kernel`).  What remains is the lever the corollary always
was: every single-core kernel-transition theorem lifts to the bracketed form
with its own proof, which is how `endpointCallOnCore_withLockSet_preserves_objects_invExt`
consumes it. -/
theorem withLockSet_invariant_preserved {α : Type} (S : LockSet) (core : CoreId)
    (action : SystemState → SystemState × α) (s : LockedSystemState)
    (post : SystemState → Prop)
    (hPre : post s.kernel)
    (hActionPreserves : ∀ s', post s' → post (action s').1) :
    post (withLockSetGhost S core action s).1.kernel :=
  hActionPreserves s.kernel hPre

-- ============================================================================
-- §5b — The word-level growing phase (retired with the words at LS3.1)
-- ============================================================================
-- These are about the lock words in kernel objects, which the word-level
-- `withLockSet` still writes until LS2.2 switches the seams and LS3.1 deletes
-- the words.  Their ghost forms are `LockState.acquireAll_unheld_heldAll_pairs`
-- (the growing phase holds the footprint, with no object-presence hypothesis)
-- and `LockState.bracket_unheld` (the round trip).
/-- WS-SM SM3.C.8 (audit-pass-1, Comment 7): **substantive**
acquire-establishes-holding theorem — replaces the previous
tautological `_unchanged_outside_lockSet` placeholder the codex
review correctly flagged as a false verification anchor.

Under the precondition that the table-level `objStoreLock` is
**available** (`unheld`), acquiring it via `acquireLockOnObject`
produces a state where the lock is genuinely **held** by `core`
in the requested mode — `lockHeld core ⟨.objStore, oid⟩ mode`
holds on the post-acquire state.

This is the honest bridge the reviewer asked for: it actually
involves the acquire phase and the transformed state, proving that
on an available lock the action runs with the lock held (not merely
`hHeld → hHeld`).  Lifts `RwLockState.unheld_acquire_grants`
through the `acquireLockOnObject` `.objStore` branch and the
`lockHeld` `.objStore` projection. -/
theorem acquireLockOnObject_objStore_establishes_lockHeld
    (s : SystemState) (core : CoreId) (oid : SeLe4n.ObjId) (mode : AccessMode)
    (hAvail : s.objStoreLock = RwLockState.unheld) :
    lockHeld core ⟨.objStore, oid⟩ mode
      (acquireLockOnObject s core ⟨.objStore, oid⟩ mode) := by
  -- The objStore branch sets objStoreLock := s.objStoreLock.applyOp …
  unfold acquireLockOnObject lockHeld
  simp only
  -- Post-state objStoreLock = unheld.applyOp (mode.toAcquireOp core).
  rw [hAvail]
  exact RwLockState.unheld_acquire_grants core mode

/-- WS-SM SM3.C.8 (audit-pass-1, Comment 4): acquiring then releasing
the table-level lock from an **available** state returns it to
`unheld` — NO waiter leak.

Refutes the waiter-leak concern for the abstract single-core model:
because the acquire GRANTED (the lock was available), the symmetric
release cleanly removes the holder and the lock round-trips to
`unheld`.  Lifts `RwLockState.unheld_acquire_release_roundtrip`
through the `acquireLockOnObject` / `releaseLockOnObject`
`.objStore` branches. -/
theorem acquireLockOnObject_objStore_release_roundtrip
    (s : SystemState) (core : CoreId) (oid : SeLe4n.ObjId) (mode : AccessMode)
    (hAvail : s.objStoreLock = RwLockState.unheld) :
    (releaseLockOnObject (acquireLockOnObject s core ⟨.objStore, oid⟩ mode)
      core ⟨.objStore, oid⟩ mode).objStoreLock = RwLockState.unheld := by
  unfold acquireLockOnObject releaseLockOnObject
  simp only
  rw [hAvail]
  exact RwLockState.unheld_acquire_release_roundtrip core mode

/-- WS-SM SM3.C.8 helper: two `LockId`s with equal `kind` and `objId`
components are equal (`LockId` carries exactly those two fields). -/
theorem lockId_eq_of_components {l₁ l₂ : LockId}
    (hk : l₁.kind = l₂.kind) (ho : l₁.objId = l₂.objId) : l₁ = l₂ := by
  cases l₁; cases l₂; simp_all

/-- WS-SM SM3.C.8 foundation: in a well-formed `LockSet` whose every pair
resolves to a present object of matching kind, the canonical acquisition
sequence has pairwise-distinct ObjIds.

Two pairs sharing an ObjId would both resolve to the object stored there, hence
have that object's `lockKind`, hence the same `kind` AND the same `objId`, hence
the same `LockId` key — contradicting the `Nodup`-keys invariant
(`LockSet.fst_inj_at_pairs`).  This is why the SM3.C.8 multi-lock establishment
hypothesis (distinct ObjIds) is automatically met by any state-resolvable
lock set. -/
theorem lockAcquireSequence_distinct_objId_of_resolves (S : LockSet)
    (s : SystemState)
    (hEach : ∀ p ∈ S.pairs, ∃ l o, p.fst = .object l ∧ s.objects[l.objId]? = some o ∧
        o.lockKind = l.kind) :
    S.lockAcquireSequence.Pairwise (fun a b => a.fst.objId? ≠ b.fst.objId?) := by
  have hPairsNodup : S.pairs.Nodup :=
    (List.pairwise_map.mp S.hUniqueKeys).imp
      (fun hfst heq => hfst (congrArg Prod.fst heq))
  have hSeqNodup : S.lockAcquireSequence.Nodup :=
    (LockSet.lockAcquireSequence_perm S).nodup_iff.mpr hPairsNodup
  refine hSeqNodup.imp_of_mem ?_
  intro a b ha hb hab hObjEq
  apply hab
  have haP : a ∈ S.pairs :=
    (LockSet.mem_def a S).mp ((LockSet.lockAcquireSequence_complete S a).mpr ha)
  have hbP : b ∈ S.pairs :=
    (LockSet.mem_def b S).mp ((LockSet.lockAcquireSequence_complete S b).mpr hb)
  obtain ⟨la, oa, hLa, hPa, hKa⟩ := hEach a haP
  obtain ⟨lb, ob, hLb, hPb, hKb⟩ := hEach b hbP
  have hIdEq : la.objId = lb.objId := by
    rw [hLa, hLb, LockKey.objId?_object, LockKey.objId?_object] at hObjEq
    exact Option.some.inj hObjEq
  have hoEq : oa = ob := by
    have hObj : s.objects[la.objId]? = s.objects[lb.objId]? := by rw [hIdEq]
    rw [hPa, hPb] at hObj
    exact Option.some.inj hObj
  have hKindEq : la.kind = lb.kind := by rw [← hKa, hoEq, hKb]
  refine LockSet.fst_inj_at_pairs S haP hbP ?_
  rw [hLa, hLb, lockId_eq_of_components hKindEq hIdEq]

/-- WS-SM SM3.C.8 (substantive — the LockSet-level "acquireAll establishes
lockSetHeld" theorem): `withLockSet`'s growing phase genuinely puts the
declared lock set into the held state.

If every lock in `S` resolves to a present, kind-matching, `unheld` object in
the pre-state `s`, then after the canonical acquire fold the executing `core`
holds the entire lock set: `lockSetHeld core S (acquireAll core
S.lockAcquireSequence s)`.

This is the bridge the SM3.C.8 metatheorem's `lockSetHeld` precondition rests
on — it is not an arbitrary assumption but a *consequence* of the 2PL growing
phase on an available lock set.  Combines the multi-lock establishment
(`acquireAll_establishes_lockHeld_of_distinct_present_unheld`) with the
automatic ObjId-distinctness
(`lockAcquireSequence_distinct_objId_of_resolves`) and the
sequence ↔ pairs membership bridge (`lockAcquireSequence_complete`). -/
theorem acquireAll_establishes_lockSetHeld (S : LockSet) (core : CoreId)
    (s : SystemState)
    (hExt : s.objects.invExt)
    (hEach : ∀ p ∈ S.pairs, ∃ l o, p.fst = .object l ∧ s.objects[l.objId]? = some o ∧
        o.lockKind = l.kind ∧ o.objectLockOf = RwLockState.unheld) :
    lockSetHeld core S (acquireAll core S.lockAcquireSequence s) := by
  have hEachSeq : ∀ p ∈ S.lockAcquireSequence, ∃ l o, p.fst = .object l ∧
      s.objects[l.objId]? = some o ∧ o.lockKind = l.kind ∧
      o.objectLockOf = RwLockState.unheld := fun p hp =>
    hEach p ((LockSet.mem_def p S).mp ((LockSet.lockAcquireSequence_complete S p).mpr hp))
  have hDistinct := lockAcquireSequence_distinct_objId_of_resolves S s
    (fun p hp => by obtain ⟨l, o, h0, h1, h2, _⟩ := hEach p hp; exact ⟨l, o, h0, h1, h2⟩)
  have hAll := acquireAll_establishes_lockHeld_of_distinct_present_unheld core
    S.lockAcquireSequence s hExt hEachSeq hDistinct
  intro p hp
  exact hAll p ((LockSet.lockAcquireSequence_complete S p).mp ((LockSet.mem_def p S).mpr hp))

-- ============================================================================
-- §6 — SM3.C aggregator theorems (architectural anchors)
-- ============================================================================

/-- WS-SM SM3.C aggregate: every `withLockSet` invocation acquires
in ascending order AND releases in descending order.

This is the strict-2PL aggregator that combines SM3.C.5 and
SM3.C.6 into a single witness — useful as an architectural anchor
for SM3.D's deadlock-freedom proof. -/
theorem withLockSet_satisfies_strict_2PL (S : LockSet) :
    (acquireOrder S).Pairwise (· ≤ ·) ∧
    (releaseOrder S).Pairwise (· ≥ ·) :=
  ⟨lockSet_acquired_in_order S, lockSet_released_in_reverse S⟩

/-- WS-SM SM3.C aggregate (**WS-LS LS2.1**: over the pair): the bracket
produces the action's kernel state beside the bracket's lock trace.

This is the canonical "what does the bracket compute" witness —
useful for SM3.E.3's serializability proof's serial-equivalent
construction. -/
theorem withLockSet_computation {α : Type} (S : LockSet) (core : CoreId)
    (action : SystemState → SystemState × α) (s : LockedSystemState) :
    withLockSetGhost S core action s =
      (⟨(action s.kernel).1, LockState.bracket core S s.locks⟩, (action s.kernel).2) :=
  withLockSetGhost_eq_decomposition S core action s

end SeLe4n.Kernel.Concurrency
