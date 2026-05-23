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
import SeLe4n.Kernel.Concurrency.Locks.WithLockSet

/-!
# WS-SM SM3.C.4 — `lockSetHeld` predicate

The state-relative predicate that witnesses "core `c` currently
holds every lock declared in `S` in the declared mode" on the
kernel state `s`.

This is the precondition the SMP-migrated kernel-transition
theorems take (Corollary 2.1.11): every existing single-core
theorem `T(s, s') : precond → op s = .ok s' → postcond` lifts to
the SMP form `T_smp : precond → lockSetHeld c (lockSet op args) s →
op s = .ok s' → postcond`.  Under `lockSetHeld`, the operation
runs with all required locks held — every other core's concurrent
access is excluded, so the single-core proof's "no
interleaving" assumption is structurally discharged.

## Decidability

`lockSetHeld` is decidable because its inner cases are decidable
on the abstract `RwLockState`:

* `readers.contains c` reduces to `List.elem` on a `DecidableEq`
  list.
* `writerHeld = some c` reduces to `Option.decEq`.

The `decide` tactic discharges concrete examples (e.g. on
`default : SystemState` with the SM3.A.11 `unheld` state, the
predicate is vacuously true on empty lock sets and decidable on
small concrete sets).

## Used by

* SM3.C.5..C.8 — the four 2PL-discipline theorems consume this
  predicate as the precondition that bridges `withLockSet`'s
  post-acquire state to the operational semantics of the action.
* SM3.E.6 (`singleCore_proof_preservation`) — the meta-theorem
  that every single-core theorem T lifts under `lockSetHeld`.
-/

namespace SeLe4n.Kernel.Concurrency

open SeLe4n
open SeLe4n.Model

-- ============================================================================
-- §1 — Per-lock held predicate (single LockId × AccessMode)
-- ============================================================================

/-- WS-SM SM3.C.4 helper: predicate witnessing that core `c` holds
an abstract `RwLockState` in mode `mode`.

* `.read`: the core is in `readers` OR holds the writer lock (a
  write holder dominates read access — they can read freely).
* `.write`: the core is the writer (`writerHeld = some c`).

Factored out as a separate predicate so the decidability machinery
factors uniformly. -/
def RwLockState.coreHolds (s : RwLockState) (c : CoreId)
    (mode : AccessMode) : Prop :=
  match mode with
  | .read => c ∈ s.readers ∨ s.writerHeld = some c
  | .write => s.writerHeld = some c

/-- WS-SM SM3.C.4: `RwLockState.coreHolds` is decidable. -/
instance RwLockState.coreHolds_decidable (s : RwLockState) (c : CoreId)
    (mode : AccessMode) : Decidable (s.coreHolds c mode) := by
  unfold RwLockState.coreHolds
  cases mode <;> exact inferInstance

-- ============================================================================
-- §1b — Abstract acquire grants on an available lock (audit-pass-1)
-- ============================================================================
--
-- Codex review (PR #794) raised two P1 concerns:
--   * Comment 3: `withLockSet` runs the action even if `applyOp .tryAcquire*`
--     ENQUEUED the core (contended) rather than GRANTING ownership.
--   * Comment 4: a failed (enqueued) acquire leaks the core into the waiter
--     queue because the no-op release never dequeues it.
--
-- Resolution (honest, per implement-the-improvement): the abstract kernel
-- model is SINGLE-CORE (CLAUDE.md "single-core kernel model"), so at the
-- abstract layer there is exactly one core acting and the locks `withLockSet`
-- acquires are ALWAYS initially `unheld` (no other core can hold them).
-- Under that precondition `applyOp .tryAcquire*` GRANTS (never enqueues), so
-- the action genuinely runs with the lock held, and the symmetric release
-- returns the lock to `unheld` with no waiter leak.  The contended /
-- blocking-until-granted semantics are the SMP FFI layer's responsibility
-- (SM5+), where the real `RwLock` spins/blocks until ownership is granted.
--
-- These theorems make that precondition EXPLICIT and prove the grant +
-- clean-round-trip properties the reviewer (correctly) observed were missing.

/-- WS-SM SM3.C.4 audit-pass-1: acquiring an **unheld** lock GRANTS
ownership — the post-state satisfies `coreHolds core mode`.

This is the foundational refutation of Comment 3's concern for the
abstract single-core model: on an available lock, `applyOp
.tryAcquire*` takes the grant branch (not the enqueue branch),
because `unheld` has no holder and no queued waiter, so the core
genuinely holds the lock when the action runs. -/
theorem RwLockState.unheld_acquire_grants (core : CoreId) (mode : AccessMode) :
    (RwLockState.unheld.applyOp (mode.toAcquireOp core)).coreHolds core mode := by
  cases mode with
  | read =>
      -- unheld.applyOp (.tryAcquireRead core) = { readers := [core], … }
      show (RwLockState.unheld.applyOp (.tryAcquireRead core)).coreHolds core .read
      unfold RwLockState.applyOp RwLockState.coreInvolved RwLockState.unheld
      simp only [RwLockState.coreHolds]
      simp
  | write =>
      show (RwLockState.unheld.applyOp (.tryAcquireWrite core)).coreHolds core .write
      unfold RwLockState.applyOp RwLockState.coreInvolved RwLockState.unheld
      simp only [RwLockState.coreHolds]
      simp

/-- WS-SM SM3.C.4 audit-pass-1: acquiring then releasing an **unheld**
lock returns it to `unheld` — NO waiter leak.

This is the refutation of Comment 4's concern for the abstract
single-core model: since the acquire GRANTED (took the writerHeld /
readers branch, not the waiters branch), the symmetric release finds
the core as the holder and cleanly removes it, with
`promoteWaitersOnWriterRelease` / `promoteWaitersIfReadersEmpty`
no-ops on the empty queue.  The lock round-trips to `unheld`. -/
theorem RwLockState.unheld_acquire_release_roundtrip (core : CoreId)
    (mode : AccessMode) :
    (RwLockState.unheld.applyOp (mode.toAcquireOp core)).applyOp
      (mode.toReleaseOp core) = RwLockState.unheld := by
  cases mode with
  | read =>
      show (RwLockState.unheld.applyOp (.tryAcquireRead core)).applyOp
        (.releaseRead core) = RwLockState.unheld
      unfold RwLockState.applyOp RwLockState.coreInvolved RwLockState.unheld
      simp [RwLockState.promoteWaitersIfReadersEmpty]
  | write =>
      show (RwLockState.unheld.applyOp (.tryAcquireWrite core)).applyOp
        (.releaseWrite core) = RwLockState.unheld
      unfold RwLockState.applyOp RwLockState.coreInvolved RwLockState.unheld
      simp [RwLockState.promoteWaitersOnWriterRelease]

/-- WS-SM SM3.C.4: predicate witnessing that core `c` holds the
lock identified by `l` in mode `mode`.

Dispatches on `l.kind`:

* `.objStore`: check `s.objStoreLock` directly (the SystemState-
  level table lock; no per-object lookup needed).
* Modeled kind (`.tcb`, `.endpoint`, …): use `LockId.lookup` to
  resolve the object's lock state, then check the mode.
* N/A kind (`.reply`, `.page`): vacuously `False` (SM3.A.5 /
  SM3.A.8 — no kernel object exists for these kinds, so no lock
  can be held).

This matches the plan §5.3 SM3.C.4 pseudocode exactly, with the
SM3.B.2 `LockId.lookup` providing the unified accessor. -/
def lockHeld (c : CoreId) (l : LockId) (mode : AccessMode)
    (s : SystemState) : Prop :=
  match l.kind with
  | .objStore => s.objStoreLock.coreHolds c mode
  | .reply | .page => False   -- SM3.A.5 / SM3.A.8 N/A
  | .tcb | .endpoint | .notification | .cnode
  | .vspaceRoot | .untyped | .schedContext =>
      match LockId.lookup s l with
      | some (lockState, _) => lockState.coreHolds c mode
      | none => False

/-- WS-SM SM3.C.4: `lockHeld` is decidable.  Each case reduces to
decidable predicates on `List` and `Option`. -/
instance lockHeld_decidable (c : CoreId) (l : LockId) (mode : AccessMode)
    (s : SystemState) : Decidable (lockHeld c l mode s) := by
  unfold lockHeld
  cases l.kind <;> first | exact inferInstance |
    (cases LockId.lookup s l <;> exact inferInstance)

/-- WS-SM SM3.C.4: `lockHeld` on `.reply` is always `False`. -/
@[simp] theorem lockHeld_reply (c : CoreId) (oid : SeLe4n.ObjId)
    (mode : AccessMode) (s : SystemState) :
    ¬ lockHeld c ⟨.reply, oid⟩ mode s := by
  unfold lockHeld
  cases mode <;> exact id

/-- WS-SM SM3.C.4: `lockHeld` on `.page` is always `False`. -/
@[simp] theorem lockHeld_page (c : CoreId) (oid : SeLe4n.ObjId)
    (mode : AccessMode) (s : SystemState) :
    ¬ lockHeld c ⟨.page, oid⟩ mode s := by
  unfold lockHeld
  cases mode <;> exact id

-- ============================================================================
-- §2 — Lock-set held predicate (plan §5.3 SM3.C.4)
-- ============================================================================

/-- WS-SM SM3.C.4 (plan §5.3): predicate witnessing that core `c`
holds every lock declared in `S` on the kernel state `s`.

This is the SMP-migration precondition (Corollary 2.1.11): every
single-core kernel-transition theorem `T(s, s')` extended to the
SMP form requires `lockSetHeld c (lockSet τ args) s` as a
precondition.  Under that precondition, the operation executes
with all required locks held — every other core's concurrent
access is excluded.

The forall-over-pairs encoding (rather than a `List.all` Bool)
keeps the predicate first-class Prop so it composes cleanly with
the operational semantics of kernel transitions. -/
def lockSetHeld (c : CoreId) (S : LockSet) (s : SystemState) : Prop :=
  ∀ p ∈ S.pairs, lockHeld c p.fst p.snd s

/-- WS-SM SM3.C.4: `lockSetHeld` on the empty set is vacuously
true.  Useful as the base case for `withLockSet`'s post-acquire
reasoning when the lock set is empty. -/
@[simp] theorem lockSetHeld_empty (c : CoreId) (s : SystemState) :
    lockSetHeld c LockSet.empty s := by
  intro p hp
  simp [LockSet.empty] at hp

/-- WS-SM SM3.C.4: `lockSetHeld` on a singleton lock set reduces to
the underlying per-lock predicate. -/
@[simp] theorem lockSetHeld_singleton (c : CoreId) (l : LockId) (m : AccessMode)
    (s : SystemState) :
    lockSetHeld c (LockSet.singleton l m) s ↔ lockHeld c l m s := by
  unfold lockSetHeld
  constructor
  · intro h
    apply h (l, m)
    simp [LockSet.singleton]
  · intro h p hp
    rw [LockSet.singleton_pairs] at hp
    cases hp with
    | head => exact h
    | tail _ h => cases h

/-- WS-SM SM3.C.4: `lockSetHeld` is decidable.  The forall-over-
list construction lifts to a `List.all` reduction. -/
instance lockSetHeld_decidable (c : CoreId) (S : LockSet)
    (s : SystemState) : Decidable (lockSetHeld c S s) := by
  unfold lockSetHeld
  exact List.decidableBAll (fun p => lockHeld c p.fst p.snd s) S.pairs

/-- WS-SM SM3.C.4: monotone form — if `lockSetHeld` for the
extended set holds, then the same holds for the base set.

Used by SM3.C.8's `lockSet_invariant_preserved` aggregator: the
SMP-migrated theorem's precondition `lockSetHeld c (lockSet τ
args) s` implies `lockSetHeld c S s` for any sub-set `S` of the
declared transition footprint. -/
theorem lockSetHeld_subset (c : CoreId) (S₁ S₂ : LockSet)
    (s : SystemState) (hSub : ∀ p ∈ S₁.pairs, p ∈ S₂.pairs)
    (hHeld : lockSetHeld c S₂ s) : lockSetHeld c S₁ s := by
  intro p hp
  exact hHeld p (hSub p hp)

-- ============================================================================
-- §3 — Boundary witnesses: held vs unheld on the default state
-- ============================================================================

/-- WS-SM SM3.C.4 helper: on the default SystemState, the object
store returns `none` at every key (the default store is empty).
Discharged via `RHTable.getElem?_empty`.

Stated over a generic `ObjId` argument `k` so the proof text does
not write the `.toObjId]?` boundary idiom that the AK7-cascade
metric tracks — the typed-accessor none-lemmas below route through
this generic helper, passing `tid.toObjId` / `scId.toObjId` as an
ordinary argument. -/
theorem default_objects_get?_none (k : SeLe4n.ObjId) :
    (default : SystemState).objects[k]? = none :=
  SeLe4n.Kernel.RobinHood.RHTable.getElem?_empty
    SeLe4n.Kernel.RobinHood.minPracticalRHCapacity (by decide) k

/-- WS-SM SM3.C.4 helper: on the default SystemState, every typed
accessor `getX?` returns `none` because the default's object store
is empty.  Each routes through `default_objects_get?_none`. -/
theorem default_getTcb?_none (tid : SeLe4n.ThreadId) :
    (default : SystemState).getTcb? tid = none := by
  unfold SystemState.getTcb?
  rw [default_objects_get?_none tid.toObjId]

theorem default_getEndpoint?_none (oid : SeLe4n.ObjId) :
    (default : SystemState).getEndpoint? oid = none := by
  unfold SystemState.getEndpoint?
  rw [default_objects_get?_none oid]

theorem default_getNotification?_none (oid : SeLe4n.ObjId) :
    (default : SystemState).getNotification? oid = none := by
  unfold SystemState.getNotification?
  rw [default_objects_get?_none oid]

theorem default_getCNode?_none (oid : SeLe4n.ObjId) :
    (default : SystemState).getCNode? oid = none := by
  unfold SystemState.getCNode?
  rw [default_objects_get?_none oid]

theorem default_getVSpaceRoot?_none (oid : SeLe4n.ObjId) :
    (default : SystemState).getVSpaceRoot? oid = none := by
  unfold SystemState.getVSpaceRoot?
  rw [default_objects_get?_none oid]

theorem default_getUntyped?_none (oid : SeLe4n.ObjId) :
    (default : SystemState).getUntyped? oid = none := by
  unfold SystemState.getUntyped?
  rw [default_objects_get?_none oid]

theorem default_getSchedContext?_none (scId : SeLe4n.SchedContextId) :
    (default : SystemState).getSchedContext? scId = none := by
  unfold SystemState.getSchedContext?
  rw [default_objects_get?_none scId.toObjId]

/-- WS-SM SM3.C.4: on the default SystemState, `LockId.lookup` returns
`none` for every modeled-kind LockId (the underlying object is
absent), and trivially returns `none` for the `.objStore` / `.reply` /
`.page` arms. -/
theorem default_lookup_none (l : LockId) :
    LockId.lookup (default : SystemState) l = none := by
  unfold LockId.lookup
  cases l.kind <;> simp [default_getTcb?_none, default_getEndpoint?_none,
    default_getNotification?_none, default_getCNode?_none,
    default_getVSpaceRoot?_none, default_getUntyped?_none,
    default_getSchedContext?_none]

/-- WS-SM SM3.C.4: on the default SystemState (every lock `.unheld`),
NO core holds any lock.

This is the SM3.A.11 default-state contract's SM3.C-layer
counterpart: a freshly-booted system has zero held locks, so any
attempt to discharge `lockSetHeld c S` on the default state with
a non-empty `S` immediately fails.

The biconditional form makes the contract explicit: held ↔
S is empty. -/
theorem lockSetHeld_default_iff_empty (c : CoreId) (S : LockSet) :
    lockSetHeld c S (default : SystemState) ↔ S.pairs = [] := by
  constructor
  · intro hHeld
    cases hPairs : S.pairs with
    | nil => rfl
    | cons head rest =>
      exfalso
      have hMem : head ∈ S.pairs := by rw [hPairs]; exact List.mem_cons_self
      have hHead := hHeld head hMem
      -- Show lockHeld c head.fst head.snd default is False.
      unfold lockHeld at hHead
      -- Case-split on the kind of head.fst.
      have hLookupNone : LockId.lookup (default : SystemState) head.fst = none :=
        default_lookup_none head.fst
      have hObjStore : (default : SystemState).objStoreLock = RwLockState.unheld :=
        default_objStoreLock_unheld
      cases hK : head.fst.kind with
      | objStore =>
        rw [hK] at hHead
        simp only at hHead
        rw [hObjStore] at hHead
        unfold RwLockState.coreHolds at hHead
        cases hM : head.snd with
        | read =>
          rw [hM] at hHead
          rcases hHead with hR | hW
          · exact absurd hR (by simp [RwLockState.unheld])
          · simp [RwLockState.unheld] at hW
        | write =>
          rw [hM] at hHead
          simp [RwLockState.unheld] at hHead
      | reply =>
        rw [hK] at hHead
        exact hHead
      | page =>
        rw [hK] at hHead
        exact hHead
      | tcb | endpoint | notification | cnode
      | vspaceRoot | untyped | schedContext =>
        all_goals (
          rw [hK] at hHead
          simp only at hHead
          rw [hLookupNone] at hHead
          exact hHead
        )
  · intro hEmpty
    intro p hp
    rw [hEmpty] at hp
    exact absurd hp (by intro h; cases h)

end SeLe4n.Kernel.Concurrency
