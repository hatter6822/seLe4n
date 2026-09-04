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
  | .page => False   -- SM3.A.8 N/A (pages inline in VSpaceRoot.mappings)
  | .tcb | .endpoint | .notification | .cnode
  | .vspaceRoot | .untyped | .schedContext | .reply =>
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

/-- WS-SM SM6.D: the `.reply` lock is not held when no Reply object is
present at `oid` — `getReply?` misses, so `lockHeld` falls through the
modeled (lookup) branch to `False`.  Reply is now a first-class kernel
object, so the former unconditional `¬ lockHeld .reply` is replaced by this
absence-conditioned form; once a Reply object is present and its lock
acquired, the lock can be held. -/
theorem lockHeld_reply (c : CoreId) (oid : SeLe4n.ObjId)
    (mode : AccessMode) (s : SystemState)
    (hAbsent : s.getReply? ⟨oid.val⟩ = none) :
    ¬ lockHeld c ⟨.reply, oid⟩ mode s := by
  have hLook : LockId.lookup s ⟨.reply, oid⟩ = none := by
    rw [LockId.lookup_reply, hAbsent]; rfl
  simp [lockHeld, hLook]

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

theorem default_getReply?_none (replyId : SeLe4n.ReplyId) :
    (default : SystemState).getReply? replyId = none := by
  unfold SystemState.getReply?
  rw [default_objects_get?_none replyId.toObjId]

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
    default_getSchedContext?_none, default_getReply?_none]

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
      | page =>
        rw [hK] at hHead
        exact hHead
      | tcb | endpoint | notification | cnode
      | vspaceRoot | untyped | schedContext | reply =>
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

-- ============================================================================
-- §4 — Acquire establishes `lockHeld` (SM3.C.8 establishment foundation +
--      SM3.C.11.c conjunct-1 foundation)
-- ============================================================================
--
-- The audit-pass-4 closure of the SM3.C.8 "no theorem that `acquireAll`
-- establishes `lockSetHeld`" gap and the SM3.C.11.c "conjunct 1 (every TCB
-- write-locked) never established" gap.  Both reduce to one substantive
-- multi-lock establishment lemma over a list of modeled per-object locks at
-- distinct ObjIds, plus the supporting single-lock establishment + frame
-- lemmas.

/-- WS-SM SM3.C.8 foundation: `LockId.lookup` reads ONLY the object stored at
`l.objId`.  If two states agree on `objects[l.objId]?` they agree on
`LockId.lookup _ l`.

The modeled-kind arms of `LockId.lookup` each route through a typed `getX?`
accessor that reads `objects[l.objId]?` (the `.tcb` / `.schedContext` arms via
`⟨l.objId.val⟩.toObjId = l.objId`); the `.objStore` / `.reply` / `.page` arms
are `none` regardless of the state.  This is the frame lemma every lock-frame
result below factors through. -/
theorem LockId.lookup_eq_of_objects_getElem?_eq (s s' : SystemState) (l : LockId)
    (h : s'.objects[l.objId]? = s.objects[l.objId]?) :
    LockId.lookup s' l = LockId.lookup s l := by
  have hObjIdTcb : (⟨l.objId.val⟩ : SeLe4n.ThreadId).toObjId = l.objId := by
    show SeLe4n.ObjId.ofNat l.objId.val = l.objId
    exact SeLe4n.ObjId.ofNat_toNat l.objId
  have hObjIdSc : (⟨l.objId.val⟩ : SeLe4n.SchedContextId).toObjId = l.objId := by
    show SeLe4n.ObjId.ofNat l.objId.val = l.objId
    exact SeLe4n.ObjId.ofNat_toNat l.objId
  have hObjIdRp : (⟨l.objId.val⟩ : SeLe4n.ReplyId).toObjId = l.objId := by
    show SeLe4n.ObjId.ofNat l.objId.val = l.objId
    exact SeLe4n.ObjId.ofNat_toNat l.objId
  unfold LockId.lookup
  cases l.kind with
  | objStore => rfl
  | reply =>
      simp only [SystemState.getReply?, hObjIdRp, h]
  | page => rfl
  | tcb =>
      simp only [SystemState.getTcb?, hObjIdTcb, h]
  | endpoint =>
      simp only [SystemState.getEndpoint?, h]
  | notification =>
      simp only [SystemState.getNotification?, h]
  | cnode =>
      simp only [SystemState.getCNode?, h]
  | vspaceRoot =>
      simp only [SystemState.getVSpaceRoot?, h]
  | untyped =>
      simp only [SystemState.getUntyped?, h]
  | schedContext =>
      simp only [SystemState.getSchedContext?, hObjIdSc, h]

/-- WS-SM SM3.C.8 foundation: `updateObjectLockAt` at lock `l` leaves the
object stored at any other ObjId unchanged.  Routes through
`RHTable.getElem?_insert_ne` for the kind-matched insert branch; both
fail-closed branches (absent / kind-mismatch) leave `objects` untouched. -/
theorem updateObjectLockAt_objects_getElem?_of_ne (s : SystemState)
    (l : LockId) (op : RwLockOp) (oid : SeLe4n.ObjId)
    (hExt : s.objects.invExt) (hNe : oid ≠ l.objId) :
    (updateObjectLockAt s l op).objects[oid]? = s.objects[oid]? := by
  unfold updateObjectLockAt
  cases LockId.lookup s l with
  | none => rfl
  | some _ =>
      unfold updateObjectAt
      cases hG : s.objects.get? l.objId with
      | none => rfl
      | some obj =>
          show (s.objects.insert l.objId (obj.updateLock op))[oid]? = s.objects[oid]?
          exact SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_ne s.objects l.objId oid
            (obj.updateLock op) (by simp [Ne.symm hNe]) hExt

/-- **WS-LC LC4.3**: the fail-closed branch of `updateObjectLockAt` is the
identity — an absent object, or one whose variant does not match `l.kind`,
leaves the state untouched. -/
theorem updateObjectLockAt_eq_self_of_lookup_none (s : SystemState)
    (l : LockId) (op : RwLockOp) (h : LockId.lookup s l = none) :
    updateObjectLockAt s l op = s := by
  unfold updateObjectLockAt; rw [h]

/-- **WS-LC LC4.3**: at the *target* key, a kind-matched `updateObjectLockAt`
maps the stored object through `updateLock`.  The `_of_ne` sibling above
covers every other key; together they characterise the update at any key,
which is what the shrinking phase's frame argument needs. -/
theorem updateObjectLockAt_objects_getElem?_self (s : SystemState)
    (l : LockId) (op : RwLockOp) (r : RwLockState × KernelObject)
    (hExt : s.objects.invExt) (hL : LockId.lookup s l = some r) :
    (updateObjectLockAt s l op).objects[l.objId]?
      = (s.objects[l.objId]?).map (fun o => o.updateLock op) := by
  unfold updateObjectLockAt
  rw [hL]
  show (updateObjectAt s l.objId (fun obj => obj.updateLock op)).objects.get? l.objId = _
  rw [updateObjectAt_get? s l.objId l.objId _ hExt, if_pos rfl]
  rfl

/-- WS-SM SM3.C.8 foundation: `acquireLockOnObject` at lock `l` leaves the
object stored at any other ObjId unchanged.  The `.objStore` / `.reply` /
`.page` arms never touch `objects`; the modeled arms route through
`updateObjectLockAt_objects_getElem?_of_ne`. -/
theorem acquireLockOnObject_objects_getElem?_of_ne (s : SystemState)
    (core : CoreId) (l : LockId) (m : AccessMode) (oid : SeLe4n.ObjId)
    (hExt : s.objects.invExt) (hNe : oid ≠ l.objId) :
    (acquireLockOnObject s core l m).objects[oid]? = s.objects[oid]? := by
  unfold acquireLockOnObject
  cases l.kind with
  | objStore => rfl
  | page => rfl
  | tcb | endpoint | notification | cnode
  | vspaceRoot | untyped | schedContext | reply =>
      all_goals exact updateObjectLockAt_objects_getElem?_of_ne s l _ oid hExt hNe

/-- WS-SM SM3.C.8 foundation: after `updateObjectLockAt s l op` on a present,
kind-matching object `o`, looking up `l` recovers the lock-advanced object.

The pre-state lookup succeeds (`lookup_some_of_kindMatch`), so the kind-checked
update re-inserts `o.updateLock op` at `l.objId`; the post-state lookup recovers
it (`getElem?_insert_self`, kind preserved by `updateLock_preserves_lockKind`).
Isolates the post-acquire lookup computation so the establishment theorem need
not unfold the object store. -/
theorem updateObjectLockAt_lookup_self (s : SystemState) (l : LockId)
    (op : RwLockOp) (o : KernelObject)
    (hExt : s.objects.invExt)
    (hPresent : s.objects[l.objId]? = some o)
    (hKind : o.lockKind = l.kind) :
    LockId.lookup (updateObjectLockAt s l op) l
      = some (KernelObject.objectLockOf (o.updateLock op), o.updateLock op) := by
  have hPre : LockId.lookup s l = some (KernelObject.objectLockOf o, o) :=
    LockId.lookup_some_of_kindMatch s l o hPresent hKind
  unfold updateObjectLockAt
  rw [hPre]
  -- Goal: lookup (updateObjectAt s l.objId (fun obj => obj.updateLock op)) l = …
  have hPresent' :
      (updateObjectAt s l.objId (fun obj => obj.updateLock op)).objects[l.objId]?
        = some (o.updateLock op) := by
    unfold updateObjectAt
    rw [show s.objects.get? l.objId = some o from hPresent]
    show (s.objects.insert l.objId (o.updateLock op))[l.objId]? = some (o.updateLock op)
    exact SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_self s.objects l.objId
      (o.updateLock op) hExt
  have hKind' : (o.updateLock op).lockKind = l.kind := by
    rw [KernelObject.updateLock_preserves_lockKind]; exact hKind
  exact LockId.lookup_some_of_kindMatch _ l (o.updateLock op) hPresent' hKind'

/-- WS-SM SM3.C.8 (substantive): acquiring a **per-object** lock on an
**available** (`unheld`), present, kind-matching object GRANTS the lock —
the post-acquire state satisfies `lockHeld core l mode`.

This is the per-object counterpart to the table-level
`acquireLockOnObject_objStore_establishes_lockHeld` (SM3.C.8 audit-pass-1):
it closes the gap where `lockHeld` on a modeled kind was never shown to be
*establishable* by the acquire primitive.  The chain of reductions:

* the modeled branch of `acquireLockOnObject` routes through
  `updateObjectLockAt`, which (since `LockId.lookup s l` succeeds) re-inserts
  the object with its lock advanced via `KernelObject.updateLock`;
* the post-state lookup recovers the updated object
  (`lookup_some_of_kindMatch` + `getElem?_insert_self`, kind preserved by
  `updateLock_preserves_lockKind`);
* the recovered lock state is `o.objectLockOf.applyOp (mode.toAcquireOp core)`
  (`objectLockOf_updateLock`), which on the `unheld` precondition GRANTS
  ownership (`RwLockState.unheld_acquire_grants`).

The `hUnheld` precondition (object's lock starts `unheld`) is the abstract
single-core model's standing assumption: no other core holds the lock when
the executing core acquires it (the contended/blocking path is the SM5+ FFI
layer's responsibility, per the §1b audit-pass-1 note). -/
theorem acquireLockOnObject_establishes_lockHeld_modeled
    (s : SystemState) (core : CoreId) (l : LockId) (mode : AccessMode)
    (o : KernelObject)
    (hExt : s.objects.invExt)
    (hPresent : s.objects[l.objId]? = some o)
    (hKind : o.lockKind = l.kind)
    (hUnheld : o.objectLockOf = RwLockState.unheld) :
    lockHeld core l mode (acquireLockOnObject s core l mode) := by
  -- The lock id names a modeled kind (its kind is the kind of a real object).
  have hNeObjStore : l.kind ≠ .objStore := by
    rw [← hKind]; exact KernelObject.lockKind_ne_objStore o
  have hNePage : l.kind ≠ .page := by
    rw [← hKind]; exact KernelObject.lockKind_ne_page o
  -- The modeled branch of `acquireLockOnObject` is `updateObjectLockAt`
  -- (WS-SM SM6.D: `.reply` is now a modeled kind, not an N/A no-op).
  have hAcq : acquireLockOnObject s core l mode
      = updateObjectLockAt s l (mode.toAcquireOp core) := by
    unfold acquireLockOnObject
    cases hk : l.kind with
    | objStore => exact absurd hk hNeObjStore
    | page => exact absurd hk hNePage
    | tcb | endpoint | notification | cnode
    | vspaceRoot | untyped | schedContext | reply => all_goals rfl
  rw [hAcq]
  -- The post-acquire lookup recovers the lock-advanced object.
  have hLookup' := updateObjectLockAt_lookup_self s l (mode.toAcquireOp core) o
    hExt hPresent hKind
  unfold lockHeld
  cases hk : l.kind with
  | objStore => exact absurd hk hNeObjStore
  | page => exact absurd hk hNePage
  | tcb | endpoint | notification | cnode
  | vspaceRoot | untyped | schedContext | reply =>
      all_goals (
        rw [hLookup']
        show (KernelObject.objectLockOf
          (o.updateLock (mode.toAcquireOp core))).coreHolds core mode
        rw [KernelObject.objectLockOf_updateLock, hUnheld]
        exact RwLockState.unheld_acquire_grants core mode)

/-- WS-SM SM3.C.8 foundation: `lockHeld` on **any** lock `lA` is unaffected by
acquiring a different-ObjId, non-`.objStore` lock `lB`.

`lockHeld` reads the state only through `s.objStoreLock` (the `.objStore` arm)
and `LockId.lookup s lA` (the modeled arms).  Acquiring a modeled `lB`
(`lB.kind ≠ .objStore`) at `lB.objId ≠ lA.objId` leaves both reads invariant:
the table-level lock is untouched
(`acquireLockOnObject_preserves_objStoreLock_of_modeled`) and the object at
`lA.objId` is untouched
(`acquireLockOnObject_objects_getElem?_of_ne` ⟶ `lookup_eq_of_objects_getElem?_eq`).
Rewriting both reads turns the goal into the pre-state `lockHeld`.  This is the
per-step frame the `acquireAll` fold induction needs to keep already-acquired
locks held. -/
theorem acquireLockOnObject_preserves_lockHeld_of_ne_objId (s : SystemState)
    (core : CoreId) (lA lB : LockId) (mA mB : AccessMode)
    (hExt : s.objects.invExt)
    (hNeObjStoreB : lB.kind ≠ .objStore)
    (hNe : lA.objId ≠ lB.objId)
    (hHeld : lockHeld core lA mA s) :
    lockHeld core lA mA (acquireLockOnObject s core lB mB) := by
  have hFrame : (acquireLockOnObject s core lB mB).objects[lA.objId]?
      = s.objects[lA.objId]? :=
    acquireLockOnObject_objects_getElem?_of_ne s core lB mB lA.objId hExt hNe
  have hLookupEq : LockId.lookup (acquireLockOnObject s core lB mB) lA
      = LockId.lookup s lA :=
    LockId.lookup_eq_of_objects_getElem?_eq s (acquireLockOnObject s core lB mB) lA hFrame
  have hObjStoreEq : (acquireLockOnObject s core lB mB).objStoreLock
      = s.objStoreLock :=
    acquireLockOnObject_preserves_objStoreLock_of_modeled s core lB mB hNeObjStoreB
  unfold lockHeld
  rw [hLookupEq, hObjStoreEq]
  exact hHeld

/-- WS-SM SM3.C.8 foundation: the `acquireAll` fold preserves an
already-established `lockHeld core lA mA` provided every lock acquired in the
remaining sequence is a non-`.objStore` lock at a different ObjId than `lA`.

Induction on the remaining sequence, applying the per-step frame
(`acquireLockOnObject_preserves_lockHeld_of_ne_objId`) and threading `invExt`
through (`acquireLockOnObject_preserves_invExt`). -/
theorem acquireAll_preserves_lockHeld_of_ne_all (core : CoreId)
    (lA : LockId) (mA : AccessMode) :
    ∀ (rest : List (LockId × AccessMode)) (s : SystemState),
      s.objects.invExt →
      (∀ p ∈ rest, p.fst.kind ≠ .objStore) →
      (∀ p ∈ rest, lA.objId ≠ p.fst.objId) →
      lockHeld core lA mA s →
      lockHeld core lA mA (acquireAll core rest s) := by
  intro rest
  induction rest with
  | nil => intro s _ _ _ hHeld; exact hHeld
  | cons head tail ih =>
      intro s hExt hMod hNe hHeld
      have hHeadModeled := hMod head List.mem_cons_self
      have hHeadNe := hNe head List.mem_cons_self
      have hHeld1 := acquireLockOnObject_preserves_lockHeld_of_ne_objId s core lA
        head.fst mA head.snd hExt hHeadModeled hHeadNe hHeld
      have hExt1 := acquireLockOnObject_preserves_invExt s core head.fst head.snd hExt
      show lockHeld core lA mA
        (acquireAll core tail (acquireLockOnObject s core head.fst head.snd))
      exact ih (acquireLockOnObject s core head.fst head.snd) hExt1
        (fun p hp => hMod p (List.mem_cons_of_mem _ hp))
        (fun p hp => hNe p (List.mem_cons_of_mem _ hp)) hHeld1

/-- WS-SM SM3.C.8 (substantive — closes the "acquireAll establishes lockHeld"
gap): the `acquireAll` fold over a sequence of modeled per-object locks at
**distinct ObjIds**, each present and `unheld` in the pre-state, establishes
`lockHeld core p.fst p.snd` for **every** lock `p` in the sequence.

This is the multi-lock counterpart to
`acquireLockOnObject_establishes_lockHeld_modeled`.  It is the lever the
SM3.C.8 metatheorem's `lockSetHeld` precondition rests on (the static lock set
is genuinely acquired by the `withLockSet` growing phase) AND the SM3.C.11.c
conjunct-1 producer (the dynamic chain's write locks are genuinely held after
`withDynamicChainExtension`'s `acquireAll`).

Induction on the sequence:
* the head lock is established by the single-lock establishment lemma, then
  preserved across the tail fold by `acquireAll_preserves_lockHeld_of_ne_all`
  (every tail lock is at a different ObjId — the distinctness hypothesis);
* the tail locks are established by the IH on the post-head state, whose
  per-lock present/unheld hypotheses survive the head acquire because the head
  is at a different ObjId (frame lemma).

The distinct-ObjId hypothesis is exactly what a `LockSet`'s `Nodup`-keys
invariant guarantees once every key resolves to a present matching-kind object
(two pairs with the same ObjId would resolve to the same object, hence the same
kind, hence the same key — contradicting `Nodup`), and what the SM0.I
ascending-ObjId chain discipline guarantees for the PIP chain. -/
theorem acquireAll_establishes_lockHeld_of_distinct_present_unheld
    (core : CoreId) :
    ∀ (pairs : List (LockId × AccessMode)) (s : SystemState),
      s.objects.invExt →
      (∀ p ∈ pairs, ∃ o, s.objects[p.fst.objId]? = some o ∧
        o.lockKind = p.fst.kind ∧ o.objectLockOf = RwLockState.unheld) →
      pairs.Pairwise (fun a b => a.fst.objId ≠ b.fst.objId) →
      ∀ p ∈ pairs, lockHeld core p.fst p.snd (acquireAll core pairs s) := by
  intro pairs
  induction pairs with
  | nil => intro s _ _ _ p hp; cases hp
  | cons head tail ih =>
      intro s hExt hEach hDistinct p hp
      obtain ⟨oHead, hPresentHead, hKindHead, hUnheldHead⟩ :=
        hEach head List.mem_cons_self
      have hExt1 := acquireLockOnObject_preserves_invExt s core head.fst head.snd hExt
      have hHeadDistinct : ∀ q ∈ tail, head.fst.objId ≠ q.fst.objId :=
        (List.pairwise_cons.mp hDistinct).1
      have hTailDistinct : tail.Pairwise (fun a b => a.fst.objId ≠ b.fst.objId) :=
        (List.pairwise_cons.mp hDistinct).2
      have hHeadHeld1 : lockHeld core head.fst head.snd
          (acquireLockOnObject s core head.fst head.snd) :=
        acquireLockOnObject_establishes_lockHeld_modeled s core head.fst head.snd
          oHead hExt hPresentHead hKindHead hUnheldHead
      -- The per-lock present/unheld hypotheses survive the head acquire.
      have hEachTail1 : ∀ q ∈ tail, ∃ o,
          (acquireLockOnObject s core head.fst head.snd).objects[q.fst.objId]?
            = some o ∧ o.lockKind = q.fst.kind ∧ o.objectLockOf = RwLockState.unheld := by
        intro q hq
        obtain ⟨oq, hPq, hKq, hUq⟩ := hEach q (List.mem_cons_of_mem _ hq)
        refine ⟨oq, ?_, hKq, hUq⟩
        rw [acquireLockOnObject_objects_getElem?_of_ne s core head.fst head.snd
          q.fst.objId hExt (Ne.symm (hHeadDistinct q hq))]
        exact hPq
      -- Tail locks are modeled (their resolving object has a modeled kind).
      have hTailModeled : ∀ q ∈ tail, q.fst.kind ≠ .objStore := by
        intro q hq
        obtain ⟨oq, _, hKq, _⟩ := hEachTail1 q hq
        rw [← hKq]; exact KernelObject.lockKind_ne_objStore oq
      rw [List.mem_cons] at hp
      show lockHeld core p.fst p.snd
        (acquireAll core tail (acquireLockOnObject s core head.fst head.snd))
      cases hp with
      | inl hpHead =>
          rw [hpHead]
          exact acquireAll_preserves_lockHeld_of_ne_all core head.fst head.snd tail
            (acquireLockOnObject s core head.fst head.snd) hExt1 hTailModeled
            hHeadDistinct hHeadHeld1
      | inr hpTail =>
          exact ih (acquireLockOnObject s core head.fst head.snd) hExt1 hEachTail1
            hTailDistinct p hpTail

-- ============================================================================
-- §N — WS-LC LC4.3: the shrinking phase leaves no queued request
-- ============================================================================

/-! The property a release-only unwind could not establish.

`lockHeld` above says a core **holds** a lock.  `lockQueued` says the
weaker thing a contended growing phase actually leaves behind: the core is
in the lock's wait queue, granted nothing.  Both release arms of `applyOp`
guard on holdership, so a release by a queued core is the identity — which
is why, before `RwLockOp.cancel` existed, a refused two-phase-locking
bracket released what was granted and left what was merely requested.

Everything here lifts the two abstract facts proved beside `unwindAll`
(`rwLock_cancel_not_queued`, `rwLock_release_preserves_not_queued`) through
`updateObjectLockAt`.  The lift carries `objects.invExt` — the object
store's own structural invariant, which every kernel state satisfies and
every frame result in this file already assumes; the abstract facts
themselves carry nothing. -/

/-- **WS-LC LC4.3**: `c` has a **queued** request at lock `l` — mirrors
`lockHeld`'s kind dispatch exactly, reading `waiters` where that reads
`coreHolds`. -/
def lockQueued (c : CoreId) (l : LockId) (s : SystemState) : Prop :=
  match l.kind with
  | .objStore => c ∈ s.objStoreLock.waiters.map Prod.fst
  | .page => False   -- SM3.A.8 N/A (pages inline in VSpaceRoot.mappings)
  | .tcb | .endpoint | .notification | .cnode
  | .vspaceRoot | .untyped | .schedContext | .reply =>
      match LockId.lookup s l with
      | some (lockState, _) => c ∈ lockState.waiters.map Prod.fst
      | none => False

/-- **WS-LC LC4.3**: `lockQueued` is decidable, like its `lockHeld` sibling. -/
instance lockQueued_decidable (c : CoreId) (l : LockId) (s : SystemState) :
    Decidable (lockQueued c l s) := by
  unfold lockQueued
  cases l.kind <;> first | exact inferInstance |
    (cases LockId.lookup s l <;> exact inferInstance)

/-- **WS-LC LC4.3**: nothing is ever queued on a `.page` lock. -/
@[simp] theorem lockQueued_page (c : CoreId) (oid : SeLe4n.ObjId) (s : SystemState) :
    ¬ lockQueued c ⟨.page, oid⟩ s := by
  unfold lockQueued
  exact id

/-- **WS-LC LC4.3**: an update at *any* lock cannot enqueue a core the
operation itself never enqueues.

The single frame lemma the whole fold argument runs on, and it needs no
case split on whether `l` and `l'` name the same lock: a successful lookup
at `l` in the post-state names the object the store actually holds there
(`LockId.lookup_object_eq`), `updateObjectAt` changes the store at one key
only (`updateObjectAt_get?`), and `KernelObject.updateLock` preserves an
object's `lockKind`.  So the post-state lock state at `l` is either the
pre-state's or the pre-state's with `op` applied, and `hOp` covers the
second. -/
theorem lockQueued_updateObjectLockAt_of_never_enqueues
    (c : CoreId) (l l' : LockId) (op : RwLockOp) (s : SystemState)
    (hExt : s.objects.invExt)
    (hOp : ∀ r : RwLockState, c ∉ r.waiters.map Prod.fst →
      c ∉ (r.applyOp op).waiters.map Prod.fst)
    (h : ¬ lockQueued c l s) :
    ¬ lockQueued c l (updateObjectLockAt s l' op) := by
  -- The `.objStore` word is untouched by a per-object update, and `.page`
  -- is never queued; the modeled kinds go through the store.
  intro hPost
  revert h hPost
  unfold lockQueued
  cases hK : l.kind with
  | objStore =>
      rw [updateObjectLockAt_preserves_objStoreLock s l' op]
      exact fun h hPost => h hPost
  | page => exact fun _ hPost => hPost
  | tcb | endpoint | notification | cnode
  | vspaceRoot | untyped | schedContext | reply =>
    all_goals (
      intro h hPost
      revert hPost
      -- Fail-closed first: an update whose own lookup misses is the identity,
      -- so the post-state is the pre-state and `h` closes it outright.
      cases hLookL' : LockId.lookup s l' with
      | none =>
          rw [updateObjectLockAt_eq_self_of_lookup_none s l' op hLookL']
          exact fun hPost => h hPost
      | some r' =>
        cases hLookPost : LockId.lookup (updateObjectLockAt s l' op) l with
        | none => exact id
        | some pr =>
          obtain ⟨stPost, oPost⟩ := pr
          intro hMemPost
          -- The returned object is the one the post-state store holds at `l.objId`.
          have hObjPost : (updateObjectLockAt s l' op).objects[l.objId]? = some oPost :=
            LockId.lookup_object_eq _ l stPost oPost hLookPost
          have hKindPost : oPost.lockKind = l.kind :=
            LockId.lookup_kindMatch _ l stPost oPost hLookPost
          have hStPost : stPost = KernelObject.objectLockOf oPost :=
            LockId.lookup_lockState_eq _ l stPost oPost hLookPost
          by_cases hSame : l.objId = l'.objId
          · -- Same object: the pre-state object is `oPost` with `op` undone.
            rw [hSame, updateObjectLockAt_objects_getElem?_self s l' op r' hExt hLookL']
              at hObjPost
            cases hPre : s.objects[l'.objId]? with
            | none => rw [hPre] at hObjPost; simp at hObjPost
            | some o =>
                rw [hPre] at hObjPost
                have hoEq : o.updateLock op = oPost := Option.some.inj hObjPost
                have hKindPre : o.lockKind = l.kind := by
                  rw [← hKindPost, ← hoEq, KernelObject.updateLock_preserves_lockKind]
                have hLookPre : LockId.lookup s l = some (KernelObject.objectLockOf o, o) :=
                  LockId.lookup_some_of_kindMatch s l o (by rw [hSame]; exact hPre) hKindPre
                have hPreNot : c ∉ (KernelObject.objectLockOf o).waiters.map Prod.fst := by
                  intro hc; exact h (by rw [hLookPre]; exact hc)
                refine hOp _ hPreNot ?_
                have hApply : KernelObject.objectLockOf oPost
                    = (KernelObject.objectLockOf o).applyOp op := by
                  rw [← hoEq, KernelObject.objectLockOf_updateLock]
                rw [← hApply, ← hStPost]
                exact hMemPost
          · -- Different object: the store read is unchanged, so is the lookup.
            rw [updateObjectLockAt_objects_getElem?_of_ne s l' op l.objId hExt hSame]
              at hObjPost
            have hLookPre : LockId.lookup s l = some (KernelObject.objectLockOf oPost, oPost) :=
              LockId.lookup_some_of_kindMatch s l oPost hObjPost hKindPost
            exact h (by rw [hLookPre, ← hStPost]; exact hMemPost))

/-- **WS-LC LC4.3**: a withdrawal at a lock leaves the withdrawing core with
no queued request **at that lock** — the establishment half.

The fail-closed branch needs no argument: where the lookup misses, the
update is the identity *and* `lockQueued` is `False` there for the same
reason.  Where it hits, the post-state lock is the pre-state's with the
withdrawal applied, and `rwLock_cancel_not_queued` finishes it. -/
theorem cancelLockOnObject_withdraws (s : SystemState) (core : CoreId)
    (l : LockId) (m : AccessMode) (hExt : s.objects.invExt) :
    ¬ lockQueued core l (cancelLockOnObject s core l m) := by
  unfold cancelLockOnObject lockQueued
  cases hK : l.kind with
  | objStore =>
      exact rwLock_cancel_not_queued s.objStoreLock core
  | page => exact id
  | tcb | endpoint | notification | cnode
  | vspaceRoot | untyped | schedContext | reply =>
    all_goals (
      cases hLook : LockId.lookup s l with
      | none =>
          rw [updateObjectLockAt_eq_self_of_lookup_none s l _ hLook, hLook]
          exact id
      | some pr =>
        obtain ⟨st, o⟩ := pr
        have hObj : s.objects[l.objId]? = some o :=
          LockId.lookup_object_eq s l st o hLook
        have hKind : o.lockKind = l.kind :=
          LockId.lookup_kindMatch s l st o hLook
        have hSt : st = KernelObject.objectLockOf o :=
          LockId.lookup_lockState_eq s l st o hLook
        rw [updateObjectLockAt_lookup_self s l _ o hExt hObj hKind,
            KernelObject.objectLockOf_updateLock]
        exact rwLock_cancel_not_queued (KernelObject.objectLockOf o) core)

/-- **WS-LC LC4.3**: the state-level counterpart of the frame lemma — an
update to `SystemState.objStoreLock` cannot enqueue a core the operation
itself never enqueues.

The `.objStore` arms of the three per-object primitives write that word
directly rather than going through `updateObjectLockAt`, so the modeled
frame lemma does not reach them; the object store is untouched, so a
modeled lock's lookup is unchanged. -/
theorem lockQueued_objStoreLock_applyOp_of_never_enqueues
    (c : CoreId) (l : LockId) (op : RwLockOp) (s : SystemState)
    (hOp : ∀ r : RwLockState, c ∉ r.waiters.map Prod.fst →
      c ∉ (r.applyOp op).waiters.map Prod.fst)
    (h : ¬ lockQueued c l s) :
    ¬ lockQueued c l { s with objStoreLock := s.objStoreLock.applyOp op } := by
  revert h
  unfold lockQueued
  cases l.kind with
  | objStore => exact fun h => hOp _ h
  | page => exact fun _ hPost => hPost
  | tcb | endpoint | notification | cnode
  | vspaceRoot | untyped | schedContext | reply =>
      all_goals (
        rw [LockId.lookup_eq_of_objects_getElem?_eq s
          { s with objStoreLock := s.objStoreLock.applyOp op } l rfl]
        exact fun h hPost => h hPost)

/-- **WS-LC LC4.3**: a withdrawal never enqueues anybody, at any lock. -/
theorem cancelLockOnObject_preserves_not_queued (c core : CoreId) (l l' : LockId)
    (m : AccessMode) (s : SystemState) (hExt : s.objects.invExt)
    (h : ¬ lockQueued c l s) :
    ¬ lockQueued c l (cancelLockOnObject s core l' m) := by
  unfold cancelLockOnObject
  cases l'.kind with
  | objStore =>
      exact lockQueued_objStoreLock_applyOp_of_never_enqueues c l _ s
        (fun r hr => rwLock_cancel_preserves_not_queued r c core hr) h
  | page => exact h
  | tcb | endpoint | notification | cnode
  | vspaceRoot | untyped | schedContext | reply =>
      all_goals (
        show ¬ lockQueued c l (updateObjectLockAt s l' (m.toCancelOp core))
        exact lockQueued_updateObjectLockAt_of_never_enqueues c l l' _ s hExt
          (fun r hr => rwLock_cancel_preserves_not_queued r c core hr) h)

/-- **WS-LC LC4.3**: no release ever enqueues, at any lock — the half that
lets the shrinking phase's payoff dispense with any distinctness hypothesis
on the footprint. -/
theorem releaseLockOnObject_preserves_not_queued (c core : CoreId) (l l' : LockId)
    (m : AccessMode) (s : SystemState) (hExt : s.objects.invExt)
    (h : ¬ lockQueued c l s) :
    ¬ lockQueued c l (releaseLockOnObject s core l' m) := by
  unfold releaseLockOnObject
  cases l'.kind with
  | objStore =>
      exact lockQueued_objStoreLock_applyOp_of_never_enqueues c l _ s
        (fun r hr => rwLock_release_preserves_not_queued r c core m hr) h
  | page => exact h
  | tcb | endpoint | notification | cnode
  | vspaceRoot | untyped | schedContext | reply =>
      all_goals (
        show ¬ lockQueued c l (updateObjectLockAt s l' (m.toReleaseOp core))
        exact lockQueued_updateObjectLockAt_of_never_enqueues c l l' _ s hExt
          (fun r hr => rwLock_release_preserves_not_queued r c core m hr) h)

/-- **WS-LC LC4.3**: the withdrawal *fold* never enqueues. -/
theorem cancelAll_preserves_not_queued (c core : CoreId) (l : LockId)
    (pairs : List (LockId × AccessMode)) :
    ∀ s : SystemState, s.objects.invExt → ¬ lockQueued c l s →
      ¬ lockQueued c l (cancelAll core pairs s) := by
  induction pairs with
  | nil => intro s _ h; exact h
  | cons head tail ih =>
      intro s hExt h
      obtain ⟨hl, hm⟩ := head
      rw [cancelAll_cons]
      exact ih _ (cancelLockOnObject_preserves_invExt s core hl hm hExt)
        (cancelLockOnObject_preserves_not_queued c core l hl hm s hExt h)

/-- **WS-LC LC4.3**: the release *fold* never enqueues. -/
theorem releaseAll_preserves_not_queued (c core : CoreId) (l : LockId)
    (pairs : List (LockId × AccessMode)) :
    ∀ s : SystemState, s.objects.invExt → ¬ lockQueued c l s →
      ¬ lockQueued c l (releaseAll core pairs s) := by
  induction pairs with
  | nil => intro s _ h; exact h
  | cons head tail ih =>
      intro s hExt h
      obtain ⟨hl, hm⟩ := head
      rw [releaseAll_cons]
      exact ih _ (releaseLockOnObject_preserves_invExt s core hl hm hExt)
        (releaseLockOnObject_preserves_not_queued c core l hl hm s hExt h)

/-- **WS-LC LC4.3**: the withdrawal fold *establishes* the property at every
member it visits.

The head is withdrawn outright; the tail preserves that, because a
withdrawal never enqueues anywhere.  No distinctness hypothesis on the
footprint: two members naming the same lock are harmless, since withdrawing
twice is still a withdrawal. -/
theorem cancelAll_leaves_no_queued_request (core : CoreId)
    (pairs : List (LockId × AccessMode)) :
    ∀ s : SystemState, s.objects.invExt →
      ∀ p ∈ pairs, ¬ lockQueued core p.fst (cancelAll core pairs s) := by
  induction pairs with
  | nil => intro s _ p hp; cases hp
  | cons head tail ih =>
      intro s hExt p hp
      obtain ⟨hl, hm⟩ := head
      rw [cancelAll_cons]
      have hExt' : (cancelLockOnObject s core hl hm).objects.invExt :=
        cancelLockOnObject_preserves_invExt s core hl hm hExt
      rw [List.mem_cons] at hp
      cases hp with
      | inl hHead =>
          subst hHead
          exact cancelAll_preserves_not_queued core core _ tail _ hExt'
            (cancelLockOnObject_withdraws s core hl hm hExt)
      | inr hTail => exact ih _ hExt' p hTail

/-- **WS-LC LC4.3 (the payoff)**: the shrinking phase leaves the unwinding
core with **no queued request at any member of the footprint**.

This is the theorem that replaces the "what 'released' does and does not
mean" caveat: that caveat's claim was that the unwind *cannot* remove a
request the growing phase queued, and this is its exact negation.

Note what it does not say — `¬ lockHeld`, which is false here: a core
holding a *write* lock, unwound at a member declared `.read`, keeps
`writerHeld`, and ruling that out needs a mode-agreement hypothesis
threaded from the growing phase, for a conclusion the caveat never made.

The only hypothesis is `objects.invExt`, the object store's own structural
invariant that every kernel state satisfies; the abstract facts underneath
(`rwLock_cancel_not_queued`, `rwLock_release_preserves_not_queued`) carry
none at all.  In particular there is **no** distinctness or resolvability
condition on the footprint, because the withdrawal fold establishes the
property everywhere before the release fold runs, and no release arm
enqueues. -/
theorem unwindAll_leaves_no_queued_request (core : CoreId)
    (pairs : List (LockId × AccessMode)) (s : SystemState)
    (hExt : s.objects.invExt) :
    ∀ p ∈ pairs, ¬ lockQueued core p.fst (unwindAll core pairs s) := by
  intro p hp
  rw [unwindAll_eq_releaseAll_cancelAll]
  exact releaseAll_preserves_not_queued core core p.fst pairs _
    (cancelAll_preserves_invExt core pairs s hExt)
    (cancelAll_leaves_no_queued_request core pairs s hExt p hp)

end SeLe4n.Kernel.Concurrency
