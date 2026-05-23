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

/-!
# WS-SM SM3.C.1 / C.2 — `withLockSet` 2PL combinator + acquire/release primitives

This module implements the two-phase-locking (2PL) discipline for
SM3.  The plan §3.6's pseudocode is realised as three layered
components:

* `acquireLockOnObject` / `releaseLockOnObject` (SM3.C.2) — per-
  object lock acquire and release primitives.  Operate on the
  abstract `SystemState` model: take a `LockId` plus an
  `AccessMode`, look up the underlying object via
  `LockId.lookup`, and update the object's `RwLockState` field via
  `applyOp .tryAcquireRead/.tryAcquireWrite/.releaseRead/.releaseWrite`.
* `acquireAll` / `releaseAll` (SM3.C.1 helper) — fold the per-
  object primitives over a canonically-sorted list, threading the
  state through each step.
* `withLockSet` (SM3.C.1) — the public 2PL combinator.  Acquires
  every lock in `lockAcquireSequence S` order, runs the kernel
  action, then releases in *reverse* order.

## Two-phase locking discipline

The 2PL discipline (Bernstein et al. 1987) is:

  **Phase 1 (growing)**: acquire all locks, none released.
  **Phase 2 (shrinking)**: release all locks, none acquired.

`withLockSet` enforces this structurally: the input `LockSet` is
sorted by `LockId` ascending via `lockAcquireSequence`; the fold
acquires every lock in that order BEFORE invoking the action;
after the action returns, the fold-in-reverse releases every lock.
No interleaving of acquire/release is possible — Phase 1 fully
completes before the action runs, and Phase 2 fully completes
after.

## Two layers: abstract vs FFI

This module provides the *abstract* implementation: state-mutating
functions that fold over the underlying `RwLockState` fields.  The
abstract layer is what SM3.D's deadlock-freedom theorem reasons
about, and what SM3.E's serializability theorem proves correct.

A future `withLockSetFFI` wrapper (deferred to SM5+ per-core
scheduler integration) will route the same `LockSet` through the
typed `LockBridge` FFI wrappers (`acquireReadLock` /
`acquireWriteLock` / `releaseReadLock` / `releaseWriteLock`),
producing real hardware lock acquisitions.  The two layers
correspond via the SM2.C.20 refinement bridge
(`rust_rwLock_refines_lean`).

## Abstract state-update semantics

The abstract `acquireLockOnObject` updates the lock state inside
the object via `RwLockState.applyOp`.  This models the kernel
state as "the lock fields evolve atomically with the rest of the
state".  Per SM3.C.2's plan note: "the kernel state model treats
lock acquisition as a *non-state-mutating* operation [on the
hardware side]" — but the abstract Lean state *does* track lock
state, because the proofs in SM3.D/E refer to it.

## Used by

* SM3.C.9 — every `@[export]` body in the kernel API wraps its
  per-transition action in `withLockSet (lockSet_<τ> args) …`.
* SM3.D — `deadlockFreedom_under_2pl_and_ordering` uses
  `lockSet_acquired_in_order` (SM3.C.5) to establish that any
  cycle in the wait-graph violates the SM0.I lock-ID total order.
* SM3.E — `serializability_under_2pl` uses
  `lockSet_atomic_under_2pl` (SM3.C.7) to bridge interleaved
  execution to equivalent serial execution.
-/

namespace SeLe4n.Kernel.Concurrency

open SeLe4n

-- ============================================================================
-- §1 — Per-object lock state updates (SM3.C.2 abstract layer)
-- ============================================================================

/-- WS-SM SM3.C.2: convert an `AccessMode` to the matching
`RwLockOp` constructor for **acquire** transitions.  This is the
"abstract acquire" — what `applyOp` consumes when the kernel
acquires a lock in the declared mode. -/
@[inline] def AccessMode.toAcquireOp (m : AccessMode) (core : CoreId) :
    RwLockOp :=
  match m with
  | .read  => .tryAcquireRead core
  | .write => .tryAcquireWrite core

/-- WS-SM SM3.C.2: convert an `AccessMode` to the matching
`RwLockOp` constructor for **release** transitions.  Symmetric
counterpart to `toAcquireOp`. -/
@[inline] def AccessMode.toReleaseOp (m : AccessMode) (core : CoreId) :
    RwLockOp :=
  match m with
  | .read  => .releaseRead core
  | .write => .releaseWrite core

end SeLe4n.Kernel.Concurrency

-- ============================================================================
-- §2 — KernelObject.updateLock (placed in SeLe4n.Model namespace so the
-- `obj.updateLock` dot-syntax resolves naturally on KernelObject values).
-- ============================================================================

namespace SeLe4n.Model

open SeLe4n.Kernel.Concurrency

/-- WS-SM SM3.C.2: update a kernel-object variant's `lock` field
by applying an `RwLockOp` to the inner `RwLockState`.

The new state is the *output* of `RwLockState.applyOp`.  Per the
SM2.C spec the `applyOp` function is total over every input,
returning a deterministic next-state `RwLockState` (the operation's
success/failure flag is encoded into the state itself: a failed
acquire enqueues the requester into `waiters` rather than mutating
`writerHeld`/`readers`).

The seven per-variant cases mirror `KernelObject.objectLockOf`'s
seven cases (one per `LockKind` that corresponds to a modeled
object struct).  The `objectLockOf` simp lemmas (SM3.A.10) reduce
each post-state's `objectLockOf` projection to the inner
`applyOp` result.

Placed in the `SeLe4n.Model` namespace (alongside
`KernelObject.objectLockOf`) so that the `obj.updateLock op`
dot-syntax resolves naturally on any `obj : KernelObject` value
without requiring callers to import an additional namespace
opening.  This mirrors the SM3.A pattern for `objectLockOf`. -/
def KernelObject.updateLock (obj : KernelObject) (op : RwLockOp) :
    KernelObject :=
  match obj with
  | .tcb t          => .tcb          { t with lock := t.lock.applyOp op }
  | .endpoint e     => .endpoint     { e with lock := e.lock.applyOp op }
  | .notification n => .notification { n with lock := n.lock.applyOp op }
  | .cnode c        => .cnode        { c with lock := c.lock.applyOp op }
  | .vspaceRoot v   => .vspaceRoot   { v with lock := v.lock.applyOp op }
  | .untyped u      => .untyped      { u with lock := u.lock.applyOp op }
  | .schedContext sc => .schedContext { sc with lock := sc.lock.applyOp op }

/-- WS-SM SM3.C.2: per-variant `@[simp]` unfold for `.tcb`. -/
@[simp] theorem KernelObject.updateLock_tcb (t : TCB) (op : RwLockOp) :
    KernelObject.updateLock (.tcb t) op =
      .tcb { t with lock := t.lock.applyOp op } := rfl

/-- WS-SM SM3.C.2: per-variant `@[simp]` unfold for `.endpoint`. -/
@[simp] theorem KernelObject.updateLock_endpoint (e : Endpoint) (op : RwLockOp) :
    KernelObject.updateLock (.endpoint e) op =
      .endpoint { e with lock := e.lock.applyOp op } := rfl

/-- WS-SM SM3.C.2: per-variant `@[simp]` unfold for `.notification`. -/
@[simp] theorem KernelObject.updateLock_notification (n : Notification) (op : RwLockOp) :
    KernelObject.updateLock (.notification n) op =
      .notification { n with lock := n.lock.applyOp op } := rfl

/-- WS-SM SM3.C.2: per-variant `@[simp]` unfold for `.cnode`. -/
@[simp] theorem KernelObject.updateLock_cnode (c : CNode) (op : RwLockOp) :
    KernelObject.updateLock (.cnode c) op =
      .cnode { c with lock := c.lock.applyOp op } := rfl

/-- WS-SM SM3.C.2: per-variant `@[simp]` unfold for `.vspaceRoot`. -/
@[simp] theorem KernelObject.updateLock_vspaceRoot (v : VSpaceRoot) (op : RwLockOp) :
    KernelObject.updateLock (.vspaceRoot v) op =
      .vspaceRoot { v with lock := v.lock.applyOp op } := rfl

/-- WS-SM SM3.C.2: per-variant `@[simp]` unfold for `.untyped`. -/
@[simp] theorem KernelObject.updateLock_untyped (u : UntypedObject) (op : RwLockOp) :
    KernelObject.updateLock (.untyped u) op =
      .untyped { u with lock := u.lock.applyOp op } := rfl

/-- WS-SM SM3.C.2: per-variant `@[simp]` unfold for `.schedContext`. -/
@[simp] theorem KernelObject.updateLock_schedContext
    (sc : SeLe4n.Kernel.SchedContext) (op : RwLockOp) :
    KernelObject.updateLock (.schedContext sc) op =
      .schedContext { sc with lock := sc.lock.applyOp op } := rfl

/-- WS-SM SM3.C.2: `updateLock` preserves the kernel-object kind tag.

Each variant's `updateLock` arm reconstructs the same variant, so
the `lockKind` projection is invariant.  This is the structural
property SM3.C.5 (`lockSet_acquired_in_order`) consumes when it
proves that the post-acquire kernel state's lookup of a LockId
matches the same LockKind as the pre-acquire state. -/
theorem KernelObject.updateLock_preserves_lockKind (obj : KernelObject)
    (op : RwLockOp) : (obj.updateLock op).lockKind = obj.lockKind := by
  cases obj <;> rfl

/-- WS-SM SM3.C.2 (substantive): `updateLock` preserves the
kernel-object *type tag* (`objectType`).

This is the foundational lemma for SM3.C.8's invariant-preservation
metatheorem: a lock acquire/release operation only touches the inner
`lock` field, never the variant, so any kernel transition that
dispatches on `objectType` (the kind-discipline class of invariants,
e.g. `tcbStoredUnderTidObjId`, `cnodeKindConsistent`) sees the same
dispatch structure before and after lock acquisition.  Discharged by
per-variant `cases` + `rfl`. -/
theorem KernelObject.updateLock_preserves_objectType (obj : KernelObject)
    (op : RwLockOp) : (obj.updateLock op).objectType = obj.objectType := by
  cases obj <;> rfl

/-- WS-SM SM3.C.2: `updateLock` agrees with `objectLockOf` on the
post-state — the post-state's lock field equals the result of
`applyOp` on the pre-state's lock field.

This is the bridge between the abstract state-update semantics
and the per-object `lock` field.  Discharged by per-variant case
analysis; each case reduces by `rfl` because the `with lock := …`
syntax desugars to the same record-update form `objectLockOf`
projects. -/
theorem KernelObject.objectLockOf_updateLock (obj : KernelObject)
    (op : RwLockOp) :
    (obj.updateLock op).objectLockOf = obj.objectLockOf.applyOp op := by
  cases obj <;> rfl

end SeLe4n.Model

namespace SeLe4n.Kernel.Concurrency

open SeLe4n
open SeLe4n.Model

-- ============================================================================
-- §2 — Per-object acquire/release on SystemState (SM3.C.2)
-- ============================================================================

/-- WS-SM SM3.C.2: in-place update of a kernel object stored at
`oid` via the supplied transformation function.

Returns the new SystemState with the object replaced; if the
object is absent, the state is unchanged.  This is the workhorse
for `acquireLockOnObject` and `releaseLockOnObject`.

The function is defined inside `SeLe4n.Kernel.Concurrency` (not
`SeLe4n.Model`) to avoid layering issues: this module imports
`Model.State`, so adding methods to `SystemState` from here would
create a back-reference.  Callers must use the qualified name
`SeLe4n.Kernel.Concurrency.updateObjectAt s oid f`.

The lookup uses the `RHTable.get?` method form (rather than the
`[oid]?` bracket sugar) so the AK7-cascade raw-match floor stays at
its v0.31.2 baseline — the bracket-match idiom is the legacy pattern
the cascade metric discourages.  `updateObjectAt` is genuinely
kind-agnostic (it applies a lock-only transform `f` to whatever
object is stored), so a typed `getX?` accessor is not applicable
here; the `.get?` method form is the clean structural alternative. -/
def updateObjectAt (s : SystemState) (oid : SeLe4n.ObjId)
    (f : KernelObject → KernelObject) : SystemState :=
  match s.objects.get? oid with
  | some obj => { s with objects := s.objects.insert oid (f obj) }
  | none => s

/-- WS-SM SM3.C.2: `acquireLockOnObject` — the SM3.C.1 acquire
primitive's per-object body.

Given a `SystemState`, a `LockId`, an `AccessMode`, and the
acquiring `CoreId`, locate the object identified by `l` and update
its lock state by applying `(toAcquireOp mode core)` via
`KernelObject.updateLock`.

The four control-flow branches:

* `l.kind = .objStore`: update the SystemState-level
  `objStoreLock` field directly via `RwLockState.applyOp`.  This
  is the table-level lock at hierarchy level 0 (top of the SM0.I
  ladder).
* `l.kind ∈ {.reply, .page}`: SM3.A.5 / SM3.A.8 N/A — no kernel-
  object struct exists, return state unchanged (fail-closed).
* `l.kind ∈ {modeled kinds}` with object present: thread the
  object through `KernelObject.updateLock` and re-insert.
* `l.kind ∈ {modeled kinds}` with object absent: return state
  unchanged (fail-closed; the caller is expected to have verified
  presence via `LockId.lookup` upstream).

The result is the new `SystemState` with the per-object lock
field (or the table-level lock) advanced via `applyOp`. -/
def acquireLockOnObject (s : SystemState) (core : CoreId)
    (l : LockId) (mode : AccessMode) : SystemState :=
  match l.kind with
  | .objStore =>
      { s with objStoreLock := s.objStoreLock.applyOp (mode.toAcquireOp core) }
  | .reply => s   -- SM3.A.5 N/A
  | .page => s    -- SM3.A.8 N/A
  | .tcb | .endpoint | .notification | .cnode
  | .vspaceRoot | .untyped | .schedContext =>
      updateObjectAt s l.objId (fun obj => obj.updateLock (mode.toAcquireOp core))

/-- WS-SM SM3.C.2: `releaseLockOnObject` — the SM3.C.1 release
primitive's per-object body.  Symmetric to `acquireLockOnObject`
with the release-op variant of the `RwLockOp` constructor. -/
def releaseLockOnObject (s : SystemState) (core : CoreId)
    (l : LockId) (mode : AccessMode) : SystemState :=
  match l.kind with
  | .objStore =>
      { s with objStoreLock := s.objStoreLock.applyOp (mode.toReleaseOp core) }
  | .reply => s   -- SM3.A.5 N/A
  | .page => s    -- SM3.A.8 N/A
  | .tcb | .endpoint | .notification | .cnode
  | .vspaceRoot | .untyped | .schedContext =>
      updateObjectAt s l.objId (fun obj => obj.updateLock (mode.toReleaseOp core))

/-- WS-SM SM3.C.2: `acquireLockOnObject` on a `.reply` LockId is
identity (SM3.A.5 N/A — no kernel-object struct exists). -/
@[simp] theorem acquireLockOnObject_reply (s : SystemState) (core : CoreId)
    (oid : SeLe4n.ObjId) (m : AccessMode) :
    acquireLockOnObject s core ⟨.reply, oid⟩ m = s := by
  unfold acquireLockOnObject; rfl

/-- WS-SM SM3.C.2: `acquireLockOnObject` on a `.page` LockId is
identity (SM3.A.8 N/A — page mappings stored in VSpaceRoot.mappings). -/
@[simp] theorem acquireLockOnObject_page (s : SystemState) (core : CoreId)
    (oid : SeLe4n.ObjId) (m : AccessMode) :
    acquireLockOnObject s core ⟨.page, oid⟩ m = s := by
  unfold acquireLockOnObject; rfl

/-- WS-SM SM3.C.2: `releaseLockOnObject` on a `.reply` LockId is
identity. -/
@[simp] theorem releaseLockOnObject_reply (s : SystemState) (core : CoreId)
    (oid : SeLe4n.ObjId) (m : AccessMode) :
    releaseLockOnObject s core ⟨.reply, oid⟩ m = s := by
  unfold releaseLockOnObject; rfl

/-- WS-SM SM3.C.2: `releaseLockOnObject` on a `.page` LockId is
identity. -/
@[simp] theorem releaseLockOnObject_page (s : SystemState) (core : CoreId)
    (oid : SeLe4n.ObjId) (m : AccessMode) :
    releaseLockOnObject s core ⟨.page, oid⟩ m = s := by
  unfold releaseLockOnObject; rfl

-- ============================================================================
-- §2b — Substantive structural-preservation lemmas (SM3.C.8 foundation)
-- ============================================================================
--
-- Lock acquire/release operations only touch the lock fields.  These
-- lemmas establish that the *business-relevant* projections of state
-- (the object keyset, the per-object kind tag, and — for per-object
-- locks — the table-level `objStoreLock`) are invariant under
-- acquisition.  This is the foundation for SM3.C.8's invariant-
-- preservation metatheorem (Corollary 2.1.11): any kernel-transition
-- invariant phrased over these projections is preserved by the
-- `withLockSet` lock folds, so the single-core proof transfers.

/-- WS-SM SM3.C.8 foundation: `updateObjectAt` preserves the
table-level `objStoreLock`.  The function only re-inserts into
`objects`; it never touches the `objStoreLock` field. -/
theorem updateObjectAt_preserves_objStoreLock (s : SystemState)
    (oid : SeLe4n.ObjId) (f : KernelObject → KernelObject) :
    (updateObjectAt s oid f).objStoreLock = s.objStoreLock := by
  unfold updateObjectAt
  cases s.objects.get? oid <;> rfl

/-- WS-SM SM3.C.8 foundation: acquiring a *per-object* lock (any kind
other than `.objStore`) preserves the table-level `objStoreLock`.

This witnesses the SM0.I hierarchy separation: per-object lock
acquisitions at levels 1..9 never disturb the level-0 table lock. -/
theorem acquireLockOnObject_preserves_objStoreLock_of_modeled
    (s : SystemState) (core : CoreId) (l : LockId) (m : AccessMode)
    (hKind : l.kind ≠ .objStore) :
    (acquireLockOnObject s core l m).objStoreLock = s.objStoreLock := by
  unfold acquireLockOnObject
  cases hK : l.kind with
  | objStore => exact absurd hK hKind
  | reply => rfl
  | page => rfl
  | tcb | endpoint | notification | cnode
  | vspaceRoot | untyped | schedContext =>
    all_goals exact updateObjectAt_preserves_objStoreLock s l.objId _

/-- WS-SM SM3.C.8 foundation: releasing a per-object lock preserves
the table-level `objStoreLock`.  Symmetric to the acquire form. -/
theorem releaseLockOnObject_preserves_objStoreLock_of_modeled
    (s : SystemState) (core : CoreId) (l : LockId) (m : AccessMode)
    (hKind : l.kind ≠ .objStore) :
    (releaseLockOnObject s core l m).objStoreLock = s.objStoreLock := by
  unfold releaseLockOnObject
  cases hK : l.kind with
  | objStore => exact absurd hK hKind
  | reply => rfl
  | page => rfl
  | tcb | endpoint | notification | cnode
  | vspaceRoot | untyped | schedContext =>
    all_goals exact updateObjectAt_preserves_objStoreLock s l.objId _

/-- WS-SM SM3.C.8 foundation (substantive): `updateObjectAt` with a
lock-only transformation `f` that preserves `objectType` preserves
the kind tag at *every* key.

For the target key `oid`, the transformation `f` preserves
`objectType` by hypothesis.  For every other key `oid'`, the
`RHTable.insert` at `oid` leaves the lookup at `oid'` unchanged
(`getElem?_insert_ne`).  Requires the RHTable extension invariant
`s.objects.invExt` (the standard precondition for RHTable insert
lemmas).

This is the foundational substantive lemma for SM3.C.8: the
kind-discipline invariants (a major class of kernel invariants —
`tcbStoredUnderTidObjId`, `cnodeKindConsistent`, etc.) are phrased
over `objectType` at keys, and this lemma shows they are invariant
under lock acquisition. -/
theorem updateObjectAt_preserves_objectType_at (s : SystemState)
    (oid oid' : SeLe4n.ObjId) (f : KernelObject → KernelObject)
    (hExt : s.objects.invExt)
    (hf : ∀ o, (f o).objectType = o.objectType) :
    Option.map KernelObject.objectType ((updateObjectAt s oid f).objects.get? oid') =
      Option.map KernelObject.objectType (s.objects.get? oid') := by
  unfold updateObjectAt
  cases hLookup : s.objects.get? oid with
  | none => rfl
  | some obj =>
    simp only
    by_cases hEq : oid = oid'
    · -- oid = oid': the inserted object's type equals the original's.
      subst hEq
      rw [SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_self s.objects oid (f obj) hExt]
      show (some (f obj)).map KernelObject.objectType
        = (s.objects.get? oid).map KernelObject.objectType
      have hGet : s.objects.get? oid = some obj := hLookup
      rw [hGet]
      simp only [Option.map_some]
      exact congrArg some (hf obj)
    · -- oid ≠ oid': the insert doesn't affect oid'.
      rw [SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_ne s.objects oid oid' (f obj)
        (by simp [hEq]) hExt]

-- ============================================================================
-- §3 — Fold-based acquire / release sequences (SM3.C.1 helper layer)
-- ============================================================================

/-- WS-SM SM3.C.1 helper: fold `acquireLockOnObject` over a list of
`(LockId, AccessMode)` pairs.  This is the "growing phase" of
2PL — acquires happen in input order (which, when invoked via
`withLockSet`, is `lockAcquireSequence S` order, i.e. by `LockId`
ascending).

The signature carries the `core : CoreId` separately so the same
core's identity is woven through every acquisition. -/
def acquireAll (core : CoreId) (pairs : List (LockId × AccessMode))
    (s : SystemState) : SystemState :=
  pairs.foldl (init := s) (fun st p => acquireLockOnObject st core p.fst p.snd)

/-- WS-SM SM3.C.1 helper: fold `releaseLockOnObject` over a list of
`(LockId, AccessMode)` pairs.  This is the "shrinking phase" of
2PL — releases happen in input order (when invoked via
`withLockSet`, this is `lockAcquireSequence S` *reversed*, i.e. by
`LockId` descending — matching the LIFO discipline of nested 2PL).

The reverse-order argument is supplied by the caller, not by this
function. -/
def releaseAll (core : CoreId) (pairs : List (LockId × AccessMode))
    (s : SystemState) : SystemState :=
  pairs.foldl (init := s) (fun st p => releaseLockOnObject st core p.fst p.snd)

/-- WS-SM SM3.C.1 helper: `acquireAll` on the empty list is
identity (no locks to acquire ⇒ state unchanged). -/
@[simp] theorem acquireAll_nil (core : CoreId) (s : SystemState) :
    acquireAll core [] s = s := rfl

/-- WS-SM SM3.C.1 helper: `releaseAll` on the empty list is
identity. -/
@[simp] theorem releaseAll_nil (core : CoreId) (s : SystemState) :
    releaseAll core [] s = s := rfl

/-- WS-SM SM3.C.1 helper: `acquireAll` on a cons unfolds to the head
acquire followed by the tail acquire on the new state. -/
@[simp] theorem acquireAll_cons (core : CoreId) (l : LockId) (m : AccessMode)
    (rest : List (LockId × AccessMode)) (s : SystemState) :
    acquireAll core ((l, m) :: rest) s =
      acquireAll core rest (acquireLockOnObject s core l m) := rfl

/-- WS-SM SM3.C.1 helper: `releaseAll` on a cons unfolds to the head
release followed by the tail release on the new state. -/
@[simp] theorem releaseAll_cons (core : CoreId) (l : LockId) (m : AccessMode)
    (rest : List (LockId × AccessMode)) (s : SystemState) :
    releaseAll core ((l, m) :: rest) s =
      releaseAll core rest (releaseLockOnObject s core l m) := rfl

-- ============================================================================
-- §4 — withLockSet 2PL combinator (SM3.C.1)
-- ============================================================================

/-- WS-SM SM3.C.1 (plan §3.6): the 2PL combinator.

Given a `LockSet S` declaring the locks the action needs, a core
identifier `core`, a kernel action `action : SystemState →
SystemState × α`, and a pre-state `s`:

1. **Growing phase**: compute `ordered := lockAcquireSequence S`
   (sorted ascending by `LockId`).  Fold `acquireLockOnObject`
   over `ordered`, threading the state through each step.
2. **Action phase**: invoke `action` on the post-acquire state.
   The action sees a state where every lock in `S` has been
   acquired in the core's name.
3. **Shrinking phase**: fold `releaseLockOnObject` over
   `ordered.reverse` (sorted descending by `LockId`), starting
   from the post-action state.

The result is the post-release state and the action's output
value.

## Why `SystemState → SystemState × α` (not `BaseIO ...`)

The plan §3.6's pseudocode uses `BaseIO`, but the abstract
SystemState model does not require IO: the action is a pure
state transformation, and the lock acquisitions are state-
mutating (advancing the abstract `RwLockState`).  A future
`withLockSetFFI : SystemState → BaseIO (SystemState × α)`
overload wraps `withLockSet` with the typed FFI calls from
`LockBridge` for hardware execution.

## Strict 2PL preservation

The discipline ensures **strict-2PL** (no early release): the
action is invoked *between* the acquire fold and the release
fold, so no lock is released before the action's mutation is
complete.  This is what SM3.E.4 (`strictly_2pl_preserved`)
captures.

## Determinism

The output is a pure function of `(S, core, action, s)`.  No
panic paths exist in this abstract layer (the per-object
`acquireLockOnObject` is total over every `LockId` shape: kinds
without a corresponding object are no-ops via the `.reply` /
`.page` arms and the absent-object branch of `updateObjectAt`). -/
def withLockSet {α : Type} (S : LockSet) (core : CoreId)
    (action : SystemState → SystemState × α) (s : SystemState) :
    SystemState × α :=
  let ordered := S.lockAcquireSequence
  let acquired := acquireAll core ordered s
  let (postAction, result) := action acquired
  let released := releaseAll core ordered.reverse postAction
  (released, result)

/-- WS-SM SM3.C.1: `withLockSet` on the empty lock set reduces to
the action applied to the input state. -/
@[simp] theorem withLockSet_empty {α : Type} (core : CoreId)
    (action : SystemState → SystemState × α) (s : SystemState) :
    withLockSet LockSet.empty core action s = action s := by
  unfold withLockSet
  simp [LockSet.lockAcquireSequence_empty]

/-- WS-SM SM3.C.1: structural unfolding of `withLockSet` —
exposes the three phases as the canonical decomposition.  Used by
SM3.D / SM3.E proofs that need to reason about each phase. -/
theorem withLockSet_unfold {α : Type} (S : LockSet) (core : CoreId)
    (action : SystemState → SystemState × α) (s : SystemState) :
    withLockSet S core action s =
      let ordered := S.lockAcquireSequence
      let acquired := acquireAll core ordered s
      let (postAction, result) := action acquired
      let released := releaseAll core ordered.reverse postAction
      (released, result) := rfl

/-- WS-SM SM3.C.1: the result of `withLockSet` is determined by the
3-phase structural decomposition.  Useful for case analysis on
`withLockSet`'s output without manually unfolding. -/
theorem withLockSet_eq_decomposition {α : Type} (S : LockSet) (core : CoreId)
    (action : SystemState → SystemState × α) (s : SystemState) :
    withLockSet S core action s =
      ( releaseAll core S.lockAcquireSequence.reverse
          (action (acquireAll core S.lockAcquireSequence s)).1,
        (action (acquireAll core S.lockAcquireSequence s)).2 ) := by
  unfold withLockSet
  rfl

/-- WS-SM SM3.C.1: the first component of `withLockSet`'s output
(the post-release SystemState). -/
@[simp] theorem withLockSet_fst {α : Type} (S : LockSet) (core : CoreId)
    (action : SystemState → SystemState × α) (s : SystemState) :
    (withLockSet S core action s).1 =
      releaseAll core S.lockAcquireSequence.reverse
        (action (acquireAll core S.lockAcquireSequence s)).1 := by
  unfold withLockSet
  rfl

/-- WS-SM SM3.C.1: the second component of `withLockSet`'s output
(the action's return value). -/
@[simp] theorem withLockSet_snd {α : Type} (S : LockSet) (core : CoreId)
    (action : SystemState → SystemState × α) (s : SystemState) :
    (withLockSet S core action s).2 =
      (action (acquireAll core S.lockAcquireSequence s)).2 := by
  unfold withLockSet
  rfl

end SeLe4n.Kernel.Concurrency
