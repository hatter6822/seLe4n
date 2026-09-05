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

/-- **WS-LC LC4.1**: the **withdrawal** op for a declared footprint member.

Third sibling of `toAcquireOp` / `toReleaseOp`, and the one that does not
branch: `RwLockOp.cancel` carries no mode, because a queued request is
withdrawn whatever mode it was queued in.  The `AccessMode` argument is
taken anyway so the three conversions have one signature and the three
folds below can share one `List (LockId × AccessMode)` sequence — the
alternative, a fold over bare `LockId`s, would need the pair list
projected at every call site and would let the withdrawal sequence drift
out of step with the acquisition sequence it must mirror.

A withdrawal is not a release: it admits nobody
(`RwLockState.applyOp_cancel_readers` / `_writerHeld` are `rfl`), so it
cannot break exclusion, and it costs the waiters behind it nothing. -/
@[inline] def AccessMode.toCancelOp (_m : AccessMode) (core : CoreId) :
    RwLockOp :=
  .cancel core

/-- **WS-LC LC4.1**: the withdrawal op does not depend on the mode.

Stated rather than left to `rfl` at use sites: it is the reason the
shrinking phase needs no mode-agreement hypothesis, and a future
mode-sensitive withdrawal would have to break this theorem to exist. -/
@[simp] theorem AccessMode.toCancelOp_eq_cancel (m : AccessMode) (core : CoreId) :
    m.toCancelOp core = .cancel core := rfl

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
  | .reply r        => .reply        { r with lock := r.lock.applyOp op }

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

/-- WS-SM SM6.D: per-variant `@[simp]` unfold for `.reply`. -/
@[simp] theorem KernelObject.updateLock_reply
    (r : SeLe4n.Kernel.Reply) (op : RwLockOp) :
    KernelObject.updateLock (.reply r) op =
      .reply { r with lock := r.lock.applyOp op } := rfl

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

/-- WS-SM SM3.C.2 (audit-pass-1, Comment 5): kind-checked lock update.

Apply the lock-only transform `obj.updateLock op` to the object at
`l.objId` **only if** the stored object's `lockKind` matches
`l.kind`.  On kind mismatch (e.g. a `.tcb`-kinded `LockId` pointing
at an Endpoint object) or absence, the state is returned unchanged
(**fail closed**).

This mirrors the SM3.B `LockId.lookup` fail-closed kind-check
discipline: a `LockId` that names the wrong object kind must never
silently mutate the wrong object's lock field — that would break
the `LockId`/object-kind correspondence the whole lock hierarchy
relies on.  The check routes through `LockId.lookup` (which already
encapsulates the kind-match logic), so the two stay in lock-step. -/
def updateObjectLockAt (s : SystemState) (l : LockId) (op : RwLockOp) :
    SystemState :=
  match LockId.lookup s l with
  | some _ => updateObjectAt s l.objId (fun obj => obj.updateLock op)
  | none => s   -- absent OR kind mismatch → fail closed

/-- **WS-SM SM3.E.5** (re-homed at **WS-LC LC4.3** beside the definition it
characterises): closed-form characterisation of `updateObjectAt`'s effect on a
lookup.  Looking up `k` after `updateObjectAt s oid f` returns `f`-mapped
content at the target key `oid`, and the unchanged content at every other key.
Unifies the present/absent branches: when `oid` is absent, `(s.get? oid).map f =
none` agrees with the unchanged lookup.

It lived in `Serializability` — three modules downstream of the function it is
about — which put it out of reach of everything in between.  The shrinking
phase's payoff needs exactly this at-any-key reading, and duplicating it would
leave one question with two answers. -/
theorem updateObjectAt_get? (s : SystemState) (oid k : SeLe4n.ObjId)
    (f : KernelObject → KernelObject) (hExt : s.objects.invExt) :
    (updateObjectAt s oid f).objects.get? k
      = if k = oid then (s.objects.get? oid).map f else s.objects.get? k := by
  unfold updateObjectAt
  by_cases hk : k = oid
  · subst hk
    rw [if_pos rfl]
    cases hg : s.objects.get? k with
    | none => simp [hg]
    | some o =>
        show (s.objects.insert k (f o)).get? k = (some o).map f
        rw [SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_self s.objects k (f o) hExt]
        rfl
  · rw [if_neg hk]
    cases hg : s.objects.get? oid with
    | none => rfl
    | some o =>
        show (s.objects.insert oid (f o)).get? k = s.objects.get? k
        exact SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_ne s.objects oid k (f o)
          (by simp [Ne.symm hk]) hExt

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
* `l.kind = .page`: SM3.A.8 N/A — no kernel-object struct exists
  (page mappings are inline in `VSpaceRoot.mappings`), return state
  unchanged (fail-closed).
* `l.kind ∈ {modeled kinds}` (now including `.reply`, WS-SM SM6.D):
  route through `updateObjectLockAt`,
  which uses `LockId.lookup` to require that an object is present
  at `l.objId` **and** its variant matches `l.kind`.  If so, the
  object's lock field is advanced via `KernelObject.updateLock`;
  otherwise (absent OR kind mismatch) the state is unchanged
  (fail-closed).

The result is the new `SystemState` with the per-object lock
field (or the table-level lock) advanced via `applyOp`.

**Audit-pass-1 (Comment 5)**: the modeled-kind branches route
through `updateObjectLockAt`, which validates the stored object's
kind against `l.kind` (fail-closed on mismatch) before mutating —
a `.tcb`-kinded `LockId` pointing at an Endpoint object is a no-op,
not a wrong-object mutation. -/
def acquireLockOnObject (s : SystemState) (core : CoreId)
    (l : LockId) (mode : AccessMode) : SystemState :=
  match l.kind with
  | .objStore =>
      { s with objStoreLock := s.objStoreLock.applyOp (mode.toAcquireOp core) }
  | .page => s    -- SM3.A.8 N/A
  | .tcb | .endpoint | .notification | .cnode
  | .vspaceRoot | .untyped | .schedContext | .reply =>
      updateObjectLockAt s l (mode.toAcquireOp core)

/-- WS-SM SM3.C.2: `releaseLockOnObject` — the SM3.C.1 release
primitive's per-object body.  Symmetric to `acquireLockOnObject`
with the release-op variant of the `RwLockOp` constructor.  Same
audit-pass-1 (Comment 5) kind-checked dispatch via
`updateObjectLockAt`. -/
def releaseLockOnObject (s : SystemState) (core : CoreId)
    (l : LockId) (mode : AccessMode) : SystemState :=
  match l.kind with
  | .objStore =>
      { s with objStoreLock := s.objStoreLock.applyOp (mode.toReleaseOp core) }
  | .page => s    -- SM3.A.8 N/A
  | .tcb | .endpoint | .notification | .cnode
  | .vspaceRoot | .untyped | .schedContext | .reply =>
      updateObjectLockAt s l (mode.toReleaseOp core)

/-- **WS-LC LC4.1**: `cancelLockOnObject` — the per-object **withdrawal**.

Third sibling of `acquireLockOnObject` / `releaseLockOnObject`, with the
same kind dispatch: `.objStore` advances the state-level lock word
directly, `.page` is the SM3.A.8 no-op, and the nine modeled kinds route
through `updateObjectLockAt`, which is where the fail-closed kind check
lives (an absent object, or one whose variant does not match `l.kind`,
leaves the state unchanged).

Withdrawing is what a release cannot do.  Both release arms guard on
holdership and are the identity for a core that is not a holder
(`rwLock_release_by_nonholder_preserves_waiters`), so where the growing
phase found a member contended — `tryAcquire*` **enqueues** rather than
granting — the shrinking phase could not remove the request it had left
behind.  This can. -/
def cancelLockOnObject (s : SystemState) (core : CoreId)
    (l : LockId) (mode : AccessMode) : SystemState :=
  match l.kind with
  | .objStore =>
      { s with objStoreLock := s.objStoreLock.applyOp (mode.toCancelOp core) }
  | .page => s    -- SM3.A.8 N/A
  | .tcb | .endpoint | .notification | .cnode
  | .vspaceRoot | .untyped | .schedContext | .reply =>
      updateObjectLockAt s l (mode.toCancelOp core)

/-- WS-SM SM3.A.10 / PR #870 round 7: the SystemState-level singleton's
`objId` is decorative — the `.objStore` arms of `acquireLockOnObject` and
`releaseLockOnObject` dispatch on the kind alone and advance
`SystemState.objStoreLock` directly, so every `.objStore`-kinded `LockId`
names the same lock word.  Recorded as a theorem so `stateLevelLock`'s
one-canonical-spelling rule is a convenience, not a soundness requirement:
two footprints spelling the singleton with different ids still exclude each
other. -/
theorem stateLevelLock_objId_irrelevant (s : SystemState) (core : CoreId)
    (o₁ o₂ : SeLe4n.ObjId) (m : AccessMode) :
    acquireLockOnObject s core ⟨.objStore, o₁⟩ m
      = acquireLockOnObject s core ⟨.objStore, o₂⟩ m := rfl

/-- WS-SM SM6.D: `acquireLockOnObject` on a `.reply` LockId routes through
`updateObjectLockAt` — Reply is now a first-class kernel object (hierarchy
level 6), so its per-object lock is acquired like any modeled kind (was an
identity no-op under the former SM3.A.5 N/A decision). -/
theorem acquireLockOnObject_reply (s : SystemState) (core : CoreId)
    (oid : SeLe4n.ObjId) (m : AccessMode) :
    acquireLockOnObject s core ⟨.reply, oid⟩ m =
      updateObjectLockAt s ⟨.reply, oid⟩ (m.toAcquireOp core) := by
  unfold acquireLockOnObject; rfl

/-- WS-SM SM3.C.2: `acquireLockOnObject` on a `.page` LockId is
identity (SM3.A.8 N/A — page mappings stored in VSpaceRoot.mappings). -/
@[simp] theorem acquireLockOnObject_page (s : SystemState) (core : CoreId)
    (oid : SeLe4n.ObjId) (m : AccessMode) :
    acquireLockOnObject s core ⟨.page, oid⟩ m = s := by
  unfold acquireLockOnObject; rfl

/-- WS-SM SM6.D: `releaseLockOnObject` on a `.reply` LockId routes through
`updateObjectLockAt` (symmetric to `acquireLockOnObject_reply`). -/
theorem releaseLockOnObject_reply (s : SystemState) (core : CoreId)
    (oid : SeLe4n.ObjId) (m : AccessMode) :
    releaseLockOnObject s core ⟨.reply, oid⟩ m =
      updateObjectLockAt s ⟨.reply, oid⟩ (m.toReleaseOp core) := by
  unfold releaseLockOnObject; rfl

/-- WS-SM SM3.C.2: `releaseLockOnObject` on a `.page` LockId is
identity. -/
@[simp] theorem releaseLockOnObject_page (s : SystemState) (core : CoreId)
    (oid : SeLe4n.ObjId) (m : AccessMode) :
    releaseLockOnObject s core ⟨.page, oid⟩ m = s := by
  unfold releaseLockOnObject; rfl

/-- **WS-LC LC4.1**: `cancelLockOnObject` on a `.reply` LockId routes through
`updateObjectLockAt` (symmetric to `acquireLockOnObject_reply`). -/
theorem cancelLockOnObject_reply (s : SystemState) (core : CoreId)
    (oid : SeLe4n.ObjId) (m : AccessMode) :
    cancelLockOnObject s core ⟨.reply, oid⟩ m =
      updateObjectLockAt s ⟨.reply, oid⟩ (m.toCancelOp core) := by
  unfold cancelLockOnObject; rfl

-- ----------------------------------------------------------------------------
-- The object store's extension invariant, across the three lock primitives
-- ----------------------------------------------------------------------------

/-! Re-homed at **WS-LC LC4.5**.  These lived in two places at once —
`LockSetHeld` (as `*_preserves_invExt`) and `NonInterferencePerCore` (as
`*_preserves_objects_invExt`) — because neither module is in the other's
import closure and each branch needed the same fact.  That is one question
with two answers, and the withdrawal would have made it three.  They belong
here, beside `updateObjectLockAt`, which both branches import. -/

/-- The lock-only object rewrite preserves the RHTable extension invariant. -/
theorem updateObjectAt_updateLock_preserves_invExt (s : SystemState)
    (oid : SeLe4n.ObjId) (op : RwLockOp) (hInv : s.objects.invExt) :
    (updateObjectAt s oid (fun obj => obj.updateLock op)).objects.invExt := by
  unfold updateObjectAt
  cases hGet : s.objects.get? oid with
  | none => exact hInv
  | some obj =>
      exact SeLe4n.Kernel.RobinHood.RHTable.insert_preserves_invExt s.objects oid _ hInv

/-- So does the kind-checked per-object lock update; both fail-closed branches
leave the table untouched. -/
theorem updateObjectLockAt_preserves_invExt (s : SystemState)
    (l : LockId) (op : RwLockOp) (hInv : s.objects.invExt) :
    (updateObjectLockAt s l op).objects.invExt := by
  unfold updateObjectLockAt
  cases hLookup : LockId.lookup s l with
  | none => exact hInv
  | some _ => exact updateObjectAt_updateLock_preserves_invExt s l.objId op hInv

/-- And each of the three per-object primitives. -/
theorem acquireLockOnObject_preserves_invExt (s : SystemState)
    (core : CoreId) (l : LockId) (m : AccessMode) (hInv : s.objects.invExt) :
    (acquireLockOnObject s core l m).objects.invExt := by
  unfold acquireLockOnObject
  cases l.kind <;> first | exact hInv | exact updateObjectLockAt_preserves_invExt s l _ hInv

theorem releaseLockOnObject_preserves_invExt (s : SystemState)
    (core : CoreId) (l : LockId) (m : AccessMode) (hInv : s.objects.invExt) :
    (releaseLockOnObject s core l m).objects.invExt := by
  unfold releaseLockOnObject
  cases l.kind <;> first | exact hInv | exact updateObjectLockAt_preserves_invExt s l _ hInv

theorem cancelLockOnObject_preserves_invExt (s : SystemState)
    (core : CoreId) (l : LockId) (m : AccessMode) (hInv : s.objects.invExt) :
    (cancelLockOnObject s core l m).objects.invExt := by
  unfold cancelLockOnObject
  cases l.kind <;> first | exact hInv | exact updateObjectLockAt_preserves_invExt s l _ hInv

/-- **WS-LC LC4.1**: `cancelLockOnObject` on a `.page` LockId is identity. -/
@[simp] theorem cancelLockOnObject_page (s : SystemState) (core : CoreId)
    (oid : SeLe4n.ObjId) (m : AccessMode) :
    cancelLockOnObject s core ⟨.page, oid⟩ m = s := by
  unfold cancelLockOnObject; rfl

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

/-- WS-SM SM3.C.8 foundation (audit-pass-1): `updateObjectLockAt`
preserves the table-level `objStoreLock`.  Both branches (kind-match
→ `updateObjectAt`; mismatch/absent → identity) leave `objStoreLock`
untouched. -/
theorem updateObjectLockAt_preserves_objStoreLock (s : SystemState)
    (l : LockId) (op : RwLockOp) :
    (updateObjectLockAt s l op).objStoreLock = s.objStoreLock := by
  unfold updateObjectLockAt
  cases LockId.lookup s l with
  | none => rfl
  | some _ => exact updateObjectAt_preserves_objStoreLock s l.objId _

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
  | page => rfl
  | tcb | endpoint | notification | cnode
  | vspaceRoot | untyped | schedContext | reply =>
    all_goals exact updateObjectLockAt_preserves_objStoreLock s l _

/-- WS-SM SM3.C.8 foundation: releasing a per-object lock preserves
the table-level `objStoreLock`.  Symmetric to the acquire form. -/
theorem releaseLockOnObject_preserves_objStoreLock_of_modeled
    (s : SystemState) (core : CoreId) (l : LockId) (m : AccessMode)
    (hKind : l.kind ≠ .objStore) :
    (releaseLockOnObject s core l m).objStoreLock = s.objStoreLock := by
  unfold releaseLockOnObject
  cases hK : l.kind with
  | objStore => exact absurd hK hKind
  | page => rfl
  | tcb | endpoint | notification | cnode
  | vspaceRoot | untyped | schedContext | reply =>
    all_goals exact updateObjectLockAt_preserves_objStoreLock s l _

/-- **WS-LC LC4.5**: and the withdrawal, the third sibling. -/
theorem cancelLockOnObject_preserves_objStoreLock_of_modeled
    (s : SystemState) (core : CoreId) (l : LockId) (m : AccessMode)
    (hKind : l.kind ≠ .objStore) :
    (cancelLockOnObject s core l m).objStoreLock = s.objStoreLock := by
  unfold cancelLockOnObject
  cases hK : l.kind with
  | objStore => exact absurd hK hKind
  | page => rfl
  | tcb | endpoint | notification | cnode
  | vspaceRoot | untyped | schedContext | reply =>
    all_goals exact updateObjectLockAt_preserves_objStoreLock s l _

/-- WS-SM SM7.B: `updateObjectAt` frames the TLB-shootdown state (a
per-object store write).  Leaf of the SM7.B debt-(5) `withLockSet`
carriage below. -/
theorem updateObjectAt_tlbShootdown_eq (s : SystemState)
    (oid : SeLe4n.ObjId) (f : KernelObject → KernelObject) :
    (updateObjectAt s oid f).tlbShootdown = s.tlbShootdown := by
  unfold updateObjectAt
  cases s.objects.get? oid <;> rfl

/-- WS-SM SM7.B: `updateObjectLockAt` frames the TLB-shootdown state. -/
theorem updateObjectLockAt_tlbShootdown_eq (s : SystemState)
    (l : LockId) (op : RwLockOp) :
    (updateObjectLockAt s l op).tlbShootdown = s.tlbShootdown := by
  unfold updateObjectLockAt
  cases LockId.lookup s l with
  | none => rfl
  | some _ => exact updateObjectAt_tlbShootdown_eq s l.objId _

/-- WS-SM SM7.B: acquiring any lock frames the TLB-shootdown state —
`.objStore` writes `objStoreLock`, every per-object kind routes through
`updateObjectLockAt`; neither touches `tlbShootdown`. -/
theorem acquireLockOnObject_tlbShootdown_eq (s : SystemState)
    (core : CoreId) (l : LockId) (m : AccessMode) :
    (acquireLockOnObject s core l m).tlbShootdown = s.tlbShootdown := by
  unfold acquireLockOnObject
  cases l.kind with
  | objStore => rfl
  | page => rfl
  | tcb | endpoint | notification | cnode
  | vspaceRoot | untyped | schedContext | reply =>
    all_goals exact updateObjectLockAt_tlbShootdown_eq s l _

/-- WS-SM SM7.B: releasing any lock frames the TLB-shootdown state
(symmetric to the acquire form). -/
theorem releaseLockOnObject_tlbShootdown_eq (s : SystemState)
    (core : CoreId) (l : LockId) (m : AccessMode) :
    (releaseLockOnObject s core l m).tlbShootdown = s.tlbShootdown := by
  unfold releaseLockOnObject
  cases l.kind with
  | objStore => rfl
  | page => rfl
  | tcb | endpoint | notification | cnode
  | vspaceRoot | untyped | schedContext | reply =>
    all_goals exact updateObjectLockAt_tlbShootdown_eq s l _

/-- **WS-LC LC4.2**: and the withdrawal primitive. -/
theorem cancelLockOnObject_tlbShootdown_eq (s : SystemState)
    (core : CoreId) (l : LockId) (m : AccessMode) :
    (cancelLockOnObject s core l m).tlbShootdown = s.tlbShootdown := by
  unfold cancelLockOnObject
  cases l.kind with
  | objStore => rfl
  | page => rfl
  | tcb | endpoint | notification | cnode
  | vspaceRoot | untyped | schedContext | reply =>
    all_goals exact updateObjectLockAt_tlbShootdown_eq s l _

/-- WS-SM SM7.B.8 foundation (substantive): `updateObjectAt` with a
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

/-- **WS-LC LC4.1**: fold `cancelLockOnObject` over a list of
`(LockId, AccessMode)` pairs — the **withdrawal** half of the shrinking
phase.

Order is irrelevant here (a withdrawal at one lock cannot enable or
disable a withdrawal at another), but the caller passes the same reversed
sequence the release fold takes, so the two halves visit the footprint in
one order and `unwindAll` reads as a single pass. -/
def cancelAll (core : CoreId) (pairs : List (LockId × AccessMode))
    (s : SystemState) : SystemState :=
  pairs.foldl (init := s) (fun st p => cancelLockOnObject st core p.fst p.snd)

/-- **WS-LC LC4.1**: the 2PL **shrinking phase** — withdraw, then release.

This is the one definition of "what a two-phase-locking bracket does on
the way out", consumed by both `withLockSet` below and by the revalidated
entry's refusal path (`FineLockFlow`).  A second, separately spelled
unwind on either of those paths is the defect this naming exists to
prevent: the two would answer the same question and drift.

## Why withdraw *before* release, and not the other way round

Two identities meet at every member.  A release by a non-holder is the
identity — both arms of `applyOp` guard on holdership.  A withdrawal by a
holder is the identity — INV-R4 keeps holders out of `waiters`.  So on a
well-formed state both orders are correct, and neither needs a branch, a
holdership test or a decidability instance.

Withdrawing first is what makes the payoff *unconditional*.  The release
arms promote **from** `waiters` (`promoteWaitersIfReadersEmpty`,
`promoteWaitersOnWriterRelease`), so a core still queued when its own
release runs can be promoted into a holder slot that the withdrawal has
already passed.  Cancelling first removes the request before any
promotion can see it, and the fold-level result then needs no distinctness
hypothesis on the footprint and no resolvability hypothesis on the state:
`cancelAll` establishes "no queued request from `core`" at every member,
and **no release arm ever enqueues**, so `releaseAll` preserves it
everywhere at once.  That is `unwindAll_leaves_no_queued_request`. -/
def unwindAll (core : CoreId) (pairs : List (LockId × AccessMode))
    (s : SystemState) : SystemState :=
  releaseAll core pairs (cancelAll core pairs s)

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

/-- **WS-LC LC4.1**: `cancelAll` on the empty list is identity. -/
@[simp] theorem cancelAll_nil (core : CoreId) (s : SystemState) :
    cancelAll core [] s = s := rfl

/-- **WS-LC LC4.1**: `cancelAll` on a cons unfolds to the head withdrawal
followed by the tail withdrawal on the new state. -/
@[simp] theorem cancelAll_cons (core : CoreId) (l : LockId) (m : AccessMode)
    (rest : List (LockId × AccessMode)) (s : SystemState) :
    cancelAll core ((l, m) :: rest) s =
      cancelAll core rest (cancelLockOnObject s core l m) := rfl

/-- **WS-LC LC4.1**: the shrinking phase on the empty list is identity —
both halves are. -/
@[simp] theorem unwindAll_nil (core : CoreId) (s : SystemState) :
    unwindAll core [] s = s := rfl

/-- **WS-LC LC4.5**: the growing phase preserves the extension invariant. -/
theorem acquireAll_preserves_invExt (core : CoreId)
    (pairs : List (LockId × AccessMode)) (s : SystemState) (hInv : s.objects.invExt) :
    (acquireAll core pairs s).objects.invExt := by
  induction pairs generalizing s with
  | nil => exact hInv
  | cons p rest ih =>
    obtain ⟨l, m⟩ := p
    rw [acquireAll_cons]
    exact ih _ (acquireLockOnObject_preserves_invExt s core l m hInv)

/-- **WS-LC LC4.5**: so does each half of the shrinking phase. -/
theorem releaseAll_preserves_invExt (core : CoreId)
    (pairs : List (LockId × AccessMode)) (s : SystemState) (hInv : s.objects.invExt) :
    (releaseAll core pairs s).objects.invExt := by
  induction pairs generalizing s with
  | nil => exact hInv
  | cons p rest ih =>
    obtain ⟨l, m⟩ := p
    rw [releaseAll_cons]
    exact ih _ (releaseLockOnObject_preserves_invExt s core l m hInv)

theorem cancelAll_preserves_invExt (core : CoreId)
    (pairs : List (LockId × AccessMode)) (s : SystemState) (hInv : s.objects.invExt) :
    (cancelAll core pairs s).objects.invExt := by
  induction pairs generalizing s with
  | nil => exact hInv
  | cons p rest ih =>
    obtain ⟨l, m⟩ := p
    rw [cancelAll_cons]
    exact ih _ (cancelLockOnObject_preserves_invExt s core l m hInv)

/-- **WS-LC LC4.5**: and hence the shrinking phase as a whole. -/
theorem unwindAll_preserves_invExt (core : CoreId)
    (pairs : List (LockId × AccessMode)) (s : SystemState) (hInv : s.objects.invExt) :
    (unwindAll core pairs s).objects.invExt :=
  releaseAll_preserves_invExt core pairs _ (cancelAll_preserves_invExt core pairs s hInv)

/-- **WS-LC LC4.1**: the shrinking phase is the withdrawal fold followed by
the release fold, over the same sequence.

Stated as a lemma rather than left to `unfold` because it is the shape
every `unwindAll_*` frame corollary composes through: a property that both
`cancelAll` and `releaseAll` preserve is preserved by the shrinking phase,
and the proof is this rewrite plus the two siblings. -/
theorem unwindAll_eq_releaseAll_cancelAll (core : CoreId)
    (pairs : List (LockId × AccessMode)) (s : SystemState) :
    unwindAll core pairs s = releaseAll core pairs (cancelAll core pairs s) := rfl

-- ============================================================================
-- §3b — The shrinking phase's abstract payoff (WS-LC LC4.3)
-- ============================================================================

/-! The two facts the whole unwind rests on, both at the abstract
`RwLockState` level and both free of hypotheses.  Everything the
`SystemState` layer proves about a footprint is these two lifted through
`updateObjectLockAt`. -/

/-- **WS-LC LC4.3**: a withdrawal leaves the withdrawing core with no queued
request — unconditionally, and by computation.

`applyOp`'s cancel arm removes the withdrawer (`RwLockState.withdraw`, a
`filter (·.1 ≠ core)`) before it hands the head's turn on (PR #890 review
round 5), and the promotion only ever drops more from the head
(`applyOp_cancel_waiters_sublist_filter`), so this is the filter's own
specification.  No `wf` hypothesis: the arm has no enabling guard. -/
theorem rwLock_cancel_not_queued (l : RwLockState) (c : CoreId) :
    c ∉ (l.applyOp (.cancel c)).waiters.map Prod.fst := by
  intro hMem
  obtain ⟨w, hw, hEq⟩ := List.mem_map.mp hMem
  have hw' := (RwLockState.applyOp_cancel_waiters_sublist_filter l c).subset hw
  exact (of_decide_eq_true (List.mem_filter.mp hw').2) hEq

/-- **WS-LC LC4.3**: no withdrawal ever enqueues — including for a core
other than the one withdrawing.

`rwLock_cancel_not_queued` is the sharper statement about the *withdrawing*
core; this is the frame every other core needs, and it is what lets the
shrinking phase's fold carry an already-established absence past members
withdrawn later. -/
theorem rwLock_cancel_preserves_not_queued (l : RwLockState) (c canceller : CoreId)
    (h : c ∉ l.waiters.map Prod.fst) :
    c ∉ (l.applyOp (.cancel canceller)).waiters.map Prod.fst :=
  fun hMem => h ((RwLockState.applyOp_cancel_waiters_sublist l canceller).map Prod.fst
    |>.subset hMem)

/-- **WS-LC LC4.3**: no release ever enqueues.

Both release arms either no-op or drop a prefix of `waiters` by promotion
(`release_waiters_sublist`), so a core absent from the queue before a
release is absent after it — whichever core released, and in whichever
mode.  This is the half that lets the fold-level payoff dispense with any
distinctness hypothesis on the footprint: the withdrawal fold establishes
absence at every member, and the release fold cannot undo it anywhere. -/
theorem rwLock_release_preserves_not_queued (l : RwLockState) (c releaser : CoreId)
    (m : AccessMode) (h : c ∉ l.waiters.map Prod.fst) :
    c ∉ (l.applyOp (m.toReleaseOp releaser)).waiters.map Prod.fst := by
  have hSub : (l.applyOp (m.toReleaseOp releaser)).waiters.Sublist l.waiters := by
    refine release_waiters_sublist l _ ?_
    cases m with
    | read => exact Or.inl ⟨releaser, rfl⟩
    | write => exact Or.inr ⟨releaser, rfl⟩
  exact fun hMem => h (hSub.map Prod.fst |>.subset hMem)

/-- **WS-LC LC4.3**: withdraw-then-release leaves no queued request — the
single-lock statement the whole shrinking phase is built from.

This is the theorem that replaces the "what 'released' does and does not
mean" caveat.  Note what it does **not** say: `¬ coreInvolved`, which is
false here — a core holding a *write* lock, unwound at a member declared
`.read`, keeps `writerHeld`, and ruling that out needs a mode-agreement
hypothesis threaded from the growing phase.  The caveat's claim was that
the unwind *cannot remove a queued request*; this is its exact negation,
and it holds with no hypotheses at all. -/
theorem rwLock_unwind_not_queued (l : RwLockState) (c : CoreId) (m : AccessMode) :
    c ∉ ((l.applyOp (.cancel c)).applyOp (m.toReleaseOp c)).waiters.map Prod.fst :=
  rwLock_release_preserves_not_queued _ c c m (rwLock_cancel_not_queued l c)

/-- **WS-LC LC4.3**: the *other* order does not give the same theorem.

Release-then-withdraw is correct on a well-formed state, but it is not
unconditional: the release arms promote **from** `waiters`, so a core still
queued when its own release runs can be promoted into a holder slot the
withdrawal has already passed.  Recorded as the reason `unwindAll` is
ordered the way it is — a future refactor that swaps the two folds has to
answer this. -/
theorem rwLock_release_then_cancel_not_queued (l : RwLockState) (c : CoreId)
    (m : AccessMode) :
    c ∉ ((l.applyOp (m.toReleaseOp c)).applyOp (.cancel c)).waiters.map Prod.fst :=
  rwLock_cancel_not_queued _ c

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

   The action sees the state the growing phase produced.  Whether
   every lock in `S` is then *held* in the core's name depends on
   the pre-state: `acquireLockOnObject` applies SM2.C's
   `tryAcquire*`, which **enqueues** a core when the lock is
   already held rather than granting it, and this function invokes
   the action either way — a pure, total state transformer has no
   way to block, and modelling the wait is SM2.C's job (a queued
   core's admission is a *trace*-level fact, `rwLock_queued_liveness`,
   not something a single state transition can express).

   So the growing phase declares a footprint and advances the lock
   words; it does not by itself establish mutual exclusion.  WS-SM
   SM8.D pins both directions —
   `lockSetAcquiredState_grants_when_free` and the load-bearing
   negative `lockSetAcquiredState_does_not_grant_when_contended`.
   Results that genuinely need exclusion take `lockSetHeld` as a
   hypothesis; the SM8.D information-flow results deliberately do
   not, being frame arguments over lock writes.  Live exclusion
   today comes from the SM5.I global kernel-entry ticket lock.
3. **Shrinking phase**: `unwindAll` over `ordered.reverse` (sorted
   descending by `LockId`), starting from the post-action state —
   **withdraw, then release**.

   A release is the identity for a core that is not a holder, so a
   release-only shrinking phase gave back exactly the members the
   growing phase had granted and left the *contended* ones queued,
   to be promoted later and strand the lock.  Withdrawing first
   closes that (`unwindAll_leaves_no_queued_request`), and it costs
   the granted members nothing: a withdrawal by a holder is the
   identity, because INV-R4 keeps holders out of the wait queue.

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
  let unwound := unwindAll core ordered.reverse postAction
  (unwound, result)

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
      let unwound := unwindAll core ordered.reverse postAction
      (unwound, result) := rfl

/-- WS-SM SM3.C.1: the result of `withLockSet` is determined by the
3-phase structural decomposition.  Useful for case analysis on
`withLockSet`'s output without manually unfolding. -/
theorem withLockSet_eq_decomposition {α : Type} (S : LockSet) (core : CoreId)
    (action : SystemState → SystemState × α) (s : SystemState) :
    withLockSet S core action s =
      ( unwindAll core S.lockAcquireSequence.reverse
          (action (acquireAll core S.lockAcquireSequence s)).1,
        (action (acquireAll core S.lockAcquireSequence s)).2 ) := by
  unfold withLockSet
  rfl

/-- WS-SM SM3.C.1: the first component of `withLockSet`'s output
(the post-unwind SystemState). -/
@[simp] theorem withLockSet_fst {α : Type} (S : LockSet) (core : CoreId)
    (action : SystemState → SystemState × α) (s : SystemState) :
    (withLockSet S core action s).1 =
      unwindAll core S.lockAcquireSequence.reverse
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

-- ============================================================================
-- WS-SM SM7.B (debt (5) slice): `withLockSet` carries `pendingBounded`
-- ============================================================================
-- The 2PL bracket touches only the object store's per-object lock fields
-- (`updateObjectLockAt`) and the table-level `objStoreLock` — never
-- `SystemState.tlbShootdown`.  So the shootdown capacity invariant (the
-- 12th `proofLayerInvariantBundle` conjunct) rides the bracket whenever
-- the guarded action preserves it: the acquire and release phases frame
-- the field, and the action carries it across.  This closes the
-- shootdown-relevant slice of the SM6.D `withLockSet` bundle-carriage
-- obligation; the remaining twenty-conjunct `ipcInvariantFull` carriage
-- stays tracked with the SM6.D item.

/-- WS-SM SM7.B: the acquire fold frames the TLB-shootdown state. -/
theorem acquireAll_tlbShootdown_eq (core : CoreId)
    (pairs : List (LockId × AccessMode)) (s : SystemState) :
    (acquireAll core pairs s).tlbShootdown = s.tlbShootdown := by
  induction pairs generalizing s with
  | nil => rfl
  | cons p rest ih =>
    rw [acquireAll_cons, ih, acquireLockOnObject_tlbShootdown_eq]

/-- WS-SM SM7.B: the release fold frames the TLB-shootdown state. -/
theorem releaseAll_tlbShootdown_eq (core : CoreId)
    (pairs : List (LockId × AccessMode)) (s : SystemState) :
    (releaseAll core pairs s).tlbShootdown = s.tlbShootdown := by
  induction pairs generalizing s with
  | nil => rfl
  | cons p rest ih =>
    rw [releaseAll_cons, ih, releaseLockOnObject_tlbShootdown_eq]

/-- **WS-LC LC4.2**: the withdrawal fold frames the TLB-shootdown state. -/
theorem cancelAll_tlbShootdown_eq (core : CoreId)
    (pairs : List (LockId × AccessMode)) (s : SystemState) :
    (cancelAll core pairs s).tlbShootdown = s.tlbShootdown := by
  induction pairs generalizing s with
  | nil => rfl
  | cons p rest ih =>
    rw [cancelAll_cons, ih, cancelLockOnObject_tlbShootdown_eq]

/-- **WS-LC LC4.2**: so does the shrinking phase as a whole. -/
theorem unwindAll_tlbShootdown_eq (core : CoreId)
    (pairs : List (LockId × AccessMode)) (s : SystemState) :
    (unwindAll core pairs s).tlbShootdown = s.tlbShootdown := by
  rw [unwindAll_eq_releaseAll_cancelAll, releaseAll_tlbShootdown_eq,
      cancelAll_tlbShootdown_eq]

/-- WS-SM SM7.B: `withLockSet` frames the TLB-shootdown state exactly
when its guarded action does — the 2PL bracket itself never touches the
field. -/
theorem withLockSet_tlbShootdown_eq {α : Type} (S : LockSet) (core : CoreId)
    (action : SystemState → SystemState × α) (s : SystemState)
    (hAction : ∀ s', ((action s').1).tlbShootdown = s'.tlbShootdown) :
    ((withLockSet S core action s).1).tlbShootdown = s.tlbShootdown := by
  rw [withLockSet_fst, unwindAll_tlbShootdown_eq, hAction,
      acquireAll_tlbShootdown_eq]

/-- WS-SM SM7.B (debt (5) slice, the carriage theorem): `withLockSet`
preserves the shootdown capacity invariant `pendingBounded` whenever
its guarded action does.  The bracket frames `tlbShootdown`, so the
12th `proofLayerInvariantBundle` conjunct rides any 2PL-guarded
transition that preserves it — the shootdown-relevant slice of the
SM6.D `withLockSet` bundle-carriage obligation. -/
theorem withLockSet_preserves_pendingBounded {α : Type} (S : LockSet)
    (core : CoreId) (action : SystemState → SystemState × α) (s : SystemState)
    (hFrame : ∀ s', ((action s').1).tlbShootdown = s'.tlbShootdown)
    (hB : SeLe4n.Kernel.Architecture.pendingBounded s.tlbShootdown) :
    SeLe4n.Kernel.Architecture.pendingBounded
      ((withLockSet S core action s).1).tlbShootdown := by
  rw [withLockSet_tlbShootdown_eq S core action s hFrame]
  exact hB

end SeLe4n.Kernel.Concurrency
