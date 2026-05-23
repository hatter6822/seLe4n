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

/-!
# WS-SM SM3.B.1/B.2 — `KernelObject.lockKind`, `LockId.fromObject`, `LockId.lookup`

This module implements the SM3.B per-object projection layer:

* `KernelObject.lockKind` — projects the SM0.I `LockKind` from a
  `KernelObject` variant.  Total, decidable, with 7 per-variant
  `@[simp]` unfold lemmas.
* `LockId.fromObject` — pairs an `ObjId` (the table key under which
  the object is stored in `SystemState.objects`) with the object's
  kind to produce a `LockId`.
* `LockId.lookup` — given a kernel state and a `LockId`, returns
  the abstract lock state and object iff the object exists AND its
  kind matches the LockId.

The plan §5.2's pseudocode `LockId.fromObject (o : KernelObject) :
LockId` uses an `id` field on each variant (`tcb.tid`, `ep.eid`, …).
In seLe4n only `TCB` and `SchedContext` carry their own ID
(`TCB.tid`, `SchedContext.scId`); the other variants (`Endpoint`,
`Notification`, `CNode`, `VSpaceRoot`, `UntypedObject`) are looked
up by external `ObjId` in the `SystemState.objects` RHTable.

Splitting the projection into `lockKind` (variant-only) and
`fromObject (oid, o)` (variant + ObjId) matches seLe4n's actual
data model: every kernel object is canonically identified by its
RHTable key, regardless of whether the inner-struct ID field
exists.  Both forms compose correctly through `LockId.lookup`,
which extracts the ObjId from the LockId itself and uses it as
both the lookup key and the LockId's `objId` component.

The Lean elaborator's pattern-match exhaustivity check on
`KernelObject` (a 7-variant inductive) is the structural
enforcement that a future variant addition — for example a
post-1.0 `Reply` or `Page` kernel object — forces the per-variant
`lockKind` arm to be added in the same PR (otherwise this module
fails to elaborate).  This is the SM3.A.5 / SM3.A.8 N/A decision's
SM3.B-layer enforcement counterpart, analogous to the
`KernelObjectType.variants_count_exactly_seven` pin in the SM3.A
audit-pass-5 inventory.
-/

namespace SeLe4n.Model

open SeLe4n.Kernel.Concurrency

namespace KernelObject

-- ============================================================================
-- SM3.B.1 — KernelObject.lockKind projection
-- ============================================================================

/-- WS-SM SM3.B.1: extract the SM0.I `LockKind` from a `KernelObject`
variant.

Total per-variant case dispatch.  The mapping is:

| `KernelObject` variant | `LockKind`        | `LockKind.level` |
|-----------------------:|:------------------|:----------------:|
| `.untyped`             | `.untyped`        | 1                |
| `.cnode`               | `.cnode`          | 2                |
| `.tcb`                 | `.tcb`            | 3                |
| `.endpoint`            | `.endpoint`       | 4                |
| `.notification`        | `.notification`   | 5                |
| `.schedContext`        | `.schedContext`   | 7                |
| `.vspaceRoot`          | `.vspaceRoot`     | 8                |

Note the level gap between `.notification` (5) and `.schedContext`
(7): level 6 is reserved for `LockKind.reply`, which seLe4n does
not (yet) model as a kernel object (SM3.A.5 N/A decision).  When
a `Reply` object lands in a future workstream, both the SM3.A
field and this projection's `.reply` arm will need to be added in
the same PR.

The Lean elaborator's pattern-match exhaustivity check ensures
this completeness obligation cannot be silently violated. -/
def lockKind : KernelObject → LockKind
  | .tcb _          => .tcb
  | .endpoint _     => .endpoint
  | .notification _ => .notification
  | .cnode _        => .cnode
  | .vspaceRoot _   => .vspaceRoot
  | .untyped _      => .untyped
  | .schedContext _ => .schedContext

/-- WS-SM SM3.B.1: per-variant `@[simp]` unfold lemma for `.tcb`. -/
@[simp] theorem lockKind_tcb (t : TCB) :
    (KernelObject.tcb t).lockKind = .tcb := rfl

/-- WS-SM SM3.B.1: per-variant `@[simp]` unfold lemma for `.endpoint`. -/
@[simp] theorem lockKind_endpoint (e : Endpoint) :
    (KernelObject.endpoint e).lockKind = .endpoint := rfl

/-- WS-SM SM3.B.1: per-variant `@[simp]` unfold lemma for `.notification`. -/
@[simp] theorem lockKind_notification (n : Notification) :
    (KernelObject.notification n).lockKind = .notification := rfl

/-- WS-SM SM3.B.1: per-variant `@[simp]` unfold lemma for `.cnode`. -/
@[simp] theorem lockKind_cnode (c : CNode) :
    (KernelObject.cnode c).lockKind = .cnode := rfl

/-- WS-SM SM3.B.1: per-variant `@[simp]` unfold lemma for `.vspaceRoot`. -/
@[simp] theorem lockKind_vspaceRoot (v : VSpaceRoot) :
    (KernelObject.vspaceRoot v).lockKind = .vspaceRoot := rfl

/-- WS-SM SM3.B.1: per-variant `@[simp]` unfold lemma for `.untyped`. -/
@[simp] theorem lockKind_untyped (u : UntypedObject) :
    (KernelObject.untyped u).lockKind = .untyped := rfl

/-- WS-SM SM3.B.1: per-variant `@[simp]` unfold lemma for `.schedContext`. -/
@[simp] theorem lockKind_schedContext (s : SeLe4n.Kernel.SchedContext) :
    (KernelObject.schedContext s).lockKind = .schedContext := rfl

/-- WS-SM SM3.B.1: totality witness — `lockKind` is defined for every
`KernelObject`.  Trivial (every total function returns a value of
its codomain), but consumed by SM3.C as the "every object has a
declared lock kind" structural lemma.  Mirrors SM3.A's
`objectLockOf_exists` totality witness. -/
theorem lockKind_exists (obj : KernelObject) :
    ∃ k : LockKind, obj.lockKind = k :=
  ⟨obj.lockKind, rfl⟩

/-- WS-SM SM3.B.1 audit-pass-2: substantive co-domain witness —
`lockKind` returns one of the seven kernel-object kinds
(`.tcb`, `.endpoint`, `.notification`, `.cnode`, `.vspaceRoot`,
`.untyped`, `.schedContext`).  It NEVER returns `.objStore`,
`.reply`, or `.page` — the three `LockKind` variants that have
no corresponding kernel-object struct in seLe4n's model.

This is the substantive counterpart to `lockKind_exists`: it tells
consumers something useful (the actual range of `lockKind`) rather
than the vacuous "lockKind has a value".  Consumed by SM3.C's
`lockSetHeld` predicate when checking that every LockId in a
`lockSet` corresponds to a modeled object kind. -/
theorem lockKind_in_modeledKinds (obj : KernelObject) :
    obj.lockKind = .tcb ∨ obj.lockKind = .endpoint ∨
    obj.lockKind = .notification ∨ obj.lockKind = .cnode ∨
    obj.lockKind = .vspaceRoot ∨ obj.lockKind = .untyped ∨
    obj.lockKind = .schedContext := by
  cases obj
  case tcb _ => exact Or.inl rfl
  case endpoint _ => exact Or.inr (Or.inl rfl)
  case notification _ => exact Or.inr (Or.inr (Or.inl rfl))
  case cnode _ => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  case vspaceRoot _ =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  case untyped _ =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  case schedContext _ =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))

/-- WS-SM SM3.B.1 audit-pass-2: `lockKind` is NEVER `.objStore`.

The `.objStore` `LockKind` corresponds to the SystemState-level
table-level lock (`SystemState.objStoreLock`), not to any
per-object struct.  A consumer that processes `obj.lockKind` and
expects a modeled kind can rely on this witness. -/
theorem lockKind_ne_objStore (obj : KernelObject) :
    obj.lockKind ≠ .objStore := by
  cases obj <;> intro h <;> cases h

/-- WS-SM SM3.B.1 audit-pass-2: `lockKind` is NEVER `.reply`
(SM3.A.5 N/A — Reply not modeled as a kernel-object struct). -/
theorem lockKind_ne_reply (obj : KernelObject) :
    obj.lockKind ≠ .reply := by
  cases obj <;> intro h <;> cases h

/-- WS-SM SM3.B.1 audit-pass-2: `lockKind` is NEVER `.page`
(SM3.A.8 N/A — page mappings stored inline in VSpaceRoot.mappings). -/
theorem lockKind_ne_page (obj : KernelObject) :
    obj.lockKind ≠ .page := by
  cases obj <;> intro h <;> cases h

/-- WS-SM SM3.B.1: agreement with `objectType` — the kind tag
projection is in lock-step with the type tag projection.

Both `objectType` and `lockKind` dispatch on the same 7-variant
case structure; this theorem witnesses their bijection
explicitly.  Consumed by the SM3.B.4 `lockSet_consistent` proof
that the declared `permittedKinds τ` set agrees with the
SystemState's actually-looked-up object kinds. -/
theorem lockKind_eq_of_objectType (obj : KernelObject) :
    match obj.objectType with
    | .tcb          => obj.lockKind = .tcb
    | .endpoint     => obj.lockKind = .endpoint
    | .notification => obj.lockKind = .notification
    | .cnode        => obj.lockKind = .cnode
    | .vspaceRoot   => obj.lockKind = .vspaceRoot
    | .untyped      => obj.lockKind = .untyped
    | .schedContext => obj.lockKind = .schedContext := by
  cases obj <;> rfl

end KernelObject

-- ============================================================================
-- SM3.B.1 — LockId.fromObject
-- ============================================================================

namespace LockId

/-- WS-SM SM3.B.1 (plan §5.2): build a `LockId` from an `ObjId` and a
`KernelObject`.

The `ObjId` is the canonical RHTable key; the `KernelObject`'s
variant determines the kind.  Together they specify a unique
lockable kernel resource.

The plan's pseudocode uses `match o with | .tcb tcb => LockId.mk
.tcb tcb.tid.toObjId` — but in seLe4n only `TCB` and
`SchedContext` carry an inner-struct ID.  We take the ObjId
externally (from the SystemState lookup) so the projection is
total for every variant.  The two TCB-specific signatures
(`fromTcb (tcb : TCB)` and the variant `fromObject`) compose
consistently under the state-level invariant
`tcbStoredUnderTidObjId` (per the existing `Model/Object/Types.lean`
note on identity-mapping). -/
def fromObject (oid : SeLe4n.ObjId) (o : KernelObject) : LockId :=
  { kind := o.lockKind, objId := oid }

/-- WS-SM SM3.B.1: structural `@[simp]` projection of the kind field. -/
@[simp] theorem fromObject_kind (oid : SeLe4n.ObjId) (o : KernelObject) :
    (LockId.fromObject oid o).kind = o.lockKind := rfl

/-- WS-SM SM3.B.1: structural `@[simp]` projection of the objId field. -/
@[simp] theorem fromObject_objId (oid : SeLe4n.ObjId) (o : KernelObject) :
    (LockId.fromObject oid o).objId = oid := rfl

/-- WS-SM SM3.B.1: per-variant convenience: `LockId.fromObject` on a TCB
specialises to `(.tcb, tid.toObjId)`. -/
@[simp] theorem fromObject_tcb (oid : SeLe4n.ObjId) (t : TCB) :
    LockId.fromObject oid (KernelObject.tcb t) = ⟨.tcb, oid⟩ := rfl

/-- WS-SM SM3.B.1: per-variant convenience for `.endpoint`. -/
@[simp] theorem fromObject_endpoint (oid : SeLe4n.ObjId) (e : Endpoint) :
    LockId.fromObject oid (KernelObject.endpoint e) = ⟨.endpoint, oid⟩ := rfl

/-- WS-SM SM3.B.1: per-variant convenience for `.notification`. -/
@[simp] theorem fromObject_notification (oid : SeLe4n.ObjId) (n : Notification) :
    LockId.fromObject oid (KernelObject.notification n) =
      ⟨.notification, oid⟩ := rfl

/-- WS-SM SM3.B.1: per-variant convenience for `.cnode`. -/
@[simp] theorem fromObject_cnode (oid : SeLe4n.ObjId) (c : CNode) :
    LockId.fromObject oid (KernelObject.cnode c) = ⟨.cnode, oid⟩ := rfl

/-- WS-SM SM3.B.1: per-variant convenience for `.vspaceRoot`. -/
@[simp] theorem fromObject_vspaceRoot (oid : SeLe4n.ObjId) (v : VSpaceRoot) :
    LockId.fromObject oid (KernelObject.vspaceRoot v) =
      ⟨.vspaceRoot, oid⟩ := rfl

/-- WS-SM SM3.B.1: per-variant convenience for `.untyped`. -/
@[simp] theorem fromObject_untyped (oid : SeLe4n.ObjId) (u : UntypedObject) :
    LockId.fromObject oid (KernelObject.untyped u) = ⟨.untyped, oid⟩ := rfl

/-- WS-SM SM3.B.1: per-variant convenience for `.schedContext`. -/
@[simp] theorem fromObject_schedContext (oid : SeLe4n.ObjId)
    (sc : SeLe4n.Kernel.SchedContext) :
    LockId.fromObject oid (KernelObject.schedContext sc) =
      ⟨.schedContext, oid⟩ := rfl

-- (Audit-pass-2: removed the duplicate `fromObject_lockKind_eq`,
-- which was literally identical to `fromObject_kind` above —
-- same statement, same `rfl` proof, only differing in the lack of
-- `@[simp]` and in the docstring's framing.  Use `fromObject_kind`.)

-- ============================================================================
-- SM3.B.2 — LockId.lookup
-- ============================================================================

/-- WS-SM SM3.B.2 (plan §5.2): given a `SystemState` and a `LockId`,
resolve the abstract lock state and the underlying object.

Returns:
* `some (lockState, object)` iff:
  - the object exists at `l.objId` in `s.objects`, AND
  - the object's variant agrees with `l.kind` (i.e., the LockId
    does not name a wrong-kind object — e.g., naming a TCB via the
    `.endpoint` kind).
* `none` otherwise — either the object is absent, the kind does
  not match, or the kind is one that does NOT correspond to a
  per-object struct in seLe4n's model (`.objStore` — the
  SystemState-level table lock; `.reply` and `.page` — kinds
  reserved for future-modeled objects, N/A at v1.0.0 per SM3.A.5 /
  SM3.A.8).

The kind-mismatch case prevents a class of capability-confusion
errors where a code path holding a `LockId.mk .tcb tid.toObjId`
accidentally resolves to a non-TCB stored at the same ObjId.

**AK7-cascade cleanliness**: this dispatcher routes through the
typed `getX?` accessors (`getTcb?`, `getEndpoint?`, etc.) defined
in `Model/State.lean` rather than performing a raw pattern-match
on the object store directly.  Each typed accessor encapsulates
its own kind-check; the lookup's structural correctness follows
from the SM3.A `objectLockOf_*` simp lemmas (which reduce
`objectLockOf (.tcb t) = t.lock`, etc.).

The `.objStore` arm returns `none`; the SystemState-level
`objStoreLock` is accessed directly via `s.objStoreLock`, not
via `LockId.lookup`.  SM3.C's `withLockSet` will dispatch the
ObjStore lock acquisition separately at the top of the 2PL ladder.

Used by:
* SM3.C.2 `acquireLockOnObject` / `releaseLockOnObject` to thread
  the lock acquire/release through the per-object lock field.
* SM3.C.4 `lockSetHeld` to check that a declared lock-set is
  currently held by the executing core. -/
def lookup (s : SystemState) (l : LockId) :
    Option (RwLockState × KernelObject) :=
  match l.kind with
  | .tcb =>
      (s.getTcb? ⟨l.objId.val⟩).map (fun (t : TCB) => (t.lock, KernelObject.tcb t))
  | .endpoint =>
      (s.getEndpoint? l.objId).map
        (fun (e : Endpoint) => (e.lock, KernelObject.endpoint e))
  | .notification =>
      (s.getNotification? l.objId).map
        (fun (n : Notification) => (n.lock, KernelObject.notification n))
  | .cnode =>
      (s.getCNode? l.objId).map (fun (c : CNode) => (c.lock, KernelObject.cnode c))
  | .vspaceRoot =>
      (s.getVSpaceRoot? l.objId).map
        (fun (v : VSpaceRoot) => (v.lock, KernelObject.vspaceRoot v))
  | .untyped =>
      (s.getUntyped? l.objId).map
        (fun (u : UntypedObject) => (u.lock, KernelObject.untyped u))
  | .schedContext =>
      (s.getSchedContext? ⟨l.objId.val⟩).map
        (fun (sc : SeLe4n.Kernel.SchedContext) =>
          (sc.lock, KernelObject.schedContext sc))
  -- SM3.A.10's table-level lock is on SystemState, not in objects.
  | .objStore => none
  -- SM3.A.5 / SM3.A.8: Reply / Page are N/A for seLe4n's object model
  -- (Reply is encoded in TCB state; Page is encoded in VSpaceRoot.mappings).
  | .reply => none
  | .page => none

/-- WS-SM SM3.B.2: lookup at a present ObjId with matching kind returns
`some` carrying the abstract lock state and the object.

Discharged via dispatch on `l.kind` and the corresponding typed
getter's behaviour: `getTcb?`, `getEndpoint?`, etc. each return
`some inner` exactly when `objects[oid]? = some (.<variant> inner)`. -/
theorem lookup_some_of_kindMatch (s : SystemState) (l : LockId)
    (o : KernelObject)
    (hPresent : s.objects[l.objId]? = some o)
    (hKind : o.lockKind = l.kind) :
    LockId.lookup s l = some (KernelObject.objectLockOf o, o) := by
  unfold LockId.lookup
  cases hVar : o with
  | tcb t =>
      have hKindTcb : l.kind = .tcb := by rw [← hKind]; subst hVar; rfl
      rw [hKindTcb]
      simp only [SystemState.getTcb?]
      have hObjIdEq : (⟨l.objId.val⟩ : SeLe4n.ThreadId).toObjId = l.objId := by
        show SeLe4n.ObjId.ofNat l.objId.val = l.objId
        exact SeLe4n.ObjId.ofNat_toNat l.objId
      rw [hObjIdEq, hPresent]
      subst hVar; simp
  | endpoint e =>
      have hKindEp : l.kind = .endpoint := by rw [← hKind]; subst hVar; rfl
      rw [hKindEp]
      simp only [SystemState.getEndpoint?]
      rw [hPresent]
      subst hVar; simp
  | notification n =>
      have hKindN : l.kind = .notification := by rw [← hKind]; subst hVar; rfl
      rw [hKindN]
      simp only [SystemState.getNotification?]
      rw [hPresent]
      subst hVar; simp
  | cnode c =>
      have hKindCn : l.kind = .cnode := by rw [← hKind]; subst hVar; rfl
      rw [hKindCn]
      simp only [SystemState.getCNode?]
      rw [hPresent]
      subst hVar; simp
  | vspaceRoot v =>
      have hKindVs : l.kind = .vspaceRoot := by rw [← hKind]; subst hVar; rfl
      rw [hKindVs]
      simp only [SystemState.getVSpaceRoot?]
      rw [hPresent]
      subst hVar; simp
  | untyped u =>
      have hKindU : l.kind = .untyped := by rw [← hKind]; subst hVar; rfl
      rw [hKindU]
      simp only [SystemState.getUntyped?]
      rw [hPresent]
      subst hVar; simp
  | schedContext sc =>
      have hKindSc : l.kind = .schedContext := by rw [← hKind]; subst hVar; rfl
      rw [hKindSc]
      simp only [SystemState.getSchedContext?]
      have hObjIdEq : (⟨l.objId.val⟩ : SeLe4n.SchedContextId).toObjId = l.objId := by
        show SeLe4n.ObjId.ofNat l.objId.val = l.objId
        exact SeLe4n.ObjId.ofNat_toNat l.objId
      rw [hObjIdEq, hPresent]
      subst hVar; simp

/-- WS-SM SM3.B.2: `lookup`-`fromObject` round-trip — looking up a
`LockId` built from a present object recovers the object and its
lock state. -/
theorem lookup_fromObject_of_present (s : SystemState)
    (oid : SeLe4n.ObjId) (o : KernelObject)
    (hPresent : s.objects[oid]? = some o) :
    LockId.lookup s (LockId.fromObject oid o) =
      some (KernelObject.objectLockOf o, o) :=
  lookup_some_of_kindMatch s (LockId.fromObject oid o) o
    (by show s.objects[oid]? = some o; exact hPresent)
    (by show o.lockKind = (LockId.fromObject oid o).kind; rfl)

/-- WS-SM SM3.B.2: lookup at the `.objStore` kind is always `none`.

The SystemState-level `objStoreLock` is accessed directly via
`s.objStoreLock`, not via `LockId.lookup`.  This `_objStore`
witness is the fail-closed acknowledgment that the dispatcher
deliberately does not handle this kind. -/
@[simp] theorem lookup_objStore (s : SystemState) (oid : SeLe4n.ObjId) :
    LockId.lookup s ⟨.objStore, oid⟩ = none := rfl

/-- WS-SM SM3.B.2: lookup at the `.reply` kind is always `none`
(SM3.A.5 N/A decision). -/
@[simp] theorem lookup_reply (s : SystemState) (oid : SeLe4n.ObjId) :
    LockId.lookup s ⟨.reply, oid⟩ = none := rfl

/-- WS-SM SM3.B.2: lookup at the `.page` kind is always `none`
(SM3.A.8 N/A decision). -/
@[simp] theorem lookup_page (s : SystemState) (oid : SeLe4n.ObjId) :
    LockId.lookup s ⟨.page, oid⟩ = none := rfl

/-- WS-SM SM3.B.2: if `lookup` returns `some (st, o)`, the LockId's
kind matches the object's kind.  This is the "consistent kind"
post-condition that SM3.C consumes when it pattern-matches on
`lookup`'s result. -/
theorem lookup_kindMatch (s : SystemState) (l : LockId)
    (st : RwLockState) (o : KernelObject)
    (hLookup : LockId.lookup s l = some (st, o)) :
    o.lockKind = l.kind := by
  unfold LockId.lookup at hLookup
  cases hK : l.kind with
  | objStore => rw [hK] at hLookup; cases hLookup
  | reply => rw [hK] at hLookup; cases hLookup
  | page => rw [hK] at hLookup; cases hLookup
  | tcb =>
      rw [hK] at hLookup
      cases hG : s.getTcb? ⟨l.objId.val⟩ with
      | none => rw [hG] at hLookup; cases hLookup
      | some t =>
          rw [hG] at hLookup
          simp at hLookup
          obtain ⟨_, hoEq⟩ := hLookup
          rw [← hoEq]; rfl
  | endpoint =>
      rw [hK] at hLookup
      cases hG : s.getEndpoint? l.objId with
      | none => rw [hG] at hLookup; cases hLookup
      | some e =>
          rw [hG] at hLookup
          simp at hLookup
          obtain ⟨_, hoEq⟩ := hLookup
          rw [← hoEq]; rfl
  | notification =>
      rw [hK] at hLookup
      cases hG : s.getNotification? l.objId with
      | none => rw [hG] at hLookup; cases hLookup
      | some n =>
          rw [hG] at hLookup
          simp at hLookup
          obtain ⟨_, hoEq⟩ := hLookup
          rw [← hoEq]; rfl
  | cnode =>
      rw [hK] at hLookup
      cases hG : s.getCNode? l.objId with
      | none => rw [hG] at hLookup; cases hLookup
      | some c =>
          rw [hG] at hLookup
          simp at hLookup
          obtain ⟨_, hoEq⟩ := hLookup
          rw [← hoEq]; rfl
  | vspaceRoot =>
      rw [hK] at hLookup
      cases hG : s.getVSpaceRoot? l.objId with
      | none => rw [hG] at hLookup; cases hLookup
      | some v =>
          rw [hG] at hLookup
          simp at hLookup
          obtain ⟨_, hoEq⟩ := hLookup
          rw [← hoEq]; rfl
  | untyped =>
      rw [hK] at hLookup
      cases hG : s.getUntyped? l.objId with
      | none => rw [hG] at hLookup; cases hLookup
      | some u =>
          rw [hG] at hLookup
          simp at hLookup
          obtain ⟨_, hoEq⟩ := hLookup
          rw [← hoEq]; rfl
  | schedContext =>
      rw [hK] at hLookup
      cases hG : s.getSchedContext? ⟨l.objId.val⟩ with
      | none => rw [hG] at hLookup; cases hLookup
      | some sc =>
          rw [hG] at hLookup
          simp at hLookup
          obtain ⟨_, hoEq⟩ := hLookup
          rw [← hoEq]; rfl

/-- WS-SM SM3.B.2: if `lookup` returns `some (st, o)`, the lock state
component equals `objectLockOf o`. -/
theorem lookup_lockState_eq (s : SystemState) (l : LockId)
    (st : RwLockState) (o : KernelObject)
    (hLookup : LockId.lookup s l = some (st, o)) :
    st = KernelObject.objectLockOf o := by
  unfold LockId.lookup at hLookup
  cases hK : l.kind with
  | objStore => rw [hK] at hLookup; cases hLookup
  | reply => rw [hK] at hLookup; cases hLookup
  | page => rw [hK] at hLookup; cases hLookup
  | tcb =>
      rw [hK] at hLookup
      cases hG : s.getTcb? ⟨l.objId.val⟩ with
      | none => rw [hG] at hLookup; cases hLookup
      | some t =>
          rw [hG] at hLookup
          simp at hLookup
          obtain ⟨hSt, hO⟩ := hLookup
          rw [← hSt, ← hO]; rfl
  | endpoint =>
      rw [hK] at hLookup
      cases hG : s.getEndpoint? l.objId with
      | none => rw [hG] at hLookup; cases hLookup
      | some e =>
          rw [hG] at hLookup
          simp at hLookup
          obtain ⟨hSt, hO⟩ := hLookup
          rw [← hSt, ← hO]; rfl
  | notification =>
      rw [hK] at hLookup
      cases hG : s.getNotification? l.objId with
      | none => rw [hG] at hLookup; cases hLookup
      | some n =>
          rw [hG] at hLookup
          simp at hLookup
          obtain ⟨hSt, hO⟩ := hLookup
          rw [← hSt, ← hO]; rfl
  | cnode =>
      rw [hK] at hLookup
      cases hG : s.getCNode? l.objId with
      | none => rw [hG] at hLookup; cases hLookup
      | some c =>
          rw [hG] at hLookup
          simp at hLookup
          obtain ⟨hSt, hO⟩ := hLookup
          rw [← hSt, ← hO]; rfl
  | vspaceRoot =>
      rw [hK] at hLookup
      cases hG : s.getVSpaceRoot? l.objId with
      | none => rw [hG] at hLookup; cases hLookup
      | some v =>
          rw [hG] at hLookup
          simp at hLookup
          obtain ⟨hSt, hO⟩ := hLookup
          rw [← hSt, ← hO]; rfl
  | untyped =>
      rw [hK] at hLookup
      cases hG : s.getUntyped? l.objId with
      | none => rw [hG] at hLookup; cases hLookup
      | some u =>
          rw [hG] at hLookup
          simp at hLookup
          obtain ⟨hSt, hO⟩ := hLookup
          rw [← hSt, ← hO]; rfl
  | schedContext =>
      rw [hK] at hLookup
      cases hG : s.getSchedContext? ⟨l.objId.val⟩ with
      | none => rw [hG] at hLookup; cases hLookup
      | some sc =>
          rw [hG] at hLookup
          simp at hLookup
          obtain ⟨hSt, hO⟩ := hLookup
          rw [← hSt, ← hO]; rfl

end LockId

end SeLe4n.Model
