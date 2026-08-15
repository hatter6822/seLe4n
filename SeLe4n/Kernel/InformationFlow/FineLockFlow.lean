-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- STATUS: staged for WS-SM SM8.D — information flow under fine locks
-- (docs/planning/SMP_INFORMATION_FLOW_PLAN.md §5 SM8.D.1 … SM8.D.6).

import SeLe4n.Kernel.InformationFlow.CovertChannelPerCore
import SeLe4n.Kernel.Concurrency.Locks.LockSetForSyscall

/-!
# WS-SM SM8.D — information flow under fine locks

Plan `docs/planning/SMP_INFORMATION_FLOW_PLAN.md` §5 sub-tasks SM8.D.1 …
SM8.D.5 (SM8.D.6 is the scenario suite in `tests/SmpInformationFlowSuite.lean`).

SM8.A built the per-core observer, SM8.B proved what the SMP kernel does not
leak and registered what it does, SM8.C audited the one flow it deliberately
permits.  This module is about the **lock words themselves**: the per-object
`RwLockState` the SM3 two-phase-locking bracket writes on every acquire and
every release, once SM3.C.9 wraps the `@[export]` bodies in `withLockSet`.

## What the plan's table said, and what SM8.B made of it

The SM8.D table was written while `projectKernelObject` carried each object's
`lock` into the observable state.  SM8.B.4 erased it — three fields of
`CoreId`s on every object kind re-opened the SM5.B placement channel — which
moves D.1 … D.3 rather than discharging them:

* **D.1** is no longer "document what an observer sees of the lock"; it is the
  statement that an observer sees *nothing* of it, and a statement is a
  theorem, not a docstring.  §1 proves it in the strongest available form: the
  observer's whole view **factors through lock erasure**, so the lock word is
  not merely absent from one arm of one projection — no part of any observer's
  view on any core is a function of it.
* **D.2** is then an instance: reader multiplicity is one coordinate of the
  erased field (§2), and what is left of it is the CC-5 *timing* claim.
* **D.3** is **false as written** at the model level — a blocked reader sees
  nothing of writer exclusion in the projection — and §3 states the true form:
  what a blocked acquirer observes is wall-clock delay, that delay is CC-5, and
  under the SM2.C fairness assumption it is **bounded**, so the channel has a
  bounded per-acquisition alphabet exactly as CC-1 does.
* **D.4** (§4) and **D.5** (§5) are unaffected by the erasure: integrity is
  about which subjects may write which objects, and the secure-flow witness is
  about the live path.

## Section map

* §1 (SM8.D.1) — `KernelObject.eraseLock`, the lock-erased content; the
  projection factors through it; `lockWritesOnly`, the state-level "this step
  moved nothing but lock words"; and the acquire / release / fold / bracket
  instances.
* §2 (SM8.D.2) — reader multiplicity is not observable, instantiated at the
  SM2.C reachable multi-reader witness; and the CC-5 restatement.
* §3 (SM8.D.3) — writer exclusion is not observable either; the blocked
  acquirer's observation is its admission delay; the delay bound, the
  alphabet bound and the trace-capacity bound.
* §4 (SM8.D.4) — Biba integrity under per-core locks, in **both** integrity
  directions, with the two theorems that stop it being vacuous.
* §5 (SM8.D.5) — the secure-information-flow witness for a 2PL-bracketed live
  syscall entry, including the sharpened fail-closed statement.

Axiom-clean: every declaration depends only on the standard foundational
axioms (`propext` / `Quot.sound` / `Classical.choice`), checked exhaustively
by `scripts/check_module_axioms.py`.
-/

namespace SeLe4n.Model

/-!
### The lock-erased content lives beside its getter

`KernelObject.setLock` / `KernelObject.eraseLock` — the setter for the SM3.A.10
`objectLockOf` getter and the quotient it induces — are defined in
`Model/Object/Structures.lean`, beside `objectLockOf` itself, together with the
setter/getter algebra (`setLock_objectLockOf`, `eraseLock_setLock`,
`setLock_objectLockOf_self`, `eq_of_eraseLock_eq_of_lock_eq`,
`eraseLock_objectType`, `eraseLock_wellFormed`).  They are model vocabulary, not
information-flow vocabulary, and putting them here would have made a
`KernelObject` setter reachable only through a staged module.

What stays here is the part that cannot: `lockKind` lives in
`Concurrency/Locks/LockIdProjection.lean` and `updateLock` in
`Concurrency/Locks/WithLockSet.lean`, both of which import `Structures`.
-/

/-- SM8.D.1: erasure preserves the SM3.B lock-kind projection, so nothing that
dispatches on `lockKind` — the whole `LockId` discipline — can tell an erased
object from its original either. -/
@[simp] theorem KernelObject.eraseLock_lockKind (obj : KernelObject) :
    obj.eraseLock.lockKind = obj.lockKind := by cases obj <;> rfl

/-- SM8.D.1: the SM3.C.2 lock *advance* is a lock write and nothing else. -/
@[simp] theorem KernelObject.eraseLock_updateLock (obj : KernelObject)
    (op : SeLe4n.Kernel.Concurrency.RwLockOp) :
    (obj.updateLock op).eraseLock = obj.eraseLock := by cases obj <;> rfl

/-- SM8.D.1 (**the non-vacuity witness for the whole section**): a lock write is
a *real* write.  Erasing the lock is therefore an abstraction over content that
genuinely moves — not a restatement of "nothing happened", which is what every
theorem below would collapse to if `updateLock` were the identity.

Stated over an arbitrary object whose lock is free, which is every object at
boot (`default_objects_locks_unheld`) and every freshly retyped one, so the
witness is about the states the kernel actually runs in. -/
theorem KernelObject.updateLock_not_identity (obj : KernelObject)
    (hFree : objectLockOf obj = SeLe4n.Kernel.Concurrency.RwLockState.unheld)
    (c : SeLe4n.Kernel.Concurrency.CoreId) :
    obj.updateLock (.tryAcquireWrite c) ≠ obj := by
  intro h
  have hLock := congrArg objectLockOf h
  rw [KernelObject.objectLockOf_updateLock, hFree] at hLock
  have hWriter := congrArg SeLe4n.Kernel.Concurrency.RwLockState.writerHeld hLock
  simp [SeLe4n.Kernel.Concurrency.RwLockState.applyOp,
    SeLe4n.Kernel.Concurrency.RwLockState.unheld,
    SeLe4n.Kernel.Concurrency.RwLockState.coreInvolved] at hWriter

end SeLe4n.Model

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId bootCoreId numCores RwLockState RwLockOp AccessMode LockId
  LockSet)

-- ============================================================================
-- §1  SM8.D.1 — the observer sees nothing of the lock
-- ============================================================================
--
-- The SM8.B.4 result is that the 2PL bracket does not move the projection.
-- That is a statement about the *operations* the bracket performs.  D.1 asks
-- the stronger question — what can an observer learn about the lock word at
-- all? — and the answer is nothing, because the projection **factors through**
-- lock erasure: `projectKernelObject` composed with `setLock l` is
-- `projectKernelObject`, for every `l`.  An operation-by-operation argument
-- could not say that; it would leave open whether some *other* way of writing
-- the field is visible.

/-- SM8.D.1 (the object-level headline): **the observer's view of an object is a
function of its lock-erased content.**  Overwriting the lock word with an
arbitrary `RwLockState` — held, contended, queued, anything — leaves the
projected object literally identical. -/
@[simp] theorem projectKernelObject_setLock (ctx : LabelingContext) (observer : IfObserver)
    (obj : KernelObject) (l : RwLockState) :
    projectKernelObject ctx observer (obj.setLock l) = projectKernelObject ctx observer obj := by
  cases obj <;> rfl

/-- SM8.D.1: the factoring, stated as such — projecting an object is projecting
its erased content. -/
theorem projectKernelObject_eq_eraseLock (ctx : LabelingContext) (observer : IfObserver)
    (obj : KernelObject) :
    projectKernelObject ctx observer obj = projectKernelObject ctx observer obj.eraseLock :=
  (projectKernelObject_setLock ctx observer obj _).symm

/-- SM8.D.1: consequently, objects that agree up to their lock words project
identically.  This is the transport §1's state-level results are built from:
a step that leaves every object's *erased* content alone leaves every
observer's object view alone, whatever it did to the locks. -/
theorem projectKernelObject_congr_of_eraseLock (ctx : LabelingContext) (observer : IfObserver)
    {o₁ o₂ : KernelObject} (h : o₁.eraseLock = o₂.eraseLock) :
    projectKernelObject ctx observer o₁ = projectKernelObject ctx observer o₂ := by
  rw [projectKernelObject_eq_eraseLock ctx observer o₁,
      projectKernelObject_eq_eraseLock ctx observer o₂, h]

/-- SM8.D.1: **the state-level relation** — this step wrote nothing but lock
words.

Two clauses, and both are load-bearing:

* the equation names the only two fields allowed to move, `objects` and the
  table-level `objStoreLock`, by *reconstructing* the post-state from the
  pre-state and those two — so every other `SystemState` field is pinned
  without enumerating them (a field added tomorrow is covered on the day it is
  added, which an enumeration would not be);
* the object clause says the object store moved only in lock words.

Note this is deliberately **not** "the state is unchanged".  Under fine locks
that claim is simply false — the bracket writes real lock words
(`KernelObject.updateLock_not_identity`) — and stating it would be the
shortcut this section exists to avoid.  What is true, and what §1 … §5 show is
enough, is that the writes are confined to a field no observer and no integrity
policy reads. -/
def lockWritesOnly (s s' : SystemState) : Prop :=
  (∃ (objs : SeLe4n.Kernel.RobinHood.RHTable SeLe4n.ObjId KernelObject) (lk : RwLockState),
      s' = { s with objects := objs, objStoreLock := lk }) ∧
    ∀ oid : SeLe4n.ObjId,
      (s'.objects[oid]?).map KernelObject.eraseLock
        = (s.objects[oid]?).map KernelObject.eraseLock

theorem lockWritesOnly_refl (s : SystemState) : lockWritesOnly s s :=
  ⟨⟨s.objects, s.objStoreLock, rfl⟩, fun _ => rfl⟩

theorem lockWritesOnly_trans {s₁ s₂ s₃ : SystemState}
    (h₁ : lockWritesOnly s₁ s₂) (h₂ : lockWritesOnly s₂ s₃) : lockWritesOnly s₁ s₃ := by
  obtain ⟨⟨objs₁, lk₁, hEq₁⟩, hObj₁⟩ := h₁
  obtain ⟨⟨objs₂, lk₂, hEq₂⟩, hObj₂⟩ := h₂
  refine ⟨⟨objs₂, lk₂, ?_⟩, fun oid => (hObj₂ oid).trans (hObj₁ oid)⟩
  rw [hEq₂, hEq₁]

/-- SM8.D.1: the fields `lockWritesOnly` pins, extracted one at a time.  Every
consumer below reaches for these rather than re-deriving them from the
reconstruction equation. -/
theorem lockWritesOnly_scheduler {s s' : SystemState} (h : lockWritesOnly s s') :
    s'.scheduler = s.scheduler := by obtain ⟨⟨_, _, hEq⟩, _⟩ := h; rw [hEq]

theorem lockWritesOnly_machine {s s' : SystemState} (h : lockWritesOnly s s') :
    s'.machine = s.machine := by obtain ⟨⟨_, _, hEq⟩, _⟩ := h; rw [hEq]

theorem lockWritesOnly_objectIndex {s s' : SystemState} (h : lockWritesOnly s s') :
    s'.objectIndex = s.objectIndex := by obtain ⟨⟨_, _, hEq⟩, _⟩ := h; rw [hEq]

theorem lockWritesOnly_services {s s' : SystemState} (h : lockWritesOnly s s') :
    s'.services = s.services := by obtain ⟨⟨_, _, hEq⟩, _⟩ := h; rw [hEq]

theorem lockWritesOnly_irqHandlers {s s' : SystemState} (h : lockWritesOnly s s') :
    s'.irqHandlers = s.irqHandlers := by obtain ⟨⟨_, _, hEq⟩, _⟩ := h; rw [hEq]

/-- SM8.D.1: a lock-only step preserves the observer's **object** view. -/
theorem lockWritesOnly_preserves_projectObjects (ctx : LabelingContext) (observer : IfObserver)
    {s s' : SystemState} (h : lockWritesOnly s s') :
    projectObjects ctx observer s' = projectObjects ctx observer s := by
  funext oid
  simp only [projectObjects]
  by_cases hObs : objectObservable ctx observer oid = true
  · rw [if_pos hObs, if_pos hObs]
    have hErase := h.2 oid
    cases hPost : s'.objects[oid]? with
    | none =>
      rw [hPost] at hErase
      cases hPre : s.objects[oid]? with
      | none => rfl
      | some o => rw [hPre] at hErase; simp at hErase
    | some o' =>
      rw [hPost] at hErase
      cases hPre : s.objects[oid]? with
      | none => rw [hPre] at hErase; simp at hErase
      | some o =>
        rw [hPre] at hErase
        simp only [Option.map_some, Option.some.injEq] at hErase
        simp only [Option.map_some, Option.some.injEq]
        exact projectKernelObject_congr_of_eraseLock ctx observer hErase
  · simp only [Bool.not_eq_true] at hObs
    rw [if_neg (by simp [hObs]), if_neg (by simp [hObs])]

/-- SM8.D.1 (**the D.1 headline at the state level**): a step that writes only
lock words is invisible to the single-core observer. -/
theorem lockWritesOnly_preserves_projection (ctx : LabelingContext) (observer : IfObserver)
    {s s' : SystemState} (h : lockWritesOnly s s') :
    projectState ctx observer s' = projectState ctx observer s :=
  projectState_eq_of_objects_projection_eq ctx observer s s'
    (lockWritesOnly_preserves_projectObjects ctx observer h)
    (lockWritesOnly_scheduler h) (lockWritesOnly_services h) (lockWritesOnly_irqHandlers h)
    (lockWritesOnly_objectIndex h) (lockWritesOnly_machine h)

/-- SM8.D.1 (**the D.1 headline, per core**): and therefore invisible to the
observer `(c, L)` on *every* core.

The per-core lift is not automatic — a step could preserve the global
projection and still move a remote core's slots (`crossCoreLeakage_bounded`
is stated because that happens) — but a lock-only step frames the scheduler
outright, so every per-core component rides through. -/
theorem lockWritesOnly_preserves_onCore (ctx : LabelingContext) (c : CoreId) (L : SecurityLabel)
    {s s' : SystemState} (h : lockWritesOnly s s') :
    ObservableState.onCore ctx c L s' = ObservableState.onCore ctx c L s :=
  projectStateOnCore_congr ctx (IfObserver.ofLabel L)
    (lockWritesOnly_preserves_projection ctx (IfObserver.ofLabel L) h)
    (by rw [lockWritesOnly_scheduler h]) (by rw [lockWritesOnly_scheduler h])
    (by rw [lockWritesOnly_scheduler h]) (by rw [lockWritesOnly_scheduler h])
    (by rw [lockWritesOnly_scheduler h]) (by rw [lockWritesOnly_machine h])

/-- SM8.D.1: the same at an arbitrary `IfObserver` rather than a clearance label.

`lockWritesOnly_preserves_onCore` is the `IfObserver.ofLabel` instance.  This form
is what the §5 bracket needs, because the SM8.B non-interference surface is stated
over observers. -/
theorem lockWritesOnly_preserves_projectionOnCore (ctx : LabelingContext)
    (observer : IfObserver) (c : CoreId) {s s' : SystemState} (h : lockWritesOnly s s') :
    projectStateOnCore ctx observer s' c = projectStateOnCore ctx observer s c :=
  projectStateOnCore_congr ctx observer
    (lockWritesOnly_preserves_projection ctx observer h)
    (by rw [lockWritesOnly_scheduler h]) (by rw [lockWritesOnly_scheduler h])
    (by rw [lockWritesOnly_scheduler h]) (by rw [lockWritesOnly_scheduler h])
    (by rw [lockWritesOnly_scheduler h]) (by rw [lockWritesOnly_machine h])

/-- SM8.D.1: a **decidable refuter** for `lockWritesOnly`.

Not an `iff`, and deliberately so: `lockWritesOnly`'s object clause quantifies
over every `ObjId` and compares whole `KernelObject`s, neither of which is
decidable (`KernelObject` has no `DecidableEq` — WS-G5 removed it because
`RHTable`'s structural equality would hide hash-layout non-determinism).  What
*is* decidable is the index and the per-object *kind*, and a step that moved
either moved something no lock write can move.  So a `false` here is a genuine
refutation of `lockWritesOnly`, which is what a test needs; a `true` is
necessary and not sufficient, which is what `lockWritesOnly_lockWritesOnlyCheck`
records. -/
def lockWritesOnlyCheck (s s' : SystemState) : Bool :=
  (s'.objectIndex == s.objectIndex) &&
    s.objectIndex.all (fun oid =>
      ((s'.objects[oid]?).map KernelObject.objectType)
        == ((s.objects[oid]?).map KernelObject.objectType))

/-- SM8.D.1: the refuter is **sound** — a lock-only step passes it, so a
failure is a real counterexample rather than an artefact of the approximation. -/
theorem lockWritesOnly_lockWritesOnlyCheck {s s' : SystemState} (h : lockWritesOnly s s') :
    lockWritesOnlyCheck s s' = true := by
  unfold lockWritesOnlyCheck
  refine Bool.and_eq_true _ _ |>.mpr ⟨?_, ?_⟩
  · simpa using lockWritesOnly_objectIndex h
  · refine List.all_eq_true.mpr ?_
    intro oid _
    have hErase := h.2 oid
    have : (s'.objects[oid]?).map KernelObject.objectType
        = (s.objects[oid]?).map KernelObject.objectType := by
      cases hPost : s'.objects[oid]? with
      | none =>
        rw [hPost] at hErase
        cases hPre : s.objects[oid]? with
        | none => rfl
        | some o => rw [hPre] at hErase; simp at hErase
      | some o' =>
        rw [hPost] at hErase
        cases hPre : s.objects[oid]? with
        | none => rw [hPre] at hErase; simp at hErase
        | some o =>
          rw [hPre] at hErase
          simp only [Option.map_some, Option.some.injEq] at hErase
          simp only [Option.map_some, Option.some.injEq]
          rw [← KernelObject.eraseLock_objectType o', ← KernelObject.eraseLock_objectType o,
            hErase]
    simpa using this

/-- SM8.D.1: the `lowEquivalent_smp` form, for composition with the SM8.B
surface. -/
theorem lockWritesOnly_lowEquivalent_smp (ctx : LabelingContext) (observer : IfObserver)
    {s s' : SystemState} (h : lockWritesOnly s s') :
    lowEquivalent_smp ctx observer s' s := fun c =>
  projectStateOnCore_congr ctx observer
    (lockWritesOnly_preserves_projection ctx observer h)
    (by rw [lockWritesOnly_scheduler h]) (by rw [lockWritesOnly_scheduler h])
    (by rw [lockWritesOnly_scheduler h]) (by rw [lockWritesOnly_scheduler h])
    (by rw [lockWritesOnly_scheduler h]) (by rw [lockWritesOnly_machine h])

-- ----------------------------------------------------------------------------
-- SM8.D.1 — the lock-writing operations, one at a time
-- ----------------------------------------------------------------------------

/-- SM8.D.1: an in-place object rewrite that preserves erased content is a
lock-only write.  Every lock primitive below is an instance of this: what
distinguishes them is only which `LockId` they resolve and which `RwLockOp`
they apply. -/
theorem updateObjectAt_lockWritesOnly (s : SystemState) (oid : SeLe4n.ObjId)
    (f : KernelObject → KernelObject) (hf : ∀ o, (f o).eraseLock = o.eraseLock)
    (hInv : s.objects.invExt) :
    lockWritesOnly s (SeLe4n.Kernel.Concurrency.updateObjectAt s oid f) := by
  unfold SeLe4n.Kernel.Concurrency.updateObjectAt
  cases hGet : s.objects.get? oid with
  | none => exact lockWritesOnly_refl s
  | some obj =>
    refine ⟨⟨s.objects.insert oid (f obj), s.objStoreLock, rfl⟩, fun o => ?_⟩
    show ((s.objects.insert oid (f obj))[o]?).map KernelObject.eraseLock = _
    simp only [RHTable_getElem?_eq_get?]
    rw [RHTable_getElem?_insert s.objects oid (f obj) hInv o]
    by_cases hEq : (oid == o) = true
    · have hOid : oid = o := eq_of_beq hEq
      subst hOid
      rw [if_pos hEq, hGet]
      simp only [Option.map_some, Option.some.injEq]
      exact hf obj
    · rw [if_neg hEq]

/-- SM8.D.1: **writing an arbitrary lock word** into the object at `oid` — the
form D.1 and D.2 quantify over. -/
def setObjectLockAt (s : SystemState) (oid : SeLe4n.ObjId) (l : RwLockState) : SystemState :=
  SeLe4n.Kernel.Concurrency.updateObjectAt s oid (fun obj => obj.setLock l)

theorem setObjectLockAt_lockWritesOnly (s : SystemState) (oid : SeLe4n.ObjId)
    (l : RwLockState) (hInv : s.objects.invExt) :
    lockWritesOnly s (setObjectLockAt s oid l) :=
  updateObjectAt_lockWritesOnly s oid _ (fun o => o.eraseLock_setLock l) hInv

/-- SM8.D.1 (**the direct form of D.1**): *whatever* an object's lock word says
— free, write-held by any core, read-held by any set of cores, with any queue of
waiters — the observer `(c, L)` sees exactly the same state on every core.

This is the statement the plan's D.1 row asked for, in the only form that
survived SM8.B.4's erasure: there is nothing about the lock to document as
visible, because none of it is. -/
theorem onCore_lock_invisible (ctx : LabelingContext) (c : CoreId) (L : SecurityLabel)
    (s : SystemState) (oid : SeLe4n.ObjId) (l : RwLockState) (hInv : s.objects.invExt) :
    ObservableState.onCore ctx c L (setObjectLockAt s oid l)
      = ObservableState.onCore ctx c L s :=
  lockWritesOnly_preserves_onCore ctx c L (setObjectLockAt_lockWritesOnly s oid l hInv)

/-- SM8.D.1: and no observer can distinguish *two* lock words either — the
version with no reference to a "starting" lock state, which is what makes it a
statement about the field rather than about a particular write. -/
theorem onCore_lock_indistinguishable (ctx : LabelingContext) (c : CoreId) (L : SecurityLabel)
    (s : SystemState) (oid : SeLe4n.ObjId) (l₁ l₂ : RwLockState) (hInv : s.objects.invExt) :
    ObservableState.onCore ctx c L (setObjectLockAt s oid l₁)
      = ObservableState.onCore ctx c L (setObjectLockAt s oid l₂) :=
  (onCore_lock_invisible ctx c L s oid l₁ hInv).trans
    (onCore_lock_invisible ctx c L s oid l₂ hInv).symm

/-- SM8.D.1: the **table-level** lock (SM3.A.10's `objStoreLock`, hierarchy
level 0) is outside the observable state as well.  Unlike the per-object locks
this needs no erasure — the field was never a component of `ObservableState` —
but it needs saying, because the level-0 lock is the one every `withLockSet`
whose set names `.objStore` writes. -/
@[simp] theorem onCore_objStoreLock (ctx : LabelingContext) (c : CoreId) (L : SecurityLabel)
    (s : SystemState) (lk : RwLockState) :
    ObservableState.onCore ctx c L { s with objStoreLock := lk }
      = ObservableState.onCore ctx c L s := rfl

theorem objStoreLock_write_lockWritesOnly (s : SystemState) (lk : RwLockState) :
    lockWritesOnly s { s with objStoreLock := lk } :=
  ⟨⟨s.objects, lk, rfl⟩, fun _ => rfl⟩

/-- SM8.D.1: the SM3.C.2 kind-checked lock update writes only lock words. -/
theorem updateObjectLockAt_lockWritesOnly (s : SystemState) (l : LockId) (op : RwLockOp)
    (hInv : s.objects.invExt) :
    lockWritesOnly s (SeLe4n.Kernel.Concurrency.updateObjectLockAt s l op) := by
  unfold SeLe4n.Kernel.Concurrency.updateObjectLockAt
  split
  · exact updateObjectAt_lockWritesOnly s l.objId _
      (fun o => o.eraseLock_updateLock op) hInv
  · exact lockWritesOnly_refl s

/-- SM8.D.1: the acquire primitive writes only lock words — the `.objStore` arm
through the table-level field, the modelled kinds through the object's, the
`.page` arm not at all. -/
theorem acquireLockOnObject_lockWritesOnly (s : SystemState) (core : CoreId)
    (l : LockId) (m : AccessMode) (hInv : s.objects.invExt) :
    lockWritesOnly s (SeLe4n.Kernel.Concurrency.acquireLockOnObject s core l m) := by
  unfold SeLe4n.Kernel.Concurrency.acquireLockOnObject
  cases l.kind <;>
    first
      | exact objStoreLock_write_lockWritesOnly s _
      | exact lockWritesOnly_refl s
      | exact updateObjectLockAt_lockWritesOnly s l _ hInv

/-- SM8.D.1: and the release primitive, symmetrically. -/
theorem releaseLockOnObject_lockWritesOnly (s : SystemState) (core : CoreId)
    (l : LockId) (m : AccessMode) (hInv : s.objects.invExt) :
    lockWritesOnly s (SeLe4n.Kernel.Concurrency.releaseLockOnObject s core l m) := by
  unfold SeLe4n.Kernel.Concurrency.releaseLockOnObject
  cases l.kind <;>
    first
      | exact objStoreLock_write_lockWritesOnly s _
      | exact lockWritesOnly_refl s
      | exact updateObjectLockAt_lockWritesOnly s l _ hInv

/-- SM8.D.1: the 2PL **growing phase** writes only lock words. -/
theorem acquireAll_lockWritesOnly (core : CoreId) (pairs : List (LockId × AccessMode))
    (s : SystemState) (hInv : s.objects.invExt) :
    lockWritesOnly s (SeLe4n.Kernel.Concurrency.acquireAll core pairs s) := by
  induction pairs generalizing s with
  | nil => exact lockWritesOnly_refl s
  | cons p rest ih =>
    obtain ⟨l, m⟩ := p
    rw [SeLe4n.Kernel.Concurrency.acquireAll_cons]
    exact lockWritesOnly_trans (acquireLockOnObject_lockWritesOnly s core l m hInv)
      (ih _ (acquireLockOnObject_preserves_objects_invExt s core l m hInv))

/-- SM8.D.1: the 2PL **shrinking phase** writes only lock words. -/
theorem releaseAll_lockWritesOnly (core : CoreId) (pairs : List (LockId × AccessMode))
    (s : SystemState) (hInv : s.objects.invExt) :
    lockWritesOnly s (SeLe4n.Kernel.Concurrency.releaseAll core pairs s) := by
  induction pairs generalizing s with
  | nil => exact lockWritesOnly_refl s
  | cons p rest ih =>
    obtain ⟨l, m⟩ := p
    rw [SeLe4n.Kernel.Concurrency.releaseAll_cons]
    exact lockWritesOnly_trans (releaseLockOnObject_lockWritesOnly s core l m hInv)
      (ih _ (releaseLockOnObject_preserves_objects_invExt s core l m hInv))

/-- SM8.D.1 (**the bracket**): `withLockSet` writes only lock words beyond
whatever its guarded action writes.

This is the composition that carries every §4 and §5 result: a 2PL-bracketed
transition's *whole* effect is its action's effect plus lock words, and lock
words are invisible to every observer (§1) and to every integrity policy
(§4). -/
theorem withLockSet_lockWritesOnly {α : Type} (S : LockSet) (core : CoreId)
    (action : SystemState → SystemState × α) (s : SystemState)
    (hInv : s.objects.invExt)
    (hActionInv : ∀ s', s'.objects.invExt → ((action s').1).objects.invExt)
    (hActionLock : ∀ s', s'.objects.invExt → lockWritesOnly s' (action s').1) :
    lockWritesOnly s (SeLe4n.Kernel.Concurrency.withLockSet S core action s).1 := by
  rw [SeLe4n.Kernel.Concurrency.withLockSet_fst]
  have hAcqInv := acquireAll_preserves_objects_invExt core S.lockAcquireSequence s hInv
  exact lockWritesOnly_trans (acquireAll_lockWritesOnly core S.lockAcquireSequence s hInv)
    (lockWritesOnly_trans (hActionLock _ hAcqInv)
      (releaseAll_lockWritesOnly core _ _ (hActionInv _ hAcqInv)))

-- ============================================================================
-- §2  SM8.D.2 — reader multiplicity is not directly observable
-- ============================================================================
--
-- The plan's D.2 row predates SM8.B.4.  With the `lock` field carried into the
-- projection, "how many cores hold this object for reading" would have been a
-- component of the observable state and the row would have been a genuine
-- proof obligation about a visible quantity.  With the field erased, reader
-- multiplicity is not a component of `ObservableState` at all, and §1's
-- factoring settles it — but it is worth stating at the multiplicity itself
-- rather than leaving it as a corollary a reader has to assemble, because the
-- plan asked a specific question and the answer should be findable under the
-- name it was asked under.
--
-- What is *not* settled is the timing claim, and that is CC-5, restated below
-- and bounded in §3.

/-- SM8.D.2 (**the headline**): **reader multiplicity is not directly
observable.**  Two states that differ only in how many cores — and which cores
— hold an object's read lock are identical to the observer `(c, L)` on every
core.

Stated over arbitrary reader lists rather than over a particular acquire, so it
covers every multiplicity the lock can reach, including the reachable
two-reader state SM2.C.6 constructs (see
`readerMultiplicity_not_observable_at_reachable_witness`). -/
theorem readerMultiplicity_not_observable (ctx : LabelingContext) (c : CoreId)
    (L : SecurityLabel) (s : SystemState) (oid : SeLe4n.ObjId)
    (readers₁ readers₂ : List CoreId) (hInv : s.objects.invExt) :
    ObservableState.onCore ctx c L
        (setObjectLockAt s oid { RwLockState.unheld with readers := readers₁ })
      = ObservableState.onCore ctx c L
        (setObjectLockAt s oid { RwLockState.unheld with readers := readers₂ }) :=
  onCore_lock_indistinguishable ctx c L s oid _ _ hInv

/-- SM8.D.2: the same statement against the **reachable** multi-reader state
SM2.C.6 exhibits, so the theorem is not about lock words the protocol can never
produce.  `rwLock_reader_multiplicity` gives a `wf` state with at least two
readers; the observer cannot tell it from a free lock. -/
theorem readerMultiplicity_not_observable_at_reachable_witness (ctx : LabelingContext)
    (c : CoreId) (L : SecurityLabel) (s : SystemState) (oid : SeLe4n.ObjId)
    (hInv : s.objects.invExt) :
    ∃ shared : RwLockState, shared.wf ∧ 2 ≤ shared.readers.length ∧
      ObservableState.onCore ctx c L (setObjectLockAt s oid shared)
        = ObservableState.onCore ctx c L (setObjectLockAt s oid RwLockState.unheld) := by
  obtain ⟨shared, hWf, hLen⟩ := SeLe4n.Kernel.Concurrency.rwLock_reader_multiplicity
  exact ⟨shared, hWf, hLen, onCore_lock_indistinguishable ctx c L s oid _ _ hInv⟩

/-- SM8.D.2 (the CC-5 restatement, which is the only open form): reader
multiplicity is invisible in the model, and the channel that remains is the
*timing* one the inventory already registers as CC-5 — `modelVisible := false`,
with §3's bound on what that timing can carry.

Stated as a conjunction so the inventory entry and this result cannot drift:
reclassifying CC-5 as model-visible without changing the projection breaks
this theorem. -/
theorem readerMultiplicity_is_timing_only (ctx : LabelingContext) (c : CoreId)
    (L : SecurityLabel) (s : SystemState) (oid : SeLe4n.ObjId)
    (l₁ l₂ : RwLockState) (hInv : s.objects.invExt) :
    acceptedCovertChannel_lockContention.modelVisible = false ∧
      acceptedCovertChannel_lockContention.perCoreInstance = true ∧
      ObservableState.onCore ctx c L (setObjectLockAt s oid l₁)
        = ObservableState.onCore ctx c L (setObjectLockAt s oid l₂) :=
  ⟨rfl, rfl, onCore_lock_indistinguishable ctx c L s oid l₁ l₂ hInv⟩

-- ============================================================================
-- §3  SM8.D.3 — writer exclusion, and what a blocked acquirer really observes
-- ============================================================================
--
-- The plan's D.3 row reads "writer-exclusion observable to blocked readers".
-- At the model level that is **false**, and it is false in the safe direction:
-- since SM8.B.4 erased `lock`, a blocked reader observes *nothing* of the
-- writer holding the object — not the holder's identity, not the queue it is
-- sitting in, not its own position in that queue.  §3.1 states the refutation
-- rather than reinstating the field.
--
-- What a blocked acquirer does observe is **delay**, and that is CC-5.  §3.2
-- makes it a quantity and bounds it; §3.3 turns the bound into an alphabet, a
-- pacing fact and a run capacity, in the same three-part shape SM8.B.9 gave
-- CC-1, so the two accepted timing channels are costed the same way rather
-- than one being quantified and the other described.
--
-- **Read the bound's premises.**  It holds under the SM2.C `FairTrace`
-- assumption — every acquired critical section is released within `maxDelay`
-- steps — which is a property of the *runtime*, assumed by SM2.C and not
-- established anywhere in the kernel.  `lockContention_unbounded_without_fairness`
-- below is the execution that shows the premise is load-bearing rather than
-- decorative: drop fairness and the queued core is never admitted at all.

/-- SM8.D.3 (**the refutation, part 1**): writer exclusion is not observable.
A state whose object is write-held by an arbitrary core is indistinguishable
from one whose object is free, to the observer `(c, L)` on every core. -/
theorem writerExclusion_not_observable (ctx : LabelingContext) (c : CoreId) (L : SecurityLabel)
    (s : SystemState) (oid : SeLe4n.ObjId) (holder : CoreId) (hInv : s.objects.invExt) :
    ObservableState.onCore ctx c L
        (setObjectLockAt s oid { RwLockState.unheld with writerHeld := some holder })
      = ObservableState.onCore ctx c L (setObjectLockAt s oid RwLockState.unheld) :=
  onCore_lock_indistinguishable ctx c L s oid _ _ hInv

/-- SM8.D.3 (**the refutation, part 2**): and a *blocked* acquirer observes
nothing either — not even its own presence in the queue.

This is the precise sense in which the plan's row is false as written: the
observer here is the very core that is blocked (`c` appears in `waiters`), and
its view is unchanged.  Whatever a blocked reader learns from writer exclusion,
it does not learn it from the kernel state. -/
theorem blockedAcquirer_observes_nothing (ctx : LabelingContext) (c : CoreId) (L : SecurityLabel)
    (s : SystemState) (oid : SeLe4n.ObjId) (holder : CoreId) (mode : AccessMode)
    (hInv : s.objects.invExt) :
    ObservableState.onCore ctx c L
        (setObjectLockAt s oid
          { RwLockState.unheld with writerHeld := some holder, waiters := [(c, mode)] })
      = ObservableState.onCore ctx c L (setObjectLockAt s oid RwLockState.unheld) :=
  onCore_lock_indistinguishable ctx c L s oid _ _ hInv

/-- SM8.D.3 (**what the blocked reader does learn, and when**): the reader at
the head of the queue becomes a holder at the very step the writer releases.

This is the operational content the plan's row was reaching for.  The reader
learns nothing from the state while it waits (the two theorems above), and the
instant the exclusion ends it is admitted — so the *only* thing writer exclusion
communicates to it is the moment of release, which is a time and not a value.
Stated at the object level, over the SM2.C `RwLockState` the kernel stores, and
with no fairness assumption: it is a single-step fact about
`promoteWaitersOnWriterRelease`. -/
theorem blockedReader_admitted_by_writer_release (c holder : CoreId) (l : RwLockState)
    (hHead : l.waiters.head? = some (c, AccessMode.read))
    (hHeld : l.writerHeld = some holder) :
    c ∈ (l.applyOp (.releaseWrite holder)).readers :=
  SeLe4n.Kernel.Concurrency.reader_at_head_admitted_by_writer_release l c holder hHead hHeld

-- ----------------------------------------------------------------------------
-- SM8.D.3 — the delay is the observation, and the delay is bounded
-- ----------------------------------------------------------------------------

/-- SM8.D.3: **the worst-case admission delay** of a contended acquire, in
execution steps.

`queueWaitDepth` counts what must drain before the acquirer is promoted —
queue position plus current holders — and SM2.C-defer D-3.9's
`queueWaitDepth_bounded` caps it at `numCores - 1` on any well-formed state,
for a queued reader exactly as for a queued writer.  Each unit of depth costs at
most `maxDelay + 1` steps by SM2.C-defer D-3.6, so this product is the whole
wait. -/
def lockContentionDelayBound (maxDelay : Nat) : Nat := (numCores - 1) * (maxDelay + 1)

/-- SM8.D.3: **the alphabet of one contention observation** — every reachable
delay, plus one code for "not admitted within the recorded execution".

`lockContentionDelayBound maxDelay + 2`, not `+ 1`: the delays run over
`0 … bound` inclusive (that is `bound + 1` values) and code `0` is reserved for
the un-admitted case, so that an observation which carries no delay is not
confused with one that carries a delay of zero. -/
def lockContentionAlphabet (maxDelay : Nat) : Nat := lockContentionDelayBound maxDelay + 2

/-- SM8.D.3: **the observation a contending core makes** — the delay between
enqueueing on a lock at step `enqueueStep` and being admitted to it, or `none`
when the recorded execution ends first.

Keyed to `admissionStepAfter`, the admission that **follows this enqueue**, not
to `admissionStep`, which is the core's first admission in the whole execution.
The distinction is not pedantic: a core that acquires, releases and re-acquires
has its first admission *before* the second enqueue, so the `admissionStep`
difference truncates to zero in `Nat` and reports no wait for an acquisition
that genuinely waited.  `lockContentionObservation_is_own_acquisition` is the
property that rules that out.

This is CC-5 as a value.  Nothing else about the lock reaches the core: §3.1 and
§3.2 above prove the state carries no information at all, so this delay is the
channel's *entire* content. -/
def lockContentionObservation (e : SeLe4n.Kernel.Concurrency.RwLockExecution) (c : CoreId)
    (enqueueStep : Nat) : Option Nat :=
  (e.admissionStepAfter c enqueueStep).map (fun admitStep => admitStep - enqueueStep)

/-- SM8.D.3: the observation belongs to **this** acquisition — the admission it
measures from strictly follows the enqueue it is keyed to.

The load-bearing property of `admissionStepAfter` over `admissionStep`, and the
reason a repeat acquirer's second wait is reported rather than swallowed. -/
theorem lockContentionObservation_is_own_acquisition
    (e : SeLe4n.Kernel.Concurrency.RwLockExecution) (c : CoreId) (kEnq delay : Nat)
    (h : lockContentionObservation e c kEnq = some delay) :
    ∃ admitStep, e.admissionStepAfter c kEnq = some admitStep ∧
      kEnq < admitStep ∧ delay = admitStep - kEnq ∧ e.holderAt admitStep c := by
  unfold lockContentionObservation at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨admitStep, hStep, hDelay⟩ := h
  obtain ⟨hGt, hHolder⟩ := e.admissionStepAfter_characterization c kEnq admitStep hStep
  exact ⟨admitStep, hStep, hGt, hDelay.symm, hHolder⟩

/-- SM8.D.3: the observation as a single natural number, with `0` reserved for
"no admission in this execution". -/
def lockContentionCode (e : SeLe4n.Kernel.Concurrency.RwLockExecution) (c : CoreId)
    (enqueueStep : Nat) : Nat :=
  match lockContentionObservation e c enqueueStep with
  | some delay => delay + 1
  | none => 0

/-- SM8.D.3: the encoding **loses nothing** — two acquisitions the contending
core can tell apart get different codes.  This is what makes §3.3's count a
capacity bound on the channel rather than a count of an arbitrary encoding. -/
theorem lockContentionCode_injective (e₁ e₂ : SeLe4n.Kernel.Concurrency.RwLockExecution)
    (c : CoreId) (k₁ k₂ : Nat)
    (h : lockContentionCode e₁ c k₁ = lockContentionCode e₂ c k₂) :
    lockContentionObservation e₁ c k₁ = lockContentionObservation e₂ c k₂ := by
  unfold lockContentionCode at h
  cases h₁ : lockContentionObservation e₁ c k₁ <;>
    cases h₂ : lockContentionObservation e₂ c k₂ <;>
    rw [h₁, h₂] at h <;> simp_all

/-- SM8.D.3 (**the CC-5 delay bound**): a contending writer's observation is
bounded.

Under the SM2.C `FairTrace` assumption — every acquired critical section is
released within `maxDelay` steps — a writer that enqueues at step `kEnq` is
admitted, and the delay it measures is at most
`(numCores - 1) × (maxDelay + 1)`.

Both factors are the SM2.C results, composed rather than restated: the wait
depth is capped by `writerWaitDepth_bounded` (SM2.C-defer D-2.3, the *tight*
`numCores - 1` bound, not the naive `2·numCores - 1`), and each unit of depth
costs at most `maxDelay + 1` steps by `rwLock_writer_admissionStepAfter_bounded`
(SM2.C-defer D-3.8, itself derived from the D-3.6 liveness theorem rather than
from its `admissionStep` corollary — see `lockContentionObservation`).

The `hWithin` premise says the recorded execution is long enough to contain the
admission; it is the bound's own worst case, so it is exactly the hypothesis
"this execution did not end mid-wait" and not a smuggled assumption about how
long the wait was.

**Any contending mode.**  The bound holds for a queued reader on the same terms
as a queued writer: SM2.C-defer D-3.10 generalises the liveness chain — keystone
included — to an arbitrary access mode, and `queueWaitDepth_bounded` caps the
depth without ever mentioning the waiter's mode.  `blockedReaderContention_delay_bounded`
and `writerContention_delay_bounded` are the two instances. -/
theorem lockContention_delay_bounded (e : SeLe4n.Kernel.Concurrency.RwLockExecution)
    (maxDelay : Nat) (hFair : SeLe4n.Kernel.Concurrency.FairTrace e maxDelay)
    (hInit : e.initial = RwLockState.unheld) (c : CoreId) (m : AccessMode) (kEnq : Nat)
    (hQueued : (c, m) ∈ (e.stateAt kEnq).waiters)
    (hWithin : kEnq + lockContentionDelayBound maxDelay < e.ops.length) :
    ∃ delay, lockContentionObservation e c kEnq = some delay ∧
      delay ≤ lockContentionDelayBound maxDelay := by
  have hDepth : SeLe4n.Kernel.Concurrency.queueWaitDepth (e.stateAt kEnq) c m ≤ numCores - 1 :=
    SeLe4n.Kernel.Concurrency.queueWaitDepth_bounded (e.stateAt kEnq) (e.stateAt_wf kEnq) c m
      hQueued
  have hMul : SeLe4n.Kernel.Concurrency.queueWaitDepth (e.stateAt kEnq) c m * (maxDelay + 1)
      ≤ lockContentionDelayBound maxDelay :=
    Nat.mul_le_mul hDepth (Nat.le_refl _)
  have hInner : kEnq + SeLe4n.Kernel.Concurrency.queueWaitDepth (e.stateAt kEnq) c m *
      (maxDelay + 1) < e.ops.length :=
    Nat.lt_of_le_of_lt (Nat.add_le_add_left hMul kEnq) hWithin
  obtain ⟨admitStep, hStep, _, hLe⟩ :=
    SeLe4n.Kernel.Concurrency.rwLock_queued_admissionStepAfter_bounded e maxDelay hFair hInit c m
      kEnq hQueued hInner
  have hBound : admitStep ≤ kEnq + lockContentionDelayBound maxDelay :=
    Nat.le_trans hLe (Nat.add_le_add_left hMul kEnq)
  refine ⟨admitStep - kEnq, ?_, by omega⟩
  unfold lockContentionObservation
  rw [hStep]
  rfl

/-- SM8.D.3: the writer instance of the delay bound. -/
theorem writerContention_delay_bounded (e : SeLe4n.Kernel.Concurrency.RwLockExecution)
    (maxDelay : Nat) (hFair : SeLe4n.Kernel.Concurrency.FairTrace e maxDelay)
    (hInit : e.initial = RwLockState.unheld) (c : CoreId) (kEnq : Nat)
    (hQueued : (c, AccessMode.write) ∈ (e.stateAt kEnq).waiters)
    (hWithin : kEnq + lockContentionDelayBound maxDelay < e.ops.length) :
    ∃ delay, lockContentionObservation e c kEnq = some delay ∧
      delay ≤ lockContentionDelayBound maxDelay :=
  lockContention_delay_bounded e maxDelay hFair hInit c AccessMode.write kEnq hQueued hWithin

/-- SM8.D.3 (**the blocked reader's temporal bound**): a *reader* waiting behind
a writer measures a delay bounded by the same figure.

This is the half of the plan's §SM8.D.3 claim that the SM2.C surface could not
supply until D-3.10 generalised the liveness chain: the reader had a queue-position
cap (`readerContentionDepth_bounded`) and a head-of-queue admission fact
(`blockedReader_admitted_by_writer_release`), but no bound in *time*.  With this,
CC-5's alphabet figure covers every contending core rather than the writers
only, which is what an accepted-channel bandwidth claim has to do. -/
theorem blockedReaderContention_delay_bounded (e : SeLe4n.Kernel.Concurrency.RwLockExecution)
    (maxDelay : Nat) (hFair : SeLe4n.Kernel.Concurrency.FairTrace e maxDelay)
    (hInit : e.initial = RwLockState.unheld) (c : CoreId) (kEnq : Nat)
    (hQueued : (c, AccessMode.read) ∈ (e.stateAt kEnq).waiters)
    (hWithin : kEnq + lockContentionDelayBound maxDelay < e.ops.length) :
    ∃ delay, lockContentionObservation e c kEnq = some delay ∧
      delay ≤ lockContentionDelayBound maxDelay :=
  lockContention_delay_bounded e maxDelay hFair hInit c AccessMode.read kEnq hQueued hWithin

/-- SM8.D.3 (**the reader's structural bound**): at most `numCores - 1` cores
can be ahead of a blocked reader.

The mode-generic depth cap (SM2.C-defer D-3.9): the pigeonhole argument counts
distinct cores and never mentions the waiter's own access mode.  It bounds *how
much* has to drain before the reader is admitted; the per-unit cost that turns it
into a temporal figure is D-3.10's mode-generic liveness chain, so
`blockedReaderContention_delay_bounded` composes the two exactly as the writer
instance does. -/
theorem readerContentionDepth_bounded (l : RwLockState) (hWf : l.wf) (c : CoreId)
    (hQueued : (c, AccessMode.read) ∈ l.waiters) :
    SeLe4n.Kernel.Concurrency.readerWaitDepth l c ≤ numCores - 1 :=
  SeLe4n.Kernel.Concurrency.readerWaitDepth_bounded l hWf c hQueued

/-- SM8.D.3 (**the CC-5 alphabet bound**): one contention observation therefore
carries at most `log₂(lockContentionAlphabet maxDelay)` bits.

This is CC-5's counterpart of `schedulingChannel_alphabet_bounded`, and it is
what the plan's §4.2 "documented and accepted" position rests on: the channel is
not closed, but it is not unbounded either. -/
theorem lockContentionChannel_alphabet_bounded (e : SeLe4n.Kernel.Concurrency.RwLockExecution)
    (maxDelay : Nat) (hFair : SeLe4n.Kernel.Concurrency.FairTrace e maxDelay)
    (hInit : e.initial = RwLockState.unheld) (c : CoreId) (m : AccessMode) (kEnq : Nat)
    (hQueued : (c, m) ∈ (e.stateAt kEnq).waiters)
    (hWithin : kEnq + lockContentionDelayBound maxDelay < e.ops.length) :
    lockContentionCode e c kEnq < lockContentionAlphabet maxDelay := by
  obtain ⟨delay, hObs, hLe⟩ :=
    lockContention_delay_bounded e maxDelay hFair hInit c m kEnq hQueued hWithin
  unfold lockContentionCode lockContentionAlphabet
  rw [hObs]
  show delay + 1 < lockContentionDelayBound maxDelay + 2
  omega

/-- SM8.D.3: the reserved code, so the `+ 2` in the alphabet is used rather than
slack.  An acquisition the recorded execution never admits reads as `0`, which
`lockContentionCode_injective` keeps distinct from a zero-step delay. -/
theorem lockContentionCode_eq_zero_iff (e : SeLe4n.Kernel.Concurrency.RwLockExecution)
    (c : CoreId) (kEnq : Nat) :
    lockContentionCode e c kEnq = 0 ↔ e.admissionStepAfter c kEnq = none := by
  unfold lockContentionCode lockContentionObservation
  cases e.admissionStepAfter c kEnq <;> simp

/-- SM8.D.3 (**the load-bearing negative**): the bound never claims the channel
is *closed*.  Whatever the fairness parameter, the alphabet has at least two
codes, so CC-5 carries at least one bit per contended acquisition — which is
why it is registered as accepted rather than discharged. -/
theorem lockContentionAlphabet_at_least_two (maxDelay : Nat) :
    2 ≤ lockContentionAlphabet maxDelay := by
  unfold lockContentionAlphabet; omega

/-- SM8.D.3: the **core-count** factor of the bound at the shipped hardware —
four RPi5 cores, so at most three can be ahead of a contending one.

This half of the figure is grounded: `numCores` is the platform's real core
count.  The other half is not — see `lockContentionAlphabet_at_release_budget`. -/
theorem lockContentionDelayBound_rpi5_coreFactor (maxDelay : Nat) :
    lockContentionDelayBound maxDelay = 3 * (maxDelay + 1) := by
  unfold lockContentionDelayBound; rfl

/-- SM8.D.3: the alphabet at SM2.C-defer D-3.7's release-delay symbol.

**`MAX_RELEASE_DELAY` is a placeholder, not a measured deployment figure.**  Its
own docstring reads "a placeholder value of `1024` (steps); SM3 will tune this
against actual kernel critical-section budgets", so `3077` is the alphabet *that
symbol currently yields*, not a property of the shipped kernel.  The
`numCores - 1 = 3` factor is real (see above); the `maxDelay + 1 = 1025` factor
moves when SM3 tunes the budget, and `lockContentionAlphabet` is parametric in
it precisely so that the bound does not have to be restated when it does. -/
theorem lockContentionAlphabet_at_release_budget :
    lockContentionAlphabet SeLe4n.Kernel.Concurrency.MAX_RELEASE_DELAY = 3077 := by
  decide

-- ----------------------------------------------------------------------------
-- SM8.D.3 — the fairness premise is load-bearing
-- ----------------------------------------------------------------------------

/-- SM8.D.3: an execution in which core 0 takes the write lock and never
releases it, and core 1 queues behind it forever. -/
def starvingExecution : SeLe4n.Kernel.Concurrency.RwLockExecution :=
  { initial := RwLockState.unheld
    ops := [.tryAcquireWrite bootCoreId, .tryAcquireWrite ⟨1, by decide⟩]
    initial_reachable := .base }

/-- SM8.D.3: core 1 really is queued in it. -/
theorem starvingExecution_queued :
    (⟨1, by decide⟩, AccessMode.write) ∈ (starvingExecution.stateAt 2).waiters := by decide

/-- SM8.D.3 (**the premise is load-bearing**): without fairness there is no
bound at all — the queued core is never admitted, and its observation is the
reserved "no admission" code rather than any delay.

`lockContention_delay_bounded` is therefore a statement about runtimes that
satisfy the SM2.C release-delay assumption, and nothing in the kernel
establishes that assumption.  Recording it as a theorem rather than a caveat is
the point: a reader who takes the bound as unconditional is taking it wrongly,
and this execution is the counterexample. -/
theorem lockContention_unbounded_without_fairness :
    starvingExecution.admissionStepAfter ⟨1, by decide⟩ 2 = none ∧
      lockContentionObservation starvingExecution ⟨1, by decide⟩ 2 = none ∧
      lockContentionCode starvingExecution ⟨1, by decide⟩ 2 = 0 := by
  refine ⟨by decide, ?_, ?_⟩
  · unfold lockContentionObservation
    rw [show starvingExecution.admissionStepAfter ⟨1, by decide⟩ 2 = none from by decide]
    rfl
  · rw [lockContentionCode_eq_zero_iff]
    decide

/-- SM8.D.3: and the execution is genuinely unfair — the holder never releases,
so no release-delay budget makes it a `FairTrace`.  Stated at the SM2.C-defer
D-3.7 symbol; the same argument holds at every budget, since core 0 holds the
write lock at *every* step from 1 onward. -/
theorem starvingExecution_writer_never_releases (k : Nat) (hk : 1 ≤ k) :
    (starvingExecution.stateAt k).writerHeld = some bootCoreId := by
  match k, hk with
  | 1, _ => decide
  | 2, _ => decide
  | (n + 3), _ =>
    rw [starvingExecution.stateAt_of_ge_length (by simp [starvingExecution])]
    decide

-- ----------------------------------------------------------------------------
-- SM8.D.3 — from one observation to a run, with a pacing bound
-- ----------------------------------------------------------------------------

/-- SM8.D.3: the premises a whole run of contended acquisitions must satisfy for
the capacity bound to apply, bundled so the trace theorem states them once.

A run is a list of **enqueue steps within one execution** — the same shared time
base CC-1's `schedulingCapacityRun` has over a list of states.  An earlier cut
modelled it as a list of unrelated executions, which made "n observations"
correspond to no wall-clock window at all and left the count uncomparable with
CC-1's.

The access mode is existential **per step**: one core's successive contended
acquisitions need not all be writes, and after SM2.C-defer D-3.10 the delay bound
does not care which they are.

The steps are required **`Nodup`**, and that conjunct is load-bearing rather than
tidiness.  A run is a list of *distinct acquisitions*; without it a caller could
repeat one queued step arbitrarily, `enqueueSteps.length` would be unbounded, and
`lockContentionChannel_run_capacity`'s per-execution figure — the whole point of
pacing the channel — would not follow for every accepted run.  The predicate
enforces it structurally instead of leaving it to the caller's good manners. -/
def lockContentionRun (maxDelay : Nat) (e : SeLe4n.Kernel.Concurrency.RwLockExecution)
    (c : CoreId) (enqueueSteps : List Nat) : Prop :=
  SeLe4n.Kernel.Concurrency.FairTrace e maxDelay ∧
  e.initial = RwLockState.unheld ∧
  enqueueSteps.Nodup ∧
  ∀ k ∈ enqueueSteps,
    (∃ m : AccessMode, (c, m) ∈ (e.stateAt k).waiters) ∧
    k + lockContentionDelayBound maxDelay < e.ops.length

/-- SM8.D.3: the sequence of codes a contending core reads off a run. -/
def lockContentionTrace (e : SeLe4n.Kernel.Concurrency.RwLockExecution) (c : CoreId)
    (enqueueSteps : List Nat) : List Nat :=
  enqueueSteps.map (lockContentionCode e c)

/-- SM8.D.3 (**the CC-5 pacing bound**): a core cannot make more observations
than the execution has steps.

CC-1's capacity figure needs two factors — how much one observation carries and
how often one can be made — and `schedulingObservation_changes_on_domain_tick`
supplies the second for the scheduling channel.  This is CC-5's: each contended
acquisition is identified by its own enqueue step, distinct acquisitions have
distinct enqueue steps, and an execution of `n` operations has `n + 1` steps.

So the run capacity below is a bound *per execution*, not merely per
observation, which is what makes it comparable with CC-1's per-tick figure. -/
theorem lockContentionChannel_observation_rate_bounded
    (e : SeLe4n.Kernel.Concurrency.RwLockExecution) (c : CoreId) (enqueueSteps : List Nat)
    (hNodup : enqueueSteps.Nodup) (hRange : ∀ k ∈ enqueueSteps, k ≤ e.ops.length) :
    (lockContentionTrace e c enqueueSteps).length ≤ e.ops.length + 1 := by
  simp only [lockContentionTrace, List.length_map]
  exact e.distinct_steps_length_le enqueueSteps hNodup hRange

/-- SM8.D.3 (**the CC-5 capacity bound**): over a run of `n` contended
acquisitions the core's whole trace is one element of
`boundedCodeTraces (lockContentionAlphabet maxDelay) n`, a set of exactly
`lockContentionAlphabet maxDelay ^ n` elements — and by the pacing bound above,
`n` is itself bounded by the execution's length.

`lockContentionCode_injective` is what makes this a bound on the *channel*
rather than on an encoding of it: distinct codes are distinct observations, so
the count counts behaviours the contending core can actually tell apart.

Deliberately the same three-part shape as CC-1's treatment — alphabet, pacing,
trace capacity — so a reader comparing the SMP kernel's two accepted timing
channels is comparing like with like. -/
theorem lockContentionChannel_trace_capacity (maxDelay : Nat)
    (e : SeLe4n.Kernel.Concurrency.RwLockExecution) (c : CoreId) (enqueueSteps : List Nat)
    (hRun : lockContentionRun maxDelay e c enqueueSteps) :
    lockContentionTrace e c enqueueSteps
      ∈ boundedCodeTraces (lockContentionAlphabet maxDelay) enqueueSteps.length := by
  obtain ⟨hFair, hInit, _, hSteps⟩ := hRun
  refine (mem_boundedCodeTraces _ _ _).mpr ⟨by simp [lockContentionTrace], ?_⟩
  intro x hx
  simp only [lockContentionTrace, List.mem_map] at hx
  obtain ⟨k, hk, rfl⟩ := hx
  obtain ⟨⟨m, hQueued⟩, hWithin⟩ := hSteps k hk
  exact lockContentionChannel_alphabet_bounded e maxDelay hFair hInit c m k hQueued hWithin

/-- SM8.D.3 (**the composed per-execution bound**): from a run alone — no extra
hypotheses — the core's trace is one of `alphabet ^ n` **and** `n` is at most the
execution's length.

`lockContentionChannel_trace_capacity` bounds the alphabet per position and
`lockContentionChannel_observation_rate_bounded` bounds the number of positions,
but the second needs the steps to be distinct.  Before that conjunct lived in
`lockContentionRun`, this composition did not typecheck from a run alone, and the
capacity docstring's "and by the pacing bound above, `n` is itself bounded by the
execution's length" was a claim about *some* runs rather than every accepted one.
Stating it as one theorem is what keeps the two halves from drifting apart
again. -/
theorem lockContentionChannel_run_capacity (maxDelay : Nat)
    (e : SeLe4n.Kernel.Concurrency.RwLockExecution) (c : CoreId) (enqueueSteps : List Nat)
    (hRun : lockContentionRun maxDelay e c enqueueSteps) :
    lockContentionTrace e c enqueueSteps
        ∈ boundedCodeTraces (lockContentionAlphabet maxDelay) enqueueSteps.length ∧
      (lockContentionTrace e c enqueueSteps).length ≤ e.ops.length + 1 := by
  refine ⟨lockContentionChannel_trace_capacity maxDelay e c enqueueSteps hRun, ?_⟩
  obtain ⟨_, _, hNodup, hSteps⟩ := hRun
  refine lockContentionChannel_observation_rate_bounded e c enqueueSteps hNodup ?_
  intro k hk
  exact Nat.le_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_right k _) (hSteps k hk).2)

/-- SM8.D.3 (**the load-bearing negative**): a list that repeats a queued step is
**not** an accepted run, however well-behaved the execution is.

This is the shape the `Nodup` conjunct exists to exclude: repeating one
acquisition inflates `enqueueSteps.length` without the core making any further
observation, so a capacity figure computed from it would count the same
behaviour twice. -/
theorem lockContentionRun_rejects_repeated_step (maxDelay : Nat)
    (e : SeLe4n.Kernel.Concurrency.RwLockExecution) (c : CoreId) (k : Nat)
    (rest : List Nat) (hMem : k ∈ rest) :
    ¬ lockContentionRun maxDelay e c (k :: rest) := by
  rintro ⟨_, _, hNodup, _⟩
  exact (List.nodup_cons.mp hNodup).1 hMem

/-- SM8.D.3: and the count itself. -/
theorem lockContentionChannel_trace_count (maxDelay n : Nat) :
    (boundedCodeTraces (lockContentionAlphabet maxDelay) n).length
      = lockContentionAlphabet maxDelay ^ n :=
  boundedCodeTraces_length _ n

-- ----------------------------------------------------------------------------
-- SM8.D.3 — CC-5's inventory entry, now carrying a bound
-- ----------------------------------------------------------------------------

/-- SM8.D.3 (**the inventory tie-in**): CC-5 is registered `modelVisible := false`
with `severity := .medium`, and SM8.D supplies what the SM8.B entry could only
describe — the quantity behind the severity.

The three conjuncts are the entry's own literals and §3's bound, stated
together so a reclassification of CC-5 that is not matched by a change to the
bound breaks this theorem rather than passing silently.  This is the same
discipline `acceptedCovertChannel_lockContention_is_timing_only` applies to the
entry's `modelVisible` flag, extended to the figure the mitigation argument
rests on.

**Why it is a separate theorem rather than an arm of SM8.B's
`CovertChannelId.evidenceProp`** — which is the device that makes a mis-mapped
channel a *type* error rather than a stale string: that device lives in
`CovertChannelPerCore.lean`, which this module imports, so the dependency runs
the wrong way.  The equivalent protection here is `FineLockClaimId`'s
`.contentionChannelRegistered` arm, whose `evidenceProp` reads the entry's
literals off `acceptedCovertChannel_lockContention` directly. -/
theorem acceptedCovertChannel_lockContention_bounded (maxDelay : Nat)
    (e : SeLe4n.Kernel.Concurrency.RwLockExecution)
    (hFair : SeLe4n.Kernel.Concurrency.FairTrace e maxDelay)
    (hInit : e.initial = RwLockState.unheld) (c : CoreId) (m : AccessMode) (kEnq : Nat)
    (hQueued : (c, m) ∈ (e.stateAt kEnq).waiters)
    (hWithin : kEnq + lockContentionDelayBound maxDelay < e.ops.length) :
    acceptedCovertChannel_lockContention.modelVisible = false ∧
      acceptedCovertChannel_lockContention.severity = .medium ∧
      lockContentionCode e c kEnq < lockContentionAlphabet maxDelay :=
  ⟨rfl, rfl,
   lockContentionChannel_alphabet_bounded e maxDelay hFair hInit c m kEnq hQueued hWithin⟩

/-- SM8.D.3 (**what the severity is a judgement about**): CC-5's `.medium` is
not derived from the bound — a severity is an engineering judgement, and
deriving one from a number would be dressing it up.  What SM8.D supplies is the
set of quantitative facts the judgement now rests on, pinned here so that a
future re-grading is a re-reading of *these* rather than of prose:

* the per-observation alphabet is **bounded** — the channel is not unbounded;
* it is **at least two** — the channel is not closed;
* the alphabet is `(numCores - 1) × (maxDelay + 1) + 2`, so it grows with the
  core count and the critical-section budget and with nothing else;
* the channel has **one instance per core**, so a deployment's exposure scales
  with `numCores` as well.

Compare CC-1, whose `.medium` rests on an alphabet *and* a tick-paced rate; CC-5
now has both (`lockContentionChannel_observation_rate_bounded`), which is what
makes the two gradings comparable. -/
theorem acceptedCovertChannel_lockContention_severity_basis (maxDelay : Nat) :
    acceptedCovertChannel_lockContention.severity = .medium ∧
      acceptedCovertChannel_lockContention.perCoreInstance = true ∧
      2 ≤ lockContentionAlphabet maxDelay ∧
      lockContentionAlphabet maxDelay = (numCores - 1) * (maxDelay + 1) + 2 :=
  ⟨rfl, rfl, lockContentionAlphabet_at_least_two maxDelay, rfl⟩

-- ============================================================================
-- §4  SM8.D.4 — Biba integrity under per-core locks
-- ============================================================================
--
-- Integrity asks which *subjects* may modify which *objects*.  Fine-grained
-- locking makes every core a writer of every object it touches — an acquire is
-- a store into that object's `lock` field — so the question the plan's D.4 row
-- raises is real: does the 2PL bracket let an untrusted core write a trusted
-- object?
--
-- It does write it.  What §4 proves is that the write is not one an integrity
-- policy governs, and it proves it in a form that does not depend on which
-- direction the deployment's integrity order runs.  seLe4n's `integrityFlowsTo`
-- is deliberately the *reverse* of standard BIBA (U6-I: the dimension tracks
-- authority delegation, not data purity), and `bibaIntegrityFlowsTo` is the
-- standard order kept as a drop-in.  A result about only one of them would say
-- nothing about a deployment configured with the other, so §4 is stated over an
-- arbitrary write rule and instantiated at both.
--
-- Two theorems keep this from being an argument about a definition:
-- `lockWrite_carries_no_subject_data` (the value written is protocol
-- bookkeeping the writing subject cannot choose) and
-- `KernelObject.updateLock_not_identity` from §1 (the write is real).
--
-- One subtlety worth stating rather than leaving to be noticed.  The *value*
-- written into a lock word carries no subject data, but *which* lock words a
-- subject causes to be written is a function of the lock set, and the lock set
-- is a function of the syscall the subject issued.  So the choice of footprint
-- is subject-influenced.  That does not open an integrity flow, for the reason
-- §1 establishes: the words it writes are invisible, so the choice cannot be
-- read back out of the state by anyone.  What the choice *can* affect is how
-- long another core spins, and that is CC-5 — bounded in §3, and a timing
-- channel rather than an integrity violation.

/-- SM8.D.4: the standard-BIBA write rule — a subject may modify an object only
if the object's integrity is no greater than the subject's (no write-up).

The argument order is the one `securityFlowsTo` uses: a flow `src → dst`
checks `integrityFlowsTo dst.integrity src.integrity`, so a *write into* `oid`
by `subject` checks the object's integrity against the subject's. -/
def bibaWritePermitted (ctx : LabelingContext) (subject : SecurityLabel)
    (oid : SeLe4n.ObjId) : Bool :=
  bibaIntegrityFlowsTo (ctx.objectLabelOf oid).integrity subject.integrity

/-- SM8.D.4: seLe4n's own (authority-flow) write rule, in the same position —
`integrityFlowsTo`, which admits untrusted → trusted and denies trusted →
untrusted, the deliberate reversal U6-I documents. -/
def authorityWritePermitted (ctx : LabelingContext) (subject : SecurityLabel)
    (oid : SeLe4n.ObjId) : Bool :=
  integrityFlowsTo (ctx.objectLabelOf oid).integrity subject.integrity

/-- SM8.D.4: **the two rules are genuinely different**, so §4's two
instantiations are two results and not one restated.

Witness: an all-trusted object labelling with an untrusted subject.  Standard
BIBA forbids the write (no write-up); seLe4n's authority direction permits it
(authority receipt).  This is `integrityFlowsTo_is_not_biba` lifted to the write
rules the section is stated over. -/
def writeRulesWitnessContext : LabelingContext :=
  { objectLabelOf := fun _ => SecurityLabel.kernelTrusted
    threadLabelOf := fun tid =>
      if tid = (⟨0⟩ : SeLe4n.ThreadId) then SecurityLabel.kernelTrusted
      else SecurityLabel.publicLabel
    endpointLabelOf := fun _ => SecurityLabel.publicLabel
    serviceLabelOf := fun _ => SecurityLabel.publicLabel }

/-- SM8.D.4: the witness context is **not** the degenerate all-public labelling.

AK6-H's `labelNonTriviality` exists because a context that assigns one label to
everything makes every flow trivially permitted and every information-flow
witness vacuous.  This one differentiates two threads, so the disagreement below
is exhibited on a labelling a deployment could hold rather than on the one the
deployment gate rejects. -/
theorem writeRulesWitnessContext_nontrivial :
    ∃ tid₁ tid₂ : SeLe4n.ThreadId,
      writeRulesWitnessContext.threadLabelOf tid₁
        ≠ writeRulesWitnessContext.threadLabelOf tid₂ :=
  ⟨⟨0⟩, ⟨1⟩, by decide⟩

theorem writeRules_differ :
    ∃ (ctx : LabelingContext) (subject : SecurityLabel) (oid : SeLe4n.ObjId),
      bibaWritePermitted ctx subject oid ≠ authorityWritePermitted ctx subject oid :=
  ⟨writeRulesWitnessContext, SecurityLabel.publicLabel, ⟨0⟩, by decide⟩

/-- SM8.D.4: **a step performs no write the rule `permitted` forbids.**

Stated over the lock-erased content, which is what makes the whole section
work: the objects an untrusted core may not modify come out of the step with
their content intact, lock words excepted.  §1 proves those lock words reach no
observer; `lockWrite_carries_no_subject_data` below proves the writing subject
does not choose them. -/
def noUnpermittedWrite (permitted : SeLe4n.ObjId → Bool) (s s' : SystemState) : Prop :=
  ∀ oid : SeLe4n.ObjId, permitted oid = false →
    (s'.objects[oid]?).map KernelObject.eraseLock
      = (s.objects[oid]?).map KernelObject.eraseLock

theorem noUnpermittedWrite_refl (permitted : SeLe4n.ObjId → Bool) (s : SystemState) :
    noUnpermittedWrite permitted s s := fun _ _ => rfl

theorem noUnpermittedWrite_trans {permitted : SeLe4n.ObjId → Bool} {s₁ s₂ s₃ : SystemState}
    (h₁ : noUnpermittedWrite permitted s₁ s₂) (h₂ : noUnpermittedWrite permitted s₂ s₃) :
    noUnpermittedWrite permitted s₁ s₃ :=
  fun oid hDenied => (h₂ oid hDenied).trans (h₁ oid hDenied)

/-- SM8.D.4: **a lock-only step satisfies every write rule at once.**  No
hypothesis on the rule, on the subject, on the labelling, or on which objects
the lock set names. -/
theorem lockWritesOnly_noUnpermittedWrite (permitted : SeLe4n.ObjId → Bool)
    {s s' : SystemState} (h : lockWritesOnly s s') : noUnpermittedWrite permitted s s' :=
  fun oid _ => h.2 oid

/-- SM8.D.4: **the lock word is not a data channel.**

Run the same acquire against two objects whose *content* differs arbitrarily but
whose lock words agree, and the installed lock word is the same.  So nothing the
writing subject holds — no message, no capability, no field it controls — can
reach the lock word; what the acquire installs is a function of the lock's own
prior value and the `(core, mode)` request.

This is what stops §4's use of `eraseLock` from being a way of defining the
write away.  The bracket does write, really
(`KernelObject.updateLock_not_identity`); §4's claim is that what it writes is
protocol bookkeeping no integrity policy governs, and this theorem is why that
claim is about the model rather than about the abstraction chosen to state
it. -/
theorem lockWrite_carries_no_subject_data (o₁ o₂ : KernelObject) (op : RwLockOp)
    (hLock : KernelObject.objectLockOf o₁ = KernelObject.objectLockOf o₂) :
    KernelObject.objectLockOf (o₁.updateLock op)
      = KernelObject.objectLockOf (o₂.updateLock op) := by
  rw [KernelObject.objectLockOf_updateLock, KernelObject.objectLockOf_updateLock, hLock]

-- ----------------------------------------------------------------------------
-- SM8.D.4 — the bracket, under an arbitrary write rule and then at both
-- ----------------------------------------------------------------------------

/-- SM8.D.4 (**the generic result**): a 2PL bracket performs no write the rule
forbids, whenever its guarded action performs none — for *any* write rule, and
for *any* acquiring core.

The genericity is the content, not convenience: it is what makes the two
instantiations below cover a deployment configured either way round, and what
makes the result independent of the labelling entirely. -/
theorem withLockSet_noUnpermittedWrite {α : Type} (permitted : SeLe4n.ObjId → Bool)
    (S : LockSet) (core : CoreId) (action : SystemState → SystemState × α) (s : SystemState)
    (hInv : s.objects.invExt)
    (hActionInv : ∀ s', s'.objects.invExt → ((action s').1).objects.invExt)
    (hAction : ∀ s', s'.objects.invExt → noUnpermittedWrite permitted s' (action s').1) :
    noUnpermittedWrite permitted s (SeLe4n.Kernel.Concurrency.withLockSet S core action s).1 := by
  rw [SeLe4n.Kernel.Concurrency.withLockSet_fst]
  have hAcqInv := acquireAll_preserves_objects_invExt core S.lockAcquireSequence s hInv
  refine noUnpermittedWrite_trans
    (lockWritesOnly_noUnpermittedWrite permitted
      (acquireAll_lockWritesOnly core S.lockAcquireSequence s hInv))
    (noUnpermittedWrite_trans (hAction _ hAcqInv)
      (lockWritesOnly_noUnpermittedWrite permitted
        (releaseAll_lockWritesOnly core _ _ (hActionInv _ hAcqInv))))

/-- SM8.D.4 (**the headline, standard BIBA**): under per-object locks, a
subject at integrity `subject.integrity` running on **any** core writes no
object standard BIBA forbids it to write, whenever the transition it brackets
writes none.

Acquiring a lock on a trusted object from an untrusted core is therefore not a
BIBA violation: the acquire's only effect on that object is its lock word, which
no observer reads (§1) and whose value the subject does not choose
(`lockWrite_carries_no_subject_data`). -/
theorem bibaIntegrity_underLockSet {α : Type} (ctx : LabelingContext) (subject : SecurityLabel)
    (S : LockSet) (core : CoreId) (action : SystemState → SystemState × α) (s : SystemState)
    (hInv : s.objects.invExt)
    (hActionInv : ∀ s', s'.objects.invExt → ((action s').1).objects.invExt)
    (hAction : ∀ s', s'.objects.invExt →
      noUnpermittedWrite (bibaWritePermitted ctx subject) s' (action s').1) :
    noUnpermittedWrite (bibaWritePermitted ctx subject) s
      (SeLe4n.Kernel.Concurrency.withLockSet S core action s).1 :=
  withLockSet_noUnpermittedWrite _ S core action s hInv hActionInv hAction

/-- SM8.D.4 (**the headline, seLe4n's authority direction**): the same, for the
integrity order the kernel actually ships with. -/
theorem authorityIntegrity_underLockSet {α : Type} (ctx : LabelingContext)
    (subject : SecurityLabel) (S : LockSet) (core : CoreId)
    (action : SystemState → SystemState × α) (s : SystemState)
    (hInv : s.objects.invExt)
    (hActionInv : ∀ s', s'.objects.invExt → ((action s').1).objects.invExt)
    (hAction : ∀ s', s'.objects.invExt →
      noUnpermittedWrite (authorityWritePermitted ctx subject) s' (action s').1) :
    noUnpermittedWrite (authorityWritePermitted ctx subject) s
      (SeLe4n.Kernel.Concurrency.withLockSet S core action s).1 :=
  withLockSet_noUnpermittedWrite _ S core action s hInv hActionInv hAction

/-- SM8.D.4 (**"under per-core locks"**, spelled out): the acquire and release
phases satisfy both integrity rules on *every* core, with no hypothesis on the
guarded action at all — because those phases are pure lock writes.

The `∀ core` is what makes this a statement about per-core locking rather than
about one core's bracket: whichever core takes the set, and however many take
sets concurrently (`noUnpermittedWrite_trans` composes their steps), the lock
traffic itself adds no integrity-relevant write. -/
theorem lockPhases_integrity_clean_on_every_core (ctx : LabelingContext)
    (subject : SecurityLabel) (S : LockSet) (s : SystemState) (hInv : s.objects.invExt) :
    ∀ core : CoreId,
      noUnpermittedWrite (bibaWritePermitted ctx subject) s
        (SeLe4n.Kernel.Concurrency.acquireAll core S.lockAcquireSequence s) ∧
      noUnpermittedWrite (authorityWritePermitted ctx subject) s
        (SeLe4n.Kernel.Concurrency.acquireAll core S.lockAcquireSequence s) ∧
      noUnpermittedWrite (bibaWritePermitted ctx subject) s
        (SeLe4n.Kernel.Concurrency.releaseAll core S.lockAcquireSequence.reverse s) ∧
      noUnpermittedWrite (authorityWritePermitted ctx subject) s
        (SeLe4n.Kernel.Concurrency.releaseAll core S.lockAcquireSequence.reverse s) :=
  fun core =>
    ⟨lockWritesOnly_noUnpermittedWrite _ (acquireAll_lockWritesOnly core _ s hInv),
     lockWritesOnly_noUnpermittedWrite _ (acquireAll_lockWritesOnly core _ s hInv),
     lockWritesOnly_noUnpermittedWrite _ (releaseAll_lockWritesOnly core _ s hInv),
     lockWritesOnly_noUnpermittedWrite _ (releaseAll_lockWritesOnly core _ s hInv)⟩

-- ============================================================================
-- §5  SM8.D.5 — the secure-information-flow witness under fine locks
-- ============================================================================
--
-- SM3.C.9 defers wrapping the `@[export]` bodies in `withLockSet`; what it does
-- not defer is the *shape* the wrap takes, which `lockSetForSyscall` already
-- fixes: resolve the syscall's declared footprint from the pre-state, bracket
-- the entry in it, commit.  §5 states the information-flow property of exactly
-- that shape, so the migration inherits its security argument instead of
-- needing a new one.
--
-- Two things are worth reading closely.
--
-- First, `commitKernelAction`: `withLockSet` brackets a *total* state
-- transformer, and a kernel entry is a partial one, so the adapter has to say
-- what a failure commits.  It commits the pre-state — which is what the runtime
-- does, and what makes the fail-closed statement below true.
--
-- Second, the fail-closed statement itself **weakens under fine locks, and §1
-- is what makes the weaker form sufficient**.  Unbracketed, a denied syscall
-- leaves the state *identical* (`…_denied_preserves_state`).  Bracketed, it
-- cannot: the growing and shrinking phases really did write lock words.  What
-- survives is `lockWritesOnly`, and by §1 that is enough — the observer's view
-- on every core is unchanged, which is the property the fail-closed theorems
-- exist to deliver.  Recording the weakening explicitly matters: a reader who
-- assumed the literal state equality still held after SM3.C.9 would be assuming
-- something false.

/-- SM8.D.5: a `Kernel` action as the total state transformer the 2PL bracket
takes — commit the post-state on success, keep the pre-state on failure.

This is the runtime's own convention (`Platform.FFI`'s commit seam installs the
post-state only for `.ok`), lifted so the bracket and the entry compose. -/
def commitKernelAction {α : Type} (k : Kernel α) (s : SystemState) :
    SystemState × Except KernelError α :=
  match k s with
  | .ok (a, s') => (s', .ok a)
  | .error e => (s, .error e)

@[simp] theorem commitKernelAction_ok {α : Type} (k : Kernel α) (s s' : SystemState) (a : α)
    (h : k s = .ok (a, s')) : commitKernelAction k s = (s', .ok a) := by
  unfold commitKernelAction; rw [h]

@[simp] theorem commitKernelAction_error {α : Type} (k : Kernel α) (s : SystemState)
    (e : KernelError) (h : k s = .error e) : commitKernelAction k s = (s, .error e) := by
  unfold commitKernelAction; rw [h]

/-- SM8.D.5: a failing action commits its input, so it writes no lock words
either — the base case the fail-closed theorem composes. -/
theorem commitKernelAction_lockWritesOnly_of_error {α : Type} (k : Kernel α) (s : SystemState)
    (e : KernelError) (h : k s = .error e) : lockWritesOnly s (commitKernelAction k s).1 := by
  rw [commitKernelAction_error k s e h]
  exact lockWritesOnly_refl s

/-- SM8.D.5 (**the missing per-core live-entry witness**): the
information-flow-checked syscall entry preserves the observer's projection when
the operation it dispatches does.

SM8.B.12 stated this for `syscallEntry`, the boot-pinned pre-SMP entry, because
that is where the release-grade witness lived; the entry the SMP dispatch seam
actually calls is `syscallEntryChecked`, and it had none.  The three steps
before the dispatch are the same as the unchecked entry's — the context check
is state-free, the register lookup is read-only, the decode is pure — plus the
SM7.F.5 access-time TLB fill, which writes `perCoreTlb` and nothing else
(`tlbFillIpcBufferOnCore_eq_setPerCoreTlb`) and is invisible by
`perCoreTlb_write_preserves_projection`.

The dispatch hypothesis is stated against the **filled** state, because that is
the state `dispatchSyscallChecked` is applied to. -/
theorem syscallEntryChecked_preserves_projection (ctx : LabelingContext) (observer : IfObserver)
    (layout : SeLe4n.SyscallRegisterLayout) (executingCore : CoreId) (regCount : Nat)
    (st st' : SystemState)
    (hOk : syscallEntryChecked ctx layout executingCore regCount st = .ok ((), st'))
    (hDispatchProj : ∀ (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId),
        dispatchSyscallChecked ctx decoded tid
            (SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore st executingCore tid
              decoded.overflowCount) = .ok ((), st') →
        projectState ctx observer st'
          = projectState ctx observer
              (SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore st executingCore tid
                decoded.overflowCount)) :
    projectState ctx observer st' = projectState ctx observer st := by
  unfold syscallEntryChecked at hOk
  split at hOk
  · exact absurd hOk (by simp)
  · split at hOk
    · exact absurd hOk (by simp)
    · next tid _ =>
      split at hOk
      · exact absurd hOk (by simp)
      · next regsPair _ =>
        obtain ⟨regs, _⟩ := regsPair
        split at hOk
        · exact absurd hOk (by simp)
        · next decoded _ =>
          rw [hDispatchProj decoded tid hOk]
          obtain ⟨t, hEq⟩ :=
            SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore_eq_setPerCoreTlb st executingCore tid
              decoded.overflowCount
          rw [hEq]
          exact perCoreTlb_write_preserves_projection ctx observer st t

/-- SM8.D.5: the state the guarded entry is actually run in — the pre-state
after the 2PL growing phase.  Named because every §5 hypothesis is stated
against it: the entry does not see `s`, it sees this. -/
def lockSetAcquiredState (S : LockSet) (lockCore : CoreId) (s : SystemState) : SystemState :=
  SeLe4n.Kernel.Concurrency.acquireAll lockCore S.lockAcquireSequence s

/-- SM8.D.5: the object-store lock set, the one `LockSet` whose grant condition
is a single field read.  Used by the two grant lemmas below as the smallest
witness that says something about `acquireAll` rather than about one primitive. -/
private def objStoreLockSet : LockSet :=
  LockSet.singleton { kind := .objStore, objId := SeLe4n.ObjId.ofNat 0 } .write

/-- SM8.D.5 (**the acquire phase grants when the lock is free**): on a state
whose object-store lock is unheld, the growing phase really does leave the
footprint held in the acquiring core's name.

This is the half of SM3's `withLockSet` contract that is true unconditionally of
nothing — it needs the pre-state to be uncontended, and saying so is the point. -/
theorem lockSetAcquiredState_grants_when_free (s : SystemState) (lockCore : CoreId)
    (hFree : s.objStoreLock = SeLe4n.Kernel.Concurrency.RwLockState.unheld) :
    SeLe4n.Kernel.Concurrency.lockSetHeld lockCore objStoreLockSet
      (lockSetAcquiredState objStoreLockSet lockCore s) := by
  intro p hp
  unfold objStoreLockSet at hp
  rw [LockSet.singleton_pairs] at hp
  simp only [List.mem_singleton] at hp
  subst hp
  show SeLe4n.Kernel.Concurrency.lockHeld lockCore
    { kind := .objStore, objId := SeLe4n.ObjId.ofNat 0 } .write _
  unfold SeLe4n.Kernel.Concurrency.lockHeld
  simp only
  show (SeLe4n.Kernel.Concurrency.acquireAll lockCore objStoreLockSet.lockAcquireSequence
    s).objStoreLock.coreHolds lockCore .write
  unfold objStoreLockSet
  rw [LockSet.lockAcquireSequence_singleton]
  show (SeLe4n.Kernel.Concurrency.acquireLockOnObject s lockCore
    { kind := .objStore, objId := SeLe4n.ObjId.ofNat 0 } .write).objStoreLock.coreHolds
      lockCore .write
  unfold SeLe4n.Kernel.Concurrency.acquireLockOnObject
  simp only
  show (s.objStoreLock.applyOp (AccessMode.write.toAcquireOp lockCore)).coreHolds lockCore .write
  rw [hFree]
  show (SeLe4n.Kernel.Concurrency.RwLockState.unheld.applyOp
    (.tryAcquireWrite lockCore)).writerHeld = some lockCore
  rfl

/-- SM8.D.5 (**the load-bearing negative**): and it does **not** grant when the
lock is already write-held by another core — the acquirer is *queued*, and
`withLockSet` runs its action anyway.

This is the fact SM3's `withLockSet` docstring elided when it said the action
"sees a state where every lock in `S` has been acquired in the core's name".  It
is not a defect in the security argument — §5 never uses exclusion — but a
contract that is false under contention is worth stating as a theorem rather
than leaving for a reader to discover. -/
theorem lockSetAcquiredState_does_not_grant_when_contended (s : SystemState)
    (lockCore holder : CoreId) (hNe : holder ≠ lockCore)
    (hHeld : s.objStoreLock = { writerHeld := some holder, readers := [], waiters := [] }) :
    ¬ SeLe4n.Kernel.Concurrency.lockSetHeld lockCore objStoreLockSet
        (lockSetAcquiredState objStoreLockSet lockCore s) := by
  intro hAll
  have hOne := hAll ({ kind := .objStore, objId := SeLe4n.ObjId.ofNat 0 }, .write)
    (by unfold objStoreLockSet; rw [LockSet.singleton_pairs]; simp)
  unfold SeLe4n.Kernel.Concurrency.lockHeld at hOne
  simp only at hOne
  rw [show (lockSetAcquiredState objStoreLockSet lockCore s).objStoreLock
        = s.objStoreLock.applyOp (AccessMode.write.toAcquireOp lockCore) from by
      unfold lockSetAcquiredState objStoreLockSet
      rw [LockSet.lockAcquireSequence_singleton]
      rfl] at hOne
  rw [hHeld] at hOne
  -- The acquire enqueues rather than granting, so the writer is still `holder`.
  have hW : (({ writerHeld := some holder, readers := [], waiters := [] } :
      SeLe4n.Kernel.Concurrency.RwLockState).applyOp
        (AccessMode.write.toAcquireOp lockCore)).writerHeld = some lockCore := hOne
  rw [show (AccessMode.write.toAcquireOp lockCore)
        = SeLe4n.Kernel.Concurrency.RwLockOp.tryAcquireWrite lockCore from rfl] at hW
  unfold SeLe4n.Kernel.Concurrency.RwLockState.applyOp at hW
  simp only [SeLe4n.Kernel.Concurrency.RwLockState.coreInvolved, List.not_mem_nil,
    List.map_nil, false_or, or_false, Option.some.injEq, Option.isSome_some, ne_eq,
    not_true_eq_false, or_self] at hW
  rw [if_neg hNe] at hW
  exact hNe (Option.some.inj hW)

/-- SM8.D.5: **the 2PL-bracketed live syscall entry** — the shape SM3.C.9
installs at the `@[export]` bodies: take the declared footprint in the executing
core's name, run the information-flow-checked entry, release.

**What the bracket does and does not provide.**  `acquireAll` folds SM2.C's
`tryAcquire*`, which *enqueues* a core when the lock is already held rather than
granting it, and `withLockSet` runs its action regardless — a pure total state
transformer has no way to block.  So the growing phase declares a footprint and
advances the lock words; it does **not** by itself establish mutual exclusion.
`lockSetAcquiredState_grants_when_free` and its load-bearing negative
`lockSetAcquiredState_does_not_grant_when_contended` pin both directions.

The §5 results do not rest on exclusion: they are frame arguments about lock
writes being invisible, so they hold whether the acquisition granted or queued —
which is precisely why the SM3.C.9 migration is a change of concurrency control
and not of the security argument.  Live exclusion today comes from the SM5.I
global kernel-entry ticket lock, not from this bracket.

`lockCore` and `executingCore` are separate parameters on purpose.  They are
the same core on the live path (the trapping core takes the locks its own
syscall needs), but nothing in the information-flow argument requires it, and
tying them here would hide that the §5 results hold for any pairing — including
the migration's intermediate states, where a coarser bracket may be taken by
one core on behalf of a transition attributed to another. -/
def syscallEntryUnderLockSet (ctx : LabelingContext) (S : LockSet) (lockCore : CoreId)
    (layout : SeLe4n.SyscallRegisterLayout) (executingCore : CoreId) (regCount : Nat)
    (s : SystemState) : SystemState × Except KernelError Unit :=
  SeLe4n.Kernel.Concurrency.withLockSet S lockCore
    (commitKernelAction (syscallEntryChecked ctx layout executingCore regCount)) s

/-- SM8.D.5: the bracket's three phases, exposed. -/
theorem syscallEntryUnderLockSet_fst (ctx : LabelingContext) (S : LockSet) (lockCore : CoreId)
    (layout : SeLe4n.SyscallRegisterLayout) (executingCore : CoreId) (regCount : Nat)
    (s : SystemState) :
    (syscallEntryUnderLockSet ctx S lockCore layout executingCore regCount s).1
      = SeLe4n.Kernel.Concurrency.releaseAll lockCore S.lockAcquireSequence.reverse
          (commitKernelAction (syscallEntryChecked ctx layout executingCore regCount)
            (lockSetAcquiredState S lockCore s)).1 :=
  SeLe4n.Kernel.Concurrency.withLockSet_fst _ _ _ _

/-- SM8.D.5 (**the headline, at the core the entry runs on**): a 2PL-bracketed
live syscall entry is non-interfering on **every core** exactly when the
operation it dispatches is confined to the core it runs on.

The confinement core is a **parameter**, and that matters rather than being
generality for its own sake.  The boot-core form below is the instance a
whole-projection hypothesis can feed, because `projectState` *is* the boot core's
view — but an ordinary SMP syscall executes on a secondary core and writes *that*
core's scheduler slots, which makes boot-core confinement false and the boot form
vacuous for it.  Pinned there, "non-interfering on every core" would be a
conclusion about transitions the live SMP path does not take.

The bracket itself contributes nothing at any core: its growing and shrinking
phases are lock writes, invisible by §1 (`lockWritesOnly_preserves_onCore`), and
their confinement rides through by SM8.B.4's `acquireAll_confinedToCore` /
`releaseAll_confinedToCore`.  So the SM3.C.9 migration does not weaken the
information-flow guarantee — the hypotheses are exactly the ones the
*unbracketed* per-core statement takes, relocated to the state the entry is run
in. -/
theorem syscallEntryUnderLockSet_preserves_projectionOnCore_atCore (ctx : LabelingContext)
    (observer : IfObserver) (S : LockSet) (lockCore : CoreId)
    (layout : SeLe4n.SyscallRegisterLayout) (executingCore : CoreId) (regCount : Nat)
    (s st' : SystemState) (c' : CoreId) (hInv : s.objects.invExt) (hOutInv : st'.objects.invExt)
    (hOk : syscallEntryChecked ctx layout executingCore regCount
        (lockSetAcquiredState S lockCore s) = .ok ((), st'))
    (hProjOn : projectStateOnCore ctx observer st' c'
        = projectStateOnCore ctx observer (lockSetAcquiredState S lockCore s) c')
    (hConfined : observableSlotsConfinedToCore (lockSetAcquiredState S lockCore s) st' c') :
    lowEquivalent_smp ctx observer
      (syscallEntryUnderLockSet ctx S lockCore layout executingCore regCount s).1 s := by
  have hAcqInv : (lockSetAcquiredState S lockCore s).objects.invExt :=
    acquireAll_preserves_objects_invExt lockCore S.lockAcquireSequence s hInv
  have hCommit : (commitKernelAction (syscallEntryChecked ctx layout executingCore regCount)
      (lockSetAcquiredState S lockCore s)) = (st', .ok ()) :=
    commitKernelAction_ok _ _ _ _ hOk
  rw [syscallEntryUnderLockSet_fst, hCommit]
  refine lowEquivalent_smp_of_projectionOnCore_and_confinement ctx observer
    (c' := c') ?_ ?_
  · -- The release phase and the acquire phase are lock writes, so both are
    -- invisible on *every* core by §1 — which is why generalising the core costs
    -- nothing here that the boot form was not already paying.
    calc projectStateOnCore ctx observer
          (SeLe4n.Kernel.Concurrency.releaseAll lockCore S.lockAcquireSequence.reverse st') c'
        = projectStateOnCore ctx observer st' c' :=
          lockWritesOnly_preserves_projectionOnCore ctx observer c'
            (releaseAll_lockWritesOnly lockCore S.lockAcquireSequence.reverse st' hOutInv)
      _ = projectStateOnCore ctx observer (lockSetAcquiredState S lockCore s) c' := hProjOn
      _ = projectStateOnCore ctx observer s c' :=
          lockWritesOnly_preserves_projectionOnCore ctx observer c'
            (acquireAll_lockWritesOnly lockCore S.lockAcquireSequence s hInv)
  · exact observableSlotsConfinedToCore_trans
      (acquireAll_confinedToCore lockCore S.lockAcquireSequence s c')
      (observableSlotsConfinedToCore_trans hConfined
        (releaseAll_confinedToCore lockCore _ st' c'))

/-- SM8.D.5 (**the headline**): a 2PL-bracketed live syscall entry is
non-interfering on **every core** exactly when the operation it dispatches is.

The boot-core instance of `…_atCore`: `projectState` is the boot core's view, so
a whole-projection hypothesis discharges the per-core premise there and nowhere
else.  Kept as its own statement because it is the form the boot-pinned
`syscallEntryChecked_preserves_projection` feeds directly. -/
theorem syscallEntryUnderLockSet_preserves_projectionOnCore (ctx : LabelingContext)
    (observer : IfObserver) (S : LockSet) (lockCore : CoreId)
    (layout : SeLe4n.SyscallRegisterLayout) (executingCore : CoreId) (regCount : Nat)
    (s st' : SystemState) (hInv : s.objects.invExt) (hOutInv : st'.objects.invExt)
    (hOk : syscallEntryChecked ctx layout executingCore regCount
        (lockSetAcquiredState S lockCore s) = .ok ((), st'))
    (hDispatchProj : ∀ (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId),
        dispatchSyscallChecked ctx decoded tid
            (SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore
              (lockSetAcquiredState S lockCore s) executingCore tid decoded.overflowCount)
              = .ok ((), st') →
        projectState ctx observer st'
          = projectState ctx observer
              (SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore
                (lockSetAcquiredState S lockCore s) executingCore tid decoded.overflowCount))
    (hConfined : observableSlotsConfinedToCore (lockSetAcquiredState S lockCore s) st'
        bootCoreId) :
    lowEquivalent_smp ctx observer
      (syscallEntryUnderLockSet ctx S lockCore layout executingCore regCount s).1 s := by
  refine syscallEntryUnderLockSet_preserves_projectionOnCore_atCore ctx observer S lockCore
    layout executingCore regCount s st' bootCoreId hInv hOutInv hOk ?_ hConfined
  rw [projectStateOnCore_bootCore, projectStateOnCore_bootCore]
  exact syscallEntryChecked_preserves_projection ctx observer layout executingCore regCount
    _ st' hOk hDispatchProj

/-- SM8.D.5 (**fail-closed, sharpened**): a refused syscall under fine locks
moves lock words and **nothing else**.

The unbracketed fail-closed theorems (`…_denied_preserves_state`) conclude the
state is *identical*.  That claim does not survive the bracket, and saying so is
the point of this theorem rather than a caveat on it: the growing and shrinking
phases wrote real lock words (`KernelObject.updateLock_not_identity`).  What
survives is `lockWritesOnly`, and §1 is why that is the same guarantee where it
counts — see the corollary below, which is the refused syscall's
non-interference statement with no hypothesis on the observer at all. -/
theorem syscallEntryUnderLockSet_failClosed (ctx : LabelingContext) (S : LockSet)
    (lockCore : CoreId) (layout : SeLe4n.SyscallRegisterLayout) (executingCore : CoreId)
    (regCount : Nat) (s : SystemState) (e : KernelError) (hInv : s.objects.invExt)
    (hDenied : syscallEntryChecked ctx layout executingCore regCount
        (lockSetAcquiredState S lockCore s) = .error e) :
    lockWritesOnly s (syscallEntryUnderLockSet ctx S lockCore layout executingCore regCount s).1
      ∧ (syscallEntryUnderLockSet ctx S lockCore layout executingCore regCount s).2
          = .error e := by
  have hAcqInv : (lockSetAcquiredState S lockCore s).objects.invExt :=
    acquireAll_preserves_objects_invExt lockCore S.lockAcquireSequence s hInv
  have hCommit : (commitKernelAction (syscallEntryChecked ctx layout executingCore regCount)
      (lockSetAcquiredState S lockCore s)) = (lockSetAcquiredState S lockCore s, .error e) :=
    commitKernelAction_error _ _ _ hDenied
  constructor
  · rw [syscallEntryUnderLockSet_fst, hCommit]
    exact lockWritesOnly_trans (acquireAll_lockWritesOnly lockCore S.lockAcquireSequence s hInv)
      (releaseAll_lockWritesOnly lockCore _ _ hAcqInv)
  · show (SeLe4n.Kernel.Concurrency.withLockSet S lockCore _ s).2 = _
    rw [SeLe4n.Kernel.Concurrency.withLockSet_snd]
    show (commitKernelAction (syscallEntryChecked ctx layout executingCore regCount)
      (lockSetAcquiredState S lockCore s)).2 = _
    rw [hCommit]

/-- SM8.D.5: and therefore a refused syscall is invisible to every observer on
every core — the guarantee the literal state equality was standing in for,
recovered from the weaker `lockWritesOnly` conclusion with no extra
hypothesis. -/
theorem syscallEntryUnderLockSet_failClosed_invisible (ctx : LabelingContext) (S : LockSet)
    (lockCore : CoreId) (layout : SeLe4n.SyscallRegisterLayout) (executingCore : CoreId)
    (regCount : Nat) (s : SystemState) (e : KernelError) (L : SecurityLabel)
    (hInv : s.objects.invExt)
    (hDenied : syscallEntryChecked ctx layout executingCore regCount
        (lockSetAcquiredState S lockCore s) = .error e) :
    ∀ c : CoreId,
      ObservableState.onCore ctx c L
          (syscallEntryUnderLockSet ctx S lockCore layout executingCore regCount s).1
        = ObservableState.onCore ctx c L s :=
  fun c => lockWritesOnly_preserves_onCore ctx c L
    (syscallEntryUnderLockSet_failClosed ctx S lockCore layout executingCore regCount s e
      hInv hDenied).1

/-- SM8.D.5 (**the witness**): *secure information flow under fine locks*, as
one statement.

For a 2PL-bracketed live syscall entry, on any pairing of lock-holding and
executing cores, and for a subject at any integrity:

1. **confidentiality** — the observer `(c, L)` sees the same state before and
   after, on **every** core;
2. **integrity, standard BIBA** — no object the subject may not write comes out
   with different content;
3. **integrity, seLe4n's authority direction** — likewise under the order the
   kernel ships with;
4. **the bracket's own contribution is nil** — the acquire and release phases
   add no write to (2) or (3) and no observation to (1), which is what
   `withLockSet_noUnpermittedWrite` and §1 supply.

Every hypothesis is a property of the *guarded entry at the state it is run
in*.  There is no hypothesis about the lock set — not about which objects it
names, not about whether those objects are observable, not about contention —
and that absence is the result: fine-grained locking is information-flow
transparent, so SM3.C.9's migration is a change of concurrency control and not
of the security argument. -/
theorem secureInformationFlow_underFineLocks (ctx : LabelingContext) (L : SecurityLabel)
    (subject : SecurityLabel) (S : LockSet) (lockCore : CoreId)
    (layout : SeLe4n.SyscallRegisterLayout) (executingCore : CoreId) (regCount : Nat)
    (s st' : SystemState) (hInv : s.objects.invExt) (hOutInv : st'.objects.invExt)
    (hOk : syscallEntryChecked ctx layout executingCore regCount
        (lockSetAcquiredState S lockCore s) = .ok ((), st'))
    (hDispatchProj : ∀ (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId),
        dispatchSyscallChecked ctx decoded tid
            (SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore
              (lockSetAcquiredState S lockCore s) executingCore tid decoded.overflowCount)
              = .ok ((), st') →
        projectState ctx (IfObserver.ofLabel L) st'
          = projectState ctx (IfObserver.ofLabel L)
              (SeLe4n.Kernel.Architecture.tlbFillIpcBufferOnCore
                (lockSetAcquiredState S lockCore s) executingCore tid decoded.overflowCount))
    (hConfined : observableSlotsConfinedToCore (lockSetAcquiredState S lockCore s) st'
        bootCoreId)
    (hBiba : noUnpermittedWrite (bibaWritePermitted ctx subject)
        (lockSetAcquiredState S lockCore s) st')
    (hAuthority : noUnpermittedWrite (authorityWritePermitted ctx subject)
        (lockSetAcquiredState S lockCore s) st') :
    (∀ c : CoreId,
        ObservableState.onCore ctx c L
            (syscallEntryUnderLockSet ctx S lockCore layout executingCore regCount s).1
          = ObservableState.onCore ctx c L s) ∧
      noUnpermittedWrite (bibaWritePermitted ctx subject) s
        (syscallEntryUnderLockSet ctx S lockCore layout executingCore regCount s).1 ∧
      noUnpermittedWrite (authorityWritePermitted ctx subject) s
        (syscallEntryUnderLockSet ctx S lockCore layout executingCore regCount s).1 := by
  have hAcqInv : (lockSetAcquiredState S lockCore s).objects.invExt :=
    acquireAll_preserves_objects_invExt lockCore S.lockAcquireSequence s hInv
  have hCommit : (commitKernelAction (syscallEntryChecked ctx layout executingCore regCount)
      (lockSetAcquiredState S lockCore s)) = (st', .ok ()) :=
    commitKernelAction_ok _ _ _ _ hOk
  refine ⟨syscallEntryUnderLockSet_preserves_projectionOnCore ctx (IfObserver.ofLabel L) S
    lockCore layout executingCore regCount s st' hInv hOutInv hOk hDispatchProj hConfined, ?_, ?_⟩
  <;> rw [syscallEntryUnderLockSet_fst, hCommit]
  · exact noUnpermittedWrite_trans
      (lockWritesOnly_noUnpermittedWrite _
        (acquireAll_lockWritesOnly lockCore S.lockAcquireSequence s hInv))
      (noUnpermittedWrite_trans hBiba
        (lockWritesOnly_noUnpermittedWrite _
          (releaseAll_lockWritesOnly lockCore _ st' hOutInv)))
  · exact noUnpermittedWrite_trans
      (lockWritesOnly_noUnpermittedWrite _
        (acquireAll_lockWritesOnly lockCore S.lockAcquireSequence s hInv))
      (noUnpermittedWrite_trans hAuthority
        (lockWritesOnly_noUnpermittedWrite _
          (releaseAll_lockWritesOnly lockCore _ st' hOutInv)))

/-- SM8.D.5: the headline with the projection hypothesis stated at the **entry**
rather than at the dispatch — the form a caller in possession of a whole-entry
witness reaches for, and the one §6's evidence table is stated over.

Strictly the same result: `syscallEntryChecked_preserves_projection` is what
turns the dispatch-level hypothesis into this one, so having both is not
redundancy but the two places a caller's evidence can come from. -/
theorem syscallEntryUnderLockSet_preserves_projectionOnCore_of_entry (ctx : LabelingContext)
    (observer : IfObserver) (S : LockSet) (lockCore : CoreId)
    (layout : SeLe4n.SyscallRegisterLayout) (executingCore : CoreId) (regCount : Nat)
    (s st' : SystemState) (hInv : s.objects.invExt) (hOutInv : st'.objects.invExt)
    (hOk : syscallEntryChecked ctx layout executingCore regCount
        (lockSetAcquiredState S lockCore s) = .ok ((), st'))
    (hProj : projectState ctx observer st'
        = projectState ctx observer (lockSetAcquiredState S lockCore s))
    (hConfined : observableSlotsConfinedToCore (lockSetAcquiredState S lockCore s) st'
        bootCoreId) :
    lowEquivalent_smp ctx observer
      (syscallEntryUnderLockSet ctx S lockCore layout executingCore regCount s).1 s := by
  have hCommit : (commitKernelAction (syscallEntryChecked ctx layout executingCore regCount)
      (lockSetAcquiredState S lockCore s)) = (st', .ok ()) :=
    commitKernelAction_ok _ _ _ _ hOk
  rw [syscallEntryUnderLockSet_fst, hCommit]
  refine lowEquivalent_smp_of_projection_and_confinement ctx observer ?_ ?_
  · calc projectState ctx observer
          (SeLe4n.Kernel.Concurrency.releaseAll lockCore S.lockAcquireSequence.reverse st')
        = projectState ctx observer st' :=
          releaseAll_preserves_projection ctx observer lockCore _ st' hOutInv
      _ = projectState ctx observer (lockSetAcquiredState S lockCore s) := hProj
      _ = projectState ctx observer s :=
          acquireAll_preserves_projection ctx observer lockCore S.lockAcquireSequence s hInv
  · exact observableSlotsConfinedToCore_trans
      (acquireAll_confinedToCore lockCore S.lockAcquireSequence s bootCoreId)
      (observableSlotsConfinedToCore_trans hConfined
        (releaseAll_confinedToCore lockCore _ st' bootCoreId))

-- ----------------------------------------------------------------------------
-- SM8.D.5 — at the one footprint SM3.C.9 has declared
-- ----------------------------------------------------------------------------
--
-- `lockSetForSyscall` is the SM3.C.9 seam: it resolves a syscall's declared
-- per-object footprint from the pre-state, and returns `none` where one has not
-- been established.  `.tcbSuspend` is the single declared arm today
-- (`lockSetForSyscall_undeclared_none` is the negative that keeps that honest),
-- so it is the one place the bracket §5 reasons about can be assembled from the
-- resolver rather than from an arbitrary `LockSet`.
--
-- The entry below is `Option`-valued **because the resolver is**: an undeclared
-- syscall has no footprint to bracket, and the caller must fall back to whatever
-- coarser serialisation it already has (today the SM5.I global kernel-entry
-- lock).  Returning a "best effort" set instead would be the one shape this must
-- not take — a declared lock set that does not cover a write is a *false*
-- footprint, and the 2PL argument would then rest on exclusion the runtime never
-- established.

/-- SM8.D.5: the caller and decode a bracketed entry will actually run.

This replays exactly the prefix `syscallEntryChecked` runs before it dispatches —
reject the insecure default context, read the current thread **of the executing
core**, read that thread's registers, decode them against the layout — and
returns `none` wherever the entry itself would fail.  It exists so the declared
footprint can be resolved from the *same* decode the entry executes, rather than
from arguments a caller supplies alongside it. -/
def entryDecode (ctx : LabelingContext) (layout : SeLe4n.SyscallRegisterLayout)
    (executingCore : CoreId) (regCount : Nat) (s : SystemState) :
    Option (SeLe4n.ThreadId × SyscallDecodeResult) :=
  if isInsecureDefaultContext ctx then none
  else
    match s.scheduler.currentOnCore executingCore with
    | none => none
    | some tid =>
      match lookupThreadRegisterContext tid s with
      | .error _ => none
      | .ok (regs, _) =>
        match SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState
                s tid layout regs regCount with
        | .error _ => none
        | .ok decoded => some (tid, decoded)

/-- SM8.D.5 (**the anti-drift tie**): where the replayed prefix gives up, the
real entry errors.

`entryDecode` duplicates `syscallEntryChecked`'s prefix, and a duplicated
computation is a drift risk unless something checks it against the original.
This is that check on the failing side: every `none` the helper returns is a
state on which the entry refuses, so a footprint is never resolved for an entry
that will not run. -/
theorem entryDecode_none_entry_error (ctx : LabelingContext)
    (layout : SeLe4n.SyscallRegisterLayout) (executingCore : CoreId) (regCount : Nat)
    (s : SystemState) (h : entryDecode ctx layout executingCore regCount s = none) :
    ∃ e, syscallEntryChecked ctx layout executingCore regCount s = .error e := by
  unfold entryDecode at h
  unfold syscallEntryChecked
  cases hIns : isInsecureDefaultContext ctx with
  | true => exact ⟨.policyDenied, by simp⟩
  | false =>
    rw [hIns] at h
    simp only [Bool.false_eq_true, if_false] at h
    cases hCur : s.scheduler.currentOnCore executingCore with
    | none => exact ⟨.illegalState, by simp⟩
    | some tid =>
      rw [hCur] at h
      simp only at h
      cases hRegs : lookupThreadRegisterContext tid s with
      | error e => exact ⟨e, by simp [hRegs]⟩
      | ok regsPair =>
        obtain ⟨regs, stAfter⟩ := regsPair
        rw [hRegs] at h
        simp only at h
        cases hDec : SeLe4n.Kernel.Architecture.RegisterDecode.decodeSyscallArgsFromState
            s tid layout regs regCount with
        | error e => exact ⟨e, by simp [hRegs, hDec]⟩
        | ok decoded =>
          rw [hDec] at h
          exact absurd h (by simp)

/-- SM8.D.5: the target a capability-addressed syscall names, read the way the
live `dispatchWithCapChecked` arms read it.

Fail-closed: a capability that does not name an object has no thread target, so
no footprint is declared for it. -/
def entryCapTarget (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId) (s : SystemState) :
    Option SeLe4n.ThreadId :=
  match s.getTcb? tid with
  | none => none
  | some tcb =>
    match s.getCNode? tcb.cspaceRoot with
    | none => none
    | some rootCn =>
      match syscallLookupCap { callerId := tid, cspaceRoot := tcb.cspaceRoot,
                               capAddr := decoded.capAddr, capDepth := rootCn.depth,
                               requiredRight := syscallRequiredRight decoded.syscallId } s with
      | .error _ => none
      | .ok (cap, _) =>
        match cap.target with
        | .object objId => some (SeLe4n.ThreadId.ofNat objId.toNat)
        | _ => none

/-- SM8.D.5: SM3.C.9's declared footprint **for the operation the entry will
actually execute**.

Every input `lockSetForSyscall` takes is derived here from the entry's own
resolution rather than supplied alongside it: the syscall id from the register
decode, the caller from the executing core's current thread, the target from the
capability that decode addresses.  An earlier cut took all three as free
parameters, which let a caller bracket `.tcbSuspend`'s footprint around whatever
the registers happened to decode to — a *false* footprint of exactly the kind the
section note above says must never be assembled, since the 2PL argument would
then rest on coverage nobody established. -/
def declaredLockSetForEntry (ctx : LabelingContext) (layout : SeLe4n.SyscallRegisterLayout)
    (executingCore : CoreId) (regCount : Nat) (s : SystemState) : Option LockSet :=
  match entryDecode ctx layout executingCore regCount s with
  | none => none
  | some (tid, decoded) =>
    match entryCapTarget decoded tid s with
    | none => none
    | some targetTid =>
      SeLe4n.Kernel.Concurrency.lockSetForSyscall decoded.syscallId tid targetTid s

/-- SM8.D.5 (**the binding, as a theorem**): a resolved footprint is
`lockSetForSyscall`'s output at the **decoded** syscall id, the **executing
core's** caller, and the target that caller's capability names.

This is the property whose absence let the free-parameter form bracket an
unrelated operation.  It is stated rather than left to the reader of the
definition, so a future cut that reintroduces an independent argument has to
break a proof to do it. -/
theorem declaredLockSetForEntry_binds_decode (ctx : LabelingContext)
    (layout : SeLe4n.SyscallRegisterLayout) (executingCore : CoreId) (regCount : Nat)
    (s : SystemState) (S : LockSet)
    (h : declaredLockSetForEntry ctx layout executingCore regCount s = some S) :
    ∃ tid decoded targetTid,
      entryDecode ctx layout executingCore regCount s = some (tid, decoded) ∧
      entryCapTarget decoded tid s = some targetTid ∧
      SeLe4n.Kernel.Concurrency.lockSetForSyscall decoded.syscallId tid targetTid s = some S := by
  unfold declaredLockSetForEntry at h
  cases hDec : entryDecode ctx layout executingCore regCount s with
  | none => rw [hDec] at h; exact absurd h (by simp)
  | some pair =>
    obtain ⟨tid, decoded⟩ := pair
    rw [hDec] at h
    simp only at h
    cases hTgt : entryCapTarget decoded tid s with
    | none => rw [hTgt] at h; exact absurd h (by simp)
    | some targetTid =>
      rw [hTgt] at h
      simp only at h
      exact ⟨tid, decoded, targetTid, rfl, hTgt, h⟩

/-- SM8.D.5 (**fail-closed**): a footprint is declared only where the **decoded**
syscall is `.tcbSuspend`.

The undeclared property, restated over the operation the entry runs.  Under the
free-parameter form this could only be said about the caller's `sid` argument,
which is not what gets executed. -/
theorem declaredLockSetForEntry_undeclared (ctx : LabelingContext)
    (layout : SeLe4n.SyscallRegisterLayout) (executingCore : CoreId) (regCount : Nat)
    (s : SystemState) (tid : SeLe4n.ThreadId) (decoded : SyscallDecodeResult)
    (hDec : entryDecode ctx layout executingCore regCount s = some (tid, decoded))
    (hSid : decoded.syscallId ≠ .tcbSuspend) :
    declaredLockSetForEntry ctx layout executingCore regCount s = none := by
  unfold declaredLockSetForEntry
  rw [hDec]
  simp only
  cases hTgt : entryCapTarget decoded tid s with
  | none => rfl
  | some targetTid =>
    exact SeLe4n.Kernel.Concurrency.lockSetForSyscall_undeclared_none decoded.syscallId tid
      targetTid s hSid

/-- SM8.D.5: the 2PL-bracketed live entry **over the declared footprint** —
`declaredLockSetForEntry`'s output, bracketed, or `none` where no footprint is
declared for the operation the entry will run. -/
def syscallEntryUnderDeclaredLockSet (ctx : LabelingContext) (lockCore : CoreId)
    (layout : SeLe4n.SyscallRegisterLayout) (executingCore : CoreId) (regCount : Nat)
    (s : SystemState) : Option (SystemState × Except KernelError Unit) :=
  (declaredLockSetForEntry ctx layout executingCore regCount s).map
    (fun S => syscallEntryUnderLockSet ctx S lockCore layout executingCore regCount s)

/-- SM8.D.5 (**fail-closed**): every syscall other than `.tcbSuspend` is
undeclared, so no footprint is bracketed and the caller keeps its existing
serialisation.  This is `declaredLockSetForEntry_undeclared` lifted to the
bracketed entry — the property that stops a future cut from silently bracketing
an operation whose coverage proof does not exist yet. -/
theorem syscallEntryUnderDeclaredLockSet_undeclared (ctx : LabelingContext) (lockCore : CoreId)
    (layout : SeLe4n.SyscallRegisterLayout) (executingCore : CoreId) (regCount : Nat)
    (s : SystemState) (tid : SeLe4n.ThreadId) (decoded : SyscallDecodeResult)
    (hDec : entryDecode ctx layout executingCore regCount s = some (tid, decoded))
    (hSid : decoded.syscallId ≠ .tcbSuspend) :
    syscallEntryUnderDeclaredLockSet ctx lockCore layout executingCore regCount s = none := by
  unfold syscallEntryUnderDeclaredLockSet
  rw [declaredLockSetForEntry_undeclared ctx layout executingCore regCount s tid decoded hDec hSid]
  rfl

/-- SM8.D.5: and nothing is bracketed where the entry itself would refuse —
the bracket never runs ahead of a decode that does not exist. -/
theorem syscallEntryUnderDeclaredLockSet_no_decode (ctx : LabelingContext) (lockCore : CoreId)
    (layout : SeLe4n.SyscallRegisterLayout) (executingCore : CoreId) (regCount : Nat)
    (s : SystemState) (h : entryDecode ctx layout executingCore regCount s = none) :
    syscallEntryUnderDeclaredLockSet ctx lockCore layout executingCore regCount s = none := by
  unfold syscallEntryUnderDeclaredLockSet declaredLockSetForEntry
  rw [h]
  rfl

/-- SM8.D.5 (**the headline at the declared footprint**): when SM3.C.9's
resolver yields a footprint for `.tcbSuspend`, the entry bracketed in **that**
footprint is non-interfering on every core.

The resolution hypothesis is *consumed*, not decorative: it is what turns the
`Option` the resolver returns into the `some` the conclusion names.  An earlier
cut stated this over an arbitrary `LockSet` with the resolver equation hanging
off it unused, which asserted nothing about the footprint the migration will
actually install. -/
theorem suspendUnderDeclaredLockSet_preserves_projectionOnCore (ctx : LabelingContext)
    (observer : IfObserver) (S : LockSet) (lockCore : CoreId)
    (layout : SeLe4n.SyscallRegisterLayout) (executingCore : CoreId)
    (regCount : Nat) (s st' : SystemState) (hInv : s.objects.invExt)
    (hOutInv : st'.objects.invExt)
    (hFootprint : declaredLockSetForEntry ctx layout executingCore regCount s = some S)
    (hOk : syscallEntryChecked ctx layout executingCore regCount
        (lockSetAcquiredState S lockCore s) = .ok ((), st'))
    (hProj : projectState ctx observer st'
        = projectState ctx observer (lockSetAcquiredState S lockCore s))
    (hConfined : observableSlotsConfinedToCore (lockSetAcquiredState S lockCore s) st'
        bootCoreId) :
    ∃ r, syscallEntryUnderDeclaredLockSet ctx lockCore layout executingCore regCount s = some r ∧
      lowEquivalent_smp ctx observer r.1 s := by
  refine ⟨syscallEntryUnderLockSet ctx S lockCore layout executingCore regCount s, ?_, ?_⟩
  · unfold syscallEntryUnderDeclaredLockSet
    rw [hFootprint]
    rfl
  · exact syscallEntryUnderLockSet_preserves_projectionOnCore_of_entry ctx observer S lockCore
      layout executingCore regCount s st' hInv hOutInv hOk hProj hConfined

/-- SM8.D.5: the fail-closed half at the declared footprint — a refused suspend
moves lock words and nothing else, and is invisible on every core. -/
theorem suspendUnderDeclaredLockSet_failClosed_invisible (ctx : LabelingContext) (S : LockSet)
    (lockCore : CoreId)
    (layout : SeLe4n.SyscallRegisterLayout) (executingCore : CoreId) (regCount : Nat)
    (s : SystemState) (e : KernelError) (L : SecurityLabel) (hInv : s.objects.invExt)
    (hFootprint : declaredLockSetForEntry ctx layout executingCore regCount s = some S)
    (hDenied : syscallEntryChecked ctx layout executingCore regCount
        (lockSetAcquiredState S lockCore s) = .error e) :
    ∃ r, syscallEntryUnderDeclaredLockSet ctx lockCore layout executingCore regCount s = some r ∧
      lockWritesOnly s r.1 ∧
      ∀ c : CoreId, ObservableState.onCore ctx c L r.1 = ObservableState.onCore ctx c L s := by
  refine ⟨syscallEntryUnderLockSet ctx S lockCore layout executingCore regCount s, ?_, ?_, ?_⟩
  · unfold syscallEntryUnderDeclaredLockSet
    rw [hFootprint]
    rfl
  · exact (syscallEntryUnderLockSet_failClosed ctx S lockCore layout executingCore regCount s e
      hInv hDenied).1
  · exact syscallEntryUnderLockSet_failClosed_invisible ctx S lockCore layout executingCore
      regCount s e L hInv hDenied

/-- SM8.D.5 (**the resolved footprint is the suspend footprint**): a declared
footprint resolves only through `suspendFootprintOf`, at the caller and target the
entry's own decode names.

`declaredLockSetForEntry_binds_decode` says the inputs come from the decode;
this says what the output then is, so the two together pin the whole resolution
rather than only its shape. -/
theorem declaredLockSetForEntry_is_suspend_footprint (ctx : LabelingContext)
    (layout : SeLe4n.SyscallRegisterLayout) (executingCore : CoreId) (regCount : Nat)
    (s : SystemState) (S : LockSet)
    (h : declaredLockSetForEntry ctx layout executingCore regCount s = some S) :
    ∃ tid decoded targetTid,
      entryDecode ctx layout executingCore regCount s = some (tid, decoded) ∧
      decoded.syscallId = .tcbSuspend ∧
      entryCapTarget decoded tid s = some targetTid ∧
      SeLe4n.Kernel.Concurrency.suspendFootprintOf s tid targetTid = some S := by
  obtain ⟨tid, decoded, targetTid, hDec, hTgt, hLock⟩ :=
    declaredLockSetForEntry_binds_decode ctx layout executingCore regCount s S h
  by_cases hSid : decoded.syscallId = .tcbSuspend
  · refine ⟨tid, decoded, targetTid, hDec, hSid, hTgt, ?_⟩
    rw [hSid, SeLe4n.Kernel.Concurrency.lockSetForSyscall_tcbSuspend] at hLock
    exact hLock
  · exact absurd hLock (by
      rw [SeLe4n.Kernel.Concurrency.lockSetForSyscall_undeclared_none decoded.syscallId tid
        targetTid s hSid]
      simp)

-- ============================================================================
-- §6  SM8.D — the phase's claims as data, each carrying its own proof
-- ============================================================================
--
-- The same device SM8.B gave the covert-channel inventory and SM8.C gave the
-- cross-core declassification rules: the sub-tasks are a finite enum, the claim
-- each one makes is a `Prop` computed from the id, and the evidence is a
-- dependently-typed function that must *inhabit* that `Prop`.  A claim whose
-- theorem is renamed fails to elaborate; a claim mapped to the wrong theorem
-- fails to typecheck; a sub-task added without evidence leaves the match
-- non-exhaustive.

/-- SM8.D: the phase's claims.  Six ids for five sub-tasks — D.3 and D.5 each
make two: D.3 refutes the model-level reading *and* bounds the timing one that
replaces it, and D.5 covers the successful path *and* the refused one.  SM8.D.6
is the scenario suite and carries no Lean claim. -/
inductive FineLockClaimId where
  /-- SM8.D.1 — an observer sees nothing of a lock word. -/
  | lockStateInvisible
  /-- SM8.D.2 — reader multiplicity is not directly observable. -/
  | readerMultiplicityHidden
  /-- SM8.D.3 — writer exclusion is not observable to a blocked acquirer either. -/
  | writerExclusionHidden
  /-- SM8.D.3 — what the blocked acquirer *does* observe is bounded. -/
  | contentionDelayBounded
  /-- SM8.D.4 — the 2PL bracket makes no integrity-forbidden write. -/
  | integrityUnderLocks
  /-- SM8.D.5 — a bracketed live entry is non-interfering when its dispatch is. -/
  | secureFlowUnderFineLocks
  /-- SM8.D.5 — and a refused one is invisible outright. -/
  | failClosedUnderFineLocks
  /-- SM8.D.3 — CC-5's inventory entry is backed by the bound, not by prose. -/
  | contentionChannelRegistered
  deriving DecidableEq, Repr

def FineLockClaimId.all : List FineLockClaimId :=
  [ .lockStateInvisible, .readerMultiplicityHidden, .writerExclusionHidden
  , .contentionDelayBounded, .integrityUnderLocks, .secureFlowUnderFineLocks
  , .failClosedUnderFineLocks, .contentionChannelRegistered ]

theorem FineLockClaimId.mem_all (id : FineLockClaimId) : id ∈ FineLockClaimId.all := by
  cases id <;> decide

theorem FineLockClaimId.all_nodup : FineLockClaimId.all.Nodup := by decide

theorem fineLockClaims_count : FineLockClaimId.all.length = 8 := by rfl

/-- SM8.D: the plan sub-task each claim discharges. -/
def FineLockClaimId.subTask : FineLockClaimId → String
  | .lockStateInvisible => "SM8.D.1"
  | .readerMultiplicityHidden => "SM8.D.2"
  | .writerExclusionHidden => "SM8.D.3"
  | .contentionDelayBounded => "SM8.D.3"
  | .integrityUnderLocks => "SM8.D.4"
  | .secureFlowUnderFineLocks => "SM8.D.5"
  | .failClosedUnderFineLocks => "SM8.D.5"
  | .contentionChannelRegistered => "SM8.D.3"

/-- SM8.D: **every proof-carrying sub-task of the phase is claimed.**  D.6 is
the scenario suite (`tests/SmpInformationFlowSuite.lean` §7), which is a Tier-2
runner rather than a theorem, so it is deliberately absent. -/
theorem fineLockClaims_cover_subTasks :
    FineLockClaimId.all.map FineLockClaimId.subTask
      = ["SM8.D.1", "SM8.D.2", "SM8.D.3", "SM8.D.3", "SM8.D.4", "SM8.D.5", "SM8.D.5",
         "SM8.D.3"] := by
  rfl

/-- SM8.D: the name of the theorem that discharges each claim, compile-time
validated through `niName!` so a rename is a build failure. -/
def fineLockClaimTheorem : FineLockClaimId → String
  | .lockStateInvisible => niName! onCore_lock_indistinguishable
  | .readerMultiplicityHidden => niName! readerMultiplicity_not_observable
  | .writerExclusionHidden => niName! blockedAcquirer_observes_nothing
  | .contentionDelayBounded => niName! lockContention_delay_bounded
  | .integrityUnderLocks => niName! bibaIntegrity_underLockSet
  | .secureFlowUnderFineLocks => niName! syscallEntryUnderLockSet_preserves_projectionOnCore_of_entry
  | .failClosedUnderFineLocks => niName! syscallEntryUnderLockSet_failClosed_invisible
  | .contentionChannelRegistered => niName! acceptedCovertChannel_lockContention_bounded

theorem fineLockClaimTheorem_nodup :
    (FineLockClaimId.all.map fineLockClaimTheorem).Nodup := by decide

/-- SM8.D: **the property each claim must establish.**

Stated as a computed `Prop` rather than as a string, for the reason SM8.B's
`CovertChannelId.evidenceProp` gives: a name-validated table checks only that
the name resolves, so mapping a claim at the *wrong* theorem passes it.  Here
each arm is the conclusion of the theorem `fineLockClaimTheorem` names, so
supplying a different one is a type error. -/
def FineLockClaimId.evidenceProp : FineLockClaimId → Prop
  | .lockStateInvisible =>
      ∀ (ctx : LabelingContext) (c : CoreId) (L : SecurityLabel) (s : SystemState)
        (oid : SeLe4n.ObjId) (l₁ l₂ : RwLockState), s.objects.invExt →
        ObservableState.onCore ctx c L (setObjectLockAt s oid l₁)
          = ObservableState.onCore ctx c L (setObjectLockAt s oid l₂)
  | .readerMultiplicityHidden =>
      ∀ (ctx : LabelingContext) (c : CoreId) (L : SecurityLabel) (s : SystemState)
        (oid : SeLe4n.ObjId) (readers₁ readers₂ : List CoreId), s.objects.invExt →
        ObservableState.onCore ctx c L
            (setObjectLockAt s oid { RwLockState.unheld with readers := readers₁ })
          = ObservableState.onCore ctx c L
            (setObjectLockAt s oid { RwLockState.unheld with readers := readers₂ })
  | .writerExclusionHidden =>
      ∀ (ctx : LabelingContext) (c : CoreId) (L : SecurityLabel) (s : SystemState)
        (oid : SeLe4n.ObjId) (holder : CoreId) (mode : AccessMode), s.objects.invExt →
        ObservableState.onCore ctx c L
            (setObjectLockAt s oid
              { RwLockState.unheld with writerHeld := some holder, waiters := [(c, mode)] })
          = ObservableState.onCore ctx c L (setObjectLockAt s oid RwLockState.unheld)
  | .contentionDelayBounded =>
      ∀ (e : SeLe4n.Kernel.Concurrency.RwLockExecution) (maxDelay : Nat),
        SeLe4n.Kernel.Concurrency.FairTrace e maxDelay →
        e.initial = RwLockState.unheld →
        ∀ (c : CoreId) (m : AccessMode) (kEnq : Nat),
          (c, m) ∈ (e.stateAt kEnq).waiters →
          kEnq + lockContentionDelayBound maxDelay < e.ops.length →
          ∃ delay, lockContentionObservation e c kEnq = some delay ∧
            delay ≤ lockContentionDelayBound maxDelay
  | .integrityUnderLocks =>
      ∀ (α : Type) (ctx : LabelingContext) (subject : SecurityLabel) (S : LockSet) (core : CoreId)
        (action : SystemState → SystemState × α) (s : SystemState), s.objects.invExt →
        (∀ s', s'.objects.invExt → ((action s').1).objects.invExt) →
        (∀ s', s'.objects.invExt →
          noUnpermittedWrite (bibaWritePermitted ctx subject) s' (action s').1) →
        noUnpermittedWrite (bibaWritePermitted ctx subject) s
          (SeLe4n.Kernel.Concurrency.withLockSet S core action s).1
  | .secureFlowUnderFineLocks =>
      ∀ (ctx : LabelingContext) (observer : IfObserver) (S : LockSet) (lockCore : CoreId)
        (layout : SeLe4n.SyscallRegisterLayout) (executingCore : CoreId) (regCount : Nat)
        (s st' : SystemState), s.objects.invExt → st'.objects.invExt →
        syscallEntryChecked ctx layout executingCore regCount
            (lockSetAcquiredState S lockCore s) = .ok ((), st') →
        projectState ctx observer st'
          = projectState ctx observer (lockSetAcquiredState S lockCore s) →
        observableSlotsConfinedToCore (lockSetAcquiredState S lockCore s) st' bootCoreId →
        lowEquivalent_smp ctx observer
          (syscallEntryUnderLockSet ctx S lockCore layout executingCore regCount s).1 s
  | .failClosedUnderFineLocks =>
      ∀ (ctx : LabelingContext) (S : LockSet) (lockCore : CoreId)
        (layout : SeLe4n.SyscallRegisterLayout) (executingCore : CoreId) (regCount : Nat)
        (s : SystemState) (e : KernelError) (L : SecurityLabel), s.objects.invExt →
        syscallEntryChecked ctx layout executingCore regCount
            (lockSetAcquiredState S lockCore s) = .error e →
        ∀ c : CoreId,
          ObservableState.onCore ctx c L
              (syscallEntryUnderLockSet ctx S lockCore layout executingCore regCount s).1
            = ObservableState.onCore ctx c L s
  | .contentionChannelRegistered =>
      ∀ (maxDelay : Nat) (e : SeLe4n.Kernel.Concurrency.RwLockExecution),
        SeLe4n.Kernel.Concurrency.FairTrace e maxDelay →
        e.initial = RwLockState.unheld →
        ∀ (c : CoreId) (m : AccessMode) (kEnq : Nat),
          (c, m) ∈ (e.stateAt kEnq).waiters →
          kEnq + lockContentionDelayBound maxDelay < e.ops.length →
          acceptedCovertChannel_lockContention.modelVisible = false ∧
            acceptedCovertChannel_lockContention.severity = CovertChannelSeverity.medium ∧
            lockContentionCode e c kEnq < lockContentionAlphabet maxDelay

/-- SM8.D: **the evidence** — every claim discharged by citation.  This
definition is the phase's completeness check: it elaborates only if every claim
has a theorem, and only if that theorem proves *that* claim. -/
def fineLockClaimEvidence : (id : FineLockClaimId) → id.evidenceProp
  | .lockStateInvisible =>
      fun ctx c L s oid l₁ l₂ hInv => onCore_lock_indistinguishable ctx c L s oid l₁ l₂ hInv
  | .readerMultiplicityHidden =>
      fun ctx c L s oid r₁ r₂ hInv => readerMultiplicity_not_observable ctx c L s oid r₁ r₂ hInv
  | .writerExclusionHidden =>
      fun ctx c L s oid holder mode hInv =>
        blockedAcquirer_observes_nothing ctx c L s oid holder mode hInv
  | .contentionDelayBounded =>
      fun e maxDelay hFair hInit c m kEnq hQueued hWithin =>
        lockContention_delay_bounded e maxDelay hFair hInit c m kEnq hQueued hWithin
  | .integrityUnderLocks =>
      fun _α ctx subject S core action s hInv hActionInv hAction =>
        bibaIntegrity_underLockSet ctx subject S core action s hInv hActionInv hAction
  | .secureFlowUnderFineLocks =>
      fun ctx observer S lockCore layout executingCore regCount s st' hInv hOutInv hOk hProj
        hConfined =>
        syscallEntryUnderLockSet_preserves_projectionOnCore_of_entry ctx observer S lockCore
          layout executingCore regCount s st' hInv hOutInv hOk hProj hConfined
  | .failClosedUnderFineLocks =>
      fun ctx S lockCore layout executingCore regCount s e L hInv hDenied =>
        syscallEntryUnderLockSet_failClosed_invisible ctx S lockCore layout executingCore
          regCount s e L hInv hDenied
  | .contentionChannelRegistered =>
      fun maxDelay e hFair hInit c m kEnq hQueued hWithin =>
        acceptedCovertChannel_lockContention_bounded maxDelay e hFair hInit c m kEnq hQueued
          hWithin

/-- SM8.D: the evidence is non-empty at every claim — the sanity check that the
table is inhabited rather than a family of vacuous `True`s. -/
theorem fineLockClaimEvidence_nonempty (id : FineLockClaimId) : Nonempty id.evidenceProp :=
  ⟨fineLockClaimEvidence id⟩

end SeLe4n.Kernel
