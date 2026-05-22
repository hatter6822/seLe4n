-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Model.State
import SeLe4n.Model.FrozenState
import SeLe4n.Model.IntermediateState
import SeLe4n.Kernel.Concurrency.Locks.RwLock

/-!
# WS-SM SM3.A — Per-object lock field regression suite

Tier-3 surface anchors + decidable examples + runtime structural
assertions for the SM3.A per-object lock fields (SM3.A.1..SM3.A.11
covering TCB, Endpoint, CNode, Notification, UntypedObject,
SchedContext, VSpaceRoot, and the ObjStore-level table lock on
`SystemState`).

The suite exercises three families of checks:

* **Surface anchors** (§1).  Every public symbol introduced by SM3.A
  is `#check`'d so a rename or signature drift fails the suite at
  elaboration time.  Catches a regression where, for example,
  `TCB.lock` is renamed to `TCB.rwLock` (a common refactor candidate)
  without updating the SM3.B `LockId.fromObject` consumer.

* **Decidable defaults** (§2).  Every kernel object's freshly-default
  state carries `lock = RwLockState.unheld`.  This is the structural
  side of the SM3.A.11 theorem `default_objects_locks_unheld`: per the
  field-level defaults the per-object `lock` field is `.unheld` by
  construction; this section asserts the property holds for every
  canonical constructor (`CNode.empty`, the named-field default
  constructors for `Endpoint`, `Notification`, `UntypedObject`, and
  `SchedContext.empty`).

* **Runtime assertions** (§3).  The `default_objects_locks_unheld`
  theorem (vacuous discharge on the empty default state) and the
  `default_objStoreLock_unheld` companion are exercised at runtime via
  `assertBool` so an inadvertent regression — e.g. someone changing
  the `default` instance to seed `objStoreLock` with a non-unheld
  state — surfaces in the `run` output.

The suite is wired into Tier 2 (`test_tier2_negative.sh`) as a
runtime exerciser and Tier 3 (`test_tier3_invariant_surface.sh`) as a
surface-anchor checkpoint.  Per the SM2.D pattern, runnable as
`lake exe per_object_lock_suite`.
-/

namespace SeLe4n.Testing.PerObjectLock

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency

-- ============================================================================
-- §1 — Surface anchors: every SM3.A public symbol resolves at elaboration
-- ============================================================================

/-! ## SM3.A.1 — TCB lock field -/

#check @TCB.lock
#check @TCB.ext

/-! ## SM3.A.2 — Endpoint lock field -/

#check @Endpoint.lock

/-! ## SM3.A.3 — CNode lock field -/

#check @CNode.lock

/-! ## SM3.A.4 — Notification lock field -/

#check @Notification.lock

/-! ## SM3.A.6 — SchedContext lock field -/

#check @SeLe4n.Kernel.SchedContext.lock

/-! ## SM3.A.7 — VSpaceRoot lock field -/

#check @VSpaceRoot.lock

/-! ## SM3.A.9 — UntypedObject lock field -/

#check @UntypedObject.lock

/-! ## SM3.A.10 — KernelObject.objectLockOf projection + ObjStore lock -/

#check @KernelObject.objectLockOf
#check @KernelObject.objectLockOf_tcb
#check @KernelObject.objectLockOf_endpoint
#check @KernelObject.objectLockOf_notification
#check @KernelObject.objectLockOf_cnode
#check @KernelObject.objectLockOf_vspaceRoot
#check @KernelObject.objectLockOf_untyped
#check @KernelObject.objectLockOf_schedContext
#check @SystemState.objStoreLock

/-! ## SM3.A.10 — Frozen-state lock-field forwarding (SM3.A.3/A.7 frozen mirror) -/

#check @FrozenCNode.lock
#check @FrozenVSpaceRoot.lock
#check @FrozenSystemState.objStoreLock

/-! ## SM3.A.10 audit-pass-2 — Frozen-state `objectLockOf` projection -/

#check @FrozenKernelObject.objectLockOf
#check @FrozenKernelObject.objectLockOf_tcb
#check @FrozenKernelObject.objectLockOf_endpoint
#check @FrozenKernelObject.objectLockOf_notification
#check @FrozenKernelObject.objectLockOf_cnode
#check @FrozenKernelObject.objectLockOf_vspaceRoot
#check @FrozenKernelObject.objectLockOf_untyped
#check @FrozenKernelObject.objectLockOf_schedContext

/-! ## SM3.A.10 audit-pass-2 — `freeze*_preserves_lock` witness theorems -/

#check @freeze_preserves_objStoreLock
#check @freezeCNode_preserves_lock
#check @freezeVSpaceRoot_preserves_lock
#check @freezeObject_preserves_objectLockOf

/-! ## SM3.A.11 — Default-state lock theorems -/

#check @default_objStoreLock_unheld
#check @default_objects_locks_unheld
#check @default_objects_toList_empty
#check @default_objects_locks_unheld_via_toList

-- ============================================================================
-- §2 — Decidable defaults
-- ============================================================================

/-! ## CNode.empty has unheld lock -/

example : CNode.empty.lock = RwLockState.unheld := by decide
example : CNode.empty.lock = RwLockState.unheld := rfl

/-! ## TCB default-construction with required fields has unheld lock

`TCB` has 6 required fields without defaults (`tid`, `priority`,
`domain`, `cspaceRoot`, `vspaceRoot`, `ipcBuffer`); the lock field
defaults to `RwLockState.unheld`, so any TCB constructed via named
field syntax (omitting `lock`) inherits the default.  This pins the
SM3.A.1 default-lock witness for TCB specifically — without it, a
regression that flipped the default to a non-unheld state would slip
through the surface-anchor check. -/

example :
    ({ tid := ⟨0⟩, priority := ⟨0⟩, domain := ⟨0⟩,
       cspaceRoot := ⟨0⟩, vspaceRoot := ⟨0⟩,
       ipcBuffer := SeLe4n.VAddr.ofNat 0 } : TCB).lock = RwLockState.unheld := rfl

/-- WS-SM SM3.A audit-pass-2 (L-6 fix): `by decide` companion form for
TCB symmetry with every other per-object example.  Exercises the
`DecidableEq` derivation on `RwLockState` through `TCB.lock`. -/
example :
    ({ tid := ⟨0⟩, priority := ⟨0⟩, domain := ⟨0⟩,
       cspaceRoot := ⟨0⟩, vspaceRoot := ⟨0⟩,
       ipcBuffer := SeLe4n.VAddr.ofNat 0 } : TCB).lock = RwLockState.unheld := by
  decide

/-! ## Endpoint default-constructor has unheld lock -/

example : ({} : Endpoint).lock = RwLockState.unheld := by decide
example : ({} : Endpoint).lock = RwLockState.unheld := rfl

/-! ## Notification with default lock yields unheld -/
-- Note: Notification requires explicit `state` + `waitingThreads`.
-- Constructing the canonical "empty/idle" notification with NoDupList.empty
-- demonstrates the lock-field default.

example :
    ({ state := NotificationState.idle,
       waitingThreads := SeLe4n.NoDupList.empty,
       pendingBadge := none } : Notification).lock = RwLockState.unheld := by decide

example :
    ({ state := NotificationState.idle,
       waitingThreads := SeLe4n.NoDupList.empty,
       pendingBadge := none } : Notification).lock = RwLockState.unheld := rfl

/-! ## UntypedObject default-constructor has unheld lock -/

example :
    ({ regionBase := SeLe4n.PAddr.ofNat 0, regionSize := 0 } : UntypedObject).lock = RwLockState.unheld := by
  decide

example :
    ({ regionBase := SeLe4n.PAddr.ofNat 0, regionSize := 0 } : UntypedObject).lock = RwLockState.unheld := rfl

/-! ## SchedContext.empty has unheld lock -/

example :
    (SeLe4n.Kernel.SchedContext.empty ⟨0⟩).lock = RwLockState.unheld := by decide

example :
    (SeLe4n.Kernel.SchedContext.empty ⟨0⟩).lock = RwLockState.unheld := rfl

/-! ## VSpaceRoot constructed with empty mappings has unheld lock -/

example :
    ({ asid := ⟨0⟩, mappings := {} } : VSpaceRoot).lock = RwLockState.unheld := rfl

-- ============================================================================
-- §3 — objectLockOf reduction lemmas (decidable)
-- ============================================================================

/-! ## `objectLockOf` reduces to the per-variant lock for each kind -/

/-- TCB variant: the projection on `.tcb tcb` reduces to `tcb.lock`. -/
example :
    KernelObject.objectLockOf
      (.tcb ({ tid := ⟨0⟩, priority := ⟨0⟩, domain := ⟨0⟩,
               cspaceRoot := ⟨0⟩, vspaceRoot := ⟨0⟩,
               ipcBuffer := SeLe4n.VAddr.ofNat 0 } : TCB))
      = RwLockState.unheld := rfl

example :
    KernelObject.objectLockOf
      (.endpoint ({} : Endpoint)) = RwLockState.unheld := by decide

example :
    KernelObject.objectLockOf (.cnode CNode.empty) = RwLockState.unheld := by decide

example :
    KernelObject.objectLockOf
      (.notification { state := NotificationState.idle,
                       waitingThreads := SeLe4n.NoDupList.empty,
                       pendingBadge := none }) = RwLockState.unheld := by decide

example :
    KernelObject.objectLockOf
      (.untyped { regionBase := SeLe4n.PAddr.ofNat 0, regionSize := 0 }) = RwLockState.unheld := by decide

example :
    KernelObject.objectLockOf
      (.schedContext (SeLe4n.Kernel.SchedContext.empty ⟨0⟩)) = RwLockState.unheld := by decide

example :
    KernelObject.objectLockOf
      (.vspaceRoot { asid := ⟨0⟩, mappings := {} }) = RwLockState.unheld := by decide

-- ============================================================================
-- §3b — FrozenKernelObject.objectLockOf (audit-pass-2 M-1)
-- ============================================================================

/-! ## Frozen-state per-variant `objectLockOf` reduction -/

example :
    FrozenKernelObject.objectLockOf
      (.endpoint ({} : Endpoint)) = RwLockState.unheld := by decide

example :
    FrozenKernelObject.objectLockOf
      (.notification { state := NotificationState.idle,
                       waitingThreads := SeLe4n.NoDupList.empty,
                       pendingBadge := none }) = RwLockState.unheld := by decide

example :
    FrozenKernelObject.objectLockOf
      (.untyped { regionBase := SeLe4n.PAddr.ofNat 0, regionSize := 0 })
      = RwLockState.unheld := by decide

example :
    FrozenKernelObject.objectLockOf
      (.schedContext (SeLe4n.Kernel.SchedContext.empty ⟨0⟩))
      = RwLockState.unheld := by decide

/-- WS-SM SM3.A audit-pass-4: closes the `FrozenKernelObject` variant
coverage gap identified by the test-coverage audit.  TCB variant
through the frozen projection.  Since `FrozenKernelObject.tcb` reuses
the runtime `TCB` struct verbatim, the projection returns `t.lock`. -/
example :
    FrozenKernelObject.objectLockOf
      (.tcb ({ tid := ⟨0⟩, priority := ⟨0⟩, domain := ⟨0⟩,
               cspaceRoot := ⟨0⟩, vspaceRoot := ⟨0⟩,
               ipcBuffer := SeLe4n.VAddr.ofNat 0 } : TCB))
      = RwLockState.unheld := rfl

/-- WS-SM SM3.A audit-pass-4: CNode variant — through `freezeCNode`,
the lock field is forwarded structurally; the projection returns
`(freezeCNode CNode.empty).lock = RwLockState.unheld`. -/
example :
    FrozenKernelObject.objectLockOf
      (.cnode (freezeCNode CNode.empty)) = RwLockState.unheld := by decide

/-- WS-SM SM3.A audit-pass-4: VSpaceRoot variant — through
`freezeVSpaceRoot`, the lock field is forwarded structurally. -/
example :
    FrozenKernelObject.objectLockOf
      (.vspaceRoot (freezeVSpaceRoot { asid := ⟨0⟩, mappings := {} }))
      = RwLockState.unheld := rfl

-- ============================================================================
-- §4 — SystemState default invariants (lock-field shape)
-- ============================================================================

/-! ## Default SystemState has unheld ObjStore lock -/

example : (default : SystemState).objStoreLock = RwLockState.unheld := by decide
example : (default : SystemState).objStoreLock = RwLockState.unheld := rfl

/-! ## Default SystemState's `objects.toList` is empty -/

example : (default : SystemState).objects.toList = [] := by decide

/-- WS-SM SM3.A audit-pass-4: non-vacuous witness for SM3.A.11 — after
inserting an Endpoint into the default state's object store, the
stored object's lock is `unheld`.  This closes the HIGH-severity
finding from the test-coverage audit ("SM3.A.11 runtime discharge is
vacuous on the default state's empty store").  The witness
exercises the `objectLockOf` projection on an actual stored object
rather than relying on vacuous quantification over an empty list.

The construction uses direct `RHTable.insert` (rather than the
`storeObject` Kernel monad action, which would require running the
monad first) on `default.objects`, then projects the result back
through `KernelObject.objectLockOf`.  Because the default `Endpoint
{}` constructor sets `lock := unheld` per SM3.A.2, the lookup
returns `some (.endpoint {})` and `objectLockOf` returns `unheld`.
The post-condition is formulated via `Option.map (·.objectLockOf) =
some unheld` to keep the predicate decidable (a direct `match`
arm would require an explicit `Decidable` instance for the
dependent shape). -/
example :
    let objects' :=
      (default : SystemState).objects.insert (⟨1⟩ : SeLe4n.ObjId)
        (.endpoint ({} : Endpoint))
    objects'[(⟨1⟩ : SeLe4n.ObjId)]?.map KernelObject.objectLockOf
      = some RwLockState.unheld := by
  decide

/-- WS-SM SM3.A audit-pass-4 (companion): non-vacuous witness for
SM3.A.11 on a CNode store.  Covers the case where the stored object
has a non-trivial inner structure (`UniqueSlotMap` slots) — verifies
that the lock-state defaulting works even with embedded data. -/
example :
    let objects' :=
      (default : SystemState).objects.insert (⟨2⟩ : SeLe4n.ObjId)
        (.cnode CNode.empty)
    objects'[(⟨2⟩ : SeLe4n.ObjId)]?.map KernelObject.objectLockOf
      = some RwLockState.unheld := by
  decide

-- ============================================================================
-- §5 — RwLockState.unheld properties (cross-referencing SM2.C)
-- ============================================================================

/-! ## `unheld` has no writer and no readers -/

example : RwLockState.unheld.writerHeld = none := by decide
example : RwLockState.unheld.readers = ([] : List CoreId) := by decide
example : RwLockState.unheld.waiters = ([] : List (CoreId × AccessMode)) := by decide

/-! ## `unheld` satisfies `wf` (5-conjunct invariant from SM2.C) -/

example : RwLockState.unheld.wf := by decide

-- ============================================================================
-- §6 — Runtime entry point
-- ============================================================================

private def assertBool (name : String) (b : Bool) : IO Unit := do
  if b then
    IO.println s!"  PASS  {name}"
  else
    IO.eprintln s!"  FAIL  {name}"
    IO.Process.exit 1

private def runDefaultStateChecks : IO Unit := do
  IO.println "--- §1 default SystemState — objStoreLock + toList ---"
  -- The default state's table-level lock is unheld.
  assertBool "default.objStoreLock = RwLockState.unheld"
    (decide ((default : SystemState).objStoreLock = RwLockState.unheld))
  -- The default state's object store has an empty toList snapshot.
  assertBool "default.objects.toList = []"
    (decide ((default : SystemState).objects.toList = []))
  -- WS-SM SM3.A audit-pass-2 (L-2 fix): replaces the previous
  -- dead-weight `assertBool ... true` invocations.  The SM2.D
  -- audit-pass-6 LOW-4 pattern is to evaluate a decidable
  -- closed-form instance — here, we check `objectLockOf` on every
  -- KernelObject value reachable via `.toList` from the default
  -- state (vacuously empty list, but the closed form is
  -- decidable).  A regression that broke the SM3.A.11 theorem
  -- discharge would fail this check rather than silently passing.
  assertBool "default_objects_locks_unheld holds on every toList entry"
    (decide
      ((default : SystemState).objects.toList.all
        (fun p => p.snd.objectLockOf = RwLockState.unheld)))
  -- Companion check: every entry's lock satisfies the SM2.C `wf`
  -- invariant (5 conjuncts).  Closed-form decidable; vacuously
  -- true on the empty default state but exercises the closed
  -- instance for a regression-resistant Tier-2 assertion.
  assertBool "every default toList lock satisfies wf"
    (decide
      ((default : SystemState).objects.toList.all
        (fun p => p.snd.objectLockOf.wf)))
  -- WS-SM SM3.A audit-pass-4 (HIGH fix): non-vacuous witness for
  -- SM3.A.11.  After inserting `.endpoint {}` into the default
  -- state's object store, lookup returns the stored Endpoint and
  -- its `objectLockOf` projection returns `unheld`.  Exercises
  -- the SM3.A.11 *conclusion* (not just its vacuous discharge on
  -- an empty store).  A regression that flipped the default lock
  -- of any kernel object to non-unheld would fail this check.
  assertBool "post-insert .endpoint lookup yields objectLockOf = unheld"
    (decide
      (let objects' :=
        (default : SystemState).objects.insert (⟨1⟩ : SeLe4n.ObjId)
          (.endpoint ({} : Endpoint))
       objects'[(⟨1⟩ : SeLe4n.ObjId)]?.map KernelObject.objectLockOf
         = some RwLockState.unheld))
  -- Companion: same for CNode (exercises a kernel object with
  -- non-trivial inner structure — `UniqueSlotMap` slots).
  assertBool "post-insert .cnode lookup yields objectLockOf = unheld"
    (decide
      (let objects' :=
        (default : SystemState).objects.insert (⟨2⟩ : SeLe4n.ObjId)
          (.cnode CNode.empty)
       objects'[(⟨2⟩ : SeLe4n.ObjId)]?.map KernelObject.objectLockOf
         = some RwLockState.unheld))
  -- Companion: same for VSpaceRoot (exercises a kernel object whose
  -- inner has `RHTable` mappings — verifies the SM3.A.7 default
  -- propagates through manual `BEq VSpaceRoot` correctly).
  assertBool "post-insert .vspaceRoot lookup yields objectLockOf = unheld"
    (decide
      (let objects' :=
        (default : SystemState).objects.insert (⟨3⟩ : SeLe4n.ObjId)
          (.vspaceRoot ({ asid := ⟨0⟩, mappings := {} } : VSpaceRoot))
       objects'[(⟨3⟩ : SeLe4n.ObjId)]?.map KernelObject.objectLockOf
         = some RwLockState.unheld))

private def runPerObjectDefaultChecks : IO Unit := do
  IO.println "--- §2 per-object defaults — every kind's lock is unheld ---"
  -- TCB: named-field construction with required fields only; lock
  -- inherits the SM3.A.1 default of `RwLockState.unheld`.  Without
  -- this assertion, a regression that flipped the TCB default to
  -- a non-unheld state would not be caught by surface anchors alone.
  assertBool "TCB{minimal}.lock = unheld"
    (decide (({ tid := ⟨0⟩, priority := ⟨0⟩, domain := ⟨0⟩,
                cspaceRoot := ⟨0⟩, vspaceRoot := ⟨0⟩,
                ipcBuffer := SeLe4n.VAddr.ofNat 0 } : TCB).lock = RwLockState.unheld))
  -- Endpoint: empty constructor yields unheld lock.
  assertBool "Endpoint {}.lock = unheld"
    (decide (({} : Endpoint).lock = RwLockState.unheld))
  -- Notification: canonical idle/empty-waiters notification.
  assertBool "Notification idle.lock = unheld"
    (decide (({ state := NotificationState.idle,
                waitingThreads := SeLe4n.NoDupList.empty,
                pendingBadge := none } : Notification).lock = RwLockState.unheld))
  -- CNode.empty: SM3.A.3 default-lock witness.
  assertBool "CNode.empty.lock = unheld"
    (decide (CNode.empty.lock = RwLockState.unheld))
  -- VSpaceRoot with empty mappings: SM3.A.7 default-lock witness.
  assertBool "VSpaceRoot{empty}.lock = unheld"
    (decide (({ asid := ⟨0⟩, mappings := {} } : VSpaceRoot).lock = RwLockState.unheld))
  -- UntypedObject default-constructor: SM3.A.9 default-lock witness.
  assertBool "UntypedObject{base, size}.lock = unheld"
    (decide
      (({ regionBase := SeLe4n.PAddr.ofNat 0, regionSize := 0 } : UntypedObject).lock = RwLockState.unheld))
  -- SchedContext.empty: SM3.A.6 default-lock witness.
  assertBool "SchedContext.empty.lock = unheld"
    (decide ((SeLe4n.Kernel.SchedContext.empty ⟨0⟩).lock = RwLockState.unheld))

private def runObjectLockOfReductionChecks : IO Unit := do
  IO.println "--- §3 objectLockOf — per-variant reduction ---"
  -- Every per-variant unfold lemma reduces `objectLockOf (.kind x) = x.lock`
  -- by `rfl`.  We can't decide BaseIO equality but we can assert that the
  -- decidable equality on the result holds.
  -- TCB variant: closes the per-variant projection gap from §2 — without
  -- this, a regression in `objectLockOf_tcb` would not be caught at the
  -- runtime tier (only at the surface-anchor tier).
  assertBool "objectLockOf (.tcb minimal) = unheld"
    (decide
      (KernelObject.objectLockOf
        (.tcb ({ tid := ⟨0⟩, priority := ⟨0⟩, domain := ⟨0⟩,
                 cspaceRoot := ⟨0⟩, vspaceRoot := ⟨0⟩,
                 ipcBuffer := SeLe4n.VAddr.ofNat 0 } : TCB))
        = RwLockState.unheld))
  assertBool "objectLockOf (.endpoint {}) = unheld"
    (decide
      (KernelObject.objectLockOf (.endpoint ({} : Endpoint)) = RwLockState.unheld))
  assertBool "objectLockOf (.cnode CNode.empty) = unheld"
    (decide
      (KernelObject.objectLockOf (.cnode CNode.empty) = RwLockState.unheld))
  assertBool "objectLockOf (.notification idle) = unheld"
    (decide
      (KernelObject.objectLockOf
        (.notification { state := NotificationState.idle,
                         waitingThreads := SeLe4n.NoDupList.empty,
                         pendingBadge := none })
        = RwLockState.unheld))
  assertBool "objectLockOf (.untyped {0, 0}) = unheld"
    (decide
      (KernelObject.objectLockOf
        (.untyped ({ regionBase := SeLe4n.PAddr.ofNat 0, regionSize := 0 } : UntypedObject))
        = RwLockState.unheld))
  assertBool "objectLockOf (.schedContext SchedContext.empty 0) = unheld"
    (decide
      (KernelObject.objectLockOf
        (.schedContext (SeLe4n.Kernel.SchedContext.empty ⟨0⟩))
        = RwLockState.unheld))
  assertBool "objectLockOf (.vspaceRoot {0, {}}) = unheld"
    (decide
      (KernelObject.objectLockOf
        (.vspaceRoot ({ asid := ⟨0⟩, mappings := {} } : VSpaceRoot))
        = RwLockState.unheld))

private def runFrozenStateForwardingChecks : IO Unit := do
  IO.println "--- §4 FrozenState — lock-field forwarding (SM3.A.3, A.7, A.10) ---"
  -- `freezeCNode CNode.empty` carries the lock unchanged.
  assertBool "freezeCNode CNode.empty preserves lock = unheld"
    (decide ((freezeCNode CNode.empty).lock = RwLockState.unheld))
  -- `freezeVSpaceRoot` carries the lock unchanged.
  assertBool "freezeVSpaceRoot preserves lock = unheld"
    (decide ((freezeVSpaceRoot { asid := ⟨0⟩, mappings := {} }).lock = RwLockState.unheld))
  -- WS-SM SM3.A audit-pass-2 (M-1): FrozenKernelObject.objectLockOf
  -- symmetry — every frozen-variant projection returns its inner
  -- struct's `lock` field.  These assertions close the SM3.A.10
  -- symmetry gap that the audit flagged.
  assertBool "FrozenKernelObject.objectLockOf (.endpoint {}) = unheld"
    (decide
      (FrozenKernelObject.objectLockOf (.endpoint ({} : Endpoint))
        = RwLockState.unheld))
  assertBool "FrozenKernelObject.objectLockOf (.cnode (freezeCNode CNode.empty)) = unheld"
    (decide
      (FrozenKernelObject.objectLockOf (.cnode (freezeCNode CNode.empty))
        = RwLockState.unheld))
  assertBool "FrozenKernelObject.objectLockOf (.vspaceRoot _) = unheld"
    (decide
      (FrozenKernelObject.objectLockOf
        (.vspaceRoot (freezeVSpaceRoot { asid := ⟨0⟩, mappings := {} }))
        = RwLockState.unheld))
  -- WS-SM SM3.A audit-pass-4: complete FrozenKernelObject.objectLockOf
  -- runtime variant coverage.  The previous block only exercised
  -- endpoint/cnode/vspaceRoot; the test-coverage audit found that the
  -- remaining 4 variants (TCB, notification, untyped, schedContext)
  -- had no runtime exerciser.  These assertions close the gap.
  assertBool "FrozenKernelObject.objectLockOf (.tcb minimal) = unheld"
    (decide
      (FrozenKernelObject.objectLockOf
        (.tcb ({ tid := ⟨0⟩, priority := ⟨0⟩, domain := ⟨0⟩,
                 cspaceRoot := ⟨0⟩, vspaceRoot := ⟨0⟩,
                 ipcBuffer := SeLe4n.VAddr.ofNat 0 } : TCB))
        = RwLockState.unheld))
  assertBool "FrozenKernelObject.objectLockOf (.notification idle) = unheld"
    (decide
      (FrozenKernelObject.objectLockOf
        (.notification { state := NotificationState.idle,
                         waitingThreads := SeLe4n.NoDupList.empty,
                         pendingBadge := none })
        = RwLockState.unheld))
  assertBool "FrozenKernelObject.objectLockOf (.untyped {0, 0}) = unheld"
    (decide
      (FrozenKernelObject.objectLockOf
        (.untyped ({ regionBase := SeLe4n.PAddr.ofNat 0, regionSize := 0 } : UntypedObject))
        = RwLockState.unheld))
  assertBool "FrozenKernelObject.objectLockOf (.schedContext _) = unheld"
    (decide
      (FrozenKernelObject.objectLockOf
        (.schedContext (SeLe4n.Kernel.SchedContext.empty ⟨0⟩))
        = RwLockState.unheld))
  -- `freezeObject` is consistent with `objectLockOf` (the aggregate
  -- audit-pass-2 witness).
  assertBool "freezeObject (.endpoint {}) preserves objectLockOf"
    (decide
      ((freezeObject (.endpoint ({} : Endpoint))).objectLockOf
        = (KernelObject.endpoint ({} : Endpoint)).objectLockOf))
  assertBool "freezeObject (.cnode CNode.empty) preserves objectLockOf"
    (decide
      ((freezeObject (.cnode CNode.empty)).objectLockOf
        = (KernelObject.cnode CNode.empty).objectLockOf))
  -- WS-SM SM3.A audit-pass-4: complete freezeObject_preserves_objectLockOf
  -- variant coverage.  The audit found that only 2 of 7 variants were
  -- runtime-exercised; these close the gap.
  assertBool "freezeObject (.notification idle) preserves objectLockOf"
    (decide
      ((freezeObject (.notification
        { state := NotificationState.idle,
          waitingThreads := SeLe4n.NoDupList.empty,
          pendingBadge := none })).objectLockOf
        = (KernelObject.notification
            { state := NotificationState.idle,
              waitingThreads := SeLe4n.NoDupList.empty,
              pendingBadge := none }).objectLockOf))
  assertBool "freezeObject (.untyped {0, 0}) preserves objectLockOf"
    (decide
      ((freezeObject (.untyped
        ({ regionBase := SeLe4n.PAddr.ofNat 0, regionSize := 0 } : UntypedObject))).objectLockOf
        = (KernelObject.untyped
            ({ regionBase := SeLe4n.PAddr.ofNat 0, regionSize := 0 } : UntypedObject)).objectLockOf))
  assertBool "freezeObject (.schedContext _) preserves objectLockOf"
    (decide
      ((freezeObject (.schedContext (SeLe4n.Kernel.SchedContext.empty ⟨0⟩))).objectLockOf
        = (KernelObject.schedContext (SeLe4n.Kernel.SchedContext.empty ⟨0⟩)).objectLockOf))
  assertBool "freezeObject (.vspaceRoot _) preserves objectLockOf"
    (decide
      ((freezeObject (.vspaceRoot
        ({ asid := ⟨0⟩, mappings := {} } : VSpaceRoot))).objectLockOf
        = (KernelObject.vspaceRoot
            ({ asid := ⟨0⟩, mappings := {} } : VSpaceRoot)).objectLockOf))
  -- WS-SM SM3.A audit-pass-4: `FrozenSystemState.objStoreLock` runtime
  -- exercise.  The test-coverage audit identified that the field had
  -- only a surface anchor — no decidable example or runtime
  -- assertion.  Closes the gap by exercising `freeze` over
  -- `mkEmptyIntermediateState` (the canonical empty IntermediateState
  -- seed) and asserting the forwarded ObjStore lock is `unheld`.
  assertBool "freeze mkEmptyIntermediateState preserves objStoreLock = unheld"
    (decide
      ((freeze mkEmptyIntermediateState).objStoreLock = RwLockState.unheld))

private def runRwLockStateAuxChecks : IO Unit := do
  IO.println "--- §5 RwLockState.unheld — auxiliary properties (SM2.C cross-ref) ---"
  -- unheld is wf (the 5-conjunct invariant from SM2.C).
  assertBool "RwLockState.unheld.wf"
    (decide RwLockState.unheld.wf)
  -- unheld has no writer.
  assertBool "RwLockState.unheld.writerHeld = none"
    (decide (RwLockState.unheld.writerHeld = none))
  -- unheld has no readers.
  assertBool "RwLockState.unheld.readers = []"
    (decide (RwLockState.unheld.readers = ([] : List CoreId)))
  -- unheld has no waiters.
  assertBool "RwLockState.unheld.waiters = []"
    (decide (RwLockState.unheld.waiters = ([] : List (CoreId × AccessMode))))

def runPerObjectLockChecks : IO Unit := do
  IO.println "WS-SM SM3.A — Per-object lock field regression suite"
  IO.println "===================================================="
  runDefaultStateChecks
  runPerObjectDefaultChecks
  runObjectLockOfReductionChecks
  runFrozenStateForwardingChecks
  runRwLockStateAuxChecks
  IO.println "===================================================="
  IO.println "All SM3.A per-object lock checks PASS."

end SeLe4n.Testing.PerObjectLock

def main : IO Unit :=
  SeLe4n.Testing.PerObjectLock.runPerObjectLockChecks
