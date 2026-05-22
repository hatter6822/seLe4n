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
-- §4 — SystemState default invariants (lock-field shape)
-- ============================================================================

/-! ## Default SystemState has unheld ObjStore lock -/

example : (default : SystemState).objStoreLock = RwLockState.unheld := by decide
example : (default : SystemState).objStoreLock = RwLockState.unheld := rfl

/-! ## Default SystemState's `objects.toList` is empty -/

example : (default : SystemState).objects.toList = [] := by decide

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
  -- The witness theorem for SM3.A.11 — every entry in toList has unheld lock.
  -- Since the list is empty, this is the vacuous discharge.
  let _proof := @default_objects_locks_unheld_via_toList
  assertBool "default_objects_locks_unheld_via_toList theorem reachable"
    true
  -- The pointwise form of SM3.A.11 — for any (id, o) ∈ default.objects,
  -- objectLockOf o = unheld.  Vacuously true (default has no entries).
  let _proofPointwise := @default_objects_locks_unheld
  assertBool "default_objects_locks_unheld theorem reachable"
    true

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
