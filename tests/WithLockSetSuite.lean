-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Concurrency.LockSet
import SeLe4n.Kernel.Concurrency.Locks.WithLockSet
import SeLe4n.Kernel.Concurrency.Locks.LockSetHeld
import SeLe4n.Kernel.Concurrency.Locks.LockSet2PL
import SeLe4n.Kernel.Concurrency.Locks.DynamicChainExtension
import SeLe4n.Kernel.Concurrency.Locks.Sm3CInventory

/-!
# WS-SM SM3.C — `withLockSet` 2PL discipline regression suite

Tier-2 / Tier-3 surface anchors + decidable examples + runtime
structural assertions for every public symbol introduced by SM3.C
(WithLockSet / LockSetHeld / LockSet2PL / DynamicChainExtension /
Sm3CInventory).

The suite exercises four families of checks:

* **Surface anchors** (§1).  Every public SM3.C symbol is
  `#check`'d so a rename or signature drift fails the suite at
  elaboration time.

* **Decidable defaults** (§2).  `withLockSet` on small concrete
  lock sets, `acquireLockOnObject` / `releaseLockOnObject` on
  the default state, and the `lockSetHeld` predicate's empty-set
  case are checked at elaboration time via `decide`.

* **Ordering / atomicity properties** (§3).  Decidable examples
  on small concrete `LockSet`s exercise the SM3.C.5 / SM3.C.6
  ordering theorems and the SM3.C.7 atomic-decomposition
  witness.

* **Runtime assertions** (§4).  Per-transition `withLockSet`
  invocations, `lockSetHeld` decidability on concrete states,
  the SM3.C.11 dynamic chain walker on synthetic blocking
  graphs, and the SM3.C inventory aggregator's count witnesses
  run at `lake exe with_lock_set_suite` and assert via
  `assertBool`.
-/

namespace SeLe4n.Testing.WithLockSet

open SeLe4n
open SeLe4n.Model
open SeLe4n.Kernel.Concurrency

-- ============================================================================
-- §1 — Surface anchors
-- ============================================================================

/-! ## SM3.C.1 — withLockSet combinator -/

#check @withLockSet
#check @withLockSet_empty
#check @withLockSet_unfold
#check @withLockSet_eq_decomposition
#check @withLockSet_fst
#check @withLockSet_snd

/-! ## SM3.C.2 — Per-object acquire/release primitives -/

#check @acquireLockOnObject
#check @releaseLockOnObject
#check @acquireLockOnObject_reply
#check @acquireLockOnObject_page
#check @releaseLockOnObject_reply
#check @releaseLockOnObject_page
#check @AccessMode.toAcquireOp
#check @AccessMode.toReleaseOp
#check @acquireAll
#check @releaseAll
#check @acquireAll_nil
#check @releaseAll_nil
#check @acquireAll_cons
#check @releaseAll_cons
#check @updateObjectAt
#check @KernelObject.updateLock
#check @KernelObject.updateLock_preserves_lockKind
#check @KernelObject.objectLockOf_updateLock

/-! ## SM3.C.4 — lockSetHeld predicate -/

#check @lockHeld
#check @lockSetHeld
#check @lockHeld_reply
#check @lockHeld_page
#check @lockSetHeld_empty
#check @lockSetHeld_singleton
#check @lockSetHeld_subset
#check @lockSetHeld_default_iff_empty
#check @RwLockState.coreHolds

/-! ## SM3.C.5 / SM3.C.6 — Ordering theorems -/

#check @lockSet_acquired_in_order
#check @lockSet_released_in_reverse
#check @acquireOrder
#check @releaseOrder
#check @releaseOrder_eq_acquireOrder_reverse

/-! ## SM3.C.7 / SM3.C.8 — Atomicity + invariant preservation -/

#check @withLockSet_three_phase_decomposition
#check @lockSet_atomic_under_2pl
#check @lockSet_invariant_preserved
#check @withLockSet_invariant_preserved
#check @withLockSet_satisfies_strict_2PL
#check @withLockSet_computation
-- Audit-pass-1 (Comment 7): substantive acquire-grants theorems
-- (replacing the removed tautological _unchanged_outside_lockSet).
#check @acquireLockOnObject_objStore_establishes_lockHeld
#check @acquireLockOnObject_objStore_release_roundtrip

/-! ## SM3.C.8 — Substantive structural-preservation lemmas -/

#check @KernelObject.updateLock_preserves_objectType
#check @updateObjectAt_preserves_objStoreLock
#check @updateObjectLockAt_preserves_objStoreLock
#check @acquireLockOnObject_preserves_objStoreLock_of_modeled

/-! ## SM3.C.4 audit-pass-1 — abstract acquire grants on available lock -/

#check @updateObjectLockAt
#check @RwLockState.unheld_acquire_grants
#check @RwLockState.unheld_acquire_release_roundtrip
#check @releaseLockOnObject_preserves_objStoreLock_of_modeled
#check @updateObjectAt_preserves_objectType_at

/-! ## SM3.C.11 — Dynamic priority-inheritance chain-walk locking -/

#check @MAX_PIP_RETRIES
#check @MAX_PIP_RETRIES_pos
#check @PipChainPath
#check @PipChainPath.singleton
#check @PipChainPath.length
#check @WalkOutcome
#check @walkStep
#check @walkAndAcquire
#check @withDynamicChainExtension
#check @withDynamicChainExtension_unfold
#check @dynamicChainHeld
#check @chainFollowsBlockingServer
#check @walkStep_extended_increases_objId
#check @walkStep_extended_blockingServer
#check @walkAndAcquire_path_ascending_in_ObjId_if_terminated
#check @walkAndAcquire_terminated_followsChain
#check @walkAndAcquire_terminated_satisfies_path_structure
#check @walkAndAcquireAux_terminated_length_le
#check @walkAndAcquire_terminated_length_bounded
#check @walkAndAcquire_total

/-! ## SM3.C.8 establishment (acquire establishes lockHeld / lockSetHeld) -/

#check @acquireLockOnObject_establishes_lockHeld_modeled
#check @acquireLockOnObject_preserves_lockHeld_of_ne_objId
#check @acquireAll_preserves_lockHeld_of_ne_all
#check @acquireAll_establishes_lockHeld_of_distinct_present_unheld
#check @acquireAll_establishes_lockSetHeld
#check @lockAcquireSequence_distinct_objId_of_resolves
#check @updateObjectLockAt_lookup_self
#check @LockId.lookup_eq_of_objects_getElem?_eq

/-! ## SM3.C.7 observational atomicity (lock-insensitive observer) -/

#check @AcquireInsensitive
#check @ReleaseInsensitive
#check @acquireAll_lockInsensitive
#check @releaseAll_lockInsensitive
#check @withLockSet_release_invisible
#check @lockSet_observer_atomic

/-! ## SM3.C.11.c/d dynamic chain — conjunct-1, capstone, deadlock-freedom -/

#check @chainLockSeq
#check @chainLockSeq_acquire_establishes_pathHeld
#check @blockingServer_eq_bind
#check @tcbReplyServer_updateLock
#check @acquireLockOnObject_preserves_blockingServer
#check @acquireAll_preserves_blockingServer
#check @chainFollowsBlockingServer_of_blockingServer_eq
#check @withDynamicChainExtension_establishes_dynamicChainHeld
#check @coreWaitsForLock
#check @dynamic_chain_deadlock_free
#check @dynamic_chain_no_mutual_wait

/-! ## SM3.C inventory -/

#check @WithLockSetCategory
#check @WithLockSetTheorem
#check @withLockSetTheorems
#check @withLockSetTheorems_count
#check @withLockSetTheorems_combinator_count
#check @withLockSetTheorems_held_count
#check @withLockSetTheorems_ordering_count
#check @withLockSetTheorems_atomicity_count
#check @withLockSetTheorems_dynamicChain_count
#check @withLockSetTheorems_partition_sum
#check @withLockSetTheorems_identifiers_nodup
#check @withLockSetTheorems_descriptions_nodup

-- ============================================================================
-- §2 — Decidable defaults (elaboration-time discharge)
-- ============================================================================

/-! ## §2.1 SM3.C.4 — Default state holds no locks -/

-- The default state's lockSetHeld for the empty lock set is vacuously true.
example : lockSetHeld bootCoreId LockSet.empty (default : SystemState) := by
  exact lockSetHeld_empty bootCoreId (default : SystemState)

example : (lockSetHeld bootCoreId LockSet.empty (default : SystemState) : Prop) ↔ True :=
  ⟨fun _ => trivial, fun _ => lockSetHeld_empty bootCoreId (default : SystemState)⟩

-- The default state's lockSetHeld for a non-empty set is False.
example : ¬ lockSetHeld bootCoreId
    (LockSet.singleton ⟨.tcb, SeLe4n.ObjId.ofNat 1⟩ .write)
    (default : SystemState) := by
  intro h
  have hEmpty := (lockSetHeld_default_iff_empty bootCoreId
    (LockSet.singleton ⟨.tcb, SeLe4n.ObjId.ofNat 1⟩ .write)).mp h
  -- The singleton list is not empty.
  simp [LockSet.singleton] at hEmpty

/-! ## §2.2 SM3.C.2 — acquireLockOnObject on N/A LockKinds is identity -/

example : acquireLockOnObject (default : SystemState) bootCoreId
    ⟨.reply, SeLe4n.ObjId.ofNat 0⟩ .write = (default : SystemState) := rfl

example : acquireLockOnObject (default : SystemState) bootCoreId
    ⟨.page, SeLe4n.ObjId.ofNat 0⟩ .read = (default : SystemState) := rfl

example : releaseLockOnObject (default : SystemState) bootCoreId
    ⟨.reply, SeLe4n.ObjId.ofNat 0⟩ .write = (default : SystemState) := rfl

example : releaseLockOnObject (default : SystemState) bootCoreId
    ⟨.page, SeLe4n.ObjId.ofNat 0⟩ .read = (default : SystemState) := rfl

/-! ## §2.3 SM3.C.1 — withLockSet on empty set reduces to action -/

example : (withLockSet LockSet.empty bootCoreId
    (fun s => (s, 42))
    (default : SystemState)).snd = 42 := by
  rw [withLockSet_empty]

/-! ## §2.4 SM3.C.4 — lockHeld on .reply / .page LockIds is False -/

example : ¬ lockHeld bootCoreId ⟨.reply, SeLe4n.ObjId.ofNat 0⟩ .write
    (default : SystemState) :=
  lockHeld_reply _ _ _ _

example : ¬ lockHeld bootCoreId ⟨.page, SeLe4n.ObjId.ofNat 0⟩ .read
    (default : SystemState) :=
  lockHeld_page _ _ _ _

-- ============================================================================
-- §3 — Ordering properties (decidable on concrete examples)
-- ============================================================================

/-! ## §3.1 SM3.C.5 — Acquire order is LockId ascending -/

-- The acquire order on an empty LockSet is empty.
example : acquireOrder LockSet.empty = [] := by
  simp [acquireOrder]

-- The release order on an empty LockSet is empty.
example : releaseOrder LockSet.empty = [] := by
  simp [releaseOrder, acquireOrder]

-- The acquire order on a singleton is a one-element list.
example : acquireOrder (LockSet.singleton ⟨.tcb, SeLe4n.ObjId.ofNat 1⟩ .write)
    = [⟨.tcb, SeLe4n.ObjId.ofNat 1⟩] := by
  simp [acquireOrder]

/-! ## §3.2 SM3.C.7 — Three-phase atomic decomposition -/

-- The decomposition theorem holds definitionally for any state and action.
example {α : Type} (S : LockSet) (core : CoreId)
    (action : SystemState → SystemState × α) (s : SystemState) :
    withLockSet S core action s =
      let ordered := S.lockAcquireSequence
      let acquired := acquireAll core ordered s
      let (postAction, result) := action acquired
      let released := releaseAll core ordered.reverse postAction
      (released, result) := withLockSet_unfold S core action s

-- ============================================================================
-- §4 — Runtime assertions
-- ============================================================================

private def assertBool (name : String) (b : Bool) : IO Unit := do
  if b then
    IO.println s!"  PASS  {name}"
  else
    IO.eprintln s!"  FAIL  {name}"
    IO.Process.exit 1

private def runWithLockSetEmptyChecks : IO Unit := do
  IO.println "--- §1 SM3.C.1 — withLockSet on empty set ---"
  -- Empty set: withLockSet reduces to the action.
  let result := withLockSet LockSet.empty bootCoreId
    (fun s => (s, "no-op")) (default : SystemState)
  assertBool "withLockSet empty: snd component = action's result"
    (decide (result.snd = "no-op"))
  -- Empty set: post-state equals input state (no locks held = no changes).
  assertBool "withLockSet empty: post-state preserves objStoreLock = unheld"
    (decide (result.fst.objStoreLock = RwLockState.unheld))

private def runAcquireReleasePrimitiveChecks : IO Unit := do
  IO.println "--- §2 SM3.C.2 — acquireLockOnObject / releaseLockOnObject ---"
  let s₀ : SystemState := default
  -- acquireLockOnObject on a .reply LockId preserves objStoreLock = unheld.
  let sReply := acquireLockOnObject s₀ bootCoreId ⟨.reply, SeLe4n.ObjId.ofNat 0⟩ .write
  assertBool "acquireLockOnObject .reply preserves objStoreLock"
    (decide (sReply.objStoreLock = RwLockState.unheld))
  -- acquireLockOnObject on a .page LockId preserves objStoreLock = unheld.
  let sPage := acquireLockOnObject s₀ bootCoreId ⟨.page, SeLe4n.ObjId.ofNat 0⟩ .read
  assertBool "acquireLockOnObject .page preserves objStoreLock"
    (decide (sPage.objStoreLock = RwLockState.unheld))
  -- releaseLockOnObject on a .reply LockId preserves objStoreLock = unheld.
  let sRelReply := releaseLockOnObject s₀ bootCoreId ⟨.reply, SeLe4n.ObjId.ofNat 0⟩ .write
  assertBool "releaseLockOnObject .reply preserves objStoreLock"
    (decide (sRelReply.objStoreLock = RwLockState.unheld))
  -- releaseLockOnObject on a .page LockId preserves objStoreLock = unheld.
  let sRelPage := releaseLockOnObject s₀ bootCoreId ⟨.page, SeLe4n.ObjId.ofNat 0⟩ .read
  assertBool "releaseLockOnObject .page preserves objStoreLock"
    (decide (sRelPage.objStoreLock = RwLockState.unheld))
  -- acquireLockOnObject on a present .objStore LockId mutates objStoreLock.
  let s₁ := acquireLockOnObject s₀ bootCoreId ⟨.objStore, SeLe4n.ObjId.ofNat 0⟩ .write
  assertBool "acquireLockOnObject .objStore .write advances objStoreLock"
    (decide (s₁.objStoreLock.writerHeld = some bootCoreId))
  -- acquireLockOnObject on a non-existent modeled object preserves objStoreLock.
  let s₂ := acquireLockOnObject s₀ bootCoreId ⟨.tcb, SeLe4n.ObjId.ofNat 99⟩ .write
  assertBool "acquireLockOnObject on absent TCB preserves objStoreLock"
    (decide (s₂.objStoreLock = s₀.objStoreLock))
  -- Acquire and release roundtrip on objStore: writer is none after release.
  let s₃ := releaseLockOnObject s₁ bootCoreId ⟨.objStore, SeLe4n.ObjId.ofNat 0⟩ .write
  assertBool "objStore acquire .write then release .write returns writer to none"
    (decide (s₃.objStoreLock.writerHeld = none))

private def runAcquireAllChecks : IO Unit := do
  IO.println "--- §3 SM3.C.1 helper — acquireAll / releaseAll ---"
  let s₀ : SystemState := default
  -- acquireAll on empty list preserves objStoreLock = unheld (identity).
  let sAcqNil := acquireAll bootCoreId [] s₀
  assertBool "acquireAll [] preserves objStoreLock"
    (decide (sAcqNil.objStoreLock = RwLockState.unheld))
  -- releaseAll on empty list preserves objStoreLock = unheld (identity).
  let sRelNil := releaseAll bootCoreId [] s₀
  assertBool "releaseAll [] preserves objStoreLock"
    (decide (sRelNil.objStoreLock = RwLockState.unheld))
  -- acquireAll on a singleton [(objStore, .read)] takes a read lock on objStore.
  let l : LockId := ⟨.objStore, SeLe4n.ObjId.ofNat 0⟩
  let acq : SystemState := acquireAll bootCoreId [(l, .read)] s₀
  assertBool "acquireAll [(.objStore, .read)] adds bootCoreId to readers"
    (decide (bootCoreId ∈ acq.objStoreLock.readers))
  -- acquireAll then releaseAll round-trip: writer is none and readers empty.
  let writeL : LockId := ⟨.objStore, SeLe4n.ObjId.ofNat 0⟩
  let acqWrite := acquireAll bootCoreId [(writeL, .write)] s₀
  let relWrite := releaseAll bootCoreId [(writeL, .write)] acqWrite
  assertBool "acquireAll then releaseAll round-trip writer = none"
    (decide (relWrite.objStoreLock.writerHeld = none))

private def runLockSetHeldChecks : IO Unit := do
  IO.println "--- §4 SM3.C.4 — lockSetHeld predicate ---"
  -- Empty lock set is vacuously held.
  assertBool "lockSetHeld bootCoreId LockSet.empty default (decide)"
    (decide (lockSetHeld bootCoreId LockSet.empty (default : SystemState)))
  -- Default state holds NO locks (every modeled-kind lookup is none).
  assertBool "¬ lockSetHeld for singleton on default state"
    (decide (¬ lockSetHeld bootCoreId
      (LockSet.singleton ⟨.tcb, SeLe4n.ObjId.ofNat 1⟩ .write)
      (default : SystemState)))
  -- Default state's objStoreLock is unheld, so even .objStore not held.
  assertBool "¬ lockSetHeld for .objStore singleton on default state"
    (decide (¬ lockSetHeld bootCoreId
      (LockSet.singleton ⟨.objStore, SeLe4n.ObjId.ofNat 0⟩ .write)
      (default : SystemState)))
  -- After acquiring objStore lock for bootCoreId, lockSetHeld is true.
  let s₁ := acquireLockOnObject (default : SystemState) bootCoreId
    ⟨.objStore, SeLe4n.ObjId.ofNat 0⟩ .write
  assertBool "lockSetHeld after acquiring objStore .write"
    (decide (lockSetHeld bootCoreId
      (LockSet.singleton ⟨.objStore, SeLe4n.ObjId.ofNat 0⟩ .write) s₁))

private def runOrderingChecks : IO Unit := do
  IO.println "--- §5 SM3.C.5 / SM3.C.6 — Ordering properties ---"
  -- Empty acquire order is empty.
  assertBool "acquireOrder LockSet.empty = []"
    (decide (acquireOrder LockSet.empty = ([] : List LockId)))
  -- Empty release order is empty.
  assertBool "releaseOrder LockSet.empty = []"
    (decide (releaseOrder LockSet.empty = ([] : List LockId)))
  -- Singleton acquire order has one element.
  let l : LockId := ⟨.tcb, SeLe4n.ObjId.ofNat 1⟩
  assertBool "acquireOrder singleton = [l]"
    (decide (acquireOrder (LockSet.singleton l .write) = [l]))
  -- Release order is reverse of acquire order.
  assertBool "releaseOrder = acquireOrder.reverse on singleton"
    (decide (releaseOrder (LockSet.singleton l .write)
              = (acquireOrder (LockSet.singleton l .write)).reverse))

private def runWithLockSetComputationChecks : IO Unit := do
  IO.println "--- §6 SM3.C.7 — withLockSet computation atomic decomposition ---"
  -- The trivial action that just returns the state and 0:
  let trivialAction (s : SystemState) : SystemState × Nat := (s, 0)
  let result := withLockSet LockSet.empty bootCoreId trivialAction (default : SystemState)
  assertBool "withLockSet returns action's second component"
    (decide (result.snd = 0))
  -- Empty lock set: withLockSet's post-state is the action's post-state.
  -- The empty lock set means no acquire/release happens, so input = output state.
  assertBool "withLockSet empty: post-state objStoreLock = unheld"
    (decide (result.fst.objStoreLock = RwLockState.unheld))

private def runDynamicChainChecks : IO Unit := do
  IO.println "--- §7 SM3.C.11 — Dynamic chain walker ---"
  -- MAX_PIP_RETRIES = 64.
  assertBool "MAX_PIP_RETRIES = 64"
    (decide (MAX_PIP_RETRIES = 64))
  -- MAX_PIP_RETRIES is positive.
  assertBool "MAX_PIP_RETRIES > 0"
    (decide (MAX_PIP_RETRIES > 0))
  -- Singleton path has length 1.
  let p := PipChainPath.singleton ⟨1⟩
  assertBool "PipChainPath.singleton has length 1"
    (decide (p.length = 1))
  -- Singleton path's startTid is the input.
  assertBool "PipChainPath.singleton startTid = input"
    (decide (p.startTid = ⟨1⟩))
  -- On default state, walkAndAcquire terminates immediately (no chain).
  let outcome := walkAndAcquire (default : SystemState) ⟨1⟩
  match outcome with
  | .terminated path =>
    assertBool "walkAndAcquire on default state: .terminated"
      (decide (path.path.length = 1))
    -- SM3.C.11.e: the terminated path is bounded by MAX_PIP_RETRIES + 1.
    assertBool "walkAndAcquire terminated path length ≤ MAX_PIP_RETRIES + 1"
      (decide (path.path.length ≤ MAX_PIP_RETRIES + 1))
    -- SM3.C.11.c (audit-pass-2): the terminated path follows the blocking
    -- graph — wires dynamicChainHeld's conjunct 4 to the walker.  On the
    -- empty default state the singleton path trivially follows it.
    assertBool "walkAndAcquire terminated path follows blockingServer (chain conjunct)"
      (decide (chainFollowsBlockingServer (default : SystemState) path.path))
    -- And it starts at the requested start (dynamicChainHeld conjunct 3).
    assertBool "walkAndAcquire terminated path starts at startTid"
      (decide (path.path.head? = some path.startTid))
  | .extended _ =>
    assertBool "walkAndAcquire .extended on default (unexpected)" false
  | .exhausted =>
    assertBool "walkAndAcquire .exhausted on default (unexpected)" false
  -- chainFollowsBlockingServer base cases: empty and singleton are trivially true.
  assertBool "chainFollowsBlockingServer [] (empty list trivially follows)"
    (decide (chainFollowsBlockingServer (default : SystemState) ([] : List SeLe4n.ThreadId)))
  assertBool "chainFollowsBlockingServer [tid] (singleton trivially follows)"
    (decide (chainFollowsBlockingServer (default : SystemState) [(⟨3⟩ : SeLe4n.ThreadId)]))
  -- SM3.C.11.e: fuel = 0 always exhausts (the walker never loops forever).
  let outcomeZero := walkAndAcquire (default : SystemState) ⟨1⟩ 0
  match outcomeZero with
  | .exhausted =>
    assertBool "walkAndAcquire with fuel 0 is .exhausted (termination)" true
  | _ =>
    assertBool "walkAndAcquire fuel 0 should exhaust" false

private def runInventoryChecks : IO Unit := do
  IO.println "--- §8 SM3.C — Inventory aggregator ---"
  -- The inventory has 86 entries (Group-B: +5 held, +4 atomicity, +6 dynamicChain).
  assertBool "withLockSetTheorems.length = 86"
    (decide (withLockSetTheorems.length = 86))
  -- Per-category counts.
  assertBool "withLockSetTheorems combinator count = 31"
    (decide ((withLockSetTheorems.filter
      (fun t => t.category == .combinator)).length = 31))
  assertBool "withLockSetTheorems held count = 16"
    (decide ((withLockSetTheorems.filter
      (fun t => t.category == .held)).length = 16))
  assertBool "withLockSetTheorems ordering count = 3"
    (decide ((withLockSetTheorems.filter
      (fun t => t.category == .ordering)).length = 3))
  assertBool "withLockSetTheorems atomicity count = 13"
    (decide ((withLockSetTheorems.filter
      (fun t => t.category == .atomicity)).length = 13))
  assertBool "withLockSetTheorems dynamicChain count = 23"
    (decide ((withLockSetTheorems.filter
      (fun t => t.category == .dynamicChain)).length = 23))
  -- Partition-sum is total.
  assertBool "withLockSetTheorems partition sum = total"
    (decide (
      (withLockSetTheorems.filter (fun t => t.category == .combinator)).length +
      (withLockSetTheorems.filter (fun t => t.category == .held)).length +
      (withLockSetTheorems.filter (fun t => t.category == .ordering)).length +
      (withLockSetTheorems.filter (fun t => t.category == .atomicity)).length +
      (withLockSetTheorems.filter (fun t => t.category == .dynamicChain)).length =
      withLockSetTheorems.length))

private def runStructuralPreservationChecks : IO Unit := do
  IO.println "--- §9 SM3.C.8 — Substantive structural preservation ---"
  let s₀ : SystemState := default
  -- Acquiring a per-object (non-objStore) lock preserves objStoreLock.
  let sTcb := acquireLockOnObject s₀ bootCoreId ⟨.tcb, SeLe4n.ObjId.ofNat 5⟩ .write
  assertBool "acquireLockOnObject .tcb preserves objStoreLock (per-object isolation)"
    (decide (sTcb.objStoreLock = s₀.objStoreLock))
  -- Releasing a per-object lock preserves objStoreLock.
  let sRelEp := releaseLockOnObject s₀ bootCoreId ⟨.endpoint, SeLe4n.ObjId.ofNat 7⟩ .write
  assertBool "releaseLockOnObject .endpoint preserves objStoreLock"
    (decide (sRelEp.objStoreLock = s₀.objStoreLock))
  -- updateObjectAt preserves objStoreLock (identity transform on absent obj).
  let sUpd := updateObjectAt s₀ (SeLe4n.ObjId.ofNat 3) (fun o => o)
  assertBool "updateObjectAt preserves objStoreLock"
    (decide (sUpd.objStoreLock = RwLockState.unheld))
  -- Acquiring objStore in read mode does change objStoreLock (the table lock).
  let sObjStore := acquireLockOnObject s₀ bootCoreId ⟨.objStore, SeLe4n.ObjId.ofNat 0⟩ .read
  assertBool "acquireLockOnObject .objStore .read DOES add bootCoreId to readers"
    (decide (bootCoreId ∈ sObjStore.objStoreLock.readers))

private def runAuditPass1Checks : IO Unit := do
  IO.println "--- §10 SM3.C audit-pass-1 — codex review closures ---"
  let s₀ : SystemState := default
  -- Comment 3: acquiring an AVAILABLE objStore lock GRANTS (the action
  -- would run with the lock genuinely held), in both modes.
  let sW := acquireLockOnObject s₀ bootCoreId ⟨.objStore, SeLe4n.ObjId.ofNat 0⟩ .write
  assertBool "Comment 3: acquiring available objStore .write GRANTS (writerHeld = some core)"
    (decide (sW.objStoreLock.writerHeld = some bootCoreId))
  assertBool "Comment 3: post-acquire lockHeld holds for objStore .write"
    (decide (lockHeld bootCoreId ⟨.objStore, SeLe4n.ObjId.ofNat 0⟩ .write sW))
  let sR := acquireLockOnObject s₀ bootCoreId ⟨.objStore, SeLe4n.ObjId.ofNat 0⟩ .read
  assertBool "Comment 3: post-acquire lockHeld holds for objStore .read"
    (decide (lockHeld bootCoreId ⟨.objStore, SeLe4n.ObjId.ofNat 0⟩ .read sR))
  -- Comment 4: acquire then release returns objStore lock to unheld — no leak.
  let sRT := releaseLockOnObject sW bootCoreId ⟨.objStore, SeLe4n.ObjId.ofNat 0⟩ .write
  assertBool "Comment 4: acquire+release round-trips objStore lock to unheld (no waiter leak)"
    (decide (sRT.objStoreLock = RwLockState.unheld))
  -- Abstract grant theorem holds for both modes (decidable witness).
  assertBool "Comment 3: RwLockState.unheld_acquire_grants .write (writerHeld set)"
    (decide ((RwLockState.unheld.applyOp ((AccessMode.write).toAcquireOp bootCoreId)).writerHeld
              = some bootCoreId))
  assertBool "Comment 4: unheld acquire+release round-trip .read = unheld"
    (decide ((RwLockState.unheld.applyOp ((AccessMode.read).toAcquireOp bootCoreId)).applyOp
              ((AccessMode.read).toReleaseOp bootCoreId) = RwLockState.unheld))
  -- Comment 5: kind-mismatched LockId fails closed.  On the default
  -- (empty) state, a .tcb-kinded LockId resolves to no object, so
  -- updateObjectLockAt is a no-op (objStoreLock untouched, objects
  -- unchanged).  The kind-check routes through LockId.lookup which
  -- returns none on absence/mismatch.
  let sKind := updateObjectLockAt s₀ ⟨.tcb, SeLe4n.ObjId.ofNat 42⟩
    ((AccessMode.write).toAcquireOp bootCoreId)
  assertBool "Comment 5: updateObjectLockAt on absent/mismatched kind is no-op (objStoreLock)"
    (decide (sKind.objStoreLock = RwLockState.unheld))

private def runIntegrationChecks : IO Unit := do
  IO.println "--- §11 SM3.B ↔ SM3.C integration (withLockSet/lockSetHeld on real lockSet_<τ>) ---"
  let s₀ : SystemState := default
  -- Build a real per-transition lockSet: notificationWait touches the
  -- caller TCB (write, level 3), the caller CNode (read, level 2), and
  -- the notification (write, level 5).
  let nwSet := lockSet_notificationWait ⟨5⟩ (SeLe4n.ObjId.ofNat 10) (SeLe4n.ObjId.ofNat 20)
  -- The lockSet has exactly 3 declared locks.
  assertBool "lockSet_notificationWait has 3 locks"
    (decide (nwSet.size = 3))
  -- SM3.C.5 on a REAL multi-lock set: the canonical acquire order is
  -- LockId-ascending — by hierarchy level here: cnode (2) < tcb (3) <
  -- notification (5).  This exercises the actual mergeSort, not a
  -- singleton.
  assertBool "acquireOrder(notificationWait) kinds = [cnode, tcb, notification] (hierarchy sort)"
    (decide ((acquireOrder nwSet).map (·.kind)
              = [LockKind.cnode, LockKind.tcb, LockKind.notification]))
  assertBool "acquireOrder(notificationWait) length = 3"
    (decide ((acquireOrder nwSet).length = 3))
  -- withLockSet over the REAL lockSet computes: the action's value flows
  -- through, and (since the set has no objStore lock) objStoreLock is
  -- preserved across the acquire/release folds.
  let nwResult := withLockSet nwSet bootCoreId (fun s => (s, (99 : Nat))) s₀
  assertBool "withLockSet(notificationWait) returns the action's value"
    (decide (nwResult.snd = 99))
  assertBool "withLockSet(notificationWait) preserves objStoreLock (no objStore lock in set)"
    (decide (nwResult.fst.objStoreLock = RwLockState.unheld))
  -- lockSetHeld over the REAL lockSet on the empty default state is False
  -- (none of the referenced objects exist, so no lock is held).
  assertBool "¬ lockSetHeld(notificationWait) on default state"
    (decide (¬ lockSetHeld bootCoreId nwSet s₀))
  -- Within-level (objId) tie-break: cspaceMove locks two CNodes (level 2)
  -- + caller TCB (read, level 3).  The two cnodes sort by objId.val
  -- ascending (7 before 9), then the tcb.
  let cmSet := lockSet_cspaceMove ⟨5⟩ (SeLe4n.ObjId.ofNat 7) (SeLe4n.ObjId.ofNat 9)
  assertBool "acquireOrder(cspaceMove) kinds = [cnode, cnode, tcb] (within-level objId sort)"
    (decide ((acquireOrder cmSet).map (·.kind)
              = [LockKind.cnode, LockKind.cnode, LockKind.tcb]))
  assertBool "acquireOrder(cspaceMove) cnode objIds ascending = [7, 9]"
    (decide (((acquireOrder cmSet).filterMap
        (fun l => if l.kind = .cnode then some l.objId.val else none)) = [7, 9]))
  -- SM3.C.5 ordering theorem applies to the real lockSet: acquireOrder is
  -- Pairwise (· ≤ ·).  (Decidable check mirroring lockSet_acquired_in_order.)
  assertBool "acquireOrder(cspaceMove) is Pairwise (· ≤ ·) [SM3.C.5 on real set]"
    (decide ((acquireOrder cmSet).Pairwise (· ≤ ·)))
  -- acquireAll over the real sequence on the empty default state leaves
  -- objStoreLock unheld (all per-object acquires fail-closed: objects absent).
  let cmAcq := acquireAll bootCoreId cmSet.lockAcquireSequence s₀
  assertBool "acquireAll(cspaceMove seq) on default preserves objStoreLock"
    (decide (cmAcq.objStoreLock = RwLockState.unheld))
  -- endpointSend with a receiver: 4 locks (caller tcb, cnode, endpoint,
  -- receiver tcb).  Exercises the Option-extended lockSet + sort.
  let esSet := lockSet_endpointSend ⟨5⟩ (SeLe4n.ObjId.ofNat 10)
    (SeLe4n.ObjId.ofNat 30) (some ⟨8⟩)
  assertBool "lockSet_endpointSend (with receiver) has 4 locks"
    (decide (esSet.size = 4))
  assertBool "acquireOrder(endpointSend) kinds = [cnode, tcb, tcb, endpoint]"
    (decide ((acquireOrder esSet).map (·.kind)
              = [LockKind.cnode, LockKind.tcb, LockKind.tcb, LockKind.endpoint]))

-- ============================================================================
-- §12 — Test fixtures for establishment / chain checks
-- ============================================================================

/-- A minimal ready TCB (ipcState defaults to `.ready` ⟹ `blockingServer` none). -/
private def mkTcbReady (n : Nat) : TCB :=
  { tid := ThreadId.ofNat n, priority := ⟨10⟩, domain := ⟨0⟩,
    cspaceRoot := SeLe4n.ObjId.ofNat 0, vspaceRoot := SeLe4n.ObjId.ofNat 0,
    ipcBuffer := SeLe4n.VAddr.ofNat 0 }

/-- A TCB reply-blocked on `server` ⟹ `blockingServer tid = some server`. -/
private def mkTcbBlockedOn (n server : Nat) : TCB :=
  { mkTcbReady n with
    ipcState := .blockedOnReply (SeLe4n.ObjId.ofNat 0) (some (ThreadId.ofNat server)) }

/-- A minimal CNode (default `lock = unheld`). -/
private def mkCNodeFixture : CNode :=
  { depth := 8, guardWidth := 0, guardValue := 0, radixWidth := 8,
    slots := SeLe4n.UniqueSlotMap.empty }

/-- A 3-TCB blocking chain `5 → 7 → 10` (10 terminates).  ObjIds ascending so
the abstract walker commits the full path. -/
private def chainState : SystemState :=
  let d : SystemState := default
  let o := d.objects.insert (ThreadId.ofNat 5).toObjId (.tcb (mkTcbBlockedOn 5 7))
  let o := o.insert (ThreadId.ofNat 7).toObjId (.tcb (mkTcbBlockedOn 7 10))
  let o := o.insert (ThreadId.ofNat 10).toObjId (.tcb (mkTcbReady 10))
  { d with objects := o }

/-- A state with caller TCB 5, src CNode 7, dst CNode 9 — all present, unheld.
Used to exercise the full lock-set establishment over a real `lockSet_<τ>`. -/
private def cspaceMoveFixture : SystemState :=
  let d : SystemState := default
  let o := d.objects.insert (ThreadId.ofNat 5).toObjId (.tcb (mkTcbReady 5))
  let o := o.insert (SeLe4n.ObjId.ofNat 7) (.cnode mkCNodeFixture)
  let o := o.insert (SeLe4n.ObjId.ofNat 9) (.cnode mkCNodeFixture)
  { d with objects := o }

private def runRaiiReleaseChecks : IO Unit := do
  IO.println "--- §12 SM3.C.10 — RAII release discipline (panic/early-exit) ---"
  let s₀ : SystemState := default
  let objStoreSet := LockSet.singleton ⟨.objStore, SeLe4n.ObjId.ofNat 0⟩ .write
  -- A "failing" action: it returns the (lock-acquired) state unchanged with an
  -- error value, modelling an early-exit / panic that does NOT release locks
  -- itself.  withLockSet's shrinking phase must still release them.
  let failingAction : SystemState → SystemState × Bool := fun st => (st, false)
  let result := withLockSet objStoreSet bootCoreId failingAction s₀
  -- The action's (error) value flows through.
  assertBool "RAII: failing action's value flows through withLockSet"
    (decide (result.snd = false))
  -- Despite the failing action, the table lock is RELEASED on exit (no leak).
  assertBool "RAII: objStore lock released after failing action (round-trip to unheld)"
    (decide (result.fst.objStoreLock = RwLockState.unheld))
  -- lockSetHeld is false on the post-withLockSet state (locks released).
  assertBool "RAII: ¬ lockSetHeld after withLockSet (shrinking phase released all)"
    (decide (¬ lockSetHeld bootCoreId objStoreSet result.fst))
  -- A read-mode failing action: same release guarantee.
  let readSet := LockSet.singleton ⟨.objStore, SeLe4n.ObjId.ofNat 0⟩ .read
  let resultR := withLockSet readSet bootCoreId failingAction s₀
  assertBool "RAII: objStore read lock released after failing action"
    (decide (resultR.fst.objStoreLock = RwLockState.unheld))
  -- The per-lock round-trip witness (SM3.C.8) underlies this at the abstract level.
  assertBool "RAII: acquireLockOnObject_objStore_release_roundtrip witness (write)"
    (decide ((releaseLockOnObject
      (acquireLockOnObject s₀ bootCoreId ⟨.objStore, SeLe4n.ObjId.ofNat 0⟩ .write)
      bootCoreId ⟨.objStore, SeLe4n.ObjId.ofNat 0⟩ .write).objStoreLock
      = RwLockState.unheld))

private def runEstablishmentChecks : IO Unit := do
  IO.println "--- §13 SM3.C.8 — acquire ESTABLISHES lockHeld / lockSetHeld (populated) ---"
  -- Single modeled establishment: a present, unheld TCB becomes write-held.
  let sTcb : SystemState := { (default : SystemState) with
    objects := (default : SystemState).objects.insert
      (ThreadId.ofNat 5).toObjId (.tcb (mkTcbReady 5)) }
  let tcbLockId : LockId := ⟨.tcb, (ThreadId.ofNat 5).toObjId⟩
  let sAcq := acquireLockOnObject sTcb bootCoreId tcbLockId .write
  assertBool "establish: acquiring present+unheld TCB write-lock ⟹ lockHeld holds"
    (decide (lockHeld bootCoreId tcbLockId .write sAcq))
  -- Read-mode establishment on a present CNode.
  let sCn : SystemState := { (default : SystemState) with
    objects := (default : SystemState).objects.insert
      (SeLe4n.ObjId.ofNat 7) (.cnode mkCNodeFixture) }
  let cnLockId : LockId := ⟨.cnode, SeLe4n.ObjId.ofNat 7⟩
  let sAcqR := acquireLockOnObject sCn bootCoreId cnLockId .read
  assertBool "establish: acquiring present+unheld CNode read-lock ⟹ lockHeld holds"
    (decide (lockHeld bootCoreId cnLockId .read sAcqR))
  -- Multi-lock establishment over a REAL lockSet on a fully-populated state:
  -- acquireAll establishes lockSetHeld for the entire declared footprint.
  let cmSet := lockSet_cspaceMove ⟨5⟩ (SeLe4n.ObjId.ofNat 7) (SeLe4n.ObjId.ofNat 9)
  let cmAcq := acquireAll bootCoreId cmSet.lockAcquireSequence cspaceMoveFixture
  assertBool "establish: acquireAll over cspaceMove ⟹ lockSetHeld (all 3 locks held)"
    (decide (lockSetHeld bootCoreId cmSet cmAcq))
  -- Each individual declared lock is held post-acquire.
  assertBool "establish: caller TCB read-lock held after cspaceMove acquireAll"
    (decide (lockHeld bootCoreId ⟨.tcb, (ThreadId.ofNat 5).toObjId⟩ .read cmAcq))
  assertBool "establish: dst CNode write-lock held after cspaceMove acquireAll"
    (decide (lockHeld bootCoreId ⟨.cnode, SeLe4n.ObjId.ofNat 9⟩ .write cmAcq))

private def runObserverAtomicChecks : IO Unit := do
  IO.println "--- §14 SM3.C.7 — observational atomicity (lock-insensitive observer) ---"
  -- A lock-insensitive observer: the kind tag of the object stored at key 5.
  -- Lock acquisition advances RwLockState but NEVER the variant, so this
  -- projection is invariant across the acquire/release folds.
  let observe : SystemState → Option KernelObjectType :=
    fun s => (s.objects.get? (ThreadId.ofNat 5).toObjId).map KernelObject.objectType
  let s : SystemState := { (default : SystemState) with
    objects := (default : SystemState).objects.insert
      (ThreadId.ofNat 5).toObjId (.tcb (mkTcbReady 5)) }
  let tcbSet := LockSet.singleton ⟨.tcb, (ThreadId.ofNat 5).toObjId⟩ .write
  -- Acquire fold is invisible to the observer.
  assertBool "observer: acquireAll invisible to objectType projection"
    (decide (observe (acquireAll bootCoreId tcbSet.lockAcquireSequence s) = observe s))
  -- The whole withLockSet (identity action) is invisible to the observer.
  let wls := withLockSet tcbSet bootCoreId (fun st => (st, ())) s
  assertBool "observer: withLockSet (identity action) invisible to objectType projection"
    (decide (observe wls.fst = observe s))
  -- Observer cannot see the lock machinery: pre and post projections agree even
  -- though the lock state DID change mid-action (acquired then released).
  assertBool "observer: post-state objectType at key 5 = .tcb (unchanged by 2PL)"
    (decide (observe wls.fst = some KernelObjectType.tcb))

private def runMultiStepChainChecks : IO Unit := do
  IO.println "--- §15 SM3.C.11.f — multi-step PIP chain (real blocking graph) ---"
  -- The walker discovers the full 3-step chain 5 → 7 → 10.
  match walkAndAcquire chainState ⟨5⟩ with
  | .terminated path =>
      assertBool "multi-step: walkAndAcquire terminates with path length 3"
        (decide (path.path.length = 3))
      assertBool "multi-step: discovered path = [5, 7, 10]"
        (decide (path.path = [⟨5⟩, ⟨7⟩, ⟨10⟩]))
      -- Conjunct 4 on the PRE-acquire state (walker invariant).
      assertBool "multi-step: path follows blockingServer on chainState"
        (decide (chainFollowsBlockingServer chainState path.path))
      -- Acquire the chain write-locks; verify conjuncts 1 & 4 on the ACQUIRED state.
      let sAcq := acquireAll bootCoreId (chainLockSeq path) chainState
      assertBool "multi-step: TCB 5 write-locked after acquireAll (conjunct 1)"
        (decide (lockHeld bootCoreId ⟨.tcb, (⟨5⟩ : ThreadId).toObjId⟩ .write sAcq))
      assertBool "multi-step: TCB 7 write-locked after acquireAll (conjunct 1)"
        (decide (lockHeld bootCoreId ⟨.tcb, (⟨7⟩ : ThreadId).toObjId⟩ .write sAcq))
      assertBool "multi-step: TCB 10 write-locked after acquireAll (conjunct 1)"
        (decide (lockHeld bootCoreId ⟨.tcb, (⟨10⟩ : ThreadId).toObjId⟩ .write sAcq))
      assertBool "multi-step: chainFollowsBlockingServer transported to acquired state (conjunct 4)"
        (decide (chainFollowsBlockingServer sAcq path.path))
  | _ =>
      assertBool "multi-step: walkAndAcquire chainState ⟨5⟩ should terminate" false
  -- Bounded retries: a chain longer than the fuel budget exhausts rather than
  -- looping.  Fuel 2 cannot reach the terminating step of a 3-link chain.
  match walkAndAcquire chainState ⟨5⟩ 2 with
  | .exhausted => assertBool "bounded: fuel 2 exhausts on a 3-link chain" true
  | _ => assertBool "bounded: fuel 2 should exhaust on a 3-link chain" false
  match walkAndAcquire chainState ⟨5⟩ 3 with
  | .terminated p =>
      assertBool "bounded: fuel 3 terminates the 3-link chain" (decide (p.path.length = 3))
  | _ => assertBool "bounded: fuel 3 should terminate the 3-link chain" false
  -- Two-core deadlock-freedom: under the ascending discipline, mutual wait is
  -- impossible (decidable instantiation of dynamic_chain_no_mutual_wait).
  let l5 : LockId := ⟨.tcb, SeLe4n.ObjId.ofNat 5⟩
  let l10 : LockId := ⟨.tcb, SeLe4n.ObjId.ofNat 10⟩
  -- The arithmetic heart of dynamic_chain_deadlock_free: under the ascending
  -- discipline a 2-cycle would require 5 < 10 AND 10 < 5 — impossible.
  assertBool "two-core: ascending ObjIds preclude a 2-cycle (5<10 ∧ 10<5 impossible)"
    (decide (¬ (l5.objId.val < l10.objId.val ∧ l10.objId.val < l5.objId.val)))
  -- Two cores walking DISJOINT chains share no lock ObjId ⟹ no contention.
  let chainA := chainLockSeq ⟨⟨5⟩, [⟨5⟩, ⟨7⟩], by rfl⟩
  let chainB := chainLockSeq ⟨⟨20⟩, [⟨20⟩, ⟨25⟩], by rfl⟩
  assertBool "two-core: disjoint chains [5,7] / [20,25] share no lock objId"
    (decide ((chainA.map (·.fst.objId.val)).all (fun a =>
      (chainB.map (·.fst.objId.val)).all (fun b => a ≠ b))))

def runWithLockSetChecks : IO Unit := do
  IO.println "WS-SM SM3.C — withLockSet 2PL discipline regression suite"
  IO.println "========================================================="
  runWithLockSetEmptyChecks
  runAcquireReleasePrimitiveChecks
  runAcquireAllChecks
  runLockSetHeldChecks
  runOrderingChecks
  runWithLockSetComputationChecks
  runDynamicChainChecks
  runStructuralPreservationChecks
  runAuditPass1Checks
  runIntegrationChecks
  runRaiiReleaseChecks
  runEstablishmentChecks
  runObserverAtomicChecks
  runMultiStepChainChecks
  runInventoryChecks
  IO.println "========================================================="
  IO.println "All SM3.C withLockSet checks PASS."

end SeLe4n.Testing.WithLockSet

def main : IO Unit :=
  SeLe4n.Testing.WithLockSet.runWithLockSetChecks
