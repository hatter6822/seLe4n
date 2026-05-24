-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Concurrency.Locks.WithLockSet
import SeLe4n.Kernel.Concurrency.Locks.LockSetHeld
import SeLe4n.Kernel.Concurrency.Locks.LockSet2PL
import SeLe4n.Kernel.Concurrency.Locks.DynamicChainExtension

/-!
# WS-SM SM3.C — Theorem inventory

Aggregates the SM3.C substantive theorems into a single typed
inventory with size and per-category witnesses.  Mirrors the
SM3.A `PerObjectLockInventory.lean` and SM3.B
`LockSetInventory.lean` patterns.

The inventory has five categories matching the plan §5.3
sub-tasks:

* `.combinator` — SM3.C.1 / C.2 (`withLockSet`,
  `acquireLockOnObject` / `releaseLockOnObject`,
  `acquireAll` / `releaseAll`, plus the `.empty`,
  `_unfold`, `_decomposition`, `_fst`, `_snd` witnesses, plus
  `KernelObject.updateLock` and its 7 per-variant `@[simp]`
  unfolds, plus `objectLockOf_updateLock` /
  `updateLock_preserves_lockKind` / `updateLock_preserves_objectType`,
  plus the four `_reply` / `_page` simp lemmas, plus the SM3.C.8
  structural-preservation foundation lemmas
  `updateObjectAt_preserves_objStoreLock`,
  `acquireLockOnObject_preserves_objStoreLock_of_modeled`,
  `releaseLockOnObject_preserves_objStoreLock_of_modeled`,
  `updateObjectAt_preserves_objectType_at`).
* `.held` — SM3.C.4 (`lockHeld` / `lockSetHeld` predicates +
  decidability + subset-monotone + default-state-empty
  witnesses).
* `.ordering` — SM3.C.5 / C.6 (`lockSet_acquired_in_order`,
  `lockSet_released_in_reverse`,
  `releaseOrder_eq_acquireOrder_reverse`).
* `.atomicity` — SM3.C.7 / C.8 (`withLockSet_three_phase_decomposition`,
  `lockSet_atomic_under_2pl`, `lockSet_invariant_preserved`,
  `withLockSet_invariant_preserved`, the worked instantiation
  `acquireAll_preserves_objStoreLock_wf`,
  `acquireLockOnObject_objStore_establishes_lockHeld`,
  `acquireLockOnObject_objStore_release_roundtrip`,
  `withLockSet_satisfies_strict_2PL`, `withLockSet_computation`).
* `.dynamicChain` — SM3.C.11 (`PipChainPath`, `walkStep`,
  `walkAndAcquire`, `withDynamicChainExtension`, `dynamicChainHeld`,
  the `chainFollowsBlockingServer` predicate, the deadlock-freedom
  witness `walkAndAcquire_path_ascending_in_ObjId_if_terminated`, the
  producer-connection theorems `walkStep_extended_blockingServer` /
  `walkAndAcquire_terminated_followsChain` /
  `walkAndAcquire_terminated_satisfies_path_structure`, plus the
  SM3.C.11.e termination witnesses
  `walkAndAcquireAux_terminated_length_le` /
  `walkAndAcquire_terminated_length_bounded` / `walkAndAcquire_total`).

## Identifier validation

Identifiers are compile-time-validated via the `wlst!` macro,
mirroring SM3.A's `polt!` / SM3.B's `lkst!` pattern.  A typo or
rename fails the build at this module's elaboration step.
-/

namespace SeLe4n.Kernel.Concurrency

open SeLe4n
open SeLe4n.Model

/-- WS-SM SM3.C: category tag for the SM3.C theorem inventory. -/
inductive WithLockSetCategory where
  /-- `withLockSet` combinator + per-object acquire/release + helpers. -/
  | combinator
  /-- `lockHeld` / `lockSetHeld` predicates + decidability. -/
  | held
  /-- Ordering theorems (SM3.C.5 / SM3.C.6). -/
  | ordering
  /-- Atomicity / invariant-preservation theorems (SM3.C.7 / SM3.C.8). -/
  | atomicity
  /-- Dynamic PIP-chain-walk machinery (SM3.C.11). -/
  | dynamicChain
  deriving Repr, DecidableEq, Inhabited

/-- WS-SM SM3.C: a theorem entry in the SM3.C inventory.

Records a description, the theorem's fully-qualified name as a
`String`, a compile-time elaboration witness, and a category tag.

The `_elabCheck` field is produced by the `wlst!` macro which
emits a `let _ := @<ident>; ()` term.  The macro forces Lean's
elaborator to resolve the referenced declaration at construction
time, so a typo or stale rename fails to elaborate with "unknown
identifier '<name>'". -/
structure WithLockSetTheorem where
  description : String
  identifier  : String
  _elabCheck  : Unit
  category    : WithLockSetCategory
  deriving Repr, Inhabited

/-- WS-SM SM3.C: build a `WithLockSetTheorem` with a compile-time-
validated identifier.  See SM3.A's `polt!` / SM3.B's `lkst!` for
the equivalent patterns. -/
syntax (name := wlstMacro) "wlst!" str ident term : term

macro_rules
  | `(wlst! $desc:str $ident:ident $cat:term) => do
      let nameStr : String := ident.getId.toString
      let nameStxLit := Lean.Syntax.mkStrLit nameStr
      `(({ description := $desc,
           identifier := $nameStxLit,
           _elabCheck := (let _ := @$ident; ()),
           category := $cat
         } : WithLockSetTheorem))

/-- WS-SM SM3.C: substantive theorem inventory.  Every entry's
identifier is compile-time-validated. -/
def withLockSetTheorems : List WithLockSetTheorem :=
  [-- §1 combinator (24 entries: combinator def + per-object acquire/release +
    -- acquireAll/releaseAll + KernelObject.updateLock + 7 simp lemmas + helpers)
    wlst! "withLockSet — the SM3.C.1 2PL combinator"
      withLockSet .combinator,
    wlst! "withLockSet_empty: combinator on empty lock set reduces to action"
      withLockSet_empty .combinator,
    wlst! "withLockSet_unfold: structural decomposition into three phases"
      withLockSet_unfold .combinator,
    wlst! "withLockSet_eq_decomposition: explicit three-phase decomposition"
      withLockSet_eq_decomposition .combinator,
    wlst! "withLockSet_fst: first-component projection (post-release state)"
      withLockSet_fst .combinator,
    wlst! "withLockSet_snd: second-component projection (action result)"
      withLockSet_snd .combinator,
    wlst! "acquireLockOnObject — per-object lock acquire primitive"
      acquireLockOnObject .combinator,
    wlst! "releaseLockOnObject — per-object lock release primitive"
      releaseLockOnObject .combinator,
    wlst! "acquireLockOnObject_reply: .reply LockId is no-op (SM3.A.5 N/A)"
      acquireLockOnObject_reply .combinator,
    wlst! "acquireLockOnObject_page: .page LockId is no-op (SM3.A.8 N/A)"
      acquireLockOnObject_page .combinator,
    wlst! "releaseLockOnObject_reply: .reply LockId is no-op"
      releaseLockOnObject_reply .combinator,
    wlst! "releaseLockOnObject_page: .page LockId is no-op"
      releaseLockOnObject_page .combinator,
    wlst! "acquireAll: fold acquireLockOnObject over a sorted list"
      acquireAll .combinator,
    wlst! "releaseAll: fold releaseLockOnObject over a sorted list"
      releaseAll .combinator,
    wlst! "acquireAll_nil: acquireAll on empty list is identity"
      acquireAll_nil .combinator,
    wlst! "releaseAll_nil: releaseAll on empty list is identity"
      releaseAll_nil .combinator,
    wlst! "acquireAll_cons: acquireAll on cons unfolds to head-then-tail"
      acquireAll_cons .combinator,
    wlst! "releaseAll_cons: releaseAll on cons unfolds to head-then-tail"
      releaseAll_cons .combinator,
    wlst! "updateObjectAt: in-place kernel-object update helper"
      updateObjectAt .combinator,
    wlst! "updateObjectLockAt: kind-checked lock update (audit-pass-1 Comment 5)"
      updateObjectLockAt .combinator,
    wlst! "updateObjectLockAt_preserves_objStoreLock: kind-checked update preserves table lock"
      updateObjectLockAt_preserves_objStoreLock .combinator,
    wlst! "AccessMode.toAcquireOp: mode → acquire RwLockOp"
      AccessMode.toAcquireOp .combinator,
    wlst! "AccessMode.toReleaseOp: mode → release RwLockOp"
      AccessMode.toReleaseOp .combinator,
    wlst! "KernelObject.updateLock: apply RwLockOp to per-object lock"
      SeLe4n.Model.KernelObject.updateLock .combinator,
    wlst! "KernelObject.updateLock_preserves_lockKind"
      SeLe4n.Model.KernelObject.updateLock_preserves_lockKind .combinator,
    wlst! "KernelObject.updateLock_preserves_objectType: kind tag invariant"
      SeLe4n.Model.KernelObject.updateLock_preserves_objectType .combinator,
    wlst! "KernelObject.objectLockOf_updateLock: post-state lock equals applyOp"
      SeLe4n.Model.KernelObject.objectLockOf_updateLock .combinator,
    wlst! "updateObjectAt_preserves_objStoreLock: lock-only update preserves table lock"
      updateObjectAt_preserves_objStoreLock .combinator,
    wlst! "acquireLockOnObject_preserves_objStoreLock_of_modeled: per-object acquire preserves table lock"
      acquireLockOnObject_preserves_objStoreLock_of_modeled .combinator,
    wlst! "releaseLockOnObject_preserves_objStoreLock_of_modeled: per-object release preserves table lock"
      releaseLockOnObject_preserves_objStoreLock_of_modeled .combinator,
    wlst! "updateObjectAt_preserves_objectType_at: lock update preserves kind tag at every key"
      updateObjectAt_preserves_objectType_at .combinator,
    -- §2 held (8 entries: lockHeld + lockSetHeld + decidability + subset
    -- monotonicity + default-state-empty witnesses)
    wlst! "RwLockState.coreHolds: per-state core-holds predicate"
      RwLockState.coreHolds .held,
    wlst! "lockHeld: per-lock held predicate"
      lockHeld .held,
    wlst! "lockHeld_reply: .reply LockId always not held (SM3.A.5 N/A)"
      lockHeld_reply .held,
    wlst! "lockHeld_page: .page LockId always not held (SM3.A.8 N/A)"
      lockHeld_page .held,
    wlst! "lockSetHeld: SMP-migration precondition (Corollary 2.1.11)"
      lockSetHeld .held,
    wlst! "lockSetHeld_empty: holding empty set is vacuously true"
      lockSetHeld_empty .held,
    wlst! "lockSetHeld_singleton: singleton reduces to single-lock predicate"
      lockSetHeld_singleton .held,
    wlst! "lockSetHeld_subset: monotone — held on larger set implies held on smaller"
      lockSetHeld_subset .held,
    wlst! "lockSetHeld_default_iff_empty: default state holds no locks"
      lockSetHeld_default_iff_empty .held,
    wlst! "RwLockState.unheld_acquire_grants: acquiring an available lock GRANTS (audit-pass-1 Comment 3)"
      RwLockState.unheld_acquire_grants .held,
    wlst! "RwLockState.unheld_acquire_release_roundtrip: acquire+release no waiter leak (audit-pass-1 Comment 4)"
      RwLockState.unheld_acquire_release_roundtrip .held,
    wlst! "acquireLockOnObject_establishes_lockHeld_modeled: SM3.C.8 single per-object acquire grants lockHeld"
      acquireLockOnObject_establishes_lockHeld_modeled .held,
    wlst! "acquireLockOnObject_preserves_lockHeld_of_ne_objId: SM3.C.8 per-step frame keeps lockHeld"
      acquireLockOnObject_preserves_lockHeld_of_ne_objId .held,
    wlst! "acquireAll_preserves_lockHeld_of_ne_all: SM3.C.8 fold-frame for already-held locks"
      acquireAll_preserves_lockHeld_of_ne_all .held,
    wlst! "acquireAll_establishes_lockHeld_of_distinct_present_unheld: SM3.C.8 multi-lock establishment"
      acquireAll_establishes_lockHeld_of_distinct_present_unheld .held,
    wlst! "acquireAll_establishes_lockSetHeld: SM3.C.8 growing phase establishes lockSetHeld"
      acquireAll_establishes_lockSetHeld .held,
    -- §3 ordering (3 entries: SM3.C.5 + SM3.C.6 + acquire/release order
    -- correspondence)
    wlst! "lockSet_acquired_in_order: SM3.C.5 — acquires by LockId ascending"
      lockSet_acquired_in_order .ordering,
    wlst! "lockSet_released_in_reverse: SM3.C.6 — releases by LockId descending"
      lockSet_released_in_reverse .ordering,
    wlst! "releaseOrder_eq_acquireOrder_reverse: structural duality"
      releaseOrder_eq_acquireOrder_reverse .ordering,
    -- §4 atomicity (5 entries: SM3.C.7 + SM3.C.8 + aggregates)
    wlst! "withLockSet_three_phase_decomposition: SM3.C.7 — atomic decomposition"
      withLockSet_three_phase_decomposition .atomicity,
    wlst! "lockSet_atomic_under_2pl: SM3.C.7 — Thm 2.1.10 operational form"
      lockSet_atomic_under_2pl .atomicity,
    wlst! "lockSet_invariant_preserved: SM3.C.8 — Corollary 2.1.11 (acquire-fold form)"
      lockSet_invariant_preserved .atomicity,
    wlst! "withLockSet_invariant_preserved: SM3.C.8 — full 2PL invariant preservation"
      withLockSet_invariant_preserved .atomicity,
    wlst! "acquireAll_preserves_objStoreLock_wf: SM3.C.8 worked instantiation (lever is dischargeable)"
      acquireAll_preserves_objStoreLock_wf .atomicity,
    wlst! "acquireLockOnObject_objStore_establishes_lockHeld: substantive acquire-grants (audit-pass-1 Comment 7)"
      acquireLockOnObject_objStore_establishes_lockHeld .atomicity,
    wlst! "acquireLockOnObject_objStore_release_roundtrip: clean round-trip (audit-pass-1 Comment 4)"
      acquireLockOnObject_objStore_release_roundtrip .atomicity,
    wlst! "withLockSet_satisfies_strict_2PL: SM3.C aggregate witness"
      withLockSet_satisfies_strict_2PL .atomicity,
    wlst! "withLockSet_computation: canonical 'what does withLockSet compute' form"
      withLockSet_computation .atomicity,
    wlst! "acquireAll_lockInsensitive: SM3.C.7 acquire fold invisible to lock-insensitive observer"
      acquireAll_lockInsensitive .atomicity,
    wlst! "releaseAll_lockInsensitive: SM3.C.7 release fold invisible to lock-insensitive observer"
      releaseAll_lockInsensitive .atomicity,
    wlst! "withLockSet_release_invisible: SM3.C.7 observational form (release contributes nothing)"
      withLockSet_release_invisible .atomicity,
    wlst! "lockSet_observer_atomic: SM3.C.7 Thm 2.1.10 observer-atomicity capstone"
      lockSet_observer_atomic .atomicity,
    -- §5 dynamicChain (8 entries: SM3.C.11.a-e)
    wlst! "MAX_PIP_RETRIES: bounded retry budget (=64)"
      MAX_PIP_RETRIES .dynamicChain,
    wlst! "MAX_PIP_RETRIES_pos: bound is positive"
      MAX_PIP_RETRIES_pos .dynamicChain,
    wlst! "PipChainPath: SM3.C.11 chain-walk path representation"
      PipChainPath .dynamicChain,
    wlst! "walkStep: single chain-walk step"
      walkStep .dynamicChain,
    wlst! "walkAndAcquire: fuel-bounded chain walker"
      walkAndAcquire .dynamicChain,
    wlst! "withDynamicChainExtension: SM3.C.11.b chain-walk combinator"
      withDynamicChainExtension .dynamicChain,
    wlst! "withDynamicChainExtension_unfold: structural unfolding"
      withDynamicChainExtension_unfold .dynamicChain,
    wlst! "dynamicChainHeld: SM3.C.11.c chain-held predicate"
      dynamicChainHeld .dynamicChain,
    wlst! "chainFollowsBlockingServer: adjacent-chain predicate (mathlib-free)"
      chainFollowsBlockingServer .dynamicChain,
    wlst! "walkStep_extended_increases_objId: each step is strictly ascending"
      walkStep_extended_increases_objId .dynamicChain,
    wlst! "walkStep_extended_blockingServer: each step follows a blocking-graph edge"
      walkStep_extended_blockingServer .dynamicChain,
    wlst! "walkAndAcquire_path_ascending_in_ObjId_if_terminated: SM3.C.11.d"
      walkAndAcquire_path_ascending_in_ObjId_if_terminated .dynamicChain,
    wlst! "walkAndAcquire_terminated_followsChain: walker output follows blockingServer"
      walkAndAcquire_terminated_followsChain .dynamicChain,
    wlst! "walkAndAcquire_terminated_satisfies_path_structure: wires dynamicChainHeld to walker"
      walkAndAcquire_terminated_satisfies_path_structure .dynamicChain,
    wlst! "walkAndAcquireAux_terminated_length_le: SM3.C.11.e fuel-bounded path"
      walkAndAcquireAux_terminated_length_le .dynamicChain,
    wlst! "walkAndAcquire_terminated_length_bounded: SM3.C.11.e path ≤ MAX_PIP_RETRIES+1"
      walkAndAcquire_terminated_length_bounded .dynamicChain,
    wlst! "walkAndAcquire_total: SM3.C.11.e totality witness"
      walkAndAcquire_total .dynamicChain,
    wlst! "chainLockSeq_acquire_establishes_pathHeld: SM3.C.11.c conjunct-1 on the acquired state"
      chainLockSeq_acquire_establishes_pathHeld .dynamicChain,
    wlst! "acquireLockOnObject_preserves_blockingServer: SM3.C.11.c blockingServer frame (single step)"
      acquireLockOnObject_preserves_blockingServer .dynamicChain,
    wlst! "acquireAll_preserves_blockingServer: SM3.C.11.c blockingServer frame (fold)"
      acquireAll_preserves_blockingServer .dynamicChain,
    wlst! "withDynamicChainExtension_establishes_dynamicChainHeld: SM3.C.11.c capstone — all four conjuncts"
      withDynamicChainExtension_establishes_dynamicChainHeld .dynamicChain,
    wlst! "dynamic_chain_deadlock_free: SM3.C.11.d two-core no mutual wait"
      dynamic_chain_deadlock_free .dynamicChain,
    wlst! "dynamic_chain_no_mutual_wait: SM3.C.11.d ¬(waitsFor ∧ waitsFor) form"
      dynamic_chain_no_mutual_wait .dynamicChain]

/-- WS-SM SM3.C: the inventory has exactly 86 entries.

Audit-pass-1 expanded 61→66; audit-pass-2 66→70; the Group-B closure
expanded 71→86 (+5 held: the SM3.C.8 establishment lemmas
`acquireLockOnObject_establishes_lockHeld_modeled` / `_preserves_lockHeld_of_ne_objId`
/ `acquireAll_preserves_lockHeld_of_ne_all` /
`acquireAll_establishes_lockHeld_of_distinct_present_unheld` /
`acquireAll_establishes_lockSetHeld`; +4 atomicity: the SM3.C.7
observational-atomicity theorems `acquireAll_lockInsensitive` /
`releaseAll_lockInsensitive` / `withLockSet_release_invisible` /
`lockSet_observer_atomic`; +6 dynamicChain: SM3.C.11.c conjunct-1
establishment + `blockingServer` frame/transport + the full
`dynamicChainHeld` capstone + the SM3.C.11.d two-core deadlock-freedom
theorems).
A regression that adds a new SM3.C theorem without updating the
inventory fails this count witness at the Tier-3 surface check. -/
theorem withLockSetTheorems_count :
    withLockSetTheorems.length = 86 := by decide

/-- WS-SM SM3.C: 31 entries in the `combinator` category
(audit-pass-1: +`updateObjectLockAt` + `updateObjectLockAt_preserves_objStoreLock`). -/
theorem withLockSetTheorems_combinator_count :
    (withLockSetTheorems.filter (fun t => t.category == .combinator)).length = 31 := by
  decide

/-- WS-SM SM3.C: 16 entries in the `held` category
(audit-pass-1: +`unheld_acquire_grants` + `unheld_acquire_release_roundtrip`;
Group-B: +5 SM3.C.8 establishment lemmas). -/
theorem withLockSetTheorems_held_count :
    (withLockSetTheorems.filter (fun t => t.category == .held)).length = 16 := by
  decide

/-- WS-SM SM3.C: 3 entries in the `ordering` category. -/
theorem withLockSetTheorems_ordering_count :
    (withLockSetTheorems.filter (fun t => t.category == .ordering)).length = 3 := by
  decide

/-- WS-SM SM3.C: 13 entries in the `atomicity` category
(audit-pass-1: −tautology +`acquireLockOnObject_objStore_establishes_lockHeld`
+`acquireLockOnObject_objStore_release_roundtrip`; Group-B: +4 SM3.C.7
observational-atomicity theorems). -/
theorem withLockSetTheorems_atomicity_count :
    (withLockSetTheorems.filter (fun t => t.category == .atomicity)).length = 13 := by
  decide

/-- WS-SM SM3.C: 23 entries in the `dynamicChain` category
(audit-pass-2: +4 chain-establishment theorems wiring `dynamicChainHeld`
to the walker; Group-B: +6 — conjunct-1 establishment, `blockingServer`
frame/transport, the full capstone, and the SM3.C.11.d two-core
deadlock-freedom theorems). -/
theorem withLockSetTheorems_dynamicChain_count :
    (withLockSetTheorems.filter (fun t => t.category == .dynamicChain)).length = 23 := by
  decide

/-- WS-SM SM3.C: per-category counts sum to the total. -/
theorem withLockSetTheorems_partition_sum :
    (withLockSetTheorems.filter (fun t => t.category == .combinator)).length +
    (withLockSetTheorems.filter (fun t => t.category == .held)).length +
    (withLockSetTheorems.filter (fun t => t.category == .ordering)).length +
    (withLockSetTheorems.filter (fun t => t.category == .atomicity)).length +
    (withLockSetTheorems.filter (fun t => t.category == .dynamicChain)).length =
    withLockSetTheorems.length := by decide

/-- WS-SM SM3.C: every inventory identifier is unique. -/
theorem withLockSetTheorems_identifiers_nodup :
    (withLockSetTheorems.map (·.identifier)).Nodup := by native_decide

/-- WS-SM SM3.C: every inventory description is unique. -/
theorem withLockSetTheorems_descriptions_nodup :
    (withLockSetTheorems.map (·.description)).Nodup := by native_decide

end SeLe4n.Kernel.Concurrency
