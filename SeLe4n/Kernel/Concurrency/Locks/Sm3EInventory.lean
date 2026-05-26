-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- STATUS: staged for WS-SM (SM3.E serializability inventory)

import SeLe4n.Kernel.Concurrency.Locks.Serializability

/-!
# WS-SM SM3.E — Theorem inventory

Aggregates the SM3.E substantive definitions and theorems into a single typed
inventory with size and per-category witnesses.  Mirrors the SM3.A
`PerObjectLockInventory.lean`, SM3.B `LockSetInventory.lean`, SM3.C
`Sm3CInventory.lean`, and SM3.D `Sm3DInventory.lean` patterns.

Seven categories matching the plan §5.5 sub-tasks:

* `.model` — `KernelTransitionInstance` + `applySequential` (SM3.E.2 infra).
* `.conflict` — `ktiSharesConflictingLock` + `conflictOrder` (SM3.E.1).
* `.strict2pl` — `followsStrict2PL` + `strictly_2pl_preserved` (SM3.E.4) + the
  strict-2PL ⟹ commit-consistency lever.
* `.commutativity` — `actionsCommute` + the adjacent-swap lever + the
  `CommutingReorder` closure + the SM3.E.5 commutativity lemmas (structural
  read/disjoint-field + observational `objStoreEquiv` write/write).
* `.acyclicity` — the commit-oriented conflict graph + `conflictGraph_acyclic`
  (the acyclic conflict graph serializability reduces to).
* `.serializability` — `commitSort` (the serialization order) + `serialEquivalent`
  (SM3.E.2) + `serializability_under_2pl` (SM3.E.3, Theorem 2.1.10) +
  conflict-consistency of the sort.
* `.preservation` — `singleCore_proof_preservation` (SM3.E.6, Corollary 2.1.11).

## Identifier validation

Identifiers are compile-time-validated via the `serlt!` macro, mirroring SM3.A's
`polt!` / SM3.B's `lkst!` / SM3.C's `wlst!` / SM3.D's `dlt!`.  A typo or stale
rename fails to elaborate with "unknown constant".
-/

namespace SeLe4n.Kernel.Concurrency

open SeLe4n

/-- WS-SM SM3.E: category tag for the SM3.E theorem inventory. -/
inductive SerializabilityCategory where
  /-- `KernelTransitionInstance` + `applySequential` (SM3.E.2 infra). -/
  | model
  /-- Conflict relation + `conflictOrder` (SM3.E.1). -/
  | conflict
  /-- Strict-2PL discipline + `strictly_2pl_preserved` (SM3.E.4). -/
  | strict2pl
  /-- Commutativity of non-conflicting operations (SM3.E.5). -/
  | commutativity
  /-- Conflict-graph acyclicity (the acyclic conflict graph, SM3.E.3). -/
  | acyclicity
  /-- Serialization order + serializability theorem (SM3.E.2/E.3). -/
  | serializability
  /-- Single-core proof preservation (SM3.E.6, Corollary 2.1.11). -/
  | preservation
  deriving Repr, DecidableEq, Inhabited

/-- WS-SM SM3.E: a theorem entry in the SM3.E inventory. -/
structure SerializabilityTheorem where
  description : String
  identifier  : String
  _elabCheck  : Unit
  category    : SerializabilityCategory
  deriving Repr, Inhabited

/-- WS-SM SM3.E: build a `SerializabilityTheorem` with a compile-time-validated
identifier.  See SM3.A's `polt!` / SM3.B's `lkst!` / SM3.C's `wlst!` / SM3.D's
`dlt!`. -/
syntax (name := serltMacro) "serlt!" str ident term : term

macro_rules
  | `(serlt! $desc:str $ident:ident $cat:term) => do
      let nameStr : String := ident.getId.toString
      let nameStxLit := Lean.Syntax.mkStrLit nameStr
      `(({ description := $desc,
           identifier := $nameStxLit,
           _elabCheck := (let _ := @$ident; ()),
           category := $cat
         } : SerializabilityTheorem))

/-- WS-SM SM3.E: substantive theorem inventory.  Every entry's identifier is
compile-time-validated. -/
def serializabilityTheorems : List SerializabilityTheorem :=
  [-- §1 model (5)
    serlt! "KernelTransitionInstance — a committed transition occurrence (SM3.E)"
      KernelTransitionInstance .model,
    serlt! "applySequential — serial application of a schedule's actions (SM3.E.2)"
      applySequential .model,
    serlt! "applySequential_nil — empty schedule is the identity"
      applySequential_nil .model,
    serlt! "applySequential_cons — head action then tail fold"
      applySequential_cons .model,
    serlt! "applySequential_append — segment composition"
      applySequential_append .model,
    -- §2 conflict (7)
    serlt! "ktiSharesConflictingLock — two instances share a conflicting lock (SM3.E.1)"
      ktiSharesConflictingLock .conflict,
    serlt! "ktiConflictsB — decidable Bool reflection of the conflict relation"
      ktiConflictsB .conflict,
    serlt! "ktiConflictsB_iff — Bool reflection agrees with the Prop relation"
      ktiConflictsB_iff .conflict,
    serlt! "ktiSharesConflictingLock_symm — conflict is symmetric"
      ktiSharesConflictingLock_symm .conflict,
    serlt! "conflictOrder — SM3.E.1 conflict-order (commit ≤ acquire on shared lock)"
      conflictOrder .conflict,
    serlt! "conflictOrder_sharesConflictingLock — conflictOrder entails a shared lock"
      conflictOrder_sharesConflictingLock .conflict,
    serlt! "conflictOrder_implies_conflictPrecedes — bridges SM3.E.1 conflictOrder to the serialization order"
      conflictOrder_implies_conflictPrecedes .conflict,
    -- §3 strict2pl (6)
    serlt! "KernelTransitionInstance.followsStrict2PL — locks held until commit (SM3.E.4)"
      KernelTransitionInstance.followsStrict2PL .strict2pl,
    serlt! "scheduleFollowsStrict2PL — every transition follows strict 2PL"
      scheduleFollowsStrict2PL .strict2pl,
    serlt! "KernelTransitionInstance.ofWithLockSet — the withLockSet-built instance"
      KernelTransitionInstance.ofWithLockSet .strict2pl,
    serlt! "strictly_2pl_preserved — SM3.E.4 withLockSet transitions follow strict 2PL"
      strictly_2pl_preserved .strict2pl,
    serlt! "scheduleFollowsStrict2PL_of_ofWithLockSet — schedule-wide strict 2PL"
      scheduleFollowsStrict2PL_of_ofWithLockSet .strict2pl,
    serlt! "conflictOrder_commit_le — strict 2PL ⟹ conflict resolved in commit order"
      conflictOrder_commit_le .strict2pl,
    -- §4 commutativity (23)
    serlt! "KernelTransitionInstance.actionsCommute — actions commute as transformers (SM3.E.5)"
      KernelTransitionInstance.actionsCommute .commutativity,
    serlt! "KernelTransitionInstance.actionsCommute_symm — commutation is symmetric"
      KernelTransitionInstance.actionsCommute_symm .commutativity,
    serlt! "KernelTransitionInstance.actionsCommute_of_action_id_left — reads commute (left)"
      KernelTransitionInstance.actionsCommute_of_action_id_left .commutativity,
    serlt! "KernelTransitionInstance.actionsCommute_of_action_id_right — reads commute (right)"
      KernelTransitionInstance.actionsCommute_of_action_id_right .commutativity,
    serlt! "applySequential_swap_adjacent — adjacent commuting transposition lever"
      applySequential_swap_adjacent .commutativity,
    serlt! "CommutingReorder — commuting-transposition closure (conflict-equivalence)"
      CommutingReorder .commutativity,
    serlt! "CommutingReorder.cons — congruence under a common head"
      CommutingReorder.cons .commutativity,
    serlt! "applySequential_eq_of_commutingReorder — commuting reorder preserves the fold"
      applySequential_eq_of_commutingReorder .commutativity,
    serlt! "readOnlyInstance — a read-only (identity-action) transition"
      readOnlyInstance .commutativity,
    serlt! "readOnlyInstance_action — its action is the identity"
      readOnlyInstance_action .commutativity,
    serlt! "readOnlyInstance_actionsCommute — a read commutes with any transition"
      readOnlyInstance_actionsCommute .commutativity,
    serlt! "readOnlyInstance_actionsCommute_readOnly — two reads commute"
      readOnlyInstance_actionsCommute_readOnly .commutativity,
    serlt! "setObjStoreLockAction — an objStoreLock-only field action"
      setObjStoreLockAction .commutativity,
    serlt! "setSchedulerAction — a scheduler-only field action"
      setSchedulerAction .commutativity,
    serlt! "setObjStoreLock_setScheduler_commute — disjoint-field actions commute"
      setObjStoreLock_setScheduler_commute .commutativity,
    serlt! "disjointField_actionsCommute — disjoint-subsystem instances commute"
      disjointField_actionsCommute .commutativity,
    serlt! "objStoreEquiv — observational equivalence of the object store"
      objStoreEquiv .commutativity,
    serlt! "objStoreEquiv_refl — observational equivalence is reflexive"
      objStoreEquiv_refl .commutativity,
    serlt! "objStoreEquiv_symm — observational equivalence is symmetric"
      objStoreEquiv_symm .commutativity,
    serlt! "objStoreEquiv_trans — observational equivalence is transitive"
      objStoreEquiv_trans .commutativity,
    serlt! "updateObjectAt_preserves_invExt — updateObjectAt preserves invExt"
      updateObjectAt_preserves_invExt .commutativity,
    serlt! "updateObjectAt_get? — closed-form lookup after updateObjectAt"
      updateObjectAt_get? .commutativity,
    serlt! "updateObjectAt_objStoreEquiv_comm — write/write on distinct objects commute (obs)"
      updateObjectAt_objStoreEquiv_comm .commutativity,
    -- §5 acyclicity (9)
    serlt! "conflictPrecedes — commit-oriented conflict edge (SM3.E.3)"
      conflictPrecedes .acyclicity,
    serlt! "conflictPrecedes_irreflexive — no self conflict-precedence (item 16)"
      conflictPrecedes_irreflexive .acyclicity,
    serlt! "conflictPrecedes_asymm — at most one orientation per conflict"
      conflictPrecedes_asymm .acyclicity,
    serlt! "ConflictReaches — transitive closure of a transition-relation"
      ConflictReaches .acyclicity,
    serlt! "conflictReaches_commitTime_lt — commit time strictly increases along a path"
      conflictReaches_commitTime_lt .acyclicity,
    serlt! "ConflictAcyclic — no transition reaches itself"
      ConflictAcyclic .acyclicity,
    serlt! "conflictGraph_acyclic — SM3.E.3 the acyclic conflict graph (Bernstein)"
      conflictGraph_acyclic .acyclicity,
    serlt! "conflictPrecedes_total_of_distinct_commit — orientation completeness (uses conflict)"
      conflictPrecedes_total_of_distinct_commit .acyclicity,
    serlt! "conflictPrecedes_strict_total_of_distinct_commit — conflict graph is a strict total order"
      conflictPrecedes_strict_total_of_distinct_commit .acyclicity,
    -- §6 serializability (22)
    serlt! "insertByCommitTime — insert into a commit-sorted schedule"
      insertByCommitTime .serializability,
    serlt! "commitSort — insertion sort by commit time (the serialization order)"
      commitSort .serializability,
    serlt! "insertByCommitTime_perm — insertion is a permutation"
      insertByCommitTime_perm .serializability,
    serlt! "commitSort_perm — the sort is a permutation (no transition lost)"
      commitSort_perm .serializability,
    serlt! "insertByCommitTime_sorted — insertion preserves commit-sortedness"
      insertByCommitTime_sorted .serializability,
    serlt! "commitSort_sorted — the sort is commit-ordered (topological sort)"
      commitSort_sorted .serializability,
    serlt! "commutesWithSmaller — commutes with smaller-commit elements"
      commutesWithSmaller .serializability,
    serlt! "commutesWithSmaller_of_perm — transports along a permutation"
      commutesWithSmaller_of_perm .serializability,
    serlt! "insertByCommitTime_commutingReorder — insertion is a commuting reorder"
      insertByCommitTime_commutingReorder .serializability,
    serlt! "outOfOrderCommute — out-of-commit-order pairs commute (strict-2PL consequence)"
      outOfOrderCommute .serializability,
    serlt! "commitSort_commutingReorder — the sort is a commuting reorder of the input"
      commitSort_commutingReorder .serializability,
    serlt! "serialEquivalent — same final state as a serial order (SM3.E.2)"
      serialEquivalent .serializability,
    serlt! "serialEquivalent_refl — serial-equivalence is reflexive"
      serialEquivalent_refl .serializability,
    serlt! "serializability_under_2pl — SM3.E.3 Theorem 2.1.10 (perm + sorted + equiv)"
      serializability_under_2pl .serializability,
    serlt! "serializability_under_2pl_exists — the existential serialization form"
      serializability_under_2pl_exists .serializability,
    serlt! "outOfOrderCommute_of_forall_action_id — read-only schedules satisfy the hypothesis"
      outOfOrderCommute_of_forall_action_id .serializability,
    serlt! "serializability_of_readOnly_schedule — unconditional serializability (non-vacuity)"
      serializability_of_readOnly_schedule .serializability,
    serlt! "commitSorted_respects_conflictPrecedes — the sort respects conflict order"
      commitSorted_respects_conflictPrecedes .serializability,
    serlt! "commitSorted_respects_conflictOrder — the sort respects the plan's SM3.E.1 conflictOrder"
      commitSorted_respects_conflictOrder .serializability,
    serlt! "conflictsCommitOrdered — strict-2PL lock-exclusion property (conflicts in commit order)"
      conflictsCommitOrdered .serializability,
    serlt! "outOfOrderCommute_of_conflictsCommitOrdered — grounds outOfOrderCommute in strict 2PL"
      outOfOrderCommute_of_conflictsCommitOrdered .serializability,
    serlt! "serializability_under_2pl_of_conflicts_ordered — grounded Theorem 2.1.10 (honest under-2PL)"
      serializability_under_2pl_of_conflicts_ordered .serializability,
    -- §7 preservation (6)
    serlt! "singleCore_invariant_preservation — SM3.E.6 Cor 2.1.11 invariant form"
      singleCore_invariant_preservation .preservation,
    serlt! "singleCore_proof_preservation — SM3.E.6 Cor 2.1.11 pre→post meta-theorem"
      singleCore_proof_preservation .preservation,
    serlt! "acquireLockOnObject_preserves_objStoreLock_wf — per-step lock-insensitivity (acquire)"
      acquireLockOnObject_preserves_objStoreLock_wf .preservation,
    serlt! "releaseLockOnObject_preserves_objStoreLock_wf — per-step lock-insensitivity (release)"
      releaseLockOnObject_preserves_objStoreLock_wf .preservation,
    serlt! "withLockSet_preserves_objStoreLock_wf — NON-VACUOUS Cor 2.1.11 witness on a real invariant"
      withLockSet_preserves_objStoreLock_wf .preservation,
    serlt! "withLockSet_growing_phase_establishes_lockSetHeld — lockSetHeld is a consequence"
      withLockSet_growing_phase_establishes_lockSetHeld .preservation]

/-- WS-SM SM3.E: the inventory has exactly 78 entries. -/
theorem serializabilityTheorems_count :
    serializabilityTheorems.length = 78 := by decide

/-- WS-SM SM3.E: 5 entries in `model`. -/
theorem serializabilityTheorems_model_count :
    (serializabilityTheorems.filter (fun t => t.category == .model)).length = 5 := by decide

/-- WS-SM SM3.E: 7 entries in `conflict`. -/
theorem serializabilityTheorems_conflict_count :
    (serializabilityTheorems.filter (fun t => t.category == .conflict)).length = 7 := by decide

/-- WS-SM SM3.E: 6 entries in `strict2pl`. -/
theorem serializabilityTheorems_strict2pl_count :
    (serializabilityTheorems.filter (fun t => t.category == .strict2pl)).length = 6 := by decide

/-- WS-SM SM3.E: 23 entries in `commutativity`. -/
theorem serializabilityTheorems_commutativity_count :
    (serializabilityTheorems.filter (fun t => t.category == .commutativity)).length = 23 := by decide

/-- WS-SM SM3.E: 9 entries in `acyclicity`. -/
theorem serializabilityTheorems_acyclicity_count :
    (serializabilityTheorems.filter (fun t => t.category == .acyclicity)).length = 9 := by decide

/-- WS-SM SM3.E: 22 entries in `serializability`. -/
theorem serializabilityTheorems_serializability_count :
    (serializabilityTheorems.filter (fun t => t.category == .serializability)).length = 22 := by decide

/-- WS-SM SM3.E: 6 entries in `preservation`. -/
theorem serializabilityTheorems_preservation_count :
    (serializabilityTheorems.filter (fun t => t.category == .preservation)).length = 6 := by decide

/-- WS-SM SM3.E: per-category counts sum to the total. -/
theorem serializabilityTheorems_partition_sum :
    (serializabilityTheorems.filter (fun t => t.category == .model)).length +
    (serializabilityTheorems.filter (fun t => t.category == .conflict)).length +
    (serializabilityTheorems.filter (fun t => t.category == .strict2pl)).length +
    (serializabilityTheorems.filter (fun t => t.category == .commutativity)).length +
    (serializabilityTheorems.filter (fun t => t.category == .acyclicity)).length +
    (serializabilityTheorems.filter (fun t => t.category == .serializability)).length +
    (serializabilityTheorems.filter (fun t => t.category == .preservation)).length =
    serializabilityTheorems.length := by decide

/-- WS-SM SM3.E: every inventory identifier is unique. -/
theorem serializabilityTheorems_identifiers_nodup :
    (serializabilityTheorems.map (·.identifier)).Nodup := by native_decide

/-- WS-SM SM3.E: every inventory description is unique. -/
theorem serializabilityTheorems_descriptions_nodup :
    (serializabilityTheorems.map (·.description)).Nodup := by native_decide

end SeLe4n.Kernel.Concurrency
