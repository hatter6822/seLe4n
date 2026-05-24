-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- STATUS: staged for WS-SM (SM3.D deadlock-freedom inventory)

import SeLe4n.Kernel.Concurrency.Locks.Deadlock

/-!
# WS-SM SM3.D — Theorem inventory

Aggregates the SM3.D substantive definitions and theorems into a single
typed inventory with size and per-category witnesses.  Mirrors the SM3.A
`PerObjectLockInventory.lean`, SM3.B `LockSetInventory.lean`, and SM3.C
`Sm3CInventory.lean` patterns.

The inventory has seven categories matching the plan §5.4 sub-tasks:

* `.model` — the abstract `KernelExecution` snapshot + `blockedAt` /
  `heldBy` predicates (SM3.D.1).
* `.hypotheses` — the 2PL + ordering hypotheses (per-core + execution-
  level) and the `ladder_of_2pl_and_order` key lemma (SM3.D.4 setup).
* `.order` — `lockOrder_strict` (SM3.D.3) and the three foundational
  `LockId` strict-order helpers it bundles (SM3.D.2/D.3).
* `.deadlock` — `noDeadlock` + its decidability scaffolding + the main
  Theorem 2.1.9 `deadlockFreedom_under_2pl_and_ordering` (SM3.D.1/D.4).
* `.waitGraph` — the wait-graph edge relations, transitive closure,
  `Acyclic`, the monotonicity lemmas, and the SM3.D.5 acyclicity theorem
  + its `noDeadlock` coherence corollary.
* `.boundedWait` — the `totalWaitCost` model and the SM3.D.6
  `boundedWait_under_2pl` bound.
* `.grounding` — the §7 bridge discharging the abstract hypotheses from
  the SM3.B/SM3.C `lockAcquireSequence` discipline (`CorePrefixOf`).

## Identifier validation

Identifiers are compile-time-validated via the `dlt!` macro, mirroring
SM3.A's `polt!` / SM3.B's `lkst!` / SM3.C's `wlst!`.  A typo or rename
fails the build at this module's elaboration step.
-/

namespace SeLe4n.Kernel.Concurrency

open SeLe4n

/-- WS-SM SM3.D: category tag for the SM3.D theorem inventory. -/
inductive DeadlockCategory where
  /-- `KernelExecution` snapshot + `blockedAt` / `heldBy` (SM3.D.1). -/
  | model
  /-- 2PL + ordering hypotheses + ladder invariant (SM3.D.4 setup). -/
  | hypotheses
  /-- `lockOrder_strict` + `LockId` strict-order helpers (SM3.D.2/D.3). -/
  | order
  /-- `noDeadlock` + Theorem 2.1.9 (SM3.D.1/D.4). -/
  | deadlock
  /-- Wait-graph acyclicity (SM3.D.5). -/
  | waitGraph
  /-- Bounded-wait corollary (SM3.D.6). -/
  | boundedWait
  /-- §7 grounding bridge to the SM3.B/C lock discipline. -/
  | grounding
  deriving Repr, DecidableEq, Inhabited

/-- WS-SM SM3.D: a theorem entry in the SM3.D inventory.

Records a description, the fully-qualified name as a `String`, a
compile-time elaboration witness, and a category tag.  The `_elabCheck`
field is produced by the `dlt!` macro (`let _ := @<ident>; ()`), forcing
the elaborator to resolve the referenced declaration at construction
time — a typo or stale rename fails with "unknown identifier". -/
structure DeadlockTheorem where
  description : String
  identifier  : String
  _elabCheck  : Unit
  category    : DeadlockCategory
  deriving Repr, Inhabited

/-- WS-SM SM3.D: build a `DeadlockTheorem` with a compile-time-validated
identifier.  See SM3.A's `polt!` / SM3.B's `lkst!` / SM3.C's `wlst!`. -/
syntax (name := dltMacro) "dlt!" str ident term : term

macro_rules
  | `(dlt! $desc:str $ident:ident $cat:term) => do
      let nameStr : String := ident.getId.toString
      let nameStxLit := Lean.Syntax.mkStrLit nameStr
      `(({ description := $desc,
           identifier := $nameStxLit,
           _elabCheck := (let _ := @$ident; ()),
           category := $cat
         } : DeadlockTheorem))

/-- WS-SM SM3.D: substantive theorem inventory.  Every entry's identifier
is compile-time-validated. -/
def deadlockTheorems : List DeadlockTheorem :=
  [-- §1 model (3 entries)
    dlt! "KernelExecution — abstract per-core lock-state snapshot (SM3.D.1)"
      KernelExecution .model,
    dlt! "blockedAt — core c blocked at lock l (SM3.D.1)"
      blockedAt .model,
    dlt! "heldBy — lock l held by core c (SM3.D.1)"
      heldBy .model,
    -- §2 hypotheses (5 entries)
    dlt! "coreFollows2PL — per-core 2PL growing-phase property"
      coreFollows2PL .hypotheses,
    dlt! "coreAcquiresInOrder — per-core LockId-ascending property"
      coreAcquiresInOrder .hypotheses,
    dlt! "executionFollows2PL — execution-level 2PL hypothesis (SM3.D.4)"
      executionFollows2PL .hypotheses,
    dlt! "executionAcquiresInLockIdOrder — execution-level ordering hypothesis (SM3.D.4)"
      executionAcquiresInLockIdOrder .hypotheses,
    dlt! "ladder_of_2pl_and_order — the ladder invariant (held locks < wanted lock)"
      ladder_of_2pl_and_order .hypotheses,
    -- §3 order (4 entries)
    dlt! "lockOrder_strict — SM3.D.3 LockId strict order is irreflexive + transitive"
      lockOrder_strict .order,
    dlt! "LockId.lt_irrefl — strict order irreflexive (SM3.D.3 half)"
      LockId.lt_irrefl .order,
    dlt! "LockId.lt_trans — strict order transitive (SM3.D.3 half)"
      LockId.lt_trans .order,
    dlt! "LockId.lt_asymm — strict order asymmetric (cycle closer)"
      LockId.lt_asymm .order,
    -- §4 deadlock (6 entries)
    dlt! "noDeadlock — SM3.D.1 two-core deadlock-freedom predicate"
      noDeadlock .deadlock,
    dlt! "mutualBlocked — per-pair mutual-block test (decidability helper)"
      mutualBlocked .deadlock,
    dlt! "noDeadlockDec — decidable reformulation of noDeadlock"
      noDeadlockDec .deadlock,
    dlt! "noDeadlock_iff_dec — spec ↔ decidable form"
      noDeadlock_iff_dec .deadlock,
    dlt! "noDeadlock_definition_decidable — Decidable (noDeadlock e) instance"
      noDeadlock_definition_decidable .deadlock,
    dlt! "deadlockFreedom_under_2pl_and_ordering — SM3.D.4 Theorem 2.1.9"
      deadlockFreedom_under_2pl_and_ordering .deadlock,
    -- §5 waitGraph (9 entries)
    dlt! "waitsForCore — wait-for edge (c blocked on a lock c' holds)"
      waitsForCore .waitGraph,
    dlt! "blockedWaitsFor — blocked wait-for edge (c' also blocked)"
      blockedWaitsFor .waitGraph,
    dlt! "ReachesPlus — transitive closure of a core-relation (mathlib-free)"
      ReachesPlus .waitGraph,
    dlt! "Acyclic — no core reaches itself in the transitive closure"
      Acyclic .waitGraph,
    dlt! "waitGraph — the wait-for graph of an execution (SM3.D.5)"
      waitGraph .waitGraph,
    dlt! "blockedWaitsFor_wanted_lt — single edge strictly increases wanted lock"
      blockedWaitsFor_wanted_lt .waitGraph,
    dlt! "reachesPlus_wanted_lt — path strictly increases wanted lock"
      reachesPlus_wanted_lt .waitGraph,
    dlt! "waitGraph_acyclic_under_2pl — SM3.D.5 wait graph is a DAG"
      waitGraph_acyclic_under_2pl .waitGraph,
    dlt! "noDeadlock_of_waitGraph_acyclic — acyclicity ⟹ noDeadlock (coherence)"
      noDeadlock_of_waitGraph_acyclic .waitGraph,
    -- §6 boundedWait (5 entries; `sum_const_map` is a generic universe-
    -- polymorphic list helper, kept in the module but not inventoried —
    -- the `dlt!` macro's `@`-reference cannot infer its universe level)
    dlt! "maxLockSetSize — static worst-case lock-set size bound (=8)"
      maxLockSetSize .boundedWait,
    dlt! "perLockWaitCost — per-lock worst-case wait ((numCores-1)*T_cs)"
      perLockWaitCost .boundedWait,
    dlt! "totalWaitCost — total worst-case wait (sum over acquire sequence)"
      totalWaitCost .boundedWait,
    dlt! "totalWaitCost_eq — total wait collapses to |S|*(numCores-1)*T_cs"
      totalWaitCost_eq .boundedWait,
    dlt! "boundedWait_under_2pl — SM3.D.6 wait ≤ maxLockSetSize*(numCores-1)*T_cs"
      boundedWait_under_2pl .boundedWait,
    -- §7 grounding (5 entries)
    dlt! "acquireOrder_nodup — projected acquire order has distinct LockIds"
      acquireOrder_nodup .grounding,
    dlt! "CorePrefixOf — a core in the 2PL growing-phase prefix of S"
      CorePrefixOf .grounding,
    dlt! "coreFollows2PL_of_prefix — prefix ⟹ per-core 2PL"
      coreFollows2PL_of_prefix .grounding,
    dlt! "coreAcquiresInOrder_of_prefix — prefix ⟹ per-core ordering"
      coreAcquiresInOrder_of_prefix .grounding,
    dlt! "execution_satisfies_hypotheses_of_all_prefix — both hypotheses are consequences of 2PL discipline"
      execution_satisfies_hypotheses_of_all_prefix .grounding]

/-- WS-SM SM3.D: the inventory has exactly 37 entries.

A regression that adds a new SM3.D theorem without updating the inventory
fails this count witness at the Tier-3 surface check. -/
theorem deadlockTheorems_count :
    deadlockTheorems.length = 37 := by decide

/-- WS-SM SM3.D: 3 entries in the `model` category. -/
theorem deadlockTheorems_model_count :
    (deadlockTheorems.filter (fun t => t.category == .model)).length = 3 := by decide

/-- WS-SM SM3.D: 5 entries in the `hypotheses` category. -/
theorem deadlockTheorems_hypotheses_count :
    (deadlockTheorems.filter (fun t => t.category == .hypotheses)).length = 5 := by decide

/-- WS-SM SM3.D: 4 entries in the `order` category. -/
theorem deadlockTheorems_order_count :
    (deadlockTheorems.filter (fun t => t.category == .order)).length = 4 := by decide

/-- WS-SM SM3.D: 6 entries in the `deadlock` category. -/
theorem deadlockTheorems_deadlock_count :
    (deadlockTheorems.filter (fun t => t.category == .deadlock)).length = 6 := by decide

/-- WS-SM SM3.D: 9 entries in the `waitGraph` category. -/
theorem deadlockTheorems_waitGraph_count :
    (deadlockTheorems.filter (fun t => t.category == .waitGraph)).length = 9 := by decide

/-- WS-SM SM3.D: 5 entries in the `boundedWait` category. -/
theorem deadlockTheorems_boundedWait_count :
    (deadlockTheorems.filter (fun t => t.category == .boundedWait)).length = 5 := by decide

/-- WS-SM SM3.D: 5 entries in the `grounding` category. -/
theorem deadlockTheorems_grounding_count :
    (deadlockTheorems.filter (fun t => t.category == .grounding)).length = 5 := by decide

/-- WS-SM SM3.D: per-category counts sum to the total. -/
theorem deadlockTheorems_partition_sum :
    (deadlockTheorems.filter (fun t => t.category == .model)).length +
    (deadlockTheorems.filter (fun t => t.category == .hypotheses)).length +
    (deadlockTheorems.filter (fun t => t.category == .order)).length +
    (deadlockTheorems.filter (fun t => t.category == .deadlock)).length +
    (deadlockTheorems.filter (fun t => t.category == .waitGraph)).length +
    (deadlockTheorems.filter (fun t => t.category == .boundedWait)).length +
    (deadlockTheorems.filter (fun t => t.category == .grounding)).length =
    deadlockTheorems.length := by decide

/-- WS-SM SM3.D: every inventory identifier is unique. -/
theorem deadlockTheorems_identifiers_nodup :
    (deadlockTheorems.map (·.identifier)).Nodup := by native_decide

/-- WS-SM SM3.D: every inventory description is unique. -/
theorem deadlockTheorems_descriptions_nodup :
    (deadlockTheorems.map (·.description)).Nodup := by native_decide

end SeLe4n.Kernel.Concurrency
