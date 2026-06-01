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
`WithLockSetInventory.lean` patterns.

Nine categories matching the plan §5.4 sub-tasks and the audit-pass
expansion:

* `.model` — `KernelExecution` snapshot + `blockedAt` / `heldBy` (SM3.D.1).
* `.hypotheses` — 2PL + ordering hypotheses + `ladder_of_2pl_and_order`.
* `.order` — `lockOrder_strict` (+ class form) and the `LockId` strict-order
  helpers (SM3.D.2/D.3).
* `.deadlock` — `noDeadlock` + decidability + Theorem 2.1.9 (SM3.D.1/D.4).
* `.waitGraph` — wait-graph acyclicity (SM3.D.5).
* `.modeAware` — the `AccessMode.conflicts`-aware (realistic) wait graph and
  its acyclicity, via `Acyclic_mono` (audit-pass extension of SM3.D.5).
* `.sizeBound` — the static `lockSet_<τ>` size bounds discharging the
  `maxLockSetSize` premise (audit-pass extension of SM3.D.6).
* `.boundedWait` — the contention-sensitive `WCRT` + `KernelOperation` +
  the full `boundedWait_under_2pl` (SM3.D.6).
* `.grounding` — the §7/§7b bridges discharging the hypotheses from the
  SM3.B/C discipline and connecting the abstract model to the concrete
  SM3.C `lockSetHeld` lock state.

## Identifier validation

Identifiers are compile-time-validated via the `dlt!` macro, mirroring
SM3.A's `polt!` / SM3.B's `lkst!` / SM3.C's `wlst!`.  Universe-polymorphic
helpers (`sum_const_map`, `sum_le_length_mul`, `sum_map_le_sum_map`,
`Irreflexive`, `Transitive`) and the 25 individual `lockSet_<τ>_size_le`
theorems are intentionally NOT inventoried: the former cannot be `@`-
referenced without a universe metavariable (the macro's elaboration check
fails); the latter are bundled by the `lockSetTransitions_within_bound`
aggregate (a single entry that uses all 25).
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
  /-- Mode-aware (conflict) wait graph + monotone acyclicity (SM3.D.5b). -/
  | modeAware
  /-- Static lock-set size bounds (SM3.D.6b). -/
  | sizeBound
  /-- Bounded-wait corollary: WCRT + KernelOperation (SM3.D.6). -/
  | boundedWait
  /-- §7/§7b grounding + model↔kernel bridge. -/
  | grounding
  deriving Repr, DecidableEq, Inhabited

/-- WS-SM SM3.D: a theorem entry in the SM3.D inventory. -/
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
  [-- §1 model (3)
    dlt! "KernelExecution — abstract per-core lock-state snapshot (SM3.D.1)"
      KernelExecution .model,
    dlt! "blockedAt — core c blocked at lock l (SM3.D.1)"
      blockedAt .model,
    dlt! "heldBy — lock l held by core c (SM3.D.1)"
      heldBy .model,
    -- §2 hypotheses (5)
    dlt! "coreFollows2PL — per-core 2PL growing-phase property"
      coreFollows2PL .hypotheses,
    dlt! "coreAcquiresInOrder — per-core LockId-ascending property"
      coreAcquiresInOrder .hypotheses,
    dlt! "executionFollows2PL — execution-level 2PL hypothesis (SM3.D.4)"
      executionFollows2PL .hypotheses,
    dlt! "executionAcquiresInLockIdOrder — execution-level ordering hypothesis"
      executionAcquiresInLockIdOrder .hypotheses,
    dlt! "ladder_of_2pl_and_order — the ladder invariant (held < wanted)"
      ladder_of_2pl_and_order .hypotheses,
    -- §3 order (5)
    dlt! "lockOrder_strict — SM3.D.3 LockId strict order irreflexive + transitive"
      lockOrder_strict .order,
    dlt! "lockOrder_strict_classes — SM3.D.3 in the plan's Irreflexive ∧ Transitive form"
      lockOrder_strict_classes .order,
    dlt! "LockId.lt_irrefl — strict order irreflexive (SM3.D.3 half)"
      LockId.lt_irrefl .order,
    dlt! "LockId.lt_trans — strict order transitive (SM3.D.3 half)"
      LockId.lt_trans .order,
    dlt! "LockId.lt_asymm — strict order asymmetric (cycle closer)"
      LockId.lt_asymm .order,
    -- §4 deadlock (6)
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
    -- §5 waitGraph (9)
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
    -- §5b modeAware (5)
    dlt! "ReachesPlus_mono — transitive closure is edge-monotone"
      ReachesPlus_mono .modeAware,
    dlt! "Acyclic_mono — acyclicity is anti-monotone (subgraph of a DAG is a DAG)"
      Acyclic_mono .modeAware,
    dlt! "conflictWaitsFor — mode-aware wait edge (AccessMode.conflicts)"
      conflictWaitsFor .modeAware,
    dlt! "conflictWaitsFor_sub_blockedWaitsFor — conflict graph ⊆ wait graph"
      conflictWaitsFor_sub_blockedWaitsFor .modeAware,
    dlt! "conflictWaitGraph_acyclic_under_2pl — mode-aware wait graph is a DAG"
      conflictWaitGraph_acyclic_under_2pl .modeAware,
    -- §6b sizeBound (8)
    dlt! "insertOrMerge_size_le — insertOrMerge grows size by ≤ 1"
      insertOrMerge_size_le .sizeBound,
    dlt! "lockSetOfList_size_le — lockSetOfList size ≤ list length"
      lockSetOfList_size_le .sizeBound,
    dlt! "lockSetExtendOpt_size_le — lockSetExtendOpt grows size by ≤ 1"
      lockSetExtendOpt_size_le .sizeBound,
    dlt! "size_le_1 — one optional extension over a base list"
      size_le_1 .sizeBound,
    dlt! "size_le_2 — two optional extensions over a base list"
      size_le_2 .sizeBound,
    dlt! "size_le_3 — three optional extensions over a base list"
      size_le_3 .sizeBound,
    dlt! "size_le_4 — four optional extensions over a base list"
      size_le_4 .sizeBound,
    dlt! "lockSetTransitions_within_bound — all 25 lockSet_<τ> sizes ≤ maxLockSetSize"
      lockSetTransitions_within_bound .sizeBound,
    -- §6/§6c/§6d boundedWait (16)
    dlt! "maxLockSetSize — static worst-case lock-set size bound (=8)"
      maxLockSetSize .boundedWait,
    dlt! "perLockWaitCost — per-lock worst-case wait ((numCores-1)*T_cs)"
      perLockWaitCost .boundedWait,
    dlt! "totalWaitCost — total worst-case wait (sum over acquire sequence)"
      totalWaitCost .boundedWait,
    dlt! "totalWaitCost_eq — total wait collapses to |S|*(numCores-1)*T_cs"
      totalWaitCost_eq .boundedWait,
    dlt! "totalWaitCost_le_bound — uniform combinatorial wait bound"
      totalWaitCost_le_bound .boundedWait,
    dlt! "KernelOperation — a transition's size-bounded lock footprint"
      KernelOperation .boundedWait,
    dlt! "KernelOperation.ofEndpointCall — KernelOperation from endpointCall"
      KernelOperation.ofEndpointCall .boundedWait,
    dlt! "KernelOperation.ofReplyRecv — KernelOperation from replyRecv"
      KernelOperation.ofReplyRecv .boundedWait,
    dlt! "KernelOperation.ofTcbSuspend — KernelOperation from tcbSuspend"
      KernelOperation.ofTcbSuspend .boundedWait,
    dlt! "otherCores — the cores other than c"
      otherCores .boundedWait,
    dlt! "otherCores_length_eq — |otherCores c| = numCores - 1"
      otherCores_length_eq .boundedWait,
    dlt! "contendersAhead — cores contending for a lock in an execution"
      contendersAhead .boundedWait,
    dlt! "contendersAhead_le — contention ≤ numCores - 1 per lock"
      contendersAhead_le .boundedWait,
    dlt! "WCRT — contention-sensitive worst-case response time"
      WCRT .boundedWait,
    dlt! "WCRT_le_totalWaitCost — WCRT ≤ the uniform combinatorial bound"
      WCRT_le_totalWaitCost .boundedWait,
    dlt! "boundedWait_under_2pl — SM3.D.6 noDeadlock ∧ WCRT ≤ maxLockSetSize*(numCores-1)*T_cs"
      boundedWait_under_2pl .boundedWait,
    -- §7/§7b/§7c grounding (9)
    dlt! "acquireOrder_nodup — projected acquire order has distinct LockIds"
      acquireOrder_nodup .grounding,
    dlt! "CorePrefixOf — a core in the 2PL growing-phase prefix of S"
      CorePrefixOf .grounding,
    dlt! "coreFollows2PL_of_prefix — prefix ⟹ per-core 2PL"
      coreFollows2PL_of_prefix .grounding,
    dlt! "coreAcquiresInOrder_of_prefix — prefix ⟹ per-core ordering"
      coreAcquiresInOrder_of_prefix .grounding,
    dlt! "execution_satisfies_hypotheses_of_all_prefix — hypotheses are consequences of 2PL"
      execution_satisfies_hypotheses_of_all_prefix .grounding,
    dlt! "executionOfHeld — KernelExecution of a core holding a lock set"
      executionOfHeld .grounding,
    dlt! "executionOfHeld_heldBy — abstract heldBy = lock set membership"
      executionOfHeld_heldBy .grounding,
    dlt! "lockSetHeld_realizes_heldBy — concrete lockSetHeld realizes abstract heldBy"
      lockSetHeld_realizes_heldBy .grounding,
    dlt! "twoCorePathScenario — SM3.D.7 two-core acquire scenario"
      twoCorePathScenario .grounding]

/-- WS-SM SM3.D: the inventory has exactly 66 entries. -/
theorem deadlockTheorems_count :
    deadlockTheorems.length = 66 := by decide

/-- WS-SM SM3.D: 3 entries in `model`. -/
theorem deadlockTheorems_model_count :
    (deadlockTheorems.filter (fun t => t.category == .model)).length = 3 := by decide

/-- WS-SM SM3.D: 5 entries in `hypotheses`. -/
theorem deadlockTheorems_hypotheses_count :
    (deadlockTheorems.filter (fun t => t.category == .hypotheses)).length = 5 := by decide

/-- WS-SM SM3.D: 5 entries in `order`. -/
theorem deadlockTheorems_order_count :
    (deadlockTheorems.filter (fun t => t.category == .order)).length = 5 := by decide

/-- WS-SM SM3.D: 6 entries in `deadlock`. -/
theorem deadlockTheorems_deadlock_count :
    (deadlockTheorems.filter (fun t => t.category == .deadlock)).length = 6 := by decide

/-- WS-SM SM3.D: 9 entries in `waitGraph`. -/
theorem deadlockTheorems_waitGraph_count :
    (deadlockTheorems.filter (fun t => t.category == .waitGraph)).length = 9 := by decide

/-- WS-SM SM3.D: 5 entries in `modeAware`. -/
theorem deadlockTheorems_modeAware_count :
    (deadlockTheorems.filter (fun t => t.category == .modeAware)).length = 5 := by decide

/-- WS-SM SM3.D: 8 entries in `sizeBound`. -/
theorem deadlockTheorems_sizeBound_count :
    (deadlockTheorems.filter (fun t => t.category == .sizeBound)).length = 8 := by decide

/-- WS-SM SM3.D: 16 entries in `boundedWait`. -/
theorem deadlockTheorems_boundedWait_count :
    (deadlockTheorems.filter (fun t => t.category == .boundedWait)).length = 16 := by decide

/-- WS-SM SM3.D: 9 entries in `grounding`. -/
theorem deadlockTheorems_grounding_count :
    (deadlockTheorems.filter (fun t => t.category == .grounding)).length = 9 := by decide

/-- WS-SM SM3.D: per-category counts sum to the total. -/
theorem deadlockTheorems_partition_sum :
    (deadlockTheorems.filter (fun t => t.category == .model)).length +
    (deadlockTheorems.filter (fun t => t.category == .hypotheses)).length +
    (deadlockTheorems.filter (fun t => t.category == .order)).length +
    (deadlockTheorems.filter (fun t => t.category == .deadlock)).length +
    (deadlockTheorems.filter (fun t => t.category == .waitGraph)).length +
    (deadlockTheorems.filter (fun t => t.category == .modeAware)).length +
    (deadlockTheorems.filter (fun t => t.category == .sizeBound)).length +
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
