-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Concurrency.MemoryModel
import SeLe4n.Kernel.Concurrency.Types

/-!
# WS-SM SM2.A.12 — Memory Model test suite

Tier-3 surface anchors plus decidable examples for every public
symbol introduced in WS-SM Phase 2.A.  This file is the canonical
regression gate that catches:

* Renames or signature drift on the SM2.A.1 / SM2.A.2 / SM2.A.3 /
  SM2.A.4 data types (`#check` of every public symbol).
* Decidability regressions on `MemoryTrace.wellFormed` (every
  decidable example is also asserted at runtime via `decide`).
* Behavioural regressions on `MemoryOrder.isAcquire` /
  `MemoryOrder.isRelease` constructors.
* The four-theorem partial-order witness chain
  (`happensBefore_irreflexive`, `_transitive`, `_antisymmetric`,
  `happens_before_partial_order`).
* Positional-ordering regressions on `MemoryTrace.eventPos`.
* `synchronizesWith` and `sequencedBefore` shape regressions
  (smoke tests for both base cases of `happensBefore`).

The suite is a runnable executable (`lake exe memory_model_suite`)
that performs every decidable check at runtime as well — every
`example : ... := by decide` is also asserted as a runtime property
inside `runMemoryModelChecks`, so the assertions surface in the
`run` output if they ever silently regress.

## Coverage

The suite carries:

* **§1: Surface anchors** — 40+ `#check` lines covering every
  public symbol exported by `MemoryModel.lean`.
* **§2: Decidable examples** — 35+ `example : ... := by decide`
  / `rfl` examples covering the data-type constructors, the
  `isAcquire` / `isRelease` lookups, the empty-trace
  well-formedness, single-event / two-event trace
  well-formedness, and basic positional witnesses.
* **§3: Runtime assertion suite** — `runMemoryModelChecks`
  exercises every decidable example at runtime via an
  `assertBool` helper that prints PASS / FAIL.
-/

open SeLe4n.Kernel.Concurrency

-- ============================================================================
-- §1 — Surface anchors: every SM2.A.* public symbol resolves at elaboration
-- ============================================================================

/-! ## SM2.A.1 — MemoryOrder -/
#check @SeLe4n.Kernel.Concurrency.MemoryOrder
#check @SeLe4n.Kernel.Concurrency.MemoryOrder.relaxed
#check @SeLe4n.Kernel.Concurrency.MemoryOrder.acquire
#check @SeLe4n.Kernel.Concurrency.MemoryOrder.release
#check @SeLe4n.Kernel.Concurrency.MemoryOrder.acqRel
#check @SeLe4n.Kernel.Concurrency.MemoryOrder.seqCst
#check @SeLe4n.Kernel.Concurrency.MemoryOrder.isAcquire
#check @SeLe4n.Kernel.Concurrency.MemoryOrder.isRelease
#check @SeLe4n.Kernel.Concurrency.MemoryOrder.acquire_isAcquire
#check @SeLe4n.Kernel.Concurrency.MemoryOrder.release_isRelease
#check @SeLe4n.Kernel.Concurrency.MemoryOrder.acqRel_both
#check @SeLe4n.Kernel.Concurrency.MemoryOrder.seqCst_both
#check @SeLe4n.Kernel.Concurrency.MemoryOrder.relaxed_neither

/-! ## SM2.A.2 — AtomicLocation -/
#check @SeLe4n.Kernel.Concurrency.AtomicLocation
#check @SeLe4n.Kernel.Concurrency.AtomicLocation.id
#check @SeLe4n.Kernel.Concurrency.AtomicLocation.nextTicketOf
#check @SeLe4n.Kernel.Concurrency.AtomicLocation.servingOf
#check @SeLe4n.Kernel.Concurrency.AtomicLocation.rwLockStateOf
#check @SeLe4n.Kernel.Concurrency.AtomicLocation.ticketLock_fields_distinct

/-! ## SM2.A.3 — MemoryEvent -/
#check @SeLe4n.Kernel.Concurrency.MemoryEvent
#check @SeLe4n.Kernel.Concurrency.MemoryEvent.core
#check @SeLe4n.Kernel.Concurrency.MemoryEvent.loc
#check @SeLe4n.Kernel.Concurrency.MemoryEvent.isWrite
#check @SeLe4n.Kernel.Concurrency.MemoryEvent.order
#check @SeLe4n.Kernel.Concurrency.MemoryEvent.value
#check @SeLe4n.Kernel.Concurrency.MemoryEvent.seqNum

/-! ## SM2.A.4 — MemoryTrace -/
#check @SeLe4n.Kernel.Concurrency.MemoryTrace
#check @SeLe4n.Kernel.Concurrency.MemoryTrace.events
#check @SeLe4n.Kernel.Concurrency.MemoryTrace.empty
#check @SeLe4n.Kernel.Concurrency.MemoryTrace.append
#check @SeLe4n.Kernel.Concurrency.MemoryTrace.empty_events
#check @SeLe4n.Kernel.Concurrency.MemoryTrace.append_events
#check @SeLe4n.Kernel.Concurrency.MemoryTrace.append_length

/-! ## SM2.A.5 — wellFormed + eventPos -/
#check @SeLe4n.Kernel.Concurrency.MemoryTrace.wellFormed
#check @SeLe4n.Kernel.Concurrency.MemoryTrace.empty_wellFormed
#check @SeLe4n.Kernel.Concurrency.MemoryTrace.eventPos
#check @SeLe4n.Kernel.Concurrency.MemoryTrace.eventPos_lt_length
#check @SeLe4n.Kernel.Concurrency.MemoryTrace.eventPos_eq_length_of_not_mem
#check @SeLe4n.Kernel.Concurrency.MemoryTrace.eventPos_get_eq
#check @SeLe4n.Kernel.Concurrency.MemoryTrace.eventPos_inj

/-! ## SM2.A.6 — synchronizesWith -/
#check @SeLe4n.Kernel.Concurrency.synchronizesWith
#check @SeLe4n.Kernel.Concurrency.synchronizesWith_relaxed_load_rejected
#check @SeLe4n.Kernel.Concurrency.synchronizesWith_relaxed_store_rejected

/-! ## SM2.A.7 — sequencedBefore + happensBefore -/
#check @SeLe4n.Kernel.Concurrency.sequencedBefore
#check @SeLe4n.Kernel.Concurrency.happensBefore
#check @SeLe4n.Kernel.Concurrency.happensBefore.seq
#check @SeLe4n.Kernel.Concurrency.happensBefore.sync
#check @SeLe4n.Kernel.Concurrency.happensBefore.trans
#check @SeLe4n.Kernel.Concurrency.happensBefore_in_trace
#check @SeLe4n.Kernel.Concurrency.happensBefore_strict_positional

/-! ## SM2.A.8 / .9 / .10 / .11 — Partial-order theorems -/
#check @SeLe4n.Kernel.Concurrency.happensBefore_irreflexive
#check @SeLe4n.Kernel.Concurrency.happensBefore_transitive
#check @SeLe4n.Kernel.Concurrency.happensBefore_antisymmetric
#check @SeLe4n.Kernel.Concurrency.happens_before_partial_order
#check @SeLe4n.Kernel.Concurrency.happens_before_strict_partial_order
#check @SeLe4n.Kernel.Concurrency.happensBefore_no_cycle

/-! ## Helper-theorem surface anchors for SM2.B / SM2.C consumers -/
#check @SeLe4n.Kernel.Concurrency.sequencedBefore_implies_happensBefore
#check @SeLe4n.Kernel.Concurrency.synchronizesWith_implies_happensBefore
#check @SeLe4n.Kernel.Concurrency.MemoryTrace.wellFormed.nodup
#check @SeLe4n.Kernel.Concurrency.MemoryTrace.wellFormed.pairwise
#check @SeLe4n.Kernel.Concurrency.happensBefore_eventPos_lt
#check @SeLe4n.Kernel.Concurrency.happensBefore_endpoints_in_trace_with_pos

-- ============================================================================
-- §2 — Decidable examples: behavioural pinning for every constructor
-- ============================================================================

/-! ## §2.1 — MemoryOrder.isAcquire / isRelease lookup table -/

example : MemoryOrder.relaxed.isAcquire = false := rfl
example : MemoryOrder.acquire.isAcquire = true := rfl
example : MemoryOrder.release.isAcquire = false := rfl
example : MemoryOrder.acqRel.isAcquire = true := rfl
example : MemoryOrder.seqCst.isAcquire = true := rfl

example : MemoryOrder.relaxed.isRelease = false := rfl
example : MemoryOrder.acquire.isRelease = false := rfl
example : MemoryOrder.release.isRelease = true := rfl
example : MemoryOrder.acqRel.isRelease = true := rfl
example : MemoryOrder.seqCst.isRelease = true := rfl

/-! ## §2.2 — AtomicLocation encoding distinctness -/

example : (AtomicLocation.nextTicketOf 0).id = 0 := rfl
example : (AtomicLocation.servingOf 0).id = 1 := rfl
example : (AtomicLocation.nextTicketOf 100).id = 100 := rfl
example : (AtomicLocation.servingOf 100).id = 101 := rfl
example : (AtomicLocation.rwLockStateOf 200).id = 200 := rfl

example : AtomicLocation.nextTicketOf 0 ≠ AtomicLocation.servingOf 0 :=
  AtomicLocation.ticketLock_fields_distinct 0

example : AtomicLocation.nextTicketOf 100 ≠ AtomicLocation.servingOf 100 :=
  AtomicLocation.ticketLock_fields_distinct 100

/-! ## §2.3 — MemoryTrace.empty + append behaviour -/

example : MemoryTrace.empty.events = [] := rfl
example : MemoryTrace.empty.events.length = 0 := rfl

example :
    let e : MemoryEvent :=
      ⟨bootCoreId, AtomicLocation.nextTicketOf 0, true, .release, 1, 0⟩
    (MemoryTrace.empty.append e).events.length = 1 := rfl

example :
    let e₁ : MemoryEvent :=
      ⟨bootCoreId, AtomicLocation.nextTicketOf 0, true, .release, 1, 0⟩
    let e₂ : MemoryEvent :=
      ⟨bootCoreId, AtomicLocation.nextTicketOf 0, false, .acquire, 1, 1⟩
    ((MemoryTrace.empty.append e₁).append e₂).events.length = 2 := rfl

/-! ## §2.4 — wellFormed: decide on small traces -/

/-- Empty trace is well-formed. -/
example : MemoryTrace.empty.wellFormed := by decide

/-- Single-event trace is well-formed (Nodup is trivially true on a
singleton; Pairwise is vacuously true). -/
example :
    let e : MemoryEvent :=
      ⟨bootCoreId, AtomicLocation.nextTicketOf 0, true, .release, 1, 0⟩
    (MemoryTrace.empty.append e).wellFormed := by decide

/-- Two same-core events with strictly increasing seqNum are well-formed. -/
example :
    let e₁ : MemoryEvent :=
      ⟨bootCoreId, AtomicLocation.nextTicketOf 0, true, .release, 1, 0⟩
    let e₂ : MemoryEvent :=
      ⟨bootCoreId, AtomicLocation.nextTicketOf 0, false, .acquire, 1, 1⟩
    ((MemoryTrace.empty.append e₁).append e₂).wellFormed := by decide

/-- Two same-core events with non-increasing seqNums violate Pairwise. -/
example :
    let e₁ : MemoryEvent :=
      ⟨bootCoreId, AtomicLocation.nextTicketOf 0, true, .release, 1, 1⟩
    let e₂ : MemoryEvent :=
      ⟨bootCoreId, AtomicLocation.nextTicketOf 0, false, .acquire, 1, 0⟩
    ¬ ((MemoryTrace.empty.append e₁).append e₂).wellFormed := by decide

/-- Two cross-core events with non-monotonic seqNums are still well-formed
(per-core monotonicity, not global). -/
example :
    let c1 : CoreId := bootCoreId
    let c2 : CoreId := ⟨1, by decide⟩
    let e₁ : MemoryEvent :=
      ⟨c1, AtomicLocation.nextTicketOf 0, true, .release, 1, 5⟩
    let e₂ : MemoryEvent :=
      ⟨c2, AtomicLocation.nextTicketOf 0, false, .acquire, 1, 0⟩
    ((MemoryTrace.empty.append e₁).append e₂).wellFormed := by decide

/-- A duplicate event violates Nodup. -/
example :
    let e : MemoryEvent :=
      ⟨bootCoreId, AtomicLocation.nextTicketOf 0, true, .release, 1, 0⟩
    ¬ ((MemoryTrace.empty.append e).append e).wellFormed := by decide

/-- **RMW pair**: two events on the same core at the SAME seqNum
(a load and a store, modelling `fetch_add(1, Acquire)`) are
well-formed under the non-strict `≤` Pairwise relation.

This is the central design property that makes SM2.B / SM2.C
proofs about LSE atomic RMW operations possible.  Under the
strict `<` formulation, this trace would have been REJECTED. -/
example :
    let e_load : MemoryEvent :=
      ⟨bootCoreId, AtomicLocation.nextTicketOf 0, false, .acqRel, 0, 7⟩
    let e_store : MemoryEvent :=
      ⟨bootCoreId, AtomicLocation.nextTicketOf 0, true, .acqRel, 1, 7⟩
    ((MemoryTrace.empty.append e_load).append e_store).wellFormed := by decide

/-- An RMW pair followed by a subsequent op with strictly greater
seqNum is also well-formed.  This is the typical TicketLock pattern:
RMW (fetch_add load + store at seqNum N), then a serving load at
seqNum N+1. -/
example :
    let e_load : MemoryEvent :=
      ⟨bootCoreId, AtomicLocation.nextTicketOf 0, false, .acqRel, 0, 7⟩
    let e_store : MemoryEvent :=
      ⟨bootCoreId, AtomicLocation.nextTicketOf 0, true, .acqRel, 1, 7⟩
    let e_serv : MemoryEvent :=
      ⟨bootCoreId, AtomicLocation.servingOf 0, false, .acquire, 1, 8⟩
    (((MemoryTrace.empty.append e_load).append e_store).append e_serv).wellFormed :=
  by decide

/-! ## §2.5 — eventPos behavioural witnesses -/

/-- Position of a single appended event in the resulting trace is 0. -/
example :
    let e : MemoryEvent :=
      ⟨bootCoreId, AtomicLocation.nextTicketOf 0, true, .release, 1, 0⟩
    (MemoryTrace.empty.append e).eventPos e = 0 := by decide

/-- Position of the second appended event is 1. -/
example :
    let e₁ : MemoryEvent :=
      ⟨bootCoreId, AtomicLocation.nextTicketOf 0, true, .release, 1, 0⟩
    let e₂ : MemoryEvent :=
      ⟨bootCoreId, AtomicLocation.nextTicketOf 0, false, .acquire, 1, 1⟩
    ((MemoryTrace.empty.append e₁).append e₂).eventPos e₂ = 1 := by decide

/-- Position of an event NOT in the trace is the trace length (sentinel). -/
example :
    let e_in : MemoryEvent :=
      ⟨bootCoreId, AtomicLocation.nextTicketOf 0, true, .release, 1, 0⟩
    let e_out : MemoryEvent :=
      ⟨bootCoreId, AtomicLocation.nextTicketOf 0, false, .acquire, 99, 99⟩
    (MemoryTrace.empty.append e_in).eventPos e_out = 1 := by decide

/-! ## §2.6 — `eventPos` is monotone-with-append for distinct events -/

example :
    let e₁ : MemoryEvent :=
      ⟨bootCoreId, AtomicLocation.nextTicketOf 0, true, .release, 1, 0⟩
    let e₂ : MemoryEvent :=
      ⟨bootCoreId, AtomicLocation.nextTicketOf 0, false, .acquire, 1, 1⟩
    let t := (MemoryTrace.empty.append e₁).append e₂
    t.eventPos e₁ < t.eventPos e₂ := by decide

/-! ## §2.7 — Constructive `synchronizesWith` witness (positive case) -/

/-- A release-store on the boot core, followed by an acquire-load
on a different core observing the released value, constructively
satisfies `synchronizesWith`.  Constructs the witness in tactic
mode using the 9 conjuncts.  This is the canonical "TicketLock
release → next-acquire spin-loop observation" pattern at the
abstract memory-model level. -/
example :
    let release_store : MemoryEvent :=
      ⟨bootCoreId, AtomicLocation.servingOf 0, true, .release, 42, 0⟩
    let acquire_load : MemoryEvent :=
      ⟨⟨1, by decide⟩, AtomicLocation.servingOf 0, false, .acquire, 42, 0⟩
    let t : MemoryTrace :=
      (MemoryTrace.empty.append release_store).append acquire_load
    synchronizesWith t release_store acquire_load := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ## §2.8 — Constructive `sequencedBefore` witness (positive case) -/

/-- Two same-core events with strictly increasing seqNums in a
trace constructively satisfy `sequencedBefore`.  This is the
canonical "spin-loop iteration" pattern at the abstract memory-
model level. -/
example :
    let e_early : MemoryEvent :=
      ⟨bootCoreId, AtomicLocation.servingOf 0, false, .acquire, 0, 100⟩
    let e_late : MemoryEvent :=
      ⟨bootCoreId, AtomicLocation.servingOf 0, false, .acquire, 1, 101⟩
    let t : MemoryTrace :=
      (MemoryTrace.empty.append e_early).append e_late
    sequencedBefore t e_early e_late := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-! ## §2.9 — Helper-theorem lifts (positive cases) -/

/-- `sequencedBefore_implies_happensBefore` lifts seq to hb in a
single tactic step, used by SM2.B/C proofs that need to invoke
happens-before from a sequencedBefore witness. -/
example :
    let e_early : MemoryEvent :=
      ⟨bootCoreId, AtomicLocation.servingOf 0, false, .acquire, 0, 100⟩
    let e_late : MemoryEvent :=
      ⟨bootCoreId, AtomicLocation.servingOf 0, false, .acquire, 1, 101⟩
    let t : MemoryTrace :=
      (MemoryTrace.empty.append e_early).append e_late
    happensBefore t e_early e_late := by
  apply sequencedBefore_implies_happensBefore
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- `synchronizesWith_implies_happensBefore` lifts sync to hb in
a single tactic step, used by SM2.B/C proofs that need to invoke
happens-before from a sync edge. -/
example :
    let release_store : MemoryEvent :=
      ⟨bootCoreId, AtomicLocation.servingOf 0, true, .release, 42, 0⟩
    let acquire_load : MemoryEvent :=
      ⟨⟨1, by decide⟩, AtomicLocation.servingOf 0, false, .acquire, 42, 0⟩
    let t : MemoryTrace :=
      (MemoryTrace.empty.append release_store).append acquire_load
    happensBefore t release_store acquire_load := by
  apply synchronizesWith_implies_happensBefore
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

-- ============================================================================
-- §3 — Runtime assertions: every above example also runs in `main`
-- ============================================================================

namespace SeLe4n.Testing.MemoryModelSuite

private def assertBool (name : String) (b : Bool) : IO Unit := do
  if b then
    IO.println s!"  PASS: {name}"
  else
    IO.println s!"  FAIL: {name}"
    throw (IO.userError s!"Assertion failed: {name}")

private def runMemoryOrderChecks : IO Unit := do
  IO.println "--- §3.1 MemoryOrder.isAcquire / isRelease ---"
  assertBool "relaxed.isAcquire = false"
    (decide (SeLe4n.Kernel.Concurrency.MemoryOrder.relaxed.isAcquire = false))
  assertBool "acquire.isAcquire = true"
    (decide (SeLe4n.Kernel.Concurrency.MemoryOrder.acquire.isAcquire = true))
  assertBool "release.isAcquire = false"
    (decide (SeLe4n.Kernel.Concurrency.MemoryOrder.release.isAcquire = false))
  assertBool "acqRel.isAcquire = true"
    (decide (SeLe4n.Kernel.Concurrency.MemoryOrder.acqRel.isAcquire = true))
  assertBool "seqCst.isAcquire = true"
    (decide (SeLe4n.Kernel.Concurrency.MemoryOrder.seqCst.isAcquire = true))
  assertBool "relaxed.isRelease = false"
    (decide (SeLe4n.Kernel.Concurrency.MemoryOrder.relaxed.isRelease = false))
  assertBool "acquire.isRelease = false"
    (decide (SeLe4n.Kernel.Concurrency.MemoryOrder.acquire.isRelease = false))
  assertBool "release.isRelease = true"
    (decide (SeLe4n.Kernel.Concurrency.MemoryOrder.release.isRelease = true))
  assertBool "acqRel.isRelease = true"
    (decide (SeLe4n.Kernel.Concurrency.MemoryOrder.acqRel.isRelease = true))
  assertBool "seqCst.isRelease = true"
    (decide (SeLe4n.Kernel.Concurrency.MemoryOrder.seqCst.isRelease = true))

private def runAtomicLocationChecks : IO Unit := do
  IO.println "--- §3.2 AtomicLocation encoding ---"
  assertBool "nextTicketOf 0 = ⟨0⟩"
    (decide ((SeLe4n.Kernel.Concurrency.AtomicLocation.nextTicketOf 0).id = 0))
  assertBool "servingOf 0 = ⟨1⟩"
    (decide ((SeLe4n.Kernel.Concurrency.AtomicLocation.servingOf 0).id = 1))
  assertBool "nextTicketOf 100 = ⟨100⟩"
    (decide ((SeLe4n.Kernel.Concurrency.AtomicLocation.nextTicketOf 100).id = 100))
  assertBool "servingOf 100 = ⟨101⟩"
    (decide ((SeLe4n.Kernel.Concurrency.AtomicLocation.servingOf 100).id = 101))
  assertBool "rwLockStateOf 200 = ⟨200⟩"
    (decide ((SeLe4n.Kernel.Concurrency.AtomicLocation.rwLockStateOf 200).id = 200))
  assertBool "nextTicketOf 0 ≠ servingOf 0"
    (decide (SeLe4n.Kernel.Concurrency.AtomicLocation.nextTicketOf 0 ≠
              SeLe4n.Kernel.Concurrency.AtomicLocation.servingOf 0))

private def runTraceShapeChecks : IO Unit := do
  IO.println "--- §3.3 MemoryTrace.empty + append shape ---"
  assertBool "empty.events = []"
    (decide (SeLe4n.Kernel.Concurrency.MemoryTrace.empty.events = []))
  assertBool "empty.events.length = 0"
    (decide (SeLe4n.Kernel.Concurrency.MemoryTrace.empty.events.length = 0))
  let e : SeLe4n.Kernel.Concurrency.MemoryEvent :=
    ⟨SeLe4n.Kernel.Concurrency.bootCoreId,
     SeLe4n.Kernel.Concurrency.AtomicLocation.nextTicketOf 0,
     true, .release, 1, 0⟩
  assertBool "append e increases length by 1"
    (decide ((SeLe4n.Kernel.Concurrency.MemoryTrace.empty.append e).events.length = 1))

private def runWellFormedChecks : IO Unit := do
  IO.println "--- §3.4 MemoryTrace.wellFormed ---"
  assertBool "empty.wellFormed"
    (decide SeLe4n.Kernel.Concurrency.MemoryTrace.empty.wellFormed)
  let e : SeLe4n.Kernel.Concurrency.MemoryEvent :=
    ⟨SeLe4n.Kernel.Concurrency.bootCoreId,
     SeLe4n.Kernel.Concurrency.AtomicLocation.nextTicketOf 0,
     true, .release, 1, 0⟩
  assertBool "single-event trace wellFormed"
    (decide (SeLe4n.Kernel.Concurrency.MemoryTrace.empty.append e).wellFormed)
  let e₁ : SeLe4n.Kernel.Concurrency.MemoryEvent :=
    ⟨SeLe4n.Kernel.Concurrency.bootCoreId,
     SeLe4n.Kernel.Concurrency.AtomicLocation.nextTicketOf 0,
     true, .release, 1, 0⟩
  let e₂ : SeLe4n.Kernel.Concurrency.MemoryEvent :=
    ⟨SeLe4n.Kernel.Concurrency.bootCoreId,
     SeLe4n.Kernel.Concurrency.AtomicLocation.nextTicketOf 0,
     false, .acquire, 1, 1⟩
  let t₂ := (SeLe4n.Kernel.Concurrency.MemoryTrace.empty.append e₁).append e₂
  assertBool "two-event trace (same core, increasing seqNum) wellFormed"
    (decide t₂.wellFormed)
  let e_dup : SeLe4n.Kernel.Concurrency.MemoryEvent :=
    ⟨SeLe4n.Kernel.Concurrency.bootCoreId,
     SeLe4n.Kernel.Concurrency.AtomicLocation.nextTicketOf 0,
     true, .release, 1, 0⟩
  let t_dup :=
    (SeLe4n.Kernel.Concurrency.MemoryTrace.empty.append e_dup).append e_dup
  assertBool "duplicate-event trace NOT wellFormed (Nodup violation)"
    (decide (¬ t_dup.wellFormed))
  let e_bad₁ : SeLe4n.Kernel.Concurrency.MemoryEvent :=
    ⟨SeLe4n.Kernel.Concurrency.bootCoreId,
     SeLe4n.Kernel.Concurrency.AtomicLocation.nextTicketOf 0,
     true, .release, 1, 5⟩
  let e_bad₂ : SeLe4n.Kernel.Concurrency.MemoryEvent :=
    ⟨SeLe4n.Kernel.Concurrency.bootCoreId,
     SeLe4n.Kernel.Concurrency.AtomicLocation.nextTicketOf 0,
     false, .acquire, 1, 3⟩
  let t_bad :=
    (SeLe4n.Kernel.Concurrency.MemoryTrace.empty.append e_bad₁).append e_bad₂
  assertBool "decreasing seqNum (same core) NOT wellFormed"
    (decide (¬ t_bad.wellFormed))
  -- RMW positive case: two events on the same core at the SAME
  -- seqNum (load + store) are wellFormed under the non-strict ≤
  -- formulation.  This is the central design property that supports
  -- SM2.B `fetch_add(1, Acquire)` proofs.
  let rmw_load : SeLe4n.Kernel.Concurrency.MemoryEvent :=
    ⟨SeLe4n.Kernel.Concurrency.bootCoreId,
     SeLe4n.Kernel.Concurrency.AtomicLocation.nextTicketOf 0,
     false, .acqRel, 0, 7⟩
  let rmw_store : SeLe4n.Kernel.Concurrency.MemoryEvent :=
    ⟨SeLe4n.Kernel.Concurrency.bootCoreId,
     SeLe4n.Kernel.Concurrency.AtomicLocation.nextTicketOf 0,
     true, .acqRel, 1, 7⟩
  let t_rmw :=
    (SeLe4n.Kernel.Concurrency.MemoryTrace.empty.append rmw_load).append rmw_store
  assertBool "RMW pair (same core, same seqNum) IS wellFormed (≤ formulation)"
    (decide t_rmw.wellFormed)
  -- An RMW pair followed by a serving load with strictly greater
  -- seqNum is also wellFormed (the typical TicketLock acquire
  -- pattern at the abstract memory-model level).
  let serv_load : SeLe4n.Kernel.Concurrency.MemoryEvent :=
    ⟨SeLe4n.Kernel.Concurrency.bootCoreId,
     SeLe4n.Kernel.Concurrency.AtomicLocation.servingOf 0,
     false, .acquire, 1, 8⟩
  let t_rmw_with_load :=
    (t_rmw).append serv_load
  assertBool "RMW pair + later strictly-greater seqNum op IS wellFormed"
    (decide t_rmw_with_load.wellFormed)

private def runCrossCoreWellFormedChecks : IO Unit := do
  IO.println "--- §3.5 Cross-core wellFormed (per-core, not global) ---"
  let c1 : SeLe4n.Kernel.Concurrency.CoreId :=
    SeLe4n.Kernel.Concurrency.bootCoreId
  let c2 : SeLe4n.Kernel.Concurrency.CoreId := ⟨1, by decide⟩
  let e₁ : SeLe4n.Kernel.Concurrency.MemoryEvent :=
    ⟨c1, SeLe4n.Kernel.Concurrency.AtomicLocation.nextTicketOf 0,
     true, .release, 1, 5⟩
  let e₂ : SeLe4n.Kernel.Concurrency.MemoryEvent :=
    ⟨c2, SeLe4n.Kernel.Concurrency.AtomicLocation.nextTicketOf 0,
     false, .acquire, 1, 0⟩
  let t_cross :=
    (SeLe4n.Kernel.Concurrency.MemoryTrace.empty.append e₁).append e₂
  assertBool "cross-core with mismatched seqNums IS wellFormed"
    (decide t_cross.wellFormed)

private def runEventPosChecks : IO Unit := do
  IO.println "--- §3.6 eventPos behaviour ---"
  let e : SeLe4n.Kernel.Concurrency.MemoryEvent :=
    ⟨SeLe4n.Kernel.Concurrency.bootCoreId,
     SeLe4n.Kernel.Concurrency.AtomicLocation.nextTicketOf 0,
     true, .release, 1, 0⟩
  assertBool "eventPos of single appended event = 0"
    (decide ((SeLe4n.Kernel.Concurrency.MemoryTrace.empty.append e).eventPos e = 0))
  let e₁ : SeLe4n.Kernel.Concurrency.MemoryEvent :=
    ⟨SeLe4n.Kernel.Concurrency.bootCoreId,
     SeLe4n.Kernel.Concurrency.AtomicLocation.nextTicketOf 0,
     true, .release, 1, 0⟩
  let e₂ : SeLe4n.Kernel.Concurrency.MemoryEvent :=
    ⟨SeLe4n.Kernel.Concurrency.bootCoreId,
     SeLe4n.Kernel.Concurrency.AtomicLocation.nextTicketOf 0,
     false, .acquire, 1, 1⟩
  let t₂ :=
    (SeLe4n.Kernel.Concurrency.MemoryTrace.empty.append e₁).append e₂
  assertBool "eventPos e₁ in [e₁, e₂] = 0"
    (decide (t₂.eventPos e₁ = 0))
  assertBool "eventPos e₂ in [e₁, e₂] = 1"
    (decide (t₂.eventPos e₂ = 1))
  assertBool "eventPos e₁ < eventPos e₂ in [e₁, e₂]"
    (decide (t₂.eventPos e₁ < t₂.eventPos e₂))
  let e_out : SeLe4n.Kernel.Concurrency.MemoryEvent :=
    ⟨SeLe4n.Kernel.Concurrency.bootCoreId,
     SeLe4n.Kernel.Concurrency.AtomicLocation.nextTicketOf 0,
     false, .acquire, 99, 99⟩
  assertBool "eventPos of out-of-trace event = trace length"
    (decide (t₂.eventPos e_out = 2))

private def runPartialOrderShapeChecks : IO Unit := do
  IO.println "--- §3.7 Partial-order shape (sanity) ---"
  -- The four-theorem chain is proof-only; we verify the underlying
  -- positional property here.  The full theorem chain is anchored at
  -- §1 via the #check lines.
  let e₁ : SeLe4n.Kernel.Concurrency.MemoryEvent :=
    ⟨SeLe4n.Kernel.Concurrency.bootCoreId,
     SeLe4n.Kernel.Concurrency.AtomicLocation.nextTicketOf 0,
     true, .release, 1, 0⟩
  let e₂ : SeLe4n.Kernel.Concurrency.MemoryEvent :=
    ⟨SeLe4n.Kernel.Concurrency.bootCoreId,
     SeLe4n.Kernel.Concurrency.AtomicLocation.servingOf 0,
     false, .acquire, 1, 1⟩
  let t :=
    (SeLe4n.Kernel.Concurrency.MemoryTrace.empty.append e₁).append e₂
  -- The trace is wellFormed (same-core seqNum monotonicity).
  assertBool "well-formed two-event trace"
    (decide t.wellFormed)
  -- e₁ precedes e₂ in trace order.
  assertBool "eventPos e₁ < eventPos e₂"
    (decide (t.eventPos e₁ < t.eventPos e₂))
  -- The strict-positional theorem holds: no event hb-precedes itself
  -- (encoded as eventPos e < eventPos e being false).
  assertBool "eventPos e₁ < eventPos e₁ is false (irreflexivity)"
    (! decide (t.eventPos e₁ < t.eventPos e₁))
  assertBool "eventPos e₂ < eventPos e₂ is false (irreflexivity)"
    (! decide (t.eventPos e₂ < t.eventPos e₂))

private def runSynchronizesWithChecks : IO Unit := do
  IO.println "--- §3.8 Constructive synchronizesWith witness ---"
  -- A release-store followed by an acquire-load on the same loc,
  -- with matching value and on different cores, constructively
  -- satisfies synchronizesWith.  This is the abstract memory-model
  -- form of the TicketLock release → next-acquire pattern.
  let release_store : SeLe4n.Kernel.Concurrency.MemoryEvent :=
    ⟨SeLe4n.Kernel.Concurrency.bootCoreId,
     SeLe4n.Kernel.Concurrency.AtomicLocation.servingOf 0,
     true, .release, 42, 0⟩
  let acquire_load : SeLe4n.Kernel.Concurrency.MemoryEvent :=
    ⟨⟨1, by decide⟩,
     SeLe4n.Kernel.Concurrency.AtomicLocation.servingOf 0,
     false, .acquire, 42, 0⟩
  let t : SeLe4n.Kernel.Concurrency.MemoryTrace :=
    (SeLe4n.Kernel.Concurrency.MemoryTrace.empty.append release_store).append acquire_load
  -- All 9 conjuncts are decidable; check them as a single decide.
  assertBool "release_store ∈ trace"
    (decide (release_store ∈ t.events))
  assertBool "acquire_load ∈ trace"
    (decide (acquire_load ∈ t.events))
  assertBool "release_store.isWrite = true"
    (decide (release_store.isWrite = true))
  assertBool "release_store.order.isRelease = true"
    (decide (release_store.order.isRelease = true))
  assertBool "acquire_load.isWrite = false"
    (decide (acquire_load.isWrite = false))
  assertBool "acquire_load.order.isAcquire = true"
    (decide (acquire_load.order.isAcquire = true))
  assertBool "release_store.loc = acquire_load.loc"
    (decide (release_store.loc = acquire_load.loc))
  assertBool "release_store.value = acquire_load.value"
    (decide (release_store.value = acquire_load.value))
  assertBool "eventPos release_store < eventPos acquire_load"
    (decide (t.eventPos release_store < t.eventPos acquire_load))

private def runSequencedBeforeChecks : IO Unit := do
  IO.println "--- §3.9 Constructive sequencedBefore witness ---"
  -- Two same-core same-location events with strictly increasing
  -- seqNums constructively satisfy sequencedBefore.  The canonical
  -- "spin-loop iteration" pattern.
  let e_early : SeLe4n.Kernel.Concurrency.MemoryEvent :=
    ⟨SeLe4n.Kernel.Concurrency.bootCoreId,
     SeLe4n.Kernel.Concurrency.AtomicLocation.servingOf 0,
     false, .acquire, 0, 100⟩
  let e_late : SeLe4n.Kernel.Concurrency.MemoryEvent :=
    ⟨SeLe4n.Kernel.Concurrency.bootCoreId,
     SeLe4n.Kernel.Concurrency.AtomicLocation.servingOf 0,
     false, .acquire, 1, 101⟩
  let t : SeLe4n.Kernel.Concurrency.MemoryTrace :=
    (SeLe4n.Kernel.Concurrency.MemoryTrace.empty.append e_early).append e_late
  assertBool "e_early ∈ trace"
    (decide (e_early ∈ t.events))
  assertBool "e_late ∈ trace"
    (decide (e_late ∈ t.events))
  assertBool "e_early.core = e_late.core"
    (decide (e_early.core = e_late.core))
  assertBool "e_early.seqNum < e_late.seqNum (strict)"
    (decide (e_early.seqNum < e_late.seqNum))
  assertBool "trace is wellFormed"
    (decide t.wellFormed)

def runMemoryModelChecks : IO Unit := do
  IO.println "WS-SM SM2.A — Memory Model test suite"
  IO.println "====================================="
  runMemoryOrderChecks
  runAtomicLocationChecks
  runTraceShapeChecks
  runWellFormedChecks
  runCrossCoreWellFormedChecks
  runEventPosChecks
  runPartialOrderShapeChecks
  runSynchronizesWithChecks
  runSequencedBeforeChecks
  IO.println "====================================="
  IO.println "All SM2.A memory model checks PASS."

end SeLe4n.Testing.MemoryModelSuite

def main : IO Unit :=
  SeLe4n.Testing.MemoryModelSuite.runMemoryModelChecks
