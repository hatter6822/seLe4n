-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- STATUS: staged for WS-SM (SM2.C.20 RwLock refinement bridge).

import SeLe4n.Kernel.Concurrency.Locks.RwLock

/-!
# WS-SM SM2.C.20 — RwLock refinement bridge

This module documents the operational refinement relation between the
Lean abstract `RwLockState` (in `Locks/RwLock.lean`) and the Rust impl
(in `rust/sele4n-hal/src/rw_lock.rs`).

## Refinement summary

The refinement φ relates a Lean `RwLockState` to a Rust `AtomicU64` state
value via the bit-packed encoding:

    φ(abstract, concrete) ↔
      concrete = encodeRwLock abstract.writerHeld.isSome abstract.readers.length

* abstract.writerHeld.isSome corresponds to bit 63 of concrete (the writer bit).
* abstract.readers.length corresponds to bits 0..62 of concrete (the reader count).
* abstract.waiters is **NOT represented** in the concrete state.  The Rust
  impl uses CAS-retry with WFE for waiters; the queue is implicit through
  the order in which threads observe the state.

## FIFO divergence

The Lean spec's `rwLock_fifo_admission` theorem states that earlier
waiters are admitted before later waiters.  The Rust impl does NOT
satisfy this property: a thread that just called `acquire_read` on a
contended lock may observe the writer-bit clear and CAS-acquire BEFORE
an earlier-arrived writer that's still parked on WFE.

The mutex and exclusion invariants (`rwLock_writer_readers_exclusion`)
ARE satisfied by the Rust impl, because the CAS-retry ensures only one
core can claim the writer bit at a time, and the same-state CAS ensures
readers don't admit while writer-bit is set.

## What SM3 must verify

SM3 (per-object locks) consumes the RwLock primitive for protecting
shared kernel objects.  Per-object lock proofs cite:

* `rwLock_writer_readers_exclusion` — for state-visibility lemmas:
  writer-protected fields are not concurrently observable by readers.
* `rwLock_release_acquire_pairing_read/write` — for happens-before
  edges across release-acquire boundaries.
* `rwLock_bounded_wait_read/write` — for WCRT analysis.

SM3 does NOT rely on `rwLock_fifo_admission`.  Kernel paths that require
strict FIFO writer admission (e.g., for response-time analysis under
heavy reader contention) are flagged at SM3 review time.  If any are
found, SM2.C.20 will be extended with a queued RwLock variant.

## Simulation φ (informal)

A formal bisimulation between the Lean operational `applyOp` and the
Rust CAS-retry loop is a substantial proof that goes through:

1. At each operational step, the Rust state's bit-packed encoding equals
   `encodeRwLock(abstract.writerHeld.isSome, abstract.readers.length)`.
2. The Rust CAS-retry loop's progress condition matches the Lean spec's
   acquire branch condition.
3. The Rust release path's atomic decrement / store matches the Lean
   spec's `applyOp .releaseRead/releaseWrite` + promote step.

We do not encode this bisimulation formally at v1.0.0; instead, the
refinement is reviewed at per-PR level (each Rust function's docstring
references the corresponding Lean operation).  The cargo unit tests
exercise the round-trip encoding (`sm2c17_encoding_round_trip`) so the
bit-level correspondence is mechanically verified.

## Why not a full bisimulation proof?

Per decision #10 in the SM2 plan, the lock primitives are "verification-
quality elevated" — the Lean spec is the source of truth.  A full
formal bisimulation between the spec and impl would require:

* A FFI-level model of the Rust atomic operations (LDAR, STLR, CAS).
* A trace-based equivalence proof at the operational-semantics level.
* Mechanically checked code generation from the Lean spec to Rust.

The first two are tractable but expensive (estimated 5-10 weeks for
RwLock alone).  The third is research-grade infrastructure.

At v1.0.0, we accept the simulation as a per-PR review obligation.  The
refinement is "live": every Rust function references its Lean
counterpart in a docstring; every Lean theorem cites the corresponding
ARM instruction in its docstring; the cargo round-trip tests verify the
bit-level encoding mechanically.  This is "weak refinement with strong
spec" — the spec is verified end-to-end; the impl correspondence is
reviewer-checked at the operational level.

Post-1.0 work (SM2.C.20.a) will introduce a stricter bisimulation
checker if SM3 surfaces correspondence bugs.
-/

namespace SeLe4n.Kernel.Concurrency

-- ============================================================================
-- SM2.C.20 — Refinement φ between abstract and concrete state
-- ============================================================================

/-- **WS-SM SM2.C.20**: the refinement relation between the Lean
abstract `RwLockState` and the Rust impl's bit-packed `state : AtomicU64`.

The relation is structural:
* The concrete state equals `encodeRwLock(writerHeld.isSome, readers.length)`.
* The abstract `waiters` field is NOT represented in the concrete state
  (the Rust impl uses CAS-retry instead of an explicit queue, weakening
  FIFO admission).

The `RwLockEncoded` value is the abstraction of the Rust `AtomicU64.load(...)`
result; bit operations on it correspond to bit operations on the Rust value. -/
def rwLockSim (abstract : RwLockState) (concrete : RwLockEncoded) : Prop :=
  concrete = encodeRwLock abstract.writerHeld.isSome abstract.readers.length

/-- **WS-SM SM2.C.20**: `rwLockSim` is decidable. -/
instance decidableRwLockSim (abstract : RwLockState) (concrete : RwLockEncoded) :
    Decidable (rwLockSim abstract concrete) := by
  unfold rwLockSim
  exact inferInstance

/-- **Witness**: the unheld abstract state corresponds to concrete state 0. -/
theorem rwLockSim_unheld : rwLockSim RwLockState.unheld 0 := by
  unfold rwLockSim encodeRwLock RwLockState.unheld
  simp

/-- **Witness**: an abstract state with a writer and no readers corresponds
to concrete state `writerBit`. -/
theorem rwLockSim_writer_only (c : CoreId) :
    rwLockSim { writerHeld := some c, readers := [], waiters := [] }
              writerBit := by
  unfold rwLockSim encodeRwLock
  simp

/-- **Witness**: an abstract state with N readers corresponds to concrete
state N. -/
theorem rwLockSim_readers_only (readers : List CoreId)
    (_h_nodup : readers.Nodup) :
    rwLockSim { writerHeld := none, readers := readers, waiters := [] }
              readers.length := by
  unfold rwLockSim encodeRwLock
  simp

/-- **Surface anchor**: the refinement relation respects the writer bit.

If the concrete state has bit 63 set, then the abstract state has a
writer held (the simulation φ requires writerHeld.isSome ↔ bit 63 set). -/
theorem rwLockSim_writer_bit_iff
    (abstract : RwLockState) (concrete : RwLockEncoded)
    (h_sim : rwLockSim abstract concrete)
    (h_count_bound : abstract.readers.length < writerBit) :
    concrete ≥ writerBit ↔ abstract.writerHeld.isSome := by
  unfold rwLockSim at h_sim
  rw [h_sim]
  constructor
  · -- encodeRwLock w c ≥ writerBit → w = true.
    intro h_ge
    cases h_some : abstract.writerHeld.isSome with
    | true => rfl
    | false =>
      -- writerHeld.isSome = false → encodeRwLock false c = c < writerBit.
      exfalso
      rw [h_some] at h_ge
      unfold encodeRwLock at h_ge
      have h_simp : (if (false : Bool) then writerBit else 0) + abstract.readers.length
                  = abstract.readers.length := by simp
      rw [h_simp] at h_ge
      exact absurd h_ge (Nat.not_le_of_lt h_count_bound)
  · -- writerHeld.isSome → encodeRwLock true c ≥ writerBit.
    intro h_is_some
    unfold encodeRwLock
    rw [h_is_some]
    show (if (true : Bool) then writerBit else 0) + abstract.readers.length ≥ writerBit
    simp

/-- **Surface anchor**: the refinement preserves reader count when no
writer is held.

If writer is not held, the concrete state equals the reader count exactly. -/
theorem rwLockSim_reader_count_iff
    (abstract : RwLockState) (concrete : RwLockEncoded)
    (h_sim : rwLockSim abstract concrete)
    (h_no_writer : abstract.writerHeld = none) :
    concrete = abstract.readers.length := by
  unfold rwLockSim at h_sim
  rw [h_sim]
  unfold encodeRwLock
  rw [h_no_writer]
  simp

-- ============================================================================
-- SM2.C.20 — Refinement preservation theorem (informal)
-- ============================================================================

/-- **Theorem (SM2.C.20, informal): refinement is preserved by operations.**

For any abstract pair `(abstract, concrete)` satisfying `rwLockSim`, the
result of applying an `RwLockOp` to `abstract` produces a state that
relates to the corresponding Rust impl's atomic-step result.

Formally, this is a bisimulation: ∀ op, if `rwLockSim abstract concrete`,
then `rwLockSim (abstract.applyOp op) (concrete')` where `concrete'` is
the result of the Rust impl's corresponding atomic step.

At v1.0.0, we do not encode the Rust impl's step function in Lean (that
would require a Lean model of atomic operations).  Instead, the
refinement is reviewed per-PR.  This theorem statement is a placeholder
for the future formal bisimulation. -/
theorem rwLock_refinement_preservation_placeholder
    (abstract : RwLockState) (concrete : RwLockEncoded)
    (_h_sim : rwLockSim abstract concrete)
    (_op : RwLockOp) :
    -- Placeholder: the Rust impl's step would produce a concrete state
    -- related to the abstract post-state.  Not encoded at v1.0.0.
    True := trivial

end SeLe4n.Kernel.Concurrency
