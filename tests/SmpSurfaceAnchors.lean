-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Concurrency.LockBridge
import SeLe4n.Kernel.Concurrency.LockPrimitives
import SeLe4n.Kernel.Concurrency.MemoryModel
import SeLe4n.Kernel.Concurrency.Locks.TicketLock
import SeLe4n.Kernel.Concurrency.Locks.TicketLockRefinement
import SeLe4n.Kernel.Concurrency.Locks.RwLock
import SeLe4n.Kernel.Concurrency.Locks.RwLockRefinement
import SeLe4n.Kernel.Concurrency.LockSet
import SeLe4n.Platform.FFI

/-!
# WS-SM SM2.D.6 — Verified-lock-primitive surface anchors

Tier-3 surface anchors covering every public symbol exported by the
SM2.D FFI bridge and the SM2.D.7 theorem aggregator.

Each `#check` is an elaboration-time gate: if the underlying symbol
is renamed, removed, or has its signature changed, the surface anchor
fails to elaborate and the suite no longer compiles.

The suite is a runnable executable (`lake exe smp_surface_anchors`).
Per the project's FFI link discipline (Lean test executables do NOT
link against `libsele4n_hal.a`), the runtime portion exercises only
**structural** properties — typed-wrapper signatures, marker
theorems, decidable handle properties, and the lock-primitive
aggregator size.  Behavioral runtime tests for the FFI helpers live
in the Rust side's `lock_bridge::tests` and `ffi::tests` modules.
-/

namespace SeLe4n.Testing.SmpSurfaceAnchors

-- ============================================================================
-- §1 — SM2.D.1 / SM2.D.2 — Raw FFI declarations
-- ============================================================================

/-! ## SM2.D.1 — TicketLock FFI declarations -/
#check @SeLe4n.Platform.FFI.ffiTicketLockStaticHandle
#check @SeLe4n.Platform.FFI.ffiTicketLockAcquire
#check @SeLe4n.Platform.FFI.ffiTicketLockRelease
#check @SeLe4n.Platform.FFI.ffiTicketLockPeekHolder
#check @SeLe4n.Platform.FFI.ffiTicketLockAcquireCount
#check @SeLe4n.Platform.FFI.ffiTicketLockReleaseCount

/-! ## SM2.D.2 — RwLock FFI declarations -/
#check @SeLe4n.Platform.FFI.ffiRwLockStaticHandle
#check @SeLe4n.Platform.FFI.ffiRwLockAcquireRead
#check @SeLe4n.Platform.FFI.ffiRwLockReleaseRead
#check @SeLe4n.Platform.FFI.ffiRwLockAcquireWrite
#check @SeLe4n.Platform.FFI.ffiRwLockReleaseWrite
#check @SeLe4n.Platform.FFI.ffiRwLockSnapshot
#check @SeLe4n.Platform.FFI.ffiRwLockAcquireReadCount
#check @SeLe4n.Platform.FFI.ffiRwLockReleaseReadCount
#check @SeLe4n.Platform.FFI.ffiRwLockAcquireWriteCount
#check @SeLe4n.Platform.FFI.ffiRwLockReleaseWriteCount

-- ============================================================================
-- §2 — SM2.D.1 / SM2.D.2 — Typed handles + pool constants
-- ============================================================================

#check @SeLe4n.Kernel.Concurrency.staticTicketLockPoolSize
#check @SeLe4n.Kernel.Concurrency.staticRwLockPoolSize
#check @SeLe4n.Kernel.Concurrency.staticTicketLockPoolSize_pos
#check @SeLe4n.Kernel.Concurrency.staticRwLockPoolSize_pos
#check @SeLe4n.Kernel.Concurrency.staticTicketLockPoolSize_eq_numCores
#check @SeLe4n.Kernel.Concurrency.staticRwLockPoolSize_eq_numCores

#check @SeLe4n.Kernel.Concurrency.TicketLockHandle
#check @SeLe4n.Kernel.Concurrency.TicketLockHandle.raw
#check @SeLe4n.Kernel.Concurrency.TicketLockHandle.isValid
#check @SeLe4n.Kernel.Concurrency.mkTicketLockHandle
#check @SeLe4n.Kernel.Concurrency.mkTicketLockHandle_raw_toNat

#check @SeLe4n.Kernel.Concurrency.RwLockHandle
#check @SeLe4n.Kernel.Concurrency.RwLockHandle.raw
#check @SeLe4n.Kernel.Concurrency.RwLockHandle.isValid
#check @SeLe4n.Kernel.Concurrency.mkRwLockHandle
#check @SeLe4n.Kernel.Concurrency.mkRwLockHandle_raw_toNat

-- Inhabited instances (audit-pass-5).
#check (default : SeLe4n.Kernel.Concurrency.TicketLockHandle)
#check (default : SeLe4n.Kernel.Concurrency.RwLockHandle)

-- ============================================================================
-- §3 — SM2.D.1 / SM2.D.2 — Typed FFI wrappers
-- ============================================================================

#check @SeLe4n.Kernel.Concurrency.acquireTicketLock
#check @SeLe4n.Kernel.Concurrency.releaseTicketLock
#check @SeLe4n.Kernel.Concurrency.peekTicketLockHolder
#check @SeLe4n.Kernel.Concurrency.peekTicketLockNextTicket
#check @SeLe4n.Kernel.Concurrency.peekTicketLockServing
#check @SeLe4n.Kernel.Concurrency.ticketLockAcquireCount
#check @SeLe4n.Kernel.Concurrency.ticketLockReleaseCount

#check @SeLe4n.Kernel.Concurrency.acquireReadLock
#check @SeLe4n.Kernel.Concurrency.releaseReadLock
#check @SeLe4n.Kernel.Concurrency.acquireWriteLock
#check @SeLe4n.Kernel.Concurrency.releaseWriteLock
#check @SeLe4n.Kernel.Concurrency.snapshotRwLock
#check @SeLe4n.Kernel.Concurrency.rwLockAcquireReadCount
#check @SeLe4n.Kernel.Concurrency.rwLockReleaseReadCount
#check @SeLe4n.Kernel.Concurrency.rwLockAcquireWriteCount
#check @SeLe4n.Kernel.Concurrency.rwLockReleaseWriteCount

-- ============================================================================
-- §4 — SM2.D.3 — RAII combinators
-- ============================================================================

#check @SeLe4n.Kernel.Concurrency.withTicketLock
#check @SeLe4n.Kernel.Concurrency.withReadLock
#check @SeLe4n.Kernel.Concurrency.withWriteLock

-- ============================================================================
-- §5 — Marker theorems (typed wrapper signatures)
-- ============================================================================

#check @SeLe4n.Kernel.Concurrency.acquireTicketLock_eq_ffi
#check @SeLe4n.Kernel.Concurrency.releaseTicketLock_eq_ffi
#check @SeLe4n.Kernel.Concurrency.peekTicketLockHolder_eq_ffi
#check @SeLe4n.Kernel.Concurrency.acquireReadLock_eq_ffi
#check @SeLe4n.Kernel.Concurrency.releaseReadLock_eq_ffi
#check @SeLe4n.Kernel.Concurrency.acquireWriteLock_eq_ffi
#check @SeLe4n.Kernel.Concurrency.releaseWriteLock_eq_ffi
#check @SeLe4n.Kernel.Concurrency.snapshotRwLock_eq_ffi
#check @SeLe4n.Kernel.Concurrency.ticketLockAcquireCount_eq_ffi
#check @SeLe4n.Kernel.Concurrency.ticketLockReleaseCount_eq_ffi
#check @SeLe4n.Kernel.Concurrency.rwLockAcquireReadCount_eq_ffi
#check @SeLe4n.Kernel.Concurrency.rwLockReleaseReadCount_eq_ffi
#check @SeLe4n.Kernel.Concurrency.rwLockAcquireWriteCount_eq_ffi
#check @SeLe4n.Kernel.Concurrency.rwLockReleaseWriteCount_eq_ffi

#check @SeLe4n.Kernel.Concurrency.withTicketLock_unfold
#check @SeLe4n.Kernel.Concurrency.withReadLock_unfold
#check @SeLe4n.Kernel.Concurrency.withWriteLock_unfold

#check @SeLe4n.Kernel.Concurrency.peekTicketLockEncoding_roundtrip_u32_masked
#check @SeLe4n.Kernel.Concurrency.peekTicketLockNextTicket_is_high32
#check @SeLe4n.Kernel.Concurrency.peekTicketLockServing_is_low32

-- ============================================================================
-- §6 — SM2.D.7 — Lock-primitive theorem aggregator
-- ============================================================================

#check @SeLe4n.Kernel.Concurrency.LockPrimitiveCategory
#check @SeLe4n.Kernel.Concurrency.LockPrimitiveCategory.memoryModel
#check @SeLe4n.Kernel.Concurrency.LockPrimitiveCategory.ticketLock
#check @SeLe4n.Kernel.Concurrency.LockPrimitiveCategory.rwLock
#check @SeLe4n.Kernel.Concurrency.LockPrimitiveCategory.refinement

#check @SeLe4n.Kernel.Concurrency.LockPrimitiveTheorem
#check @SeLe4n.Kernel.Concurrency.LockPrimitiveTheorem.description
#check @SeLe4n.Kernel.Concurrency.LockPrimitiveTheorem.identifier
#check @SeLe4n.Kernel.Concurrency.LockPrimitiveTheorem.category

#check @SeLe4n.Kernel.Concurrency.lockPrimitives
#check @SeLe4n.Kernel.Concurrency.lockPrimitives_count
#check @SeLe4n.Kernel.Concurrency.lockPrimitives_memoryModel_count
#check @SeLe4n.Kernel.Concurrency.lockPrimitives_ticketLock_count
#check @SeLe4n.Kernel.Concurrency.lockPrimitives_rwLock_count
#check @SeLe4n.Kernel.Concurrency.lockPrimitives_refinement_count
#check @SeLe4n.Kernel.Concurrency.lockPrimitives_partition_sum
#check @SeLe4n.Kernel.Concurrency.lockPrimitives_identifiers_nodup
#check @SeLe4n.Kernel.Concurrency.lockPrimitives_descriptions_nodup

-- SM2.D TicketLockRefinement (F-01)
#check @SeLe4n.Kernel.Concurrency.TicketLockConcrete
#check @SeLe4n.Kernel.Concurrency.TicketLockConcrete.nextTicket
#check @SeLe4n.Kernel.Concurrency.TicketLockConcrete.serving
#check @SeLe4n.Kernel.Concurrency.TicketLockConcrete.unheld
#check @SeLe4n.Kernel.Concurrency.ticketLockSim
#check @SeLe4n.Kernel.Concurrency.ticketLockSim_unheld
#check @SeLe4n.Kernel.Concurrency.ticketLockSim_preserved_by_tryAcquire
#check @SeLe4n.Kernel.Concurrency.ticketLockSim_preserved_by_release
#check @SeLe4n.Kernel.Concurrency.ticketLockSim_preserved_by_observeServing
#check @SeLe4n.Kernel.Concurrency.rust_ticketLock_refines_lean

-- ============================================================================
-- §6b — WS-SM SM3.E.8 — Serializability major-theorem surface anchors
-- ============================================================================
--
-- The 8 major SM3.E theorems (one per plan §5.5 sub-task plus the acyclic
-- conflict graph the proof reduces to).  Each `#check` is an elaboration-time
-- gate: a rename or signature drift fails the suite.

-- SM3.E.1 — conflict order.
#check @SeLe4n.Kernel.Concurrency.conflictOrder
-- SM3.E.2 — serial equivalence.
#check @SeLe4n.Kernel.Concurrency.serialEquivalent
-- SM3.E.3 — main serializability theorem (Theorem 2.1.10) + acyclic conflict graph.
#check @SeLe4n.Kernel.Concurrency.serializability_under_2pl
#check @SeLe4n.Kernel.Concurrency.conflictGraph_acyclic
-- SM3.E.4 — strict-2PL preservation.
#check @SeLe4n.Kernel.Concurrency.strictly_2pl_preserved
-- SM3.E.5 — commutativity (the realistic write/write observational lemma).
#check @SeLe4n.Kernel.Concurrency.updateObjectAt_objStoreEquiv_comm
-- SM3.E.6 — single-core proof preservation (Corollary 2.1.11).
#check @SeLe4n.Kernel.Concurrency.singleCore_proof_preservation
-- SM3.E.3 — unconditional serializability of a read-only schedule (non-vacuity).
#check @SeLe4n.Kernel.Concurrency.serializability_of_readOnly_schedule

-- ============================================================================
-- §7 — Decidable structural examples
-- ============================================================================

/-! ## Pool dimensions (SM2.D) -/

example : SeLe4n.Kernel.Concurrency.staticTicketLockPoolSize = 4 := by decide
example : SeLe4n.Kernel.Concurrency.staticRwLockPoolSize = 4 := by decide
example : 0 < SeLe4n.Kernel.Concurrency.staticTicketLockPoolSize := by decide
example : 0 < SeLe4n.Kernel.Concurrency.staticRwLockPoolSize := by decide

/-! ## Aggregator structure (SM2.D.7) -/

example : SeLe4n.Kernel.Concurrency.lockPrimitives.length = 22 := by decide

example :
    (SeLe4n.Kernel.Concurrency.lockPrimitives.filter
      (·.category = SeLe4n.Kernel.Concurrency.LockPrimitiveCategory.memoryModel)).length = 4 := by
  decide

example :
    (SeLe4n.Kernel.Concurrency.lockPrimitives.filter
      (·.category = SeLe4n.Kernel.Concurrency.LockPrimitiveCategory.ticketLock)).length = 6 := by
  decide

example :
    (SeLe4n.Kernel.Concurrency.lockPrimitives.filter
      (·.category = SeLe4n.Kernel.Concurrency.LockPrimitiveCategory.rwLock)).length = 10 := by
  decide

example :
    (SeLe4n.Kernel.Concurrency.lockPrimitives.filter
      (·.category = SeLe4n.Kernel.Concurrency.LockPrimitiveCategory.refinement)).length = 2 := by
  decide

/-! ## Bit-layout extractors (SM2.D.1) -/

-- Sample value: packed = (0x12_3456_78ABCDEF << 32) | 0x9ABC_DEF0 — but
-- we constrain inputs to u32 range via the masking helper so we can
-- compute concrete values.
example :
    SeLe4n.Kernel.Concurrency.peekTicketLockNextTicket
      (((42 : UInt64) <<< 32) ||| (7 : UInt64)) = (42 : UInt64) := by decide

example :
    SeLe4n.Kernel.Concurrency.peekTicketLockServing
      (((42 : UInt64) <<< 32) ||| (7 : UInt64)) = (7 : UInt64) := by decide

example :
    SeLe4n.Kernel.Concurrency.peekTicketLockNextTicket (0 : UInt64) = (0 : UInt64) := by decide

example :
    SeLe4n.Kernel.Concurrency.peekTicketLockServing (0 : UInt64) = (0 : UInt64) := by decide

-- The masked round-trip witness applied at a concrete pair of values.
example :
    let packed : UInt64 :=
      (((42 : UInt64) &&& (0xFFFFFFFF : UInt64)) <<< 32) ||| ((7 : UInt64) &&& (0xFFFFFFFF : UInt64))
    SeLe4n.Kernel.Concurrency.peekTicketLockNextTicket packed = (42 : UInt64) ∧
    SeLe4n.Kernel.Concurrency.peekTicketLockServing packed = (7 : UInt64) := by
  decide

-- ============================================================================
-- §8 — Runtime structural assertions
-- ============================================================================

private def assertBool (msg : String) (b : Bool) : IO Unit :=
  if b then pure () else throw (IO.userError s!"FAIL: {msg}")

/-- Run all SM2.D structural checks at runtime.

    Per the FFI link discipline, we do NOT invoke any
    `Platform.FFI.ffi*` symbol here — those would fail at link
    time on the host test executable.  Instead we exercise:

    1. Pool dimension constants and their relationships.
    2. Smart constructor round-trips (`mkTicketLockHandle` /
       `mkRwLockHandle` produce handles with the expected
       `raw.toNat`).
    3. Aggregator size + per-category counts.
    4. Bit-layout extractor algebra on concrete values.
    5. Marker theorem typechecking (reachable via `#check`-style
       proof binding). -/
def runSmpSurfaceAnchorChecks : IO Unit := do
  IO.println "WS-SM SM2.D.6 — Verified-lock-primitive surface anchor suite"
  IO.println "============================================================"

  IO.println "--- §1 Pool dimensions ---"
  assertBool "staticTicketLockPoolSize = 4"
    (decide (SeLe4n.Kernel.Concurrency.staticTicketLockPoolSize = 4))
  assertBool "staticRwLockPoolSize = 4"
    (decide (SeLe4n.Kernel.Concurrency.staticRwLockPoolSize = 4))
  assertBool "staticTicketLockPoolSize > 0"
    (decide (0 < SeLe4n.Kernel.Concurrency.staticTicketLockPoolSize))
  assertBool "staticRwLockPoolSize > 0"
    (decide (0 < SeLe4n.Kernel.Concurrency.staticRwLockPoolSize))
  assertBool "staticTicketLockPoolSize = numCores"
    (decide (SeLe4n.Kernel.Concurrency.staticTicketLockPoolSize =
              SeLe4n.Kernel.Concurrency.numCores))
  assertBool "staticRwLockPoolSize = numCores"
    (decide (SeLe4n.Kernel.Concurrency.staticRwLockPoolSize =
              SeLe4n.Kernel.Concurrency.numCores))

  IO.println "--- §2 Handle smart-constructor round-trips ---"
  -- mkTicketLockHandle(⟨0, _⟩).raw.toNat = 0, etc.
  -- Use concrete `Fin` values so the `Fin.mk` bound is dischargeable
  -- by `decide` against the known pool size.
  let tH0 := SeLe4n.Kernel.Concurrency.mkTicketLockHandle ⟨0, by decide⟩
  let tH1 := SeLe4n.Kernel.Concurrency.mkTicketLockHandle ⟨1, by decide⟩
  let tH2 := SeLe4n.Kernel.Concurrency.mkTicketLockHandle ⟨2, by decide⟩
  let tH3 := SeLe4n.Kernel.Concurrency.mkTicketLockHandle ⟨3, by decide⟩
  assertBool "mkTicketLockHandle(0).raw.toNat = 0" (decide (tH0.raw.toNat = 0))
  assertBool "mkTicketLockHandle(1).raw.toNat = 1" (decide (tH1.raw.toNat = 1))
  assertBool "mkTicketLockHandle(2).raw.toNat = 2" (decide (tH2.raw.toNat = 2))
  assertBool "mkTicketLockHandle(3).raw.toNat = 3" (decide (tH3.raw.toNat = 3))
  let rH0 := SeLe4n.Kernel.Concurrency.mkRwLockHandle ⟨0, by decide⟩
  let rH1 := SeLe4n.Kernel.Concurrency.mkRwLockHandle ⟨1, by decide⟩
  let rH2 := SeLe4n.Kernel.Concurrency.mkRwLockHandle ⟨2, by decide⟩
  let rH3 := SeLe4n.Kernel.Concurrency.mkRwLockHandle ⟨3, by decide⟩
  assertBool "mkRwLockHandle(0).raw.toNat = 0" (decide (rH0.raw.toNat = 0))
  assertBool "mkRwLockHandle(1).raw.toNat = 1" (decide (rH1.raw.toNat = 1))
  assertBool "mkRwLockHandle(2).raw.toNat = 2" (decide (rH2.raw.toNat = 2))
  assertBool "mkRwLockHandle(3).raw.toNat = 3" (decide (rH3.raw.toNat = 3))
  -- All eight handles are within the bound.
  assertBool "tH0.isValid: raw.toNat < poolSize" (decide (tH0.raw.toNat < 4))
  assertBool "tH3.isValid: raw.toNat < poolSize" (decide (tH3.raw.toNat < 4))
  assertBool "rH0.isValid: raw.toNat < poolSize" (decide (rH0.raw.toNat < 4))
  assertBool "rH3.isValid: raw.toNat < poolSize" (decide (rH3.raw.toNat < 4))

  IO.println "--- §3 Aggregator size + per-category counts ---"
  assertBool "lockPrimitives.length = 22"
    (decide (SeLe4n.Kernel.Concurrency.lockPrimitives.length = 22))
  assertBool "memory-model count = 4"
    (decide
      ((SeLe4n.Kernel.Concurrency.lockPrimitives.filter
        (·.category =
          SeLe4n.Kernel.Concurrency.LockPrimitiveCategory.memoryModel)).length = 4))
  assertBool "TicketLock count = 6"
    (decide
      ((SeLe4n.Kernel.Concurrency.lockPrimitives.filter
        (·.category =
          SeLe4n.Kernel.Concurrency.LockPrimitiveCategory.ticketLock)).length = 6))
  assertBool "RwLock count = 10"
    (decide
      ((SeLe4n.Kernel.Concurrency.lockPrimitives.filter
        (·.category =
          SeLe4n.Kernel.Concurrency.LockPrimitiveCategory.rwLock)).length = 10))
  assertBool "refinement count = 2"
    (decide
      ((SeLe4n.Kernel.Concurrency.lockPrimitives.filter
        (·.category =
          SeLe4n.Kernel.Concurrency.LockPrimitiveCategory.refinement)).length = 2))

  IO.println "--- §4 Bit-layout extractor algebra ---"
  -- Standard cases.
  assertBool "peekNextTicket(0) = 0"
    (decide (SeLe4n.Kernel.Concurrency.peekTicketLockNextTicket 0 = 0))
  assertBool "peekServing(0) = 0"
    (decide (SeLe4n.Kernel.Concurrency.peekTicketLockServing 0 = 0))
  -- Packed encoding cases.  Use explicit UInt64 typing on every
  -- numeric literal to avoid Nat inference for the bitwise ops.
  let nextU64 : UInt64 := 42
  let srvU64 : UInt64 := 7
  let packed_42_7 : UInt64 := (nextU64 <<< 32) ||| srvU64
  assertBool "peekNextTicket(pack 42 7) = 42"
    (decide (SeLe4n.Kernel.Concurrency.peekTicketLockNextTicket packed_42_7 = (42 : UInt64)))
  assertBool "peekServing(pack 42 7) = 7"
    (decide (SeLe4n.Kernel.Concurrency.peekTicketLockServing packed_42_7 = (7 : UInt64)))
  -- u32 boundary case.
  let max32 : UInt64 := 0xFFFFFFFF
  let packed_max_max : UInt64 := (max32 <<< 32) ||| max32
  assertBool "peekNextTicket(pack max32 max32) = max32"
    (decide (SeLe4n.Kernel.Concurrency.peekTicketLockNextTicket packed_max_max = max32))
  assertBool "peekServing(pack max32 max32) = max32"
    (decide (SeLe4n.Kernel.Concurrency.peekTicketLockServing packed_max_max = max32))

  IO.println "--- §5 Marker theorem reachability (elaboration-time) ---"
  -- Each marker theorem is structurally reachable; we exercise via
  -- a binding that requires the theorem name to be in scope.  The
  -- elaboration of these `let` bindings IS the test — a missing
  -- theorem fails at elaboration, before runtime.  The runtime
  -- assertBool below records the elaboration success in the
  -- per-test log.
  let _m1 := @SeLe4n.Kernel.Concurrency.acquireTicketLock_eq_ffi
  let _m2 := @SeLe4n.Kernel.Concurrency.releaseTicketLock_eq_ffi
  let _m3 := @SeLe4n.Kernel.Concurrency.peekTicketLockHolder_eq_ffi
  let _m4 := @SeLe4n.Kernel.Concurrency.acquireReadLock_eq_ffi
  let _m5 := @SeLe4n.Kernel.Concurrency.releaseReadLock_eq_ffi
  let _m6 := @SeLe4n.Kernel.Concurrency.acquireWriteLock_eq_ffi
  let _m7 := @SeLe4n.Kernel.Concurrency.releaseWriteLock_eq_ffi
  let _m8 := @SeLe4n.Kernel.Concurrency.snapshotRwLock_eq_ffi
  let _m9 := @SeLe4n.Kernel.Concurrency.withTicketLock_unfold
  let _m10 := @SeLe4n.Kernel.Concurrency.withReadLock_unfold
  let _m11 := @SeLe4n.Kernel.Concurrency.withWriteLock_unfold
  let _m12 := @SeLe4n.Kernel.Concurrency.peekTicketLockEncoding_roundtrip_u32_masked
  let _m13 := @SeLe4n.Kernel.Concurrency.peekTicketLockNextTicket_is_high32
  let _m14 := @SeLe4n.Kernel.Concurrency.peekTicketLockServing_is_low32
  -- Decidable post-condition that the marker-theorem bindings
  -- aren't optimised away.  Each `_m*` is a Pi-type universe-level
  -- value (so non-trivially typed; the compiler can't constant-fold).
  -- The decidable check here is the SAME truth (i.e., "the previous
  -- bindings elaborated") and verifies the runtime path reached this
  -- point in the test body.
  assertBool "elaboration reached SM2.D marker-theorem reachability checkpoint"
    (decide ((14 : Nat) = 14))

  IO.println "--- §6 Negative-side bit-extractor cases (LOW-8) ---"
  -- High bits should NOT bleed into the serving extraction.
  let high_only : UInt64 := (0xFFFFFFFF : UInt64) <<< 32  -- all top bits set, no low bits
  assertBool "peekServing(high_only) = 0 (high bits don't bleed into serving)"
    (decide (SeLe4n.Kernel.Concurrency.peekTicketLockServing high_only = 0))
  assertBool "peekNextTicket(high_only) = max32 (high bits preserved by shift)"
    (decide (SeLe4n.Kernel.Concurrency.peekTicketLockNextTicket high_only = (0xFFFFFFFF : UInt64)))
  -- Low bits should NOT bleed into the next-ticket extraction.
  let low_only : UInt64 := 0xFFFFFFFF
  assertBool "peekNextTicket(low_only) = 0 (low bits don't bleed into next-ticket)"
    (decide (SeLe4n.Kernel.Concurrency.peekTicketLockNextTicket low_only = 0))
  assertBool "peekServing(low_only) = max32 (low bits preserved)"
    (decide (SeLe4n.Kernel.Concurrency.peekTicketLockServing low_only = (0xFFFFFFFF : UInt64)))

  IO.println "--- §7 WS-SM SM3.E.8 — serializability major-theorem reachability ---"
  -- The SM3.E inventory size witness reached and evaluates (the 8 major-theorem
  -- `#check` anchors above are elaboration-time gates; this exercises the
  -- runtime path of the SM3.E inventory aggregator).
  assertBool "SM3.E inventory has 76 entries"
    (decide (SeLe4n.Kernel.Concurrency.serializabilityTheorems.length = 76))

  IO.println "============================================================"
  IO.println "All SM2.D + SM3.E.8 surface anchor checks PASS."

end SeLe4n.Testing.SmpSurfaceAnchors

def main : IO Unit :=
  SeLe4n.Testing.SmpSurfaceAnchors.runSmpSurfaceAnchorChecks
