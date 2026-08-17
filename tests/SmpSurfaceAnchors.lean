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
import SeLe4n.Kernel.InformationFlow.ObservableStatePerCore
import SeLe4n.Kernel.InformationFlow.CovertChannelPerCore
import SeLe4n.Kernel.InformationFlow.DeclassificationPerCore
import SeLe4n.Kernel.InformationFlow.FineLockFlow

/-!
# WS-SM SM2.D.6 / SM8.E.1 — Verified-lock-primitive and information-flow anchors

Tier-3 surface anchors covering every public symbol exported by the
SM2.D FFI bridge and the SM2.D.7 theorem aggregator, plus (§8) the
headline theorem surface of WS-SM SM8 — the plan's §6.1 "what SM8
proves" enumeration, across SM8.A per-core observable state, SM8.B
per-core non-interference, SM8.C the declassification audit, SM8.D
information flow under fine locks, and SM8.E's promotion of the
two-phase-locking bracket into the canonical enforcement boundary.

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
-- SM3.E.3/E.5 — OBSERVATIONAL serializability (covers write/write on distinct objects).
#check @SeLe4n.Kernel.Concurrency.serializability_under_2pl_obs
-- SM3.E.2 — atomicity bridge (applySequential models the withLockSet execution).
#check @SeLe4n.Kernel.Concurrency.applySequentialWithLockSet_observation

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
  assertBool "SM3.E inventory has 111 entries"
    (decide (SeLe4n.Kernel.Concurrency.serializabilityTheorems.length = 111))

  IO.println "--- §8 WS-SM SM8 — the information-flow headline surface ---"
  -- The plan (§5 SM8.E.1) names this file as the SM8 anchor home, and SM8.E.1
  -- is where the list is completed: every theorem the plan's §6.1 "what SM8
  -- proves" enumeration names now resolves here, across all five sub-phases.
  -- The *exhaustive* per-symbol anchors live in
  -- `tests/SmpInformationFlowSuite.lean` next to the runtime groups that
  -- exercise them; what is pinned here is the phase's headline surface, so a
  -- rename that slipped past the dedicated suite still fails this file.
  -- Elaboration-time only — the checks above are the runtime part of this
  -- suite.
  -- Assertion labels below name the *semantics*, not the phase: the Tier-3
  -- companion greps them from a shell string, where the identifier-naming
  -- gate reads a phase code as code rather than as prose.  The phase is
  -- named in the comments above, which are exempt.
  assertBool "per-core observer surface resolves (observer, partition, decidability)"
    (have _o : SeLe4n.Kernel.LabelingContext → SeLe4n.Kernel.Concurrency.CoreId →
        SeLe4n.Kernel.SecurityLabel → SeLe4n.Model.SystemState → SeLe4n.Kernel.ObservableState :=
      SeLe4n.Kernel.ObservableState.onCore
     have _f : ∀ v : SeLe4n.Kernel.ObservableState,
        SeLe4n.Kernel.ObservableState.ofFragments v.sharedFragment v.perCoreFragment = v :=
      SeLe4n.Kernel.ObservableState.ofFragments_eta
     true)
  assertBool "per-core independence + clearance monotonicity headlines resolve"
    (have _i := @SeLe4n.Kernel.onCore_perCore_independence
     have _m := @SeLe4n.Kernel.onCore_label_monotone
     have _s := @SeLe4n.Kernel.onCore_label_monotone_smp
     have _p := @SeLe4n.Kernel.onCore_isProjection_of_globalProjection
     true)
  assertBool "cross-core non-interference + per-core lift headlines resolve"
    (have _x := @SeLe4n.Kernel.crossCoreNonInterference
     have _n := @SeLe4n.Kernel.nonInterference_perCore
     have _c := @SeLe4n.Kernel.observableSlotsConfinedToCore
     have _s := @SeLe4n.Kernel.sharedViewUnchanged
     have _v := @SeLe4n.Kernel.niStepCoverage_perCore
     have _b := @SeLe4n.Kernel.crossCoreLeakage_bounded
     true)
  assertBool "lock-set non-interference + the covert-channel inventory resolve"
    (have _w := @SeLe4n.Kernel.withLockSet_preserves_projection
     have _u := @SeLe4n.Kernel.nonInterference_perCore_underLockSet
     have _e : SeLe4n.Kernel.enforcementBoundaryPerCore.length = 57 :=
       SeLe4n.Kernel.enforcementBoundaryPerCore_count
     -- PR #861 review round 4: the boundary now also classifies the live
     -- cross-core wrappers, and the SMP completeness half audits them.  Rounds
     -- 10 and 12 took that set from seven to fourteen — the two priority arms
     -- and `.send`/`.tcbResume` were rerouted off boot-pinned operations, and
     -- the three SM7.D/SM7.F architecture wrappers had been live all along.
     -- Round 37's widened routing gate found the fifteenth, `.tcbSetAffinity`.
     -- WS-SM SM8.C then took the boundary itself from 54 to 55 with the live
     -- declassification entry point (`.declassify`), which is policy-gated in
     -- the canonical list and re-routed per-core like the rest.
     have _x := @SeLe4n.Kernel.syscallIdToEnforcementNamePerCore
     have _c := SeLe4n.Kernel.enforcementBoundaryPerCore_is_complete_crossCore
     have _i : SeLe4n.Kernel.acceptedCovertChannelsPerCore.length = 7 :=
       SeLe4n.Kernel.acceptedCovertChannel_perCoreCount
     have _l := SeLe4n.Kernel.acceptedCovertChannel_lockContention
     have _r := @SeLe4n.Kernel.endpointPolicyRestricted_perCore
     true)
  -- WS-SM SM8.C: the per-core declassification audit.  The headline is the
  -- *producer* — before SM8.C nothing in the tree constructed a
  -- `DeclassificationEvent`, so the audit trail was a type with no writer — and
  -- the attributed entry point, which reads the source domain off the subject
  -- the executing core is running rather than taking it from the caller.
  assertBool "the declassification producer, its attribution and its partition resolve"
    (have _p := @SeLe4n.Kernel.declassifyStoreOnCore
     have _i := @SeLe4n.Kernel.declassifyStoreOnCore_ok_inv
     have _o := @SeLe4n.Kernel.declassifyStoreOnCore_records_one
     have _f := @SeLe4n.Kernel.declassifyStoreFromCore
     have _a := @SeLe4n.Kernel.declassifyStoreFromCore_event_attributable
     have _u := @SeLe4n.Kernel.declassifyStoreOnCore_admits_unattributable
     have _v := @SeLe4n.Kernel.auditLogOnCore
     have _q := @SeLe4n.Kernel.declassificationAuditLog_partitions_by_core
     have _m := @SeLe4n.Kernel.DeclassificationEvent_perCore_audit
     true)
  -- Cross-core chains are what decide ONE global log over the per-CPU buffers a
  -- kernel would naturally reach for: a chain spanning cores is in no single
  -- core's view, so a per-core log could not reconstruct it.  The laundering
  -- detector is the other half — per-hop authorization does not compose.
  assertBool "cross-core chains, the laundering detector and the basis check resolve"
    (have _r := @SeLe4n.Kernel.declassificationChain_recorded_across_cores
     have _n := @SeLe4n.Kernel.crossCoreChain_not_within_one_view
     have _t := @SeLe4n.Kernel.declassificationAuditLog_timestamp_identifies_event
     have _c := @SeLe4n.Kernel.declassificationChain_hop_authorization_does_not_compose
     have _l := @SeLe4n.Kernel.chainLaunders
     have _e := @SeLe4n.Kernel.endpointOverride_is_not_a_declassification_basis
     have _v := @SeLe4n.Kernel.liveEndpointOverride_is_not_a_declassification_basis
     have _b := @SeLe4n.Kernel.authorizationBasis_perCore
     have _g := @SeLe4n.Kernel.endpointFlowGate
     have _s := @SeLe4n.Kernel.endpointFlowGate_implies_securityFlowsTo
     have _d := @SeLe4n.Kernel.declassificationRuleEvidence
     have _k : SeLe4n.Kernel.DeclassificationRuleId.all.length = 12 :=
       SeLe4n.Kernel.declassificationRules_count
     true)
  -- SM8.C.8 / SM8.C.9: the trail mounted in `SystemState` and the live
  -- `.declassify` syscall.  The load-bearing pair is *never unaudited* (an
  -- authorized downgrade is either recorded or does not happen — which is what
  -- the fail-closed capacity bound buys) and *denied before capacity* (a caller
  -- the policy refuses learns nothing about the trail's occupancy, so trail
  -- length is not a channel from every declassifying subject to every caller).
  assertBool "the mounted trail, the live syscall and its fail-closed bound resolve"
    (have _c : SeLe4n.Kernel.maxDeclassificationAuditEntries = 256 := rfl
     have _b := @SeLe4n.Kernel.auditLogBounded
     have _r := @SeLe4n.Kernel.recordDeclassificationChecked
     have _o := @SeLe4n.Kernel.declassifyObjectFromCore
     have _d := @SeLe4n.Kernel.declassifyObjectFromCore_destination_is_target_domain
     have _u := @SeLe4n.Kernel.authorizeDeclassificationOnCore_never_unaudited
     have _s := @SeLe4n.Kernel.declassifyStoreOnCore_never_unaudited
     have _p := @SeLe4n.Kernel.authorizeDeclassificationOnCore_denied_before_capacity
     have _n := @SeLe4n.Kernel.declassifyStoreOnCore_perCore_NI
     have _t := @SeLe4n.Kernel.declassifyStoreOnCore_state_trail_independent
     have _e := @SeLe4n.Kernel.declassifyRun_records_each
     -- The registered gap, as a theorem rather than a caveat: a *refused*
     -- declassification leaves no trace (fail-closed, so a detection gap and
     -- not an enforcement one).
     have _g := @SeLe4n.Kernel.declassification_refusal_is_unrecorded
     have _z := @SeLe4n.Kernel.declassifyStoreOnCore_denied_no_audit_entry
     -- …and the faithful lift of the legacy 2x2 lattice, which is what lets a
     -- deployment configure a downgrade along the one pair `linearOrder`
     -- over-approximated and actually reach the declassification policy.
     have _y := @SeLe4n.Kernel.DomainFlowPolicy.legacyLattice
     have _q := @SeLe4n.Kernel.legacyLattice_canFlow_embed
     have _w := @SeLe4n.Kernel.linearOrder_is_not_faithful_to_legacy
     true)
  -- WS-SM SM8.D: information flow under fine locks.  The headline is the
  -- *factoring* — an observer's view is a function of an object's lock-erased
  -- content — because that is what makes "the lock is invisible" a statement
  -- about the field rather than about one operation.  The bound is the other
  -- half: CC-5 is accepted, not closed, and SM8.D says how much it carries.
  assertBool "fine-lock invisibility, the contention bound and the integrity twins resolve"
    (have _p := @SeLe4n.Kernel.projectKernelObject_setLock
     have _i := @SeLe4n.Kernel.onCore_lock_indistinguishable
     have _l := @SeLe4n.Kernel.lockWritesOnly_preserves_onCore
     have _r := @SeLe4n.Kernel.readerMultiplicity_not_observable
     have _a := @SeLe4n.Kernel.blockedAcquirer_observes_nothing
     have _d := @SeLe4n.Kernel.lockContention_delay_bounded
     -- The two §6.1 headline names the SM8.D landing left unanchored here: the
     -- per-observation alphabet and the run-length capacity built on it.  A
     -- bound on the delay alone is not a bound on the channel.
     have _ab := @SeLe4n.Kernel.lockContentionChannel_alphabet_bounded
     have _tc := @SeLe4n.Kernel.lockContentionChannel_trace_capacity
     have _rc := @SeLe4n.Kernel.lockContentionChannel_run_capacity
     -- …and the unit the bound is denominated in: lock OPERATIONS, with the
     -- wall-clock reading conditional on a cost model.
     have _wc := @SeLe4n.Kernel.lockContention_wallClock_bounded
     have _re := @SeLe4n.Kernel.lockContentionChannel_rate_per_elapsed_time
     have _o := @SeLe4n.Kernel.lockContentionObservation_is_own_acquisition
     have _t := @SeLe4n.Kernel.lockContentionChannel_observation_rate_bounded
     have _f := @SeLe4n.Kernel.lockContention_unbounded_without_fairness
     have _k := @SeLe4n.Kernel.readerContentionDepth_bounded
     have _h := @SeLe4n.Kernel.blockedReader_admitted_by_writer_release
     have _rt := @SeLe4n.Kernel.blockedReaderContention_delay_bounded
     have _wt := @SeLe4n.Kernel.writerContention_delay_bounded
     have _ml := @SeLe4n.Kernel.Concurrency.rwLock_queued_liveness
     have _ma := @SeLe4n.Kernel.Concurrency.rwLock_queued_admissionStepAfter_bounded
     have _n := @SeLe4n.Kernel.syscallEntryUnderDeclaredLockSet_undeclared
     have _b := @SeLe4n.Kernel.bibaIntegrity_underLockSet
     have _u := @SeLe4n.Kernel.authorityIntegrity_underLockSet
     have _w := @SeLe4n.Kernel.secureInformationFlow_underFineLocks
     have _2c := @SeLe4n.Kernel.lockContentionChannel_two_codes_reachable
     have _ge := @SeLe4n.Kernel.acceptedContentionCode_ge_two
     have _ac := @SeLe4n.Kernel.secureInformationFlow_underFineLocks_atCore
     have _ai := @SeLe4n.Kernel.authorityIntegrity_underLockSet
     have _c : SeLe4n.Kernel.FineLockClaimId.all.length = 11 :=
       SeLe4n.Kernel.fineLockClaims_count
     have _e := SeLe4n.Kernel.fineLockClaimEvidence
     true)
  -- WS-SM SM8.E.3: the 2PL bracket promoted into the CANONICAL enforcement
  -- boundary, which is the count SM8.B deliberately left for this phase to
  -- move.  Pinned here as the equation rather than as a name, so a promotion
  -- that silently reverted — or a second entry added without reconciling the
  -- per-core list — fails the anchor file too, not only the dedicated suite.
  assertBool "the canonical enforcement boundary carries the two-phase-locking bracket"
    (have _e : SeLe4n.Kernel.enforcementBoundaryExtended.length = 42 :=
       SeLe4n.Kernel.enforcementBoundaryExtended_count
     have _c := SeLe4n.Kernel.enforcementBoundary_classifies_withLockSet
     have _o := SeLe4n.Kernel.enforcementBoundaryPerCore_classifies_withLockSet_once
     have _x := SeLe4n.Kernel.crossCoreEnforcementEntries_omits_withLockSet
     have _p := @SeLe4n.Kernel.enforcementBoundary_prefix_of_perCore
     -- The promotion is count-neutral for the per-core list, which is the whole
     -- reason the entry was appended last: the extension is the plain
     -- `canonical ++ crossCore`, so the canonical count is the only thing that
     -- moves when a syscall joins (SM9.A took it 40 → 42).
     decide (SeLe4n.Kernel.enforcementBoundaryPerCore.length
       = SeLe4n.Kernel.enforcementBoundaryExtended.length
         + SeLe4n.Kernel.crossCoreEnforcementEntries.length))

  -- ==========================================================================
  -- §9  WS-SM SM9.A — the declassification audit trail's READER
  -- ==========================================================================
  --
  -- SM8.C shipped a durable, bounded, fail-closed trail that nothing could
  -- read, so a deployment performing `maxDeclassificationAuditEntries`
  -- authorized downgrades stopped being able to declassify at all.  These are
  -- the headline names of the read side; the full 113-symbol surface is
  -- anchored in `tests/SmpInformationFlowSuite.lean` §1.10.
  assertBool "SM9.A: the clearance-filtered view, the chunk protocol and the atomic status word"
    (have _v := @SeLe4n.Kernel.auditLogVisibleTo
     -- The no-gap-leak property: the view is a function of the reader's
     -- clearance alone, so a hidden entry shifts no index the reader can see.
     have _g := @SeLe4n.Kernel.auditLogVisibleTo_hidden_insert
     have _dc := @SeLe4n.Kernel.auditLogVisibleTo_determined_by_clearance
     have _sl := @SeLe4n.Kernel.auditLogVisibleTo_sublist
     -- The arbitrary-length chunk protocol: every exported field is an
     -- unbounded `Nat`, so a fixed low/high pair would only move the
     -- truncation point to `2^64`.
     have _rf := @SeLe4n.Kernel.auditReadField_reconstructs
     have _rb := @SeLe4n.Kernel.auditReadBasis_reconstructs_designation
     have _fb := @SeLe4n.Kernel.auditFieldBound_unreachable_in_kernel
     -- One read for both status components: chunking `status` would have
     -- traded aliasing for tearing on the first interleaved drain.
     have _sa := @SeLe4n.Kernel.auditReadStatus_atomic
     have _st := @SeLe4n.Kernel.auditStatusSplitRead_tears
     true)
  assertBool "SM9.A: the two reader classes, and what a partial reader cannot learn"
    (have _vl := @SeLe4n.Kernel.auditReadIndex_is_view_local
     have _gi := @SeLe4n.Kernel.dominatingReader_sees_global_identity
     have _hp := @SeLe4n.Kernel.auditRead_hides_global_position
     have _pg := @SeLe4n.Kernel.auditReadStatus_partial_hides_generation
     -- Why the generation is global rather than per-observer: labels are an
     -- unbounded `Nat`, so there is no finite family to key state by.
     have _nm := @SeLe4n.Kernel.observerScopedGeneration_not_mountable
     true)
  assertBool "SM9.A: drain under the configuration-derived dominance gate"
    (have _d := @SeLe4n.Kernel.auditDrainVisiblePrefix
     have _fd := @SeLe4n.Kernel.auditDrain_requires_full_dominance_of_subjects
     have _pr := @SeLe4n.Kernel.auditDrain_partial_reader_drains_nothing
     have _cl := @SeLe4n.Kernel.auditDrain_fully_clears_for_dominating_reader
     -- The gate is derived from the CONFIGURATION, never from the rows the
     -- trail currently holds: drain a trail to `[]` and a rows-derived
     -- predicate goes vacuously true exactly where it matters.
     have _cd := @SeLe4n.Kernel.auditMonitorGate_is_configuration_derived
     have _ru := @SeLe4n.Kernel.auditMonitorGate_records_derived_unsound
     have _ud := @SeLe4n.Kernel.auditDrain_unconfigured_denied
     true)
  assertBool "SM9.A.1a: the persistent epoch — a drain never frees a timestamp for reuse"
    (have _e := @SeLe4n.Kernel.declassificationTrailWellFormed
     have _wf := @SeLe4n.Kernel.auditDrain_preserves_wellFormed_at_epoch
     have _fr := @SeLe4n.Kernel.auditDrain_next_timestamp_fresh
     have _id := @SeLe4n.Kernel.declassificationTrail_timestamp_identifies_event
     have _me := @SeLe4n.Kernel.auditDrain_monotone_epoch
     -- The witness that the pre-epoch producer is genuinely unsound once drain
     -- exists — a theorem, so a regression to `timestamp := log.length` fails
     -- to build rather than quietly reintroducing the collision.
     have _pe := @SeLe4n.Kernel.preEpochTimestamp_reused_after_drain
     -- …and the 16th bundle conjunct rides the drain.
     have _b := @SeLe4n.Kernel.auditDrain_preserves_proofLayerInvariantBundle
     true)
  assertBool "SM9.A.4a/.4b: the reader-visibility discipline as a TOTAL function, and the flow argument"
    (have _c := @SeLe4n.Kernel.readableStructureAgrees
     have _t := @SeLe4n.Kernel.auditReadOp_structure_total
     -- The refuted design, kept refuted: a `mem_all` list plus an
     -- "everything listed is readable" gate cannot force a NEW structure to
     -- join it, whereas a missing case in a total function is a build error.
     have _lg := @SeLe4n.Kernel.readableStructure_list_gate_insufficient
     have _oe := @SeLe4n.Kernel.auditObservationalEquivalence
     -- The lemma `lowEquivalent` cannot supply: the trail is deliberately not
     -- in `ObservableState`, so "low-equivalent states give identical visible
     -- views" is FALSE and cannot be the flow argument.
     have _nd := @SeLe4n.Kernel.lowEquivalent_does_not_determine_visible_view
     have _nc := @SeLe4n.Kernel.auditRead_no_channel
     have _fc := @SeLe4n.Kernel.auditReadFromCore_no_channel
     have _ni := @SeLe4n.Kernel.auditReadFromCore_perCore_NI
     have _dn := @SeLe4n.Kernel.auditDrain_perCore_NI
     true)
  assertBool "SM9.A.9/.10: authority is a CapTarget, and the live arms return the SELECTED word"
    (-- The v0.32.97 confused-deputy class: `syscallLookupCap` never constrains
     -- `cap.target`, so a rights-only gate would repeat it exactly.
     have _x := @SeLe4n.Kernel.extractAuditAuthority
     have _r := @SeLe4n.Kernel.extractAuditAuthority_rejects_non_audit_capability
     have _cd := @SeLe4n.Model.Capability.auditTrailRead_cannot_drain
     have _cm := @SeLe4n.Model.Capability.auditTrailManage_can_drain
     -- The WS-RA half: without a staged return frame the reader computes
     -- correctly and hands back the caller's own preloaded `x0`.
     have _sr := @SeLe4n.Kernel.dispatchArm_auditRead_matches_returnShape
     have _sd := @SeLe4n.Kernel.dispatchArm_auditDrain_matches_returnShape
     have _lr := @SeLe4n.Kernel.syscallDelegates_auditRead
     have _ld := @SeLe4n.Kernel.syscallDelegates_auditDrain
     have _ll := @SeLe4n.Kernel.auditReadFromCore_toUInt64_lossless
     -- Fail-closed by default: an unconfigured deployment has NO audit reader,
     -- which keeps the 256-entry cliff as the conservative default.
     have _u := @SeLe4n.Kernel.unconfiguredDeployment_has_no_audit_reader
     have _n := @SeLe4n.Kernel.dispatchWithCap_auditRead_denied
     -- Both syscalls are in the ABI and value-returning.
     decide (SeLe4n.Model.SyscallId.auditRead.toNat = 31
       ∧ SeLe4n.Model.SyscallId.auditDrain.toNat = 32
       ∧ SeLe4n.Model.SyscallId.count = 33
       ∧ SeLe4n.Kernel.Architecture.syscallReturnShape .auditRead = .word
       ∧ SeLe4n.Kernel.Architecture.syscallReturnShape .auditDrain = .word))

  IO.println "============================================================"
  IO.println "All SM2.D + SM3.E.8 + SM8.A + SM8.B + SM8.C + SM8.D + SM8.E + SM9.A \
surface anchor checks PASS."

end SeLe4n.Testing.SmpSurfaceAnchors

def main : IO Unit :=
  SeLe4n.Testing.SmpSurfaceAnchors.runSmpSurfaceAnchorChecks
