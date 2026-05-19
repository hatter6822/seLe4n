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
import SeLe4n.Platform.FFI

/-!
# WS-SM SM2.D.3 — Lock-bridge RAII combinator regression suite

Tier-3 surface anchors + decidable examples + runtime structural
assertions for the SM2.D.3 RAII combinators (`withTicketLock`,
`withReadLock`, `withWriteLock`).

Per the FFI link discipline (Lean test executables do NOT link
against `libsele4n_hal.a`), the runtime portion exercises only
**structural** properties — the combinators' definitional
unfolding, type signatures, and marker theorem reachability.
Behavioral runtime tests for the actual FFI semantics live on the
Rust side in `lock_bridge::tests` and `ffi::tests`.

This suite complements `SmpSurfaceAnchors.lean` by focusing
specifically on the RAII pattern (SM2.D.3 acceptance gate).
-/

namespace SeLe4n.Testing.LockBridge

-- ============================================================================
-- §1 — Decidable structural properties
-- ============================================================================

/-! ## Smart constructor round-trips on every valid index -/

example :
    (SeLe4n.Kernel.Concurrency.mkTicketLockHandle ⟨0, by decide⟩).raw.toNat = 0 := by
  decide

example :
    (SeLe4n.Kernel.Concurrency.mkTicketLockHandle ⟨1, by decide⟩).raw.toNat = 1 := by
  decide

example :
    (SeLe4n.Kernel.Concurrency.mkTicketLockHandle ⟨2, by decide⟩).raw.toNat = 2 := by
  decide

example :
    (SeLe4n.Kernel.Concurrency.mkTicketLockHandle ⟨3, by decide⟩).raw.toNat = 3 := by
  decide

example :
    (SeLe4n.Kernel.Concurrency.mkRwLockHandle ⟨0, by decide⟩).raw.toNat = 0 := by
  decide

example :
    (SeLe4n.Kernel.Concurrency.mkRwLockHandle ⟨3, by decide⟩).raw.toNat = 3 := by
  decide

/-! ## Handle isValid bound -/

example :
    (SeLe4n.Kernel.Concurrency.mkTicketLockHandle ⟨0, by decide⟩).raw.toNat
      < SeLe4n.Kernel.Concurrency.staticTicketLockPoolSize := by
  exact (SeLe4n.Kernel.Concurrency.mkTicketLockHandle ⟨0, by decide⟩).isValid

example :
    (SeLe4n.Kernel.Concurrency.mkRwLockHandle ⟨0, by decide⟩).raw.toNat
      < SeLe4n.Kernel.Concurrency.staticRwLockPoolSize := by
  exact (SeLe4n.Kernel.Concurrency.mkRwLockHandle ⟨0, by decide⟩).isValid

/-! ## RAII combinator marker theorems are reachable -/

example {α : Type} (h : SeLe4n.Kernel.Concurrency.TicketLockHandle) (a : BaseIO α) :
    SeLe4n.Kernel.Concurrency.withTicketLock h a =
      (SeLe4n.Kernel.Concurrency.acquireTicketLock h >>= fun _ticket =>
        a >>= fun result =>
          SeLe4n.Kernel.Concurrency.releaseTicketLock h >>= fun _ => pure result) :=
  SeLe4n.Kernel.Concurrency.withTicketLock_unfold h a

example {α : Type} (h : SeLe4n.Kernel.Concurrency.RwLockHandle) (a : BaseIO α) :
    SeLe4n.Kernel.Concurrency.withReadLock h a =
      (SeLe4n.Kernel.Concurrency.acquireReadLock h >>= fun _ =>
        a >>= fun result =>
          SeLe4n.Kernel.Concurrency.releaseReadLock h >>= fun _ => pure result) :=
  SeLe4n.Kernel.Concurrency.withReadLock_unfold h a

example {α : Type} (h : SeLe4n.Kernel.Concurrency.RwLockHandle) (a : BaseIO α) :
    SeLe4n.Kernel.Concurrency.withWriteLock h a =
      (SeLe4n.Kernel.Concurrency.acquireWriteLock h >>= fun _ =>
        a >>= fun result =>
          SeLe4n.Kernel.Concurrency.releaseWriteLock h >>= fun _ => pure result) :=
  SeLe4n.Kernel.Concurrency.withWriteLock_unfold h a

/-! ## FFI pass-through markers are rfl -/

example (h : SeLe4n.Kernel.Concurrency.TicketLockHandle) :
    (SeLe4n.Kernel.Concurrency.acquireTicketLock h : BaseIO UInt64) =
      SeLe4n.Platform.FFI.ffiTicketLockAcquire h.raw :=
  SeLe4n.Kernel.Concurrency.acquireTicketLock_eq_ffi h

example (h : SeLe4n.Kernel.Concurrency.RwLockHandle) :
    (SeLe4n.Kernel.Concurrency.acquireReadLock h : BaseIO Unit) =
      SeLe4n.Platform.FFI.ffiRwLockAcquireRead h.raw :=
  SeLe4n.Kernel.Concurrency.acquireReadLock_eq_ffi h

example (h : SeLe4n.Kernel.Concurrency.RwLockHandle) :
    (SeLe4n.Kernel.Concurrency.snapshotRwLock h : BaseIO UInt64) =
      SeLe4n.Platform.FFI.ffiRwLockSnapshot h.raw :=
  SeLe4n.Kernel.Concurrency.snapshotRwLock_eq_ffi h

/-! ## Peek decoders match Rust encoding -/

-- High-32-bit extraction.
example : SeLe4n.Kernel.Concurrency.peekTicketLockNextTicket (0 : UInt64) = (0 : UInt64) := by decide
example : SeLe4n.Kernel.Concurrency.peekTicketLockServing (0 : UInt64) = (0 : UInt64) := by decide

-- Synthetic packed value: (42 << 32) | 7.
example :
    SeLe4n.Kernel.Concurrency.peekTicketLockNextTicket
      (((42 : UInt64) <<< 32) ||| (7 : UInt64)) = (42 : UInt64) := by
  decide

example :
    SeLe4n.Kernel.Concurrency.peekTicketLockServing
      (((42 : UInt64) <<< 32) ||| (7 : UInt64)) = (7 : UInt64) := by
  decide

-- u32 boundary at the next-ticket position.
example :
    SeLe4n.Kernel.Concurrency.peekTicketLockNextTicket
      (((0xFFFFFFFF : UInt64) <<< 32) ||| (0 : UInt64)) = (0xFFFFFFFF : UInt64) := by
  decide

-- u32 boundary at the serving position.
example :
    SeLe4n.Kernel.Concurrency.peekTicketLockServing
      ((0 : UInt64) ||| (0xFFFFFFFF : UInt64)) = (0xFFFFFFFF : UInt64) := by
  decide

-- ============================================================================
-- §2 — Runtime structural assertions
-- ============================================================================

private def assertBool (msg : String) (b : Bool) : IO Unit :=
  if b then pure () else throw (IO.userError s!"FAIL: {msg}")

/-- Run all SM2.D.3 RAII combinator structural checks at runtime.

    Per the FFI link discipline, we cannot invoke any
    `Platform.FFI.ffi*` symbol here.  We exercise:

    1. Smart constructors produce handles with the expected
       `raw.toNat` value on every valid pool index.
    2. The `isValid` proof carrier is dischargeable.
    3. Marker theorems are reachable (i.e., the names exist and
       the proofs typecheck).
    4. Peek decoder algebra on concrete u32-bound values. -/
def runLockBridgeChecks : IO Unit := do
  IO.println "WS-SM SM2.D.3 — LockBridge RAII combinator suite"
  IO.println "================================================"

  IO.println "--- §1 Smart-constructor round-trips ---"
  -- TicketLock pool: 4 indices.
  for ix in [(0 : Nat), 1, 2, 3] do
    let idx : Fin SeLe4n.Kernel.Concurrency.staticTicketLockPoolSize :=
      match ix with
      | 0 => ⟨0, by decide⟩
      | 1 => ⟨1, by decide⟩
      | 2 => ⟨2, by decide⟩
      | _ => ⟨3, by decide⟩
    let h := SeLe4n.Kernel.Concurrency.mkTicketLockHandle idx
    assertBool s!"mkTicketLockHandle({ix}).raw.toNat = {ix}"
      (decide (h.raw.toNat = ix))
  -- RwLock pool: 4 indices.
  for ix in [(0 : Nat), 1, 2, 3] do
    let idx : Fin SeLe4n.Kernel.Concurrency.staticRwLockPoolSize :=
      match ix with
      | 0 => ⟨0, by decide⟩
      | 1 => ⟨1, by decide⟩
      | 2 => ⟨2, by decide⟩
      | _ => ⟨3, by decide⟩
    let h := SeLe4n.Kernel.Concurrency.mkRwLockHandle idx
    assertBool s!"mkRwLockHandle({ix}).raw.toNat = {ix}"
      (decide (h.raw.toNat = ix))

  IO.println "--- §2 Marker theorem reachability ---"
  -- Bind each marker theorem to a local variable to confirm the
  -- name resolves and the theorem typechecks.  A renamed or removed
  -- theorem would fail to bind.
  let _t1 := @SeLe4n.Kernel.Concurrency.acquireTicketLock_eq_ffi
  let _t2 := @SeLe4n.Kernel.Concurrency.releaseTicketLock_eq_ffi
  let _t3 := @SeLe4n.Kernel.Concurrency.peekTicketLockHolder_eq_ffi
  let _r1 := @SeLe4n.Kernel.Concurrency.acquireReadLock_eq_ffi
  let _r2 := @SeLe4n.Kernel.Concurrency.releaseReadLock_eq_ffi
  let _r3 := @SeLe4n.Kernel.Concurrency.acquireWriteLock_eq_ffi
  let _r4 := @SeLe4n.Kernel.Concurrency.releaseWriteLock_eq_ffi
  let _r5 := @SeLe4n.Kernel.Concurrency.snapshotRwLock_eq_ffi
  let _u1 := @SeLe4n.Kernel.Concurrency.withTicketLock_unfold
  let _u2 := @SeLe4n.Kernel.Concurrency.withReadLock_unfold
  let _u3 := @SeLe4n.Kernel.Concurrency.withWriteLock_unfold
  let _p1 := @SeLe4n.Kernel.Concurrency.peekTicketLockEncoding_roundtrip_u32_masked
  let _p2 := @SeLe4n.Kernel.Concurrency.peekTicketLockNextTicket_is_high32
  let _p3 := @SeLe4n.Kernel.Concurrency.peekTicketLockServing_is_low32
  assertBool "every SM2.D marker theorem reachable" true

  IO.println "--- §3 Peek decoder algebra on concrete values ---"
  assertBool "peekNextTicket(0) = 0"
    (decide (SeLe4n.Kernel.Concurrency.peekTicketLockNextTicket (0 : UInt64) =
              (0 : UInt64)))
  assertBool "peekServing(0) = 0"
    (decide (SeLe4n.Kernel.Concurrency.peekTicketLockServing (0 : UInt64) =
              (0 : UInt64)))
  let packed_5_3 : UInt64 := ((5 : UInt64) <<< 32) ||| (3 : UInt64)
  assertBool "peekNextTicket(pack 5 3) = 5"
    (decide (SeLe4n.Kernel.Concurrency.peekTicketLockNextTicket packed_5_3 = (5 : UInt64)))
  assertBool "peekServing(pack 5 3) = 3"
    (decide (SeLe4n.Kernel.Concurrency.peekTicketLockServing packed_5_3 = (3 : UInt64)))
  -- Boundary: u32::MAX in both halves.
  let max32 : UInt64 := 0xFFFFFFFF
  let packed_max : UInt64 := (max32 <<< 32) ||| max32
  assertBool "peekNextTicket(max32 ‖ max32) = max32"
    (decide (SeLe4n.Kernel.Concurrency.peekTicketLockNextTicket packed_max = max32))
  assertBool "peekServing(max32 ‖ max32) = max32"
    (decide (SeLe4n.Kernel.Concurrency.peekTicketLockServing packed_max = max32))

  IO.println "--- §4 Aggregator size verification ---"
  assertBool "lockPrimitives.length = 22"
    (decide (SeLe4n.Kernel.Concurrency.lockPrimitives.length = 22))

  IO.println "================================================"
  IO.println "All SM2.D.3 LockBridge RAII checks PASS."

end SeLe4n.Testing.LockBridge

def main : IO Unit :=
  SeLe4n.Testing.LockBridge.runLockBridgeChecks
