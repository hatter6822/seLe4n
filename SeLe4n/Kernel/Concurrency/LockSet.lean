-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Concurrency.Locks.LockSet
import SeLe4n.Kernel.Concurrency.Locks.LockIdProjection
import SeLe4n.Kernel.Concurrency.Locks.LockSetTransitions
import SeLe4n.Kernel.Concurrency.Locks.LockSetInventory
import SeLe4n.Kernel.Concurrency.Locks.WithLockSet
import SeLe4n.Kernel.Concurrency.Locks.LockSetHeld
import SeLe4n.Kernel.Concurrency.Locks.LockSet2PL
import SeLe4n.Kernel.Concurrency.Locks.DynamicChainExtension
import SeLe4n.Kernel.Concurrency.Locks.Sm3CInventory
import SeLe4n.Kernel.Concurrency.Locks.Deadlock
import SeLe4n.Kernel.Concurrency.Locks.Sm3DInventory
import SeLe4n.Kernel.Concurrency.Locks.Serializability
import SeLe4n.Kernel.Concurrency.Locks.Sm3EInventory

/-!
# WS-SM SM3.B + SM3.C + SM3.D + SM3.E — LockSet re-export hub

Re-exports the SM3.B + SM3.C modules into a single import surface,
mirroring the `Operations / Invariant` split pattern documented in
`CLAUDE.md`'s "Source layout" section: re-export hubs are
import-only files that preserve backward compatibility, so future
callers can `import SeLe4n.Kernel.Concurrency.LockSet` instead of
the underlying modules.

## SM3.B modules (per-transition lock-set declarations)

* `LockSet` — abstract LockSet type + canonical sort + ordered /
  complete / canonical theorems.
* `LockIdProjection` — `KernelObject.lockKind`, `LockId.fromObject`,
  `LockId.lookup`.
* `LockSetTransitions` — per-syscall `lockSet_<τ>` definitions +
  `permittedKinds` + `lockSet_consistent_<τ>` theorems.
* `LockSetInventory` — SM3.B typed theorem inventory.

## SM3.C modules (2PL discipline + SMP-migration contract)

* `WithLockSet` — `withLockSet` 2PL combinator (SM3.C.1) +
  per-object `acquireLockOnObject` / `releaseLockOnObject`
  (SM3.C.2) + `KernelObject.updateLock` helper.
* `LockSetHeld` — `lockHeld` / `lockSetHeld` predicates
  (SM3.C.4) — the SMP-migration precondition for Corollary 2.1.11.
* `LockSet2PL` — 2PL discipline theorems: `lockSet_acquired_in_order`
  (SM3.C.5), `lockSet_released_in_reverse` (SM3.C.6),
  `lockSet_atomic_under_2pl` (SM3.C.7),
  `lockSet_invariant_preserved` (SM3.C.8).
* `DynamicChainExtension` — `withDynamicChainExtension` (SM3.C.11)
  for PIP-chain dynamic locking under the SM0.I total-order
  discipline.
* `Sm3CInventory` — SM3.C typed theorem inventory.

## SM3.D modules (deadlock-freedom)

* `Deadlock` — the abstract `KernelExecution` model + the 2PL +
  ordering hypotheses + `deadlockFreedom_under_2pl_and_ordering`
  (Theorem 2.1.9, SM3.D.4), `waitGraph_acyclic_under_2pl` (the
  N-core DAG form, SM3.D.5), `boundedWait_under_2pl` (SM3.D.6), and
  the §7 grounding bridge that discharges the hypotheses from the
  SM3.B/SM3.C `lockAcquireSequence` discipline.
* `Sm3DInventory` — SM3.D typed theorem inventory.

## SM3.E modules (serializability)

* `Serializability` — the `KernelTransitionInstance` schedule model +
  `conflictOrder` (SM3.E.1) + `serialEquivalent` (SM3.E.2) +
  `serializability_under_2pl` (Theorem 2.1.10, SM3.E.3) +
  `strictly_2pl_preserved` (SM3.E.4) + the commutativity lemmas
  (SM3.E.5) + `singleCore_proof_preservation` (Corollary 2.1.11,
  SM3.E.6), built on the conflict-graph acyclicity
  (`conflictGraph_acyclic`).
* `Sm3EInventory` — SM3.E typed theorem inventory.
-/
