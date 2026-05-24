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

/-!
# WS-SM SM3.B + SM3.C — LockSet re-export hub

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

SM3.D (deadlock-freedom) and SM3.E (serializability) will consume
this hub.
-/
