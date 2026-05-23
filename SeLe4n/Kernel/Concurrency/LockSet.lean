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

/-!
# WS-SM SM3.B — LockSet re-export hub

Re-exports the four SM3.B modules into a single import surface,
mirroring the `Operations / Invariant` split pattern documented in
`CLAUDE.md`'s "Source layout" section: re-export hubs are
import-only files that preserve backward compatibility, so future
callers can `import SeLe4n.Kernel.Concurrency.LockSet` instead of
the four underlying modules.

* `LockSet` — abstract LockSet type + canonical sort + ordered /
  complete / canonical theorems.
* `LockIdProjection` — `KernelObject.lockKind`, `LockId.fromObject`,
  `LockId.lookup`.
* `LockSetTransitions` — per-syscall `lockSet_<τ>` definitions +
  `permittedKinds` + `lockSet_consistent_<τ>` theorems.
* `LockSetInventory` — typed theorem inventory + per-category
  count witnesses.

SM3.C (`withLockSet` 2PL combinator) and SM3.D (deadlock-freedom)
will consume this hub.
-/
