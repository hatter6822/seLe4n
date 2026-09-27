-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Prelude

/-!
# WS-BP BP7.2 — the physical writes a committed transition owes

Kernel transitions are pure functions of `SystemState`, so a transition that
changes an address space's translation — a mapping, an installed table, a page
carved for a thread — describes the change and does not perform it.  The
hardware walker reads **physical memory**, so each such change owes a store to
RAM: a descriptor in a table page, or a scrub of a page a thread is about to be
handed.  `PhysicalWrite` is that store, recorded in the order the transition
made the change (`SystemState.pendingPhysicalWrites`) and emitted by the syscall
seam after the commit and **before** the shootdown round, so a translation the
transition retired is gone from memory before any core is told to drop it from
its TLB.

This is the ledger shape `pendingIcacheMaintenance` established (SM7.D.1), and
it is extracted to this pure module for that ledger's reason: a state-layer field
must not pull the architecture layer's import closure.

## Encoding contract

The tag/operand encoding **must** stay in lockstep with
`rust/sele4n-hal/src/user_translation.rs::apply_physical_write`:

  tag 0 = zero one 4 KiB page at `addr`            (`value` ignored)
  tag 1 = store the descriptor `value` at `addr`
  tag 2 = invalidate every translation tagged `addr` as an ASID (`value` ignored)
-/

namespace SeLe4n.Kernel.Architecture

/-- **WS-BP BP7.2: one physical write a committed transition owes.** -/
inductive PhysicalWrite where
  /-- Zero the 4 KiB page at `base` — a page carved for a thread (a frame, a
      table, an address space's top-level table), scrubbed before any
      capability to it exists.  The model performs the same write on
      `MachineState.memory` (`zeroMemoryRange`). -/
  | zeroPage (base : SeLe4n.PAddr)
  /-- Store the 64-bit translation descriptor `value` at `entry`, the address
      of one entry of a table page. -/
  | storeDescriptor (entry : SeLe4n.PAddr) (value : UInt64)
  /-- Invalidate every translation cached under `asid`, on every PE — owed
      when a table descriptor is cleared (the walk caches intermediate levels,
      and a leaf TLBI names one address) and when an ASID is handed to a new
      address space. -/
  | invalidateAsid (asid : SeLe4n.ASID)
  deriving Repr, DecidableEq

namespace PhysicalWrite

/-- The FFI tag (see the module's encoding contract). -/
def tag : PhysicalWrite → UInt64
  | .zeroPage _ => 0
  | .storeDescriptor _ _ => 1
  | .invalidateAsid _ => 2

/-- The FFI address operand. -/
def addr : PhysicalWrite → UInt64
  | .zeroPage base => base.toNat.toUInt64
  | .storeDescriptor entry _ => entry.toNat.toUInt64
  | .invalidateAsid asid => asid.toNat.toUInt64

/-- The FFI value operand. -/
def value : PhysicalWrite → UInt64
  | .zeroPage _ => 0
  | .storeDescriptor _ v => v
  | .invalidateAsid _ => 0

/-- Every tag is one of the three the HAL decodes. -/
theorem tag_le_two (w : PhysicalWrite) : w.tag ≤ 2 := by
  cases w <;> simp [tag]

end PhysicalWrite

end SeLe4n.Kernel.Architecture
