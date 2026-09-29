-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Prelude
import SeLe4n.Kernel.Architecture.CacheInvalidation

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

  tag 0 = zero one 4 KiB page at `addr`, then clean it to the Point of
          Unification and invalidate every instruction cache in the domain
          (`PhysicalWrite.icacheMaintenance`)  (`value` ignored)
  tag 1 = store the **level-3 page** descriptor `value` at `addr`
  tag 2 = invalidate every translation tagged `addr` as an ASID (`value` ignored)
  tag 3 = store the user word `value` at `addr`, in a thread's RAM page (WS-BP BP7.8)
  tag 4 = store the **table** descriptor `value` at `addr`, an entry of a level
          0–2 table page (PR #904, `v0.36.41`)

The two descriptor tags are distinct because the walker reads a descriptor by
the **level** of the table it sits in, and bits `[1:0] = 0b11` mean a page at
level 3 and a table at levels 0–2.  The HAL validates what a descriptor
*says* — a page's output address is a thread's frame or the device window, a
table's is a thread table page — and it can do that only if it knows which
reading the walker will apply.
-/

namespace SeLe4n.Kernel.Architecture

/-- **WS-BP BP7.2: one physical write a committed transition owes.** -/
inductive PhysicalWrite where
  /-- Zero the 4 KiB page at `base` — a page carved for a thread (a frame, a
      table, an address space's top-level table), scrubbed before any
      capability to it exists.  The model performs the same write on
      `MachineState.memory` (`zeroMemoryRange`). -/
  | zeroPage (base : SeLe4n.PAddr)
  /-- Store the 64-bit **level-3 page** descriptor `value` at `entry`, the
      address of one entry of a level-3 table page — a thread's mapping, or its
      clear (`0`). -/
  | storeDescriptor (entry : SeLe4n.PAddr) (value : UInt64)
  /-- Invalidate every translation cached under `asid`, on every PE — owed
      when a table descriptor is cleared (the walk caches intermediate levels,
      and a leaf TLBI names one address) and when an ASID is handed to a new
      address space. -/
  | invalidateAsid (asid : SeLe4n.ASID)
  /-- **WS-BP BP7.8**: store the 64-bit word `value` at `addr`, an eight-byte
      aligned address in a page of RAM a thread maps — a delivered message
      register past the four the return frame carries, written into the
      receiver's IPC buffer.  Distinct from `storeDescriptor` because the two
      name different memory: a descriptor lives in a table page (the boot pool
      or a carved table), a user word in a thread's own frame.  The HAL refuses
      a user word in the **pool**; a *carved* table is RAM past the kernel's
      extent like a frame, which the HAL cannot tell apart, so what keeps a
      user word out of it is this model — the address is resolved through the
      thread's own VSpace (`IpcBufferRead.ipcBufferSlotPAddr?`), which maps
      only frames, and carves are disjoint, so no mapped page is a table
      page. -/
  | storeUserWord (addr : SeLe4n.PAddr) (value : UInt64)
  /-- **PR #904 (`v0.36.41`)**: store the 64-bit **table** descriptor `value`
      at `entry`, the address of one entry of a level 0–2 table page — an
      installed table, or its clear (`0`).  Distinct from `storeDescriptor`
      because the walker reads a `0b11` descriptor as a table at these levels
      and as a page at level 3, and the HAL validates the output address
      against the reading the walker will apply. -/
  | storeTableDescriptor (entry : SeLe4n.PAddr) (value : UInt64)
  deriving Repr, DecidableEq

namespace PhysicalWrite

/-- The FFI tag (see the module's encoding contract). -/
def tag : PhysicalWrite → UInt64
  | .zeroPage _ => 0
  | .storeDescriptor _ _ => 1
  | .invalidateAsid _ => 2
  | .storeUserWord _ _ => 3
  | .storeTableDescriptor _ _ => 4

/-- The FFI address operand. -/
def addr : PhysicalWrite → UInt64
  | .zeroPage base => base.toNat.toUInt64
  | .storeDescriptor entry _ => entry.toNat.toUInt64
  | .invalidateAsid asid => asid.toNat.toUInt64
  | .storeUserWord a _ => a.toNat.toUInt64
  | .storeTableDescriptor entry _ => entry.toNat.toUInt64

/-- The FFI value operand. -/
def value : PhysicalWrite → UInt64
  | .zeroPage _ => 0
  | .storeDescriptor _ v => v
  | .invalidateAsid _ => 0
  | .storeUserWord _ v => v
  | .storeTableDescriptor _ v => v

/-- Every tag is one of the five the HAL decodes. -/
theorem tag_le_four (w : PhysicalWrite) : w.tag ≤ 4 := by
  cases w <;> simp [tag]

/-- **WS-BP post-landing audit (`v0.36.32`): the instruction-cache maintenance a
physical write owes after its store**, which the HAL performs as the last step
of the write itself (`user_translation::apply_physical_write`, through
`user_translation::icache_maintenance`).

A zeroing is the only write that needs it.  It scrubs a page the kernel is about
to hand out — a frame a thread may map **executable** — through the kernel's
data cache, and an instruction fetch reads at the Point of Unification: until a
clean pushes the zeroes there, a fetch of the page can still read the bytes its
**previous owner** left (Cortex-A76 reports `CTR_EL0.IDC = 0`, so the data side
is not coherent with instruction fetch without that clean).  The operand is the
re-type's own (`ICacheInvalidation.cleanRangeIallu`, whose docstring states the
hazard for the in-place re-type's scrub and cites seL4's `clearMemory`): clean
the page, then invalidate every instruction cache in the domain, so no core
keeps a line of the page fetched before the carve.  The carve's scrub is a
kernel code-write site for that reason (`KernelCodeWriteSite.carveScrub`), and
this is its emission — carried by the write, so the clean can never be separated
from the zero it follows or reordered before it.

A descriptor store needs none (the table walk is coherent with the data cache
under `TCR_EL1`'s write-back, inner-shareable walk attributes), nor an ASID
invalidation, nor a user word (a thread's own buffer: a thread that executes
what it or the kernel wrote there unifies it itself, through
`.vspaceUnifyInstruction`). -/
def icacheMaintenance : PhysicalWrite → Option ICacheInvalidation
  | .zeroPage base => some (.cleanRangeIallu base SeLe4n.pageBytes)
  | .storeDescriptor _ _ => none
  | .invalidateAsid _ => none
  | .storeUserWord _ _ => none
  | .storeTableDescriptor _ _ => none

/-- **WS-BP post-landing audit (`v0.36.32`)**: a zeroing owes the clean of exactly
the page it zeroes, then the domain-wide invalidate. -/
@[simp] theorem icacheMaintenance_zeroPage (base : SeLe4n.PAddr) :
    (zeroPage base).icacheMaintenance = some (.cleanRangeIallu base SeLe4n.pageBytes) := rfl

/-- **WS-BP post-landing audit (`v0.36.32`)**: exactly the zeroings owe
instruction-cache maintenance. -/
theorem icacheMaintenance_isSome_iff (w : PhysicalWrite) :
    w.icacheMaintenance.isSome ↔ ∃ base, w = zeroPage base := by
  cases w <;> simp [icacheMaintenance]

end PhysicalWrite

end SeLe4n.Kernel.Architecture
