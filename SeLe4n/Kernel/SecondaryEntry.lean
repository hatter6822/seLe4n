-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- STATUS: staged for WS-SM SM5+ (SM1.C.6 placeholder secondary kernel
-- entry; consumed when the per-core scheduler lands at SM5)
import SeLe4n.Kernel.Concurrency.Types
import SeLe4n.Platform.FFI

/-!
# WS-SM SM1.C.6 — Secondary-core kernel entry

This module provides the Lean-side entry point that the Rust HAL's
`rust_secondary_main` (see `rust/sele4n-hal/src/smp.rs`) calls into
after completing the per-core hardware-init sequence (MMU, VBAR, GIC
CPU interface, timer, IRQ unmask).

## SM1.C.6 placeholder semantics

At SM1.C the function is intentionally a pass-through that returns
`pure ()`.  The Rust caller falls into a low-power `wfe` idle loop
after this returns, so a secondary core that reaches SM1.C arrives
fully-initialised and parks until either:

  1. SM5 replaces this body with the per-core scheduler entry, or
  2. SM7 cross-core IPC sends an SGI that wakes the parked core.

Returning immediately at SM1.C is **deliberate**:  the per-core
scheduler state, idle TCB, and runnable thread set do not exist until
SM5 lands.  Spinning here without runnable work would defer the
secondary's first opportunity to receive an IRQ (the WFE in the Rust
caller is interruptible, but a Lean-side spin is not).

## Lean → Rust ABI contract

`@[export lean_secondary_kernel_main]` instructs the Lean compiler to
emit a C-callable wrapper named `lean_secondary_kernel_main` against
which the Rust side resolves
`extern "C" { fn lean_secondary_kernel_main(core_id: u64); }`.  The
attribute is required so the symbol is linkable; without it the Rust
extern would fail at link time.

## Build reachability

This module is in the production import closure via
`SeLe4n/Platform/Staged.lean` (added to the staged-module allowlist
per the WS-RC R12.B partition gate).  CI builds the bridge on every
push; SM5 will move it from staged → production-reached when per-core
scheduler state lands.

## Anti-cycle note

`Concurrency.Types` is foundational (no `Platform.*` deps).
`Platform.FFI` imports `Platform.Boot`, which transitively imports
`Platform.Contract` → `Concurrency.Types`.  This file imports both:

```
Concurrency.Types  ← Platform.Contract  ← Platform.Boot
                                        ← Platform.FFI
                                        ← SecondaryEntry (this file)
```

A future refactor that moved this file's logic into `Concurrency.*`
would break layering — `Concurrency.*` must not depend on
`Platform.*`.
-/

namespace SeLe4n.Kernel

/-- **WS-SM SM1.C.6** (closes SMP-C2 Lean side): Secondary-core
kernel entry.

Called from Rust `smp.rs::rust_secondary_main` once per secondary
core after the per-core hardware-init sequence (MMU, VBAR, GIC,
timer, IRQ unmask) completes.

The `coreId` argument is the PSCI `context_id` (1..=`MAX_SECONDARY_CORES`
on RPi5; the `Fin numCores` range invariant is verified by
`Concurrency.currentCoreId` at the first per-core kernel-state lookup
SM5+ wires up).

**SM1.C semantics**: this function returns `pure ()` immediately.
The Rust caller idles on `wfe` after this returns.  SM5 will replace
the body with the per-core scheduler entry (selecting from the
runnable thread set, dispatching, and handling per-core tick IRQs).

**SM5 transition**: the body will switch from `pure ()` to
something like:

```lean
do
  let st ← getKernelState
  let coreId ← Concurrency.currentCoreId  -- typed CoreId
  let st' := perCoreSchedulerEntry coreId st
  initialiseKernelState st'
```

reusing the verified `Kernel` monad to update kernel state under
the per-core scheduler's transition. -/
@[export lean_secondary_kernel_main]
def secondaryKernelMain (_coreId : UInt64) : BaseIO Unit :=
  pure ()

/-- **WS-SM SM1.C.6** structural marker: `secondaryKernelMain`
totality.

A trivial witness used as a surface anchor — the function takes a
`UInt64` and returns `BaseIO Unit`, and the return value is always
`()`.  Pinning this here lets downstream Tier-3 scans verify the
SM1.C placeholder semantics are preserved (SM5 will replace this
theorem with a substantive scheduler-entry correctness witness). -/
theorem secondaryKernelMain_returns_unit_marker (coreId : UInt64) :
    secondaryKernelMain coreId = pure () := by
  rfl

end SeLe4n.Kernel
