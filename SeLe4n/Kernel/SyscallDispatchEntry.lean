-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- WS-SM SM6.A: PRODUCTION (LANDED).  The cross-core-aware syscall dispatch entry
-- `syscallDispatchCrossCoreEntry` (`@[export lean_syscall_dispatch_cross_core]`)
-- is the live seam the Rust SVC handler resolves against; it runs the verified
-- `syscallDispatchFromAbi` (per-core caller via the threaded `executingCore`) and
-- fires the diff-recovered cross-core `.reschedule` SGIs.  (Former "STATUS:
-- staged" marker replaced with this landing note per the implement-the-improvement
-- rule; see docs/planning/SMP_CROSS_CORE_IPC_PLAN.md.)

import SeLe4n.Kernel.Scheduler.PriorityInheritance.PerCore
import SeLe4n.Kernel.Concurrency.Runtime
import SeLe4n.Platform.FFI

/-!
# WS-SM SM6.A — Cross-core syscall dispatch entry (the live SGI-dispatch seam)

The C-callable seam the Rust SVC trap handler (`svc_dispatch::dispatch_svc`)
invokes for every syscall, in its cross-core-aware form.  It is the syscall
analogue of `perCoreTimerTickEntry` (the per-core timer ISR seam): it runs the
verified pure dispatch (`Platform.FFI.syscallDispatchFromAbi`) atomically against
the live kernel state, then **fires the cross-core `.reschedule` SGIs that the
state transition warrants** — recovered purely from the `(pre, post)` diff by
the SM5.F.4 dispatch `computeCrossCoreSgis`.

This closes the live half of the SM5.F.4 diff-based cross-core SGI dispatch for
the syscall path: the existing `Platform.FFI.syscallDispatchInner` commits the
post-state but never pokes a remote core, so a syscall whose effect makes a remote
thread newly runnable (an endpoint-call receiver or notification waiter / bound TCB
woken on another core — WS-SM SM6.A/SM6.B) or migrates its run-queue bucket (a
`.call`'s donation boosting a passive server pinned to another core) would leave
that core unscheduled until its next local timer tick.  This entry fires the IPI
immediately after the commit.  (The `computeCrossCoreSgis` diff recovers *both*
cases — see `crossCoreSgiBody_remote_wake` for the wake direction.)

**Single-core inertness (trace safety).** On the boot core,
`PriorityInheritance.computeCrossCoreSgis pre post bootCoreId = []` whenever every
thread's home core is the boot core (`computeCrossCoreSgis_nil_single_core`), and
`Concurrency.fireCrossCoreSgis [] = pure ()`.  So on the single-core
configuration the entry is observably identical to the boot-pinned
`syscallDispatchInner` — it commits the same state and performs no IPI.  The
model-layer trace harness exercises the pure `syscallEntry`, not this BaseIO
seam, so the golden trace is unaffected.

The `@[export lean_syscall_dispatch_cross_core]` keeps the symbol live for the
Rust extern.  The live switchover (the trap handler calling this instead of the
boot-pinned `syscall_dispatch_inner`) lands with the per-core dispatch seam,
when the executing core is threaded into `syscallDispatchFromAbi` so the calling
thread is identified and descheduled on its own core rather than the boot core.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId SgiKind)

/-- **WS-SM SM6.A**: the cross-core-aware syscall dispatch entry — the live
SGI-dispatch seam.  Reads the deployment labeling context and the executing core
from the hardware (`currentCoreId`), runs the verified
`Platform.FFI.syscallDispatchFromAbi` atomically against the kernel state ref
(`modifyGetKernelState`, committing the post-state), then — *after* the commit —
fires the cross-core `.reschedule` SGIs recovered from the `(pre, post)` diff by
`PriorityInheritance.computeCrossCoreSgis`.  Returns the ABI-encoded result word
(every kernel rejection is encoded into the success word with bit 63 set, so the
pure dispatch never takes the `.error` arm; the arm is discharged inertly). -/
@[export lean_syscall_dispatch_cross_core]
def syscallDispatchCrossCoreEntry
    (syscallId : UInt32) (msgInfo : UInt64)
    (x0 x1 x2 x3 x4 x5 : UInt64)
    (ipcBufferAddr : UInt64) : BaseIO UInt64 := do
  let ctx ← Platform.FFI.getKernelLabelingContext
  let execCore ← Concurrency.currentCoreId
  let result ← Platform.FFI.modifyGetKernelState (fun st =>
    match Platform.FFI.syscallDispatchFromAbi ctx execCore syscallId msgInfo x0 x1 x2 x3 x4 x5
        ipcBufferAddr st with
    | Except.ok (encoded, st') =>
        ((encoded, PriorityInheritance.computeCrossCoreSgis st st' execCore), st')
    | Except.error e =>
        ((Platform.FFI.encodeError e, ([] : List (CoreId × SgiKind))), st))
  Concurrency.fireCrossCoreSgis result.2
  pure result.1

/-- **WS-SM SM6.A** structural marker: `syscallDispatchCrossCoreEntry` unfolds to
the read-context / read-core / commit-dispatch / fire-SGIs / return-encoded
driver.  Pins the body shape (atomic `modifyGetKernelState` over
`syscallDispatchFromAbi`, then `fireCrossCoreSgis` of the diff-recovered SGIs) so
a refactor that drops the SGI firing or the state commit breaks this marker at
elaboration; combined with `@[export]` (which the Rust extern resolves against)
the seam cannot regress silently. -/
theorem syscallDispatchCrossCoreEntry_def
    (syscallId : UInt32) (msgInfo : UInt64) (x0 x1 x2 x3 x4 x5 : UInt64)
    (ipcBufferAddr : UInt64) :
    syscallDispatchCrossCoreEntry syscallId msgInfo x0 x1 x2 x3 x4 x5 ipcBufferAddr =
      (do
        let ctx ← Platform.FFI.getKernelLabelingContext
        let execCore ← Concurrency.currentCoreId
        let result ← Platform.FFI.modifyGetKernelState (fun st =>
          match Platform.FFI.syscallDispatchFromAbi ctx execCore syscallId msgInfo x0 x1 x2 x3 x4 x5
              ipcBufferAddr st with
          | Except.ok (encoded, st') =>
              ((encoded, PriorityInheritance.computeCrossCoreSgis st st' execCore), st')
          | Except.error e =>
              ((Platform.FFI.encodeError e, ([] : List (CoreId × SgiKind))), st))
        Concurrency.fireCrossCoreSgis result.2
        pure result.1) := rfl

/-- **WS-SM SM6.A** trace-safety witness: on the boot core, when every thread's
home core is the boot core (the single-core configuration), the diff-recovered
SGI list the entry fires is empty.  Combined with `fireCrossCoreSgis [] = pure ()`
this is the machine-checked statement that the cross-core entry is observably
identical to a plain commit-and-return on single-core — it commits the same
post-state and performs no IPI.  Re-exports `computeCrossCoreSgis_nil_single_core`
at the entry's dispatch granularity. -/
theorem syscallDispatchCrossCoreEntry_sgis_nil_single_core
    (pre post : SystemState)
    (hAllBoot : ∀ t : SeLe4n.ThreadId,
      determineTargetCore post t = Concurrency.bootCoreId) :
    PriorityInheritance.computeCrossCoreSgis pre post Concurrency.bootCoreId = [] :=
  PriorityInheritance.computeCrossCoreSgis_nil_single_core pre post hAllBoot

end SeLe4n.Kernel
