-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Concurrency.Types
import SeLe4n.Kernel.Concurrency.Runtime
import SeLe4n.Kernel.IPC.CrossCore.Fault
import SeLe4n.Kernel.IPC.Invariant.FaultProgress
import SeLe4n.Kernel.Scheduler.PriorityInheritance.PerCore
import SeLe4n.Platform.FFI

/-!
# WS-RR RR4.23/RR4.25 — the fault kernel entry

The C-callable seam the Rust trap handler's abort and exception arms invoke,
and the classification export that makes the Lean model the **only** place an
ESR_EL1 value becomes an exception class.

## Three exports, one classifier

* `lean_classify_synchronous_exception` (RR4.25) answers "what kind of
  synchronous exception is this?" from `ESR_EL1` alone.  `trap.rs` calls it on
  the hardware target instead of running its own `esr_ec` match, so the two
  classifications cannot diverge: there is only one for a core that may enter
  Lean.  A core whose runtime is not yet initialized classifies through the
  Rust mirror pinned to this table over all 64 EC values (PR #887 review
  round 2) — the readiness contract is about the symbol, not the function.
* `lean_handle_fault` (RR4.23) is the delivery: it classifies, spills the trap
  frame's fault window, builds the fault, and runs the flow-checked
  `faultDeliverOnCoreChecked` against the live kernel state, firing the
  cross-core SGIs the pre/post diff surfaces.
* `lean_handle_unknown_syscall` (review round, PR #887) is the same delivery
  for seL4's `UnknownSyscall`: `trap.rs`'s `SVC` arm invokes it when the
  syscall prefilter rejects the syscall number, so the fault the model carried
  since RR4 has a live producer.

The split exists because `trap.rs` must still *route* — an `SVC` goes to the
syscall dispatcher, everything else to the fault entry — and routing needs the
class before the state commit.  Both exports read the same
`classifySynchronousException`, so the routing decision and the delivery agree
by construction rather than by inspection.

## Concurrency

`lean_handle_fault` commits through `Platform.FFI.modifyGetKernelState`, an
`IO.Ref` read-then-write and **not** a cross-core atomic, so it must run inside
the global kernel-entry lock: `trap.rs` wraps the call in
`kernel_entry::with_kernel_entry`, like every other state-committing seam.

## Readiness

The entry is behind the per-core `lean_ready` gate on the Rust side, like the
timer tick and the `.reschedule` receiver; since WS-BP BP6 every serving PE
marks itself ready, so an abort on hardware is delivered here, and since WS-BP
BP7.6 the core returns through the successor the delivery installed.
-/

namespace SeLe4n.Kernel

open SeLe4n
open SeLe4n.Model
open SeLe4n.Kernel.Architecture
open SeLe4n.Kernel.Concurrency

-- ============================================================================
-- §1  RR4.25 — the single classification path
-- ============================================================================

/-- WS-RR RR4.25: the wire tag for each synchronous exception class.

`trap.rs` mirrors these eight values (`sync_class` in that module) and nothing
else: the *mapping* from `ESR_EL1` to a class lives only here, so the Rust
side cannot classify differently — it can only fail to recognise a tag, which
it treats as `unknownReason` (the same fail-closed default this map has). -/
def syncExceptionClassTag : SynchronousExceptionClass → UInt32
  | .svc           => 0
  | .dataAbort     => 1
  | .instrAbort    => 2
  | .pcAlignment   => 3
  | .spAlignment   => 4
  | .unknownReason => 5
  | .kernelAbort   => 6
  | .fpAccess      => 7

/-- WS-RR RR4.25: the tags are pairwise distinct, so the Rust router's match
on them is a total, unambiguous decoding of the Lean classification. -/
theorem syncExceptionClassTag_injective (a b : SynchronousExceptionClass)
    (h : syncExceptionClassTag a = syncExceptionClassTag b) : a = b := by
  cases a <;> cases b <;> first | rfl | (exact absurd h (by decide))

/-- WS-RR RR4.25 (**the export**): classify an `ESR_EL1` value.

The Rust trap handler calls this on the hardware target rather than running
its own `esr_ec` match, so a ready core has one classification path, not two.
Pure: it reads no kernel state and commits none, so it needs no entry lock —
`trap.rs` calls it *before* taking one, to decide where to route.  It is
still a Lean-emitted symbol, so `trap.rs` consults the per-core readiness
gate first and classifies through its pinned mirror on a core whose runtime
is not yet initialized (PR #887 review round 2).

It classifies the word (`classifySynchronousExceptionOfEsr`), not a context
built around it, so its compiled body allocates nothing: the one upcall that
runs outside the entry lock on every synchronous exception does not touch the
heap (WS-CV CV0.4). -/
@[export lean_classify_synchronous_exception]
def classifySynchronousExceptionExport (esr : UInt64) : UInt32 :=
  syncExceptionClassTag (classifySynchronousExceptionOfEsr esr)

/-- WS-RR RR4.25: the export is the classification, tagged — the structural
marker that a refactor cannot quietly replace the body with a second table. -/
theorem classifySynchronousExceptionExport_def (esr : UInt64) :
    classifySynchronousExceptionExport esr =
      syncExceptionClassTag (classifySynchronousExceptionOfEsr esr) := rfl

/-- The export classifies as the context form does on any context carrying the
word: the routing decision and the delivery agree. -/
theorem classifySynchronousExceptionExport_eq_context (ectx : ExceptionContext) :
    classifySynchronousExceptionExport ectx.esr =
      syncExceptionClassTag (classifySynchronousException ectx) := rfl

/-- WS-RR RR4.25: classification reads the ESR alone — the other three
syndrome words the export does not receive cannot change the answer, which is
what makes a one-argument export faithful rather than lossy. -/
theorem classifySynchronousException_depends_only_on_esr (ectx : ExceptionContext) :
    classifySynchronousException ectx =
      classifySynchronousException { esr := ectx.esr, elr := 0, spsr := 0, far := 0 } := rfl

-- ============================================================================
-- §2  RR4.23 — the fault delivery entry
-- ============================================================================

-- `writeFaultRegistersToTcb` and its three lemmas (`_id_when_not_tcb`,
-- `_getTcb?`, `faultContextOfThread_writeFaultRegistersToTcb`) live in
-- `SeLe4n/Kernel/IPC/Operations/Fault.lean` §8 since PR #887 review round 3:
-- the SVC seam (`Platform.FFI.syscallDispatchFromAbi`, below this module in the
-- import graph) spills the same window when it delivers a capability fault.

/-- The state the delivery commits for the faulting thread `tid` on core `c`,
before the core's successor is chosen: the trap frame's window spilled into the
thread, the fault context built from the spilled registers, the flow-checked
delivery.  Named so the entry and its progress theorem read the one state. -/
def faultDeliveredState (lctx : LabelingContext) (st : SystemState) (f : Fault)
    (ectx : ExceptionContext) (w : FaultRegisterWindow) (c : CoreId)
    (tid : SeLe4n.ThreadId) : SystemState :=
  let stRegs := writeFaultRegistersToTcb st tid w
  let fctx := faultContextOfThread stRegs tid ectx.elr ectx.spsr
  (faultDeliverOnCoreChecked lctx stRegs tid f fctx c).1

/-- Review round (PR #887): **the delivery the two fault entries share**, given
the fault already chosen.  Spill the trap frame's window, build the context
from the spilled file, run the flow-checked delivery, dispatch the executing
core's successor through the seam gate, and derive every cross-core poke from
the pre/post diff.

Separated from the classification so that the two producers — the
syndrome-classified entry (`faultEntryStep`) and the unknown-syscall entry
(`unknownSyscallEntryStep`), whose fault the syscall prefilter names rather
than the ESR — commit through one body, and so every theorem below is stated
once about it.

**The delivery is the flow-checked one** (`faultDeliverOnCoreChecked`), not the
bare transition.  The live syscall seam gates every endpoint operation through
`syscallEntryChecked`, and a fault message is an endpoint operation the kernel
performs on a thread's behalf: leaving this entry ungated would let the kernel
carry a faulting thread's fault address, syndrome and register window into a
handler's domain across a boundary the deployment policy forbids — the one
flow no syscall can make.  Because a denied flow takes the RR4.9 suspend
rather than an error, the gate costs the progress guarantee nothing
(`faultDeliverOnCoreChecked_not_dispatchable`).

**The context is built from the spilled trap frame, never from the mirror
alone** (`writeFaultRegistersToTcb` first, then `faultContextOfThread` on the
spilled state): `TCB.registerContext` is a partial mirror of the hardware file
and between syscalls holds the *last syscall's* arguments, so a context built
from it would report a stale argument window and, on a payload-free resume,
reinstall it over the thread's live registers
(`faultContextOfThread_writeFaultRegistersToTcb`).

**The SGIs are read off the reschedule flags, not off the delivery.**  The
Call chain surfaces at most one poke — the woken handler's home core — but the
delivery can change more than one core's view: the priority-inheritance walk
re-buckets a handler already queued elsewhere, and a passive handler's
donation moves a replenishment queue.  Every such write raises the flag of the
core it stales, and the entry pokes each remote core whose flag the step
raised, exactly as `syscallDispatchCrossCoreEntry` does for the `.call` arm
this delivery composes (KSC-1: `faultEntryDeliver_sgis_cover_diff` — the flags
cover the whole-index diff `PriorityInheritance.computeCrossCoreSgis`, which
stays as the specification); reading only the surfaced poke would leave a
re-bucketed remote core running the wrong thread until something else woke it.

**The executing core's successor** is dispatched in the same atomic step, as
at every other state-committing entry (`scheduleLocalSuccessor`): the delivery
vacates this core, and since WS-BP BP7.6 the context restore installs the
successor, so the flags are read off the *final* state. -/
def faultEntryDeliver (lctx : LabelingContext) (st : SystemState) (f : Fault)
    (ectx : ExceptionContext) (w : FaultRegisterWindow) (c : CoreId) :
    List (CoreId × SgiKind) × SystemState :=
  -- KSC-1: the reschedule flags are captured before the delivery consumes `st`;
  -- a remote core is poked when the step raised its flag.
  let pending0 := reschedulePendingSnapshot st
  match st.scheduler.currentOnCore c with
  | none =>
      -- `v0.36.40`: another core vacated this one (a remote `.tcbSuspend` or
      -- holder deschedule cleared the slot while the trapping thread still ran
      -- here).  There is no thread to deliver for, but the core must be handed
      -- something to resume, or the trap layer halts it.
      let st' := PriorityInheritance.dispatchVacatedCore st c
      (rescheduleSgisFromFlags pending0 st'.scheduler.reschedulePending, st')
  | some tid =>
      let st' := faultDeliveredState lctx st f ectx w c tid
      let st'' := PriorityInheritance.scheduleLocalSuccessorFrom (some tid) st' c
      (rescheduleSgisFromFlags pending0 st''.scheduler.reschedulePending, st'')

/-- WS-RR RR4.23: the verified step the fault entry commits — classify, spill
the trap frame's window, build the fault context from the spilled registers,
deliver.

Separated from the `BaseIO` entry so the whole decision is a pure function of
the pre-state, the syndrome and the window, and so the tests exercise exactly
what the seam runs.  Returns the SGI list the entry fires after the commit, in
the shape `fireCrossCoreSgis` consumes.

Three inert arms, each fail-closed: an out-of-range core id (no run queue to
attribute the trap to), an `SVC` or a **kernel abort** (`faultOfExceptionContext`
yields `none` — an `SVC` never reaches here because `trap.rs` routes it to the
syscall dispatcher, and a current-EL abort is the kernel's own fault, which the
trap layer halts on), and — review round, PR #887 — an exception **taken from
EL1** whatever its syndrome (`ExceptionContext.takenFromEl0` is false): an
alignment fault or an undefined instruction has one EC whichever EL raised it,
and a kernel-origin exception attributed to the current user thread would hand
that thread's handler the kernel's fault address and register window, with a
reply that could resume the kernel at the faulting instruction.  On every
inert arm the trap layer never `eret`s into user: the not-ready path publishes
a fail-closed frame, and the kernel-origin path halts. -/
def faultEntryStep (lctx : LabelingContext) (st : SystemState)
    (ectx : ExceptionContext) (w : FaultRegisterWindow) (coreId : UInt64) :
    List (CoreId × SgiKind) × SystemState :=
  if h : coreId.toNat < numCores then
    if ectx.takenFromEl0 then
      match faultOfExceptionContext ectx with
      | none => ([], st)
      | some f => faultEntryDeliver lctx st f ectx w ⟨coreId.toNat, h⟩
    else ([], st)
  else
    -- An out-of-range core id cannot name a run queue, so there is no faulting
    -- thread to attribute the trap to.  Fail-closed and inert, like every
    -- other per-core entry's bound check.
    ([], st)

/-- Review round (PR #887): **the unknown-syscall step.**  The syscall
prefilter (`dispatch_svc`) rejects a syscall number outside `SyscallId`
*before* the Lean dispatcher sees it; seL4 raises `seL4_Fault_UnknownSyscall`
for exactly that case, and RR4 modelled and tested the fault without a live
producer.  This is the producer: the fault is `unknownSyscall n` with `n` the
syscall-number register (`x7`, `arm64DefaultLayout.syscallNumReg`) as the trap
frame carries it, and the delivery is the shared body — the handler receives
the thirteen-word message (`x0`-`x7`, the restart PC, `SP`, `LR`, `SPSR`, the
number) and its reply either emulates the call and continues the thread after
the `SVC` (the ELR of an `SVC` already addresses the next instruction) or
abandons it.  The same EL0 gate applies: an `SVC` issued at EL1 is a kernel
bug, not a user fault. -/
def unknownSyscallEntryStep (lctx : LabelingContext) (st : SystemState)
    (ectx : ExceptionContext) (w : FaultRegisterWindow) (coreId : UInt64) :
    List (CoreId × SgiKind) × SystemState :=
  if h : coreId.toNat < numCores then
    if ectx.takenFromEl0 then
      faultEntryDeliver lctx st (.unknownSyscall (w.gprAt 7)) ectx w ⟨coreId.toNat, h⟩
    else ([], st)
  else ([], st)

/-- **`v0.36.40`: a trap on a core another core vacated hands the core a
successor.**  The shared delivery body, on a core whose committed slot is
already `none`, commits the core's reschedule — so neither fault producer leaves
the core in the idle loop while a runnable thread waits on its queue.  No fault is delivered: the model no longer runs the thread that
trapped here, and attributing the trap to it would act on a thread another core
has already taken off this one. -/
theorem faultEntryDeliver_vacated (lctx : LabelingContext) (st st' : SystemState)
    (f : Fault) (ectx : ExceptionContext) (w : FaultRegisterWindow) (c : CoreId)
    (hVac : st.scheduler.currentOnCore c = none)
    (hR : handleRescheduleSgiOnCore st c = .ok st') :
    (faultEntryDeliver lctx st f ectx w c).2 = st' := by
  unfold faultEntryDeliver
  rw [hVac]
  exact PriorityInheritance.dispatchVacatedCore_of_vacated st st' c hVac hR

/-- WS-RR RR4.23: an out-of-range core id commits nothing — the FFI bound
check, stated so a caller cannot mistake the inert arm for a delivery. -/
theorem faultEntryStep_invalid_core (lctx : LabelingContext) (st : SystemState)
    (ectx : ExceptionContext) (w : FaultRegisterWindow)
    (coreId : UInt64) (h : ¬ coreId.toNat < numCores) :
    faultEntryStep lctx st ectx w coreId = ([], st) := by
  unfold faultEntryStep; rw [dif_neg h]

/-- Review round (PR #887): **an exception taken from EL1 is never delivered as
a user fault** — the entry is inert, and the trap layer halts.  Stated on the
step so the property is a fact about what the seam commits, not about the
Rust gate in front of it. -/
theorem faultEntryStep_kernel_origin_inert (lctx : LabelingContext) (st : SystemState)
    (ectx : ExceptionContext) (w : FaultRegisterWindow) (coreId : UInt64)
    (hEl1 : ectx.takenFromEl0 = false) :
    faultEntryStep lctx st ectx w coreId = ([], st) := by
  unfold faultEntryStep
  split
  · rw [hEl1]; rfl
  · rfl

/-- Review round (PR #887): and a kernel abort commits nothing even when the
saved PSTATE claims EL0 — the classifier refuses it on the syndrome alone. -/
theorem faultEntryStep_kernelAbort_inert (lctx : LabelingContext) (st : SystemState)
    (ectx : ExceptionContext) (w : FaultRegisterWindow) (coreId : UInt64)
    (hK : classifySynchronousException ectx = .kernelAbort) :
    faultEntryStep lctx st ectx w coreId = ([], st) := by
  unfold faultEntryStep
  rw [faultOfExceptionContext_kernelAbort ectx hK]
  split
  · split <;> rfl
  · rfl

/-- The same inertness for the unknown-syscall step: an `SVC` from EL1 is a
kernel bug, and no user thread is charged with it. -/
theorem unknownSyscallEntryStep_kernel_origin_inert (lctx : LabelingContext)
    (st : SystemState) (ectx : ExceptionContext) (w : FaultRegisterWindow)
    (coreId : UInt64) (hEl1 : ectx.takenFromEl0 = false) :
    unknownSyscallEntryStep lctx st ectx w coreId = ([], st) := by
  unfold unknownSyscallEntryStep
  split
  · rw [hEl1]; rfl
  · rfl

/-- **The frame the two fault exports deliver from, decoded once** (`v0.36.47`
audit).  The HAL hands `lean_handle_fault` and `lean_handle_unknown_syscall`
three scalars — the core, and the two syndrome words that are the trap's and
not the context's (`ESR_EL1`, `FAR_EL1`) — and every other word the delivery
needs is read from the one context the trap handler published
(`Platform.FFI.ffiTrapContext`): the frame to save into the core and the
caller's TCB, the exception context (`ELR_EL1`, `SPSR_EL1`), and the fault
window (`x0`–`x7`, `SP_EL0`, `x30`).  Before this the exports took the window
as fifteen scalars *and* re-captured the same frame — two sources for one set
of registers inside one handler.

`none` is the arm the hardware never reaches — an entry handed no context — and
it fails closed exactly as the syscall entry's `syscallEntryContextOrFaulted`
does: nothing is read, nothing is committed, no restore is staged, and the
trap layer, finding no restored frame, halts the PE.  Pure, so the host suite
runs that arm and checks the decode word for word
(`tests/FaultHandlingSuite.lean` §6g). -/
def faultEntryFrame? (esr far : UInt64) : Option Architecture.TrapContext →
    Option (SeLe4n.RegisterFile × ExceptionContext × FaultRegisterWindow)
  | none => none
  | some c =>
      some (Architecture.registerFileOfTrapContext c,
            { esr := esr, elr := c.pc, spsr := c.pstate, far := far },
            { gprs := #[c.x0, c.x1, c.x2, c.x3, c.x4, c.x5, c.x6, c.x7],
              sp := c.sp, lr := c.x30 })

/-- The decode, word for word: the saved frame is the context's register file,
the exception context carries the trap's syndrome words beside the context's
`ELR_EL1` and `SPSR_EL1`, and the window is `x0`–`x7`, `SP_EL0` and `x30`. -/
theorem faultEntryFrame?_some (esr far : UInt64) (c : Architecture.TrapContext) :
    faultEntryFrame? esr far (some c) =
      some (Architecture.registerFileOfTrapContext c,
            { esr := esr, elr := c.pc, spsr := c.pstate, far := far },
            { gprs := #[c.x0, c.x1, c.x2, c.x3, c.x4, c.x5, c.x6, c.x7],
              sp := c.sp, lr := c.x30 }) := rfl

/-- …and the arm no hardware path reaches decodes nothing, so the entries
commit nothing. -/
theorem faultEntryFrame?_none (esr far : UInt64) :
    faultEntryFrame? esr far none = none := rfl

/-- WS-RR RR4.23 (**the export**): the C-callable fault seam.

`trap.rs`'s abort and exception arms invoke this inside
`kernel_entry::with_kernel_entry`, having routed the `SVC` class away first
and halted on a kernel-origin exception.  Takes the core and the trap's two
syndrome words (`ESR_EL1`, `FAR_EL1`) — three scalars; the fault window
(`x0`-`x7`, `SP_EL0`, `x30`) and the exception context's `ELR_EL1` and
`SPSR_EL1` are decoded from the one published trap context
(`faultEntryFrame?`), read once.  Reads the deployment labeling context,
atomically commits `faultEntryStep` against the live kernel state, then fires
the cross-core SGIs the diff surfaced — the same read-context / read-frame /
commit / fire-SGIs shape `syscallDispatchCrossCoreEntry` has, and for the
same reason: the context read is a pure read of a boot-installed value, so it
need not be inside the commit closure, while the delivery must be.  An entry
handed no context commits nothing and stages no restore, on which the trap
layer halts the PE.

**WS-BP BP7.8**: and it drains the physical-write ledger the same way, read and
cleared in the atomic step and performed first.  A fault message carries up to
thirteen words, and a handler already blocked in receive is delivered them at
once, so the words past the fourth are user-word stores into its IPC buffer —
recorded by the delivery (`Architecture.stageDeliveredMessage`) and owed to RAM
by this seam. -/
@[export lean_handle_fault]
def faultEntry (coreId esr far : UInt64) : BaseIO Unit := do
  let lctx ← Platform.FFI.getKernelLabelingContext
  match faultEntryFrame? esr far (← Platform.FFI.ffiTrapContext) with
  | none => pure ()
  | some (frame, ectx, w) =>
    let r ← Platform.FFI.modifyGetKernelState (fun st0 =>
      let st := Concurrency.saveCapturedTrapFrameAt st0 coreId (some frame)
      let (sgis, st') := faultEntryStep lctx st ectx w coreId
      let st' := PriorityInheritance.settleResidencyAt st' coreId
      ((sgis,
        (Concurrency.coreIdOfUInt64? coreId).map
          (fun c => (c, st'.scheduler.currentOnCore c)),
        Concurrency.restoreTargetAt st' coreId,
        (st'.pendingPhysicalWrites, st'.pendingIcacheMaintenance)),
        Architecture.clearIcacheMaintenance (Architecture.clearPhysicalWrites st')))
    Platform.FFI.completePhysicalWrites r.2.2.2.1
    Concurrency.fireCrossCoreSgis r.1
    Platform.FFI.completeIcacheMaintenance r.2.2.2.2
    Concurrency.releaseSwitchedFpOwner coreId
    Platform.FFI.restoreTrapFrame r.2.2.1
    Concurrency.recordCommittedCurrentThreadHw r.2.1

/-- Review round (PR #887, **the export**): the C-callable unknown-syscall
seam.  `trap.rs`'s `SVC` arm invokes it — inside `with_kernel_entry`, behind
the per-core `lean_ready` gate — when `dispatch_svc` rejects the syscall
number, instead of publishing an `invalidSyscallNumber` error frame: the
thread is delivered to its fault handler as seL4's `UnknownSyscall`, or
suspended fail-closed.  Same three scalars and the same one-frame decode as
`lean_handle_fault`; the syscall number rides in the window's `x7`. -/
@[export lean_handle_unknown_syscall]
def unknownSyscallEntry (coreId esr far : UInt64) : BaseIO Unit := do
  let lctx ← Platform.FFI.getKernelLabelingContext
  match faultEntryFrame? esr far (← Platform.FFI.ffiTrapContext) with
  | none => pure ()
  | some (frame, ectx, w) =>
    let r ← Platform.FFI.modifyGetKernelState (fun st0 =>
      let st := Concurrency.saveCapturedSyscallFrameAt st0 coreId (some frame)
      let (sgis, st') := unknownSyscallEntryStep lctx st ectx w coreId
      let st' := PriorityInheritance.settleResidencyAt st' coreId
      ((sgis,
        (Concurrency.coreIdOfUInt64? coreId).map
          (fun c => (c, st'.scheduler.currentOnCore c)),
        Concurrency.restoreTargetAt st' coreId,
        (st'.pendingPhysicalWrites, st'.pendingIcacheMaintenance)),
        Architecture.clearIcacheMaintenance (Architecture.clearPhysicalWrites st')))
    Platform.FFI.completePhysicalWrites r.2.2.2.1
    Concurrency.fireCrossCoreSgis r.1
    Platform.FFI.completeIcacheMaintenance r.2.2.2.2
    Concurrency.releaseSwitchedFpOwner coreId
    Platform.FFI.restoreTrapFrame r.2.2.1
    Concurrency.recordCommittedCurrentThreadHw r.2.1

-- ============================================================================
-- §2b  WS-BP BP7.9 — the lazy FP/SIMD switch's entry
-- ============================================================================

/-- **WS-BP BP7.9**: the step the FP/SIMD access entry commits — the lazy switch
on the core the raw id names, inert for an id that names none. -/
def fpAccessEntryStep (st : SystemState) (coreId : UInt64) (live : Option FpContext) :
    Architecture.FpAccessOutcome × SystemState :=
  match Concurrency.coreIdOfUInt64? coreId with
  | none => (.inert, st)
  | some c =>
      -- `v0.36.40`: a core another core vacated has no thread to switch FP/SIMD
      -- state for, and dispatches a successor instead of resuming nothing.
      let res := Architecture.fpAccessOnCore st c live
      (res.1, PriorityInheritance.dispatchVacatedCore res.2 c)

/-- **WS-BP BP7.9**: what the HAL does with the switch's outcome — load the
answered context and lift the trap, or nothing (the restore then leaves the trap
armed). -/
def applyFpAccessOutcome : Architecture.FpAccessOutcome → BaseIO Unit
  | .load ctx => Platform.FFI.loadFpContext ctx
  | .retry => pure ()
  | .inert => pure ()

/-- **WS-BP BP7.9 (the export)**: EC `0x07` from EL0 — a thread used FP/SIMD
while its core's trap was armed.

`trap.rs` routes the `fpAccess` class here, inside `with_kernel_entry` and
behind the per-core readiness gate, having halted on an EL1-origin exception
first.  It saves the trap frame like every other entry, captures the core's
registers when they hold a recorded owner's live values, commits the lazy switch,
loads the context it answers (`.load`) and lifts the trap, and restores what the
core resumes — the faulting thread, whose `ELR_EL1` still names the FP/SIMD
instruction, so it re-executes with its own FP state.  On `.retry` nothing is
loaded and the restore leaves the trap armed, so the thread traps again until the
core holding its live values has released them.  On a core that runs a thread
nothing here schedules, so no SGI is fired and no successor is chosen
(`fpAccessEntryStep_scheduler`).

**`v0.36.40`**: on a core another core has vacated, the step dispatches a
successor (`PriorityInheritance.dispatchVacatedCore`), so the restore has
something to install; the entry then releases a switched-out FP owner and records
the committed current thread on the HAL, as every entry that can change what a
core runs does.  Both are inert on the ordinary path — the owner is the current
thread or nobody, and the recorded thread is the one already recorded. -/
@[export lean_handle_fp_access]
def fpAccessEntry (coreId : UInt64) : BaseIO Unit := do
  let frame ← Platform.FFI.captureTrapFrame
  let live ← Concurrency.captureOwnedFp coreId
  let r ← Platform.FFI.modifyGetKernelState (fun st0 =>
    let st := Concurrency.saveCapturedTrapFrameAt st0 coreId frame
    let res := fpAccessEntryStep st coreId live
    let res := (res.1, PriorityInheritance.settleResidencyAt res.2 coreId)
    ((res.1, Concurrency.restoreTargetAt res.2 coreId,
      (Concurrency.coreIdOfUInt64? coreId).map
        (fun c => (c, res.2.scheduler.currentOnCore c))), res.2))
  applyFpAccessOutcome r.1
  Concurrency.releaseSwitchedFpOwner coreId
  Platform.FFI.restoreTrapFrame r.2.1
  Concurrency.recordCommittedCurrentThreadHw r.2.2

/-- **WS-BP BP7.9** structural marker: the FP/SIMD access entry is the frame
save, the owner capture, the lazy switch, the load it answers and the restore —
pinned so a refactor that loads before committing, or restores without the
switch, fails here. -/
theorem fpAccessEntry_def (coreId : UInt64) :
    fpAccessEntry coreId =
      (do
        let frame ← Platform.FFI.captureTrapFrame
        let live ← Concurrency.captureOwnedFp coreId
        let r ← Platform.FFI.modifyGetKernelState (fun st0 =>
          let st := Concurrency.saveCapturedTrapFrameAt st0 coreId frame
          let res := fpAccessEntryStep st coreId live
          let res := (res.1, PriorityInheritance.settleResidencyAt res.2 coreId)
          ((res.1, Concurrency.restoreTargetAt res.2 coreId,
            (Concurrency.coreIdOfUInt64? coreId).map
              (fun c => (c, res.2.scheduler.currentOnCore c))), res.2))
        applyFpAccessOutcome r.1
        Concurrency.releaseSwitchedFpOwner coreId
        Platform.FFI.restoreTrapFrame r.2.1
        Concurrency.recordCommittedCurrentThreadHw r.2.2) := rfl

/-- **WS-BP BP7.9**: on a core that runs a thread, the FP/SIMD access schedules
nothing — the step commits no scheduler change, so the core resumes the thread
that trapped.  (Until `v0.36.40` this was stated for every core, and held only
because a vacated core was left resuming nothing — see the next theorem.) -/
theorem fpAccessEntryStep_scheduler (st : SystemState) (coreId : UInt64)
    (live : Option FpContext) (c : CoreId) (tid : SeLe4n.ThreadId)
    (hC : Concurrency.coreIdOfUInt64? coreId = some c)
    (hCur : st.scheduler.currentOnCore c = some tid) :
    (fpAccessEntryStep st coreId live).2.scheduler = st.scheduler := by
  unfold fpAccessEntryStep
  rw [hC]
  dsimp only
  have hS := Architecture.fpAccessOnCore_scheduler st c live
  rw [PriorityInheritance.dispatchVacatedCore_of_current _ c tid
    (by rw [hS]; exact hCur)]
  exact hS

/-- **`v0.36.40`**: on a core another core vacated, the FP/SIMD access
dispatches the core's reschedule — the committed state is the reschedule's, so
the restore installs a successor rather than nothing, and the trap layer does not
halt the core. -/
theorem fpAccessEntryStep_vacated (st st' : SystemState) (coreId : UInt64)
    (live : Option FpContext) (c : CoreId)
    (hC : Concurrency.coreIdOfUInt64? coreId = some c)
    (hVac : st.scheduler.currentOnCore c = none)
    (hR : handleRescheduleSgiOnCore st c = .ok st') :
    (fpAccessEntryStep st coreId live).2 = st' := by
  unfold fpAccessEntryStep
  rw [hC]
  dsimp only
  have hInert : Architecture.fpAccessOnCore st c live = (.inert, st) := by
    simp [Architecture.fpAccessOnCore, hVac]
  rw [hInert]
  exact PriorityInheritance.dispatchVacatedCore_of_vacated st st' c hVac hR

/-- WS-RR RR4.23 structural marker: `faultEntry` unfolds to the atomic commit
of the verified step followed by the SGI firing.

Pins the entry's body shape so a refactor that drops the state commit, drops
the SGI firing, drops the labeling-context read that makes the delivery
flow-checked, drops the **WS-RR RR7.26** HAL current-thread record, or inserts
a side effect the verified step does not describe breaks this marker at
elaboration.  Combined with the `@[export]` attribute (which the Rust
`lean_handle_fault` extern resolves against) and the `build.rs` trap-path
scanner, the seam cannot regress silently — the discipline the timer and
`.reschedule` entries already carry.

The record matters here even though the trap layer halts after a delivered
fault on a core with no restore staged: the delivery *vacates* this core, so leaving the HAL
mirror naming the faulted thread would be a stale name pointing at a
descheduled frame — exactly what RR7.26's clear-on-vacate exists to prevent.

**`v0.36.47` audit**: the marker also pins that the entry reads the frame
**once** — the window and the exception context are `faultEntryFrame?`'s
decode of the one captured context, and the `none` arm commits nothing. -/
theorem faultEntry_def (coreId esr far : UInt64) :
    faultEntry coreId esr far =
      (do
        let lctx ← Platform.FFI.getKernelLabelingContext
        match faultEntryFrame? esr far (← Platform.FFI.ffiTrapContext) with
        | none => pure ()
        | some (frame, ectx, w) =>
          let r ← Platform.FFI.modifyGetKernelState (fun st0 =>
            let st := Concurrency.saveCapturedTrapFrameAt st0 coreId (some frame)
            let (sgis, st') := faultEntryStep lctx st ectx w coreId
            let st' := PriorityInheritance.settleResidencyAt st' coreId
            ((sgis,
              (Concurrency.coreIdOfUInt64? coreId).map
                (fun c => (c, st'.scheduler.currentOnCore c)),
              Concurrency.restoreTargetAt st' coreId,
              (st'.pendingPhysicalWrites, st'.pendingIcacheMaintenance)),
              Architecture.clearIcacheMaintenance (Architecture.clearPhysicalWrites st')))
          Platform.FFI.completePhysicalWrites r.2.2.2.1
          Concurrency.fireCrossCoreSgis r.1
          Platform.FFI.completeIcacheMaintenance r.2.2.2.2
          Concurrency.releaseSwitchedFpOwner coreId
          Platform.FFI.restoreTrapFrame r.2.2.1
          Concurrency.recordCommittedCurrentThreadHw r.2.1) := rfl

/-- The same marker for the unknown-syscall seam. -/
theorem unknownSyscallEntry_def (coreId esr far : UInt64) :
    unknownSyscallEntry coreId esr far =
      (do
        let lctx ← Platform.FFI.getKernelLabelingContext
        match faultEntryFrame? esr far (← Platform.FFI.ffiTrapContext) with
        | none => pure ()
        | some (frame, ectx, w) =>
          let r ← Platform.FFI.modifyGetKernelState (fun st0 =>
            let st := Concurrency.saveCapturedSyscallFrameAt st0 coreId (some frame)
            let (sgis, st') := unknownSyscallEntryStep lctx st ectx w coreId
            let st' := PriorityInheritance.settleResidencyAt st' coreId
            ((sgis,
              (Concurrency.coreIdOfUInt64? coreId).map
                (fun c => (c, st'.scheduler.currentOnCore c)),
              Concurrency.restoreTargetAt st' coreId,
              (st'.pendingPhysicalWrites, st'.pendingIcacheMaintenance)),
              Architecture.clearIcacheMaintenance (Architecture.clearPhysicalWrites st')))
          Platform.FFI.completePhysicalWrites r.2.2.2.1
          Concurrency.fireCrossCoreSgis r.1
          Platform.FFI.completeIcacheMaintenance r.2.2.2.2
          Concurrency.releaseSwitchedFpOwner coreId
          Platform.FFI.restoreTrapFrame r.2.2.1
          Concurrency.recordCommittedCurrentThreadHw r.2.1) := rfl

/-- The shared delivery inherits the progress guarantee: whatever it commits,
the thread that was current on `c` is not dispatchable there afterwards.

**WS-BP BP7.6: the SM10.1 obligation, discharged.**  The core's successor is
dispatched now, and it is drawn from the run queue the faulting thread is no
longer on (`handleRescheduleSgiOnCore_preserves_not_dispatchable`).  That the
chooser draws from the queue's *members* is what the queue's well-formedness
says — its bucket scan and its membership agree — so the theorem takes it of
the state the successor is chosen on — and that is derived, not assumed: the
theorem takes every core's queue well-formed on the **pre**-state, which is a
conjunct of `schedulerInvariant_perCore` every reachable state carries, and
`faultDeliverOnCoreChecked_preserves_runQueuesWellFormed` carries it across the
spill and the delivery. -/
theorem faultEntryDeliver_not_dispatchable (lctx : LabelingContext) (st : SystemState)
    (f : Fault) (ectx : ExceptionContext) (w : FaultRegisterWindow) (c : CoreId)
    (tid : SeLe4n.ThreadId) (hCur : st.scheduler.currentOnCore c = some tid)
    (hwf : runQueuesWellFormed st.scheduler) :
    ¬ dispatchableOnCore (faultEntryDeliver lctx st f ectx w c).2 tid c := by
  have hwfD : (faultDeliveredState lctx st f ectx w c tid).scheduler.runQueueOnCore c
      |>.wellFormed := by
    unfold faultDeliveredState
    refine faultDeliverOnCoreChecked_preserves_runQueuesWellFormed lctx _ tid f _ c ?_ c
    rw [writeFaultRegistersToTcb_scheduler]; exact hwf
  unfold faultEntryDeliver
  simp only [hCur]
  have hD : ¬ dispatchableOnCore (faultDeliveredState lctx st f ectx w c tid) tid c :=
    faultDeliverOnCoreChecked_not_dispatchable lctx _ tid f _ c
  unfold PriorityInheritance.scheduleLocalSuccessorFrom
  split
  · split
    · rename_i stH hH
      exact handleRescheduleSgiOnCore_preserves_not_dispatchable _ stH c tid hwfD hH hD
    · exact hD
  · exact hD

/-- WS-RR RR4.23/RR4.19: **the entry inherits the progress guarantee.**

Whatever the fault entry commits, the thread that faulted on `coreId` is not
dispatchable there afterwards — the live-path statement of RR4.19, one level
up from the transition.  The inert arms (an `SVC`, a kernel abort, an
exception from EL1, a core with no current thread) change nothing, so there is
no thread they could leave runnable at a faulting instruction. -/
theorem faultEntryStep_not_dispatchable (lctx : LabelingContext) (st : SystemState)
    (ectx : ExceptionContext) (w : FaultRegisterWindow)
    (coreId : UInt64) (tid : SeLe4n.ThreadId) (h : coreId.toNat < numCores)
    (hEl0 : ectx.takenFromEl0 = true)
    (hCur : st.scheduler.currentOnCore ⟨coreId.toNat, h⟩ = some tid)
    (hFault : (faultOfExceptionContext ectx).isSome)
    (hwf : runQueuesWellFormed st.scheduler) :
    ¬ dispatchableOnCore (faultEntryStep lctx st ectx w coreId).2 tid ⟨coreId.toNat, h⟩ := by
  unfold faultEntryStep
  rw [dif_pos h, if_pos hEl0]
  cases hF : faultOfExceptionContext ectx with
  | none => rw [hF] at hFault; exact absurd hFault (by simp)
  | some f => exact faultEntryDeliver_not_dispatchable lctx st f ectx w _ tid hCur hwf

/-- Review round (PR #887): the unknown-syscall entry carries the same
guarantee — a thread that issued an unknown syscall is never resumed at it
without handler action. -/
theorem unknownSyscallEntryStep_not_dispatchable (lctx : LabelingContext)
    (st : SystemState) (ectx : ExceptionContext) (w : FaultRegisterWindow)
    (coreId : UInt64) (tid : SeLe4n.ThreadId) (h : coreId.toNat < numCores)
    (hEl0 : ectx.takenFromEl0 = true)
    (hCur : st.scheduler.currentOnCore ⟨coreId.toNat, h⟩ = some tid)
    (hwf : runQueuesWellFormed st.scheduler) :
    ¬ dispatchableOnCore (unknownSyscallEntryStep lctx st ectx w coreId).2 tid
      ⟨coreId.toNat, h⟩ := by
  unfold unknownSyscallEntryStep
  rw [dif_pos h, if_pos hEl0]
  exact faultEntryDeliver_not_dispatchable lctx st _ ectx w _ tid hCur hwf

/-- PR #887 review round 3: **the syscall seam's capability fault carries the
same guarantee.**  `deliverSyscallCapFault` is the abort entry's delivery at
the `SVC` seam — spill, context, flow-checked delivery — so whatever it
commits, the thread whose capability lookup failed is not dispatchable on the
executing core afterwards: it waits on its handler, or it took the fail-closed
suspend, and either way the `SVC` is not re-issued until a reply restarts it. -/
theorem syscallCapFault_not_dispatchable (lctx : LabelingContext) (st : SystemState)
    (tid : SeLe4n.ThreadId) (f : Fault) (w : FaultRegisterWindow) (elr spsr : UInt64)
    (c : CoreId) :
    ¬ dispatchableOnCore (Platform.FFI.deliverSyscallCapFault lctx c st tid f w elr spsr) tid c := by
  unfold Platform.FFI.deliverSyscallCapFault
  exact faultDeliverOnCoreChecked_not_dispatchable lctx _ tid f _ c

/-- PR #887 review round 3: the same statement one level up, at the typed ABI
entry the hardware calls.  When `syscallDispatchFromAbi` takes the
capability-fault arm (`syscallDispatchFromAbi_capFault_faulted`), the state it
commits leaves the caller undispatchable on the executing core — the `.faulted`
outcome the seam hands the Rust side (tag 2, on which the trap layer halts) is
backed by a thread that is in fact descheduled, never one left runnable at the
`SVC`. -/
theorem syscallDispatchFromAbi_capFault_not_dispatchable
    (ctx : LabelingContext) (executingCore : CoreId)
    (syscallId : UInt32)
    (x0 x1 x2 x3 x4 x5 ipcBufferAddr elr spsr spEl0 x30 : UInt64)
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ke : KernelError) (fault : Fault)
    (hCur : (st.scheduler.currentOnCore executingCore) = some tid)
    (hSyscall :
      syscallEntryChecked ctx SeLe4n.arm64DefaultLayout executingCore 32
          (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5)
        = Except.error ke)
    (hCap : Platform.FFI.syscallCapFaultOf SeLe4n.arm64DefaultLayout
        (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5) tid ke
        = some fault)
    (hCommit : Platform.FFI.syscallDispatchFromAbi ctx executingCore syscallId
        x0 x1 x2 x3 x4 x5 ipcBufferAddr elr spsr spEl0 x30 st = Except.ok (.faulted, st')) :
    ¬ dispatchableOnCore st' tid executingCore := by
  rw [Platform.FFI.syscallDispatchFromAbi_capFault_faulted ctx executingCore syscallId
    x0 x1 x2 x3 x4 x5 ipcBufferAddr elr spsr spEl0 x30 st tid ke fault hCur hSyscall hCap]
    at hCommit
  have hSt : st' = Platform.FFI.deliverSyscallCapFault ctx executingCore
      (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5) tid fault
      (Platform.FFI.syscallWindow syscallId x0 x1 x2 x3 x4 x5 ipcBufferAddr spEl0 x30)
      elr spsr := by
    have := Except.ok.inj hCommit
    exact (Prod.mk.inj this).2.symm
  rw [hSt]
  exact syscallCapFault_not_dispatchable ctx _ tid fault _ elr spsr executingCore

end SeLe4n.Kernel
