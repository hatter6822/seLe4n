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
timer tick and the `.reschedule` receiver.  Until SM10.1 flips it, an abort on
hardware takes the Rust-only half: a label-encoded error frame
(RR4.22) rather than a delivered fault.  New code must not assume this seam
executes on hardware merely because it is wired.
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

`trap.rs` mirrors these five values (`sync_class` in that module) and nothing
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
is not yet initialized (PR #887 review round 2). -/
@[export lean_classify_synchronous_exception]
def classifySynchronousExceptionExport (esr : UInt64) : UInt32 :=
  syncExceptionClassTag (classifySynchronousException { esr := esr, elr := 0, spsr := 0, far := 0 })

/-- WS-RR RR4.25: the export is the classification, tagged — the structural
marker that a refactor cannot quietly replace the body with a second table. -/
theorem classifySynchronousExceptionExport_def (esr : UInt64) :
    classifySynchronousExceptionExport esr =
      syncExceptionClassTag
        (classifySynchronousException { esr := esr, elr := 0, spsr := 0, far := 0 }) := rfl

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

**The SGIs are derived from the diff, not read off the delivery.**  The Call
chain surfaces at most one poke — the woken handler's home core — but the
delivery can change more than one core's view: the priority-inheritance walk
re-buckets a handler already queued elsewhere, and a passive handler's
donation moves a replenishment queue.  `PriorityInheritance.computeCrossCoreSgis`
recovers every such change from the pre/post states, exactly as
`syscallDispatchCrossCoreEntry` does for the `.call` arm this delivery
composes; reading only the surfaced poke would leave a re-bucketed remote core
running the wrong thread until something else woke it.

**The executing core's successor** goes through the same gate as every other
state-committing entry (`scheduleLocalSuccessorLive`, inert until SM10.1
flips `contextRestoreSeamLive`): the delivery vacates this core, and when the
context restore can install a successor the entry dispatches one in the same
atomic step, with the SGI diff taken against the *final* state. -/
def faultEntryDeliver (lctx : LabelingContext) (st : SystemState) (f : Fault)
    (ectx : ExceptionContext) (w : FaultRegisterWindow) (c : CoreId) :
    List (CoreId × SgiKind) × SystemState :=
  match st.scheduler.currentOnCore c with
  | none => ([], st)
  | some tid =>
      let stRegs := writeFaultRegistersToTcb st tid w
      let fctx := faultContextOfThread stRegs tid ectx.elr ectx.spsr
      let st' := (faultDeliverOnCoreChecked lctx stRegs tid f fctx c).1
      let st'' := PriorityInheritance.scheduleLocalSuccessorLive st st' c
      (PriorityInheritance.computeCrossCoreSgis st st'' c, st'')

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

/-- WS-RR RR4.23 (**the export**): the C-callable fault seam.

`trap.rs`'s abort and exception arms invoke this inside
`kernel_entry::with_kernel_entry`, having routed the `SVC` class away first
and halted on a kernel-origin exception.  Takes the syndrome and the trap
frame's fault window — `x0`-`x7`, `SP_EL0`, `x30` — fifteen words in all.
Reads the deployment labeling context, atomically commits `faultEntryStep`
against the live kernel state, then fires the cross-core SGIs the diff
surfaced — the same read-context / commit / fire-SGIs shape
`syscallDispatchCrossCoreEntry` has, and for the same reason: the context read
is a pure read of a boot-installed value, so it need not be inside the commit
closure, while the delivery must be. -/
@[export lean_handle_fault]
def faultEntry (coreId : UInt64) (esr elr spsr far : UInt64)
    (x0 x1 x2 x3 x4 x5 x6 x7 : UInt64) (sp lr : UInt64) : BaseIO Unit := do
  let lctx ← Platform.FFI.getKernelLabelingContext
  let sgis ← Platform.FFI.modifyGetKernelState (fun st =>
    faultEntryStep lctx st { esr := esr, elr := elr, spsr := spsr, far := far }
      { gprs := #[x0, x1, x2, x3, x4, x5, x6, x7], sp := sp, lr := lr } coreId)
  Concurrency.fireCrossCoreSgis sgis

/-- Review round (PR #887, **the export**): the C-callable unknown-syscall
seam.  `trap.rs`'s `SVC` arm invokes it — inside `with_kernel_entry`, behind
the per-core `lean_ready` gate — when `dispatch_svc` rejects the syscall
number, instead of publishing an `invalidSyscallNumber` error frame: the
thread is delivered to its fault handler as seL4's `UnknownSyscall`, or
suspended fail-closed.  Same fifteen words as `lean_handle_fault`; the
syscall number rides in the window's `x7`. -/
@[export lean_handle_unknown_syscall]
def unknownSyscallEntry (coreId : UInt64) (esr elr spsr far : UInt64)
    (x0 x1 x2 x3 x4 x5 x6 x7 : UInt64) (sp lr : UInt64) : BaseIO Unit := do
  let lctx ← Platform.FFI.getKernelLabelingContext
  let sgis ← Platform.FFI.modifyGetKernelState (fun st =>
    unknownSyscallEntryStep lctx st { esr := esr, elr := elr, spsr := spsr, far := far }
      { gprs := #[x0, x1, x2, x3, x4, x5, x6, x7], sp := sp, lr := lr } coreId)
  Concurrency.fireCrossCoreSgis sgis

/-- WS-RR RR4.23 structural marker: `faultEntry` unfolds to the atomic commit
of the verified step followed by the SGI firing.

Pins the entry's body shape so a refactor that drops the state commit, drops
the SGI firing, drops the labeling-context read that makes the delivery
flow-checked, or inserts a side effect the verified step does not describe
breaks this marker at elaboration.  Combined with the `@[export]` attribute
(which the Rust `lean_handle_fault` extern resolves against) and the `build.rs`
trap-path scanner, the seam cannot regress silently — the discipline the timer
and `.reschedule` entries already carry. -/
theorem faultEntry_def (coreId : UInt64) (esr elr spsr far : UInt64)
    (x0 x1 x2 x3 x4 x5 x6 x7 : UInt64) (sp lr : UInt64) :
    faultEntry coreId esr elr spsr far x0 x1 x2 x3 x4 x5 x6 x7 sp lr =
      (do
        let lctx ← Platform.FFI.getKernelLabelingContext
        let sgis ← Platform.FFI.modifyGetKernelState (fun st =>
          faultEntryStep lctx st { esr := esr, elr := elr, spsr := spsr, far := far }
            { gprs := #[x0, x1, x2, x3, x4, x5, x6, x7], sp := sp, lr := lr } coreId)
        Concurrency.fireCrossCoreSgis sgis) := rfl

/-- The same marker for the unknown-syscall seam. -/
theorem unknownSyscallEntry_def (coreId : UInt64) (esr elr spsr far : UInt64)
    (x0 x1 x2 x3 x4 x5 x6 x7 : UInt64) (sp lr : UInt64) :
    unknownSyscallEntry coreId esr elr spsr far x0 x1 x2 x3 x4 x5 x6 x7 sp lr =
      (do
        let lctx ← Platform.FFI.getKernelLabelingContext
        let sgis ← Platform.FFI.modifyGetKernelState (fun st =>
          unknownSyscallEntryStep lctx st { esr := esr, elr := elr, spsr := spsr, far := far }
            { gprs := #[x0, x1, x2, x3, x4, x5, x6, x7], sp := sp, lr := lr } coreId)
        Concurrency.fireCrossCoreSgis sgis) := rfl

/-- The shared delivery inherits the progress guarantee: whatever it commits,
the thread that was current on `c` is not dispatchable there afterwards.
`scheduleLocalSuccessorLive` is the identity until SM10.1 flips the restore
seam (`scheduleLocalSuccessorLive_inert`); when it does, the successor it
installs is drawn from the run queue the faulting thread is no longer on, and
this proof is the SM10.1 obligation that records that. -/
theorem faultEntryDeliver_not_dispatchable (lctx : LabelingContext) (st : SystemState)
    (f : Fault) (ectx : ExceptionContext) (w : FaultRegisterWindow) (c : CoreId)
    (tid : SeLe4n.ThreadId) (hCur : st.scheduler.currentOnCore c = some tid) :
    ¬ dispatchableOnCore (faultEntryDeliver lctx st f ectx w c).2 tid c := by
  unfold faultEntryDeliver
  simp only [hCur, PriorityInheritance.scheduleLocalSuccessorLive_inert]
  exact faultDeliverOnCoreChecked_not_dispatchable lctx _ tid f _ c

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
    (hFault : (faultOfExceptionContext ectx).isSome) :
    ¬ dispatchableOnCore (faultEntryStep lctx st ectx w coreId).2 tid ⟨coreId.toNat, h⟩ := by
  unfold faultEntryStep
  rw [dif_pos h, if_pos hEl0]
  cases hF : faultOfExceptionContext ectx with
  | none => rw [hF] at hFault; exact absurd hFault (by simp)
  | some f => exact faultEntryDeliver_not_dispatchable lctx st f ectx w _ tid hCur

/-- Review round (PR #887): the unknown-syscall entry carries the same
guarantee — a thread that issued an unknown syscall is never resumed at it
without handler action. -/
theorem unknownSyscallEntryStep_not_dispatchable (lctx : LabelingContext)
    (st : SystemState) (ectx : ExceptionContext) (w : FaultRegisterWindow)
    (coreId : UInt64) (tid : SeLe4n.ThreadId) (h : coreId.toNat < numCores)
    (hEl0 : ectx.takenFromEl0 = true)
    (hCur : st.scheduler.currentOnCore ⟨coreId.toNat, h⟩ = some tid) :
    ¬ dispatchableOnCore (unknownSyscallEntryStep lctx st ectx w coreId).2 tid
      ⟨coreId.toNat, h⟩ := by
  unfold unknownSyscallEntryStep
  rw [dif_pos h, if_pos hEl0]
  exact faultEntryDeliver_not_dispatchable lctx st _ ectx w _ tid hCur

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
    (syscallId : UInt32) (msgInfo : UInt64)
    (x0 x1 x2 x3 x4 x5 ipcBufferAddr elr spsr spEl0 x30 : UInt64)
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ke : KernelError) (fault : Fault)
    (hMsg : msgInfo = x1)
    (hCur : (st.scheduler.currentOnCore executingCore) = some tid)
    (hSyscall :
      syscallEntryChecked ctx SeLe4n.arm64DefaultLayout executingCore 32
          (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5)
        = Except.error ke)
    (hCap : Platform.FFI.syscallCapFaultOf SeLe4n.arm64DefaultLayout
        (Platform.FFI.writeFfiRegistersToTcb st tid syscallId x0 x1 x2 x3 x4 x5) tid ke
        = some fault)
    (hCommit : Platform.FFI.syscallDispatchFromAbi ctx executingCore syscallId msgInfo
        x0 x1 x2 x3 x4 x5 ipcBufferAddr elr spsr spEl0 x30 st = Except.ok (.faulted, st')) :
    ¬ dispatchableOnCore st' tid executingCore := by
  rw [Platform.FFI.syscallDispatchFromAbi_capFault_faulted ctx executingCore syscallId msgInfo
    x0 x1 x2 x3 x4 x5 ipcBufferAddr elr spsr spEl0 x30 st tid ke fault hMsg hCur hSyscall hCap]
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
