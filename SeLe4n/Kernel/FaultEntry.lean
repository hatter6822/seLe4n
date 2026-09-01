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

## Two exports, one classifier

* `lean_classify_synchronous_exception` (RR4.25) answers "what kind of
  synchronous exception is this?" from `ESR_EL1` alone.  `trap.rs` calls it on
  the hardware target instead of running its own `esr_ec` match, so the two
  classifications cannot diverge: there is only one.
* `lean_handle_fault` (RR4.23) is the delivery: it classifies, builds the
  fault, and runs `faultDeliverOnCore` against the live kernel state, firing
  the cross-core SGI the delivery surfaced.

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

/-- WS-RR RR4.25: the tags are pairwise distinct, so the Rust router's match
on them is a total, unambiguous decoding of the Lean classification. -/
theorem syncExceptionClassTag_injective (a b : SynchronousExceptionClass)
    (h : syncExceptionClassTag a = syncExceptionClassTag b) : a = b := by
  cases a <;> cases b <;> first | rfl | (exact absurd h (by decide))

/-- WS-RR RR4.25 (**the export**): classify an `ESR_EL1` value.

The Rust trap handler calls this on the hardware target rather than running
its own `esr_ec` match, so `trap.rs` has one classification path, not two.
Pure: it reads no kernel state and commits none, so it needs no entry lock —
`trap.rs` calls it *before* taking one, to decide where to route. -/
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

/-- WS-RR RR4 (audit round): spill the trap frame's fault window into the
faulting thread's saved register context — the fault seam's twin of the SVC
seam's `Platform.FFI.writeFfiRegistersToTcb`.

`TCB.registerContext` is a partial mirror of the hardware file and, between
syscalls, holds the *last syscall's* arguments; the fault context has to be
built from what the thread held **at the trap**, because the unknown-syscall
message reports that window and a resume reinstalls it
(`applyFaultRestart`).  Total: a target that is not a TCB returns the state
unchanged, and the delivery then fails closed on its own lookup. -/
def writeFaultRegistersToTcb (st : SystemState) (tid : SeLe4n.ThreadId)
    (w : FaultRegisterWindow) : SystemState :=
  match st.getTcb? tid with
  | some tcb =>
      let tcb' : TCB := { tcb with registerContext := w.spill tcb.registerContext }
      { st with objects := st.objects.insert tid.toObjId (.tcb tcb') }
  | none => st

/-- The spill touches no scheduler state — it is a register write, and the
delivery it precedes is what deschedules the thread. -/
@[simp] theorem writeFaultRegistersToTcb_scheduler (st : SystemState)
    (tid : SeLe4n.ThreadId) (w : FaultRegisterWindow) :
    (writeFaultRegistersToTcb st tid w).scheduler = st.scheduler := by
  unfold writeFaultRegistersToTcb; cases st.getTcb? tid <;> rfl

/-- A target that is not a TCB is left alone. -/
theorem writeFaultRegistersToTcb_id_when_not_tcb (st : SystemState)
    (tid : SeLe4n.ThreadId) (w : FaultRegisterWindow) (hNone : st.getTcb? tid = none) :
    writeFaultRegistersToTcb st tid w = st := by
  unfold writeFaultRegistersToTcb; simp [hNone]

/-- The spilled thread's saved context is the spill of what it was. -/
theorem writeFaultRegistersToTcb_getTcb? (st : SystemState) (tid : SeLe4n.ThreadId)
    (w : FaultRegisterWindow) (tcb : TCB) (hTcb : st.getTcb? tid = some tcb)
    (hObjInv : st.objects.invExt) :
    (writeFaultRegistersToTcb st tid w).getTcb? tid
      = some { tcb with registerContext := w.spill tcb.registerContext } := by
  unfold writeFaultRegistersToTcb
  rw [hTcb]
  simp only
  unfold SystemState.getTcb?
  rw [RHTable_getElem?_eq_get?,
      SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_self st.objects tid.toObjId
        (KernelObject.tcb { tcb with registerContext := w.spill tcb.registerContext }) hObjInv]

/-- **The fault context the entry delivers is the trap frame's**, word for
word: `sp` and `lr` are the saved `SP_EL0` and `x30`, and `x0`-`x7` are the
saved argument window — never the mirror's stale contents.  Composed from the
spill and `FaultRegisterWindow.ofRegisterFile_spill`; this is the theorem the
audit-round fix exists to make true. -/
theorem faultContextOfThread_writeFaultRegistersToTcb (st : SystemState)
    (tid : SeLe4n.ThreadId) (w : FaultRegisterWindow) (tcb : TCB)
    (hTcb : st.getTcb? tid = some tcb) (hObjInv : st.objects.invExt)
    (faultIP spsr : UInt64) :
    faultContextOfThread (writeFaultRegistersToTcb st tid w) tid faultIP spsr =
      { faultIP := faultIP, sp := w.sp, lr := w.lr, spsr := spsr,
        gprs := (Array.range FaultContext.gprWindow).map w.gprAt } := by
  unfold faultContextOfThread
  rw [writeFaultRegistersToTcb_getTcb? st tid w tcb hTcb hObjInv]
  exact FaultRegisterWindow.ofRegisterFile_spill w tcb.registerContext faultIP spsr

/-- WS-RR RR4.23: the verified step the fault entry commits — spill the trap
frame's window, classify, build the fault context from the spilled registers,
deliver, and derive the cross-core pokes from the state diff.

Separated from the `BaseIO` entry so the whole decision is a pure function of
the pre-state, the syndrome and the register window, and so the tests
exercise exactly what the seam runs.  Returns the SGI list the entry fires
after the commit, in the shape `fireCrossCoreSgis` consumes.

An `SVC` never reaches here (`trap.rs` routes it to the syscall dispatcher),
and if one did, `faultOfExceptionContext` yields `none` and this is the
identity — the fail-closed answer for a class this entry does not own.

**The delivery is the flow-checked one** (`faultDeliverOnCoreChecked`), not the
bare transition.  The live syscall seam gates every endpoint operation through
`syscallEntryChecked`, and a fault message is an endpoint operation the kernel
performs on a thread's behalf: leaving this entry ungated would let the kernel
carry a faulting thread's fault address, syndrome and register window into a
handler's domain across a boundary the deployment policy forbids — the one
flow no syscall can make.  Because a denied flow takes the RR4.9 suspend
rather than an error, the gate costs the progress guarantee nothing
(`faultDeliverOnCoreChecked_not_dispatchable`).

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
def faultEntryStep (lctx : LabelingContext) (st : SystemState)
    (ectx : ExceptionContext) (w : FaultRegisterWindow) (coreId : UInt64) :
    List (CoreId × SgiKind) × SystemState :=
  if h : coreId.toNat < numCores then
    let c : CoreId := ⟨coreId.toNat, h⟩
    match faultOfExceptionContext ectx with
    | none => ([], st)
    | some f =>
        match st.scheduler.currentOnCore c with
        | none => ([], st)
        | some tid =>
            let stRegs := writeFaultRegistersToTcb st tid w
            let fctx := faultContextOfThread stRegs tid ectx.elr ectx.spsr
            let st' := (faultDeliverOnCoreChecked lctx stRegs tid f fctx c).1
            let st'' := PriorityInheritance.scheduleLocalSuccessorLive st st' c
            (PriorityInheritance.computeCrossCoreSgis st st'' c, st'')
  else
    -- An out-of-range core id cannot name a run queue, so there is no faulting
    -- thread to attribute the trap to.  Fail-closed and inert, like every
    -- other per-core entry's bound check.
    ([], st)

/-- WS-RR RR4.23: an out-of-range core id commits nothing — the FFI bound
check, stated so a caller cannot mistake the inert arm for a delivery. -/
theorem faultEntryStep_invalid_core (lctx : LabelingContext) (st : SystemState)
    (ectx : ExceptionContext) (w : FaultRegisterWindow)
    (coreId : UInt64) (h : ¬ coreId.toNat < numCores) :
    faultEntryStep lctx st ectx w coreId = ([], st) := by
  unfold faultEntryStep; rw [dif_neg h]

/-- WS-RR RR4.23 (**the export**): the C-callable fault seam.

`trap.rs`'s abort and exception arms invoke this inside
`kernel_entry::with_kernel_entry`, having routed the `SVC` class away first.
The fifteen words are the syndrome (`ESR_EL1`, `ELR_EL1`, `SPSR_EL1`,
`FAR_EL1`) and the fault window the trap frame saved (`x0`-`x7`, `SP_EL0`,
`x30`) — the registers seL4's `setMRs_fault` reads and `handleFaultReply`
writes.  Reads the deployment labeling context, atomically commits
`faultEntryStep` against the live kernel state, then fires the cross-core SGIs
the diff surfaced — the same read-context / commit / fire-SGIs shape
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

/-- WS-RR RR4.23 structural marker: `faultEntry` unfolds to the atomic commit
of the verified step followed by the SGI firing.

Pins the entry's body shape so a refactor that drops the state commit, drops
the SGI firing, drops the labeling-context read that makes the delivery
flow-checked, drops a word of the register window, or inserts a side effect
the verified step does not describe breaks this marker at elaboration.
Combined with the `@[export]` attribute (which the Rust `lean_handle_fault`
extern resolves against) and the `build.rs` trap-path scanner, the seam cannot
regress silently — the discipline the timer and `.reschedule` entries already
carry. -/
theorem faultEntry_def (coreId : UInt64) (esr elr spsr far : UInt64)
    (x0 x1 x2 x3 x4 x5 x6 x7 : UInt64) (sp lr : UInt64) :
    faultEntry coreId esr elr spsr far x0 x1 x2 x3 x4 x5 x6 x7 sp lr =
      (do
        let lctx ← Platform.FFI.getKernelLabelingContext
        let sgis ← Platform.FFI.modifyGetKernelState (fun st =>
          faultEntryStep lctx st { esr := esr, elr := elr, spsr := spsr, far := far }
            { gprs := #[x0, x1, x2, x3, x4, x5, x6, x7], sp := sp, lr := lr } coreId)
        Concurrency.fireCrossCoreSgis sgis) := rfl

/-- WS-RR RR4.23/RR4.19: **the entry inherits the progress guarantee.**

Whatever the fault entry commits, the thread that faulted on `coreId` is not
dispatchable there afterwards — the live-path statement of RR4.19, one level
up from the transition.  The two identity arms (an `SVC` that should never
arrive, and a core with no current thread) change nothing, so there is no
thread they could leave runnable at a faulting instruction.  The register
spill precedes the delivery and touches no scheduler state, so the
transition-level theorem applies to the spilled state verbatim.

The successor gate is discharged by its inertness
(`scheduleLocalSuccessorLive_inert`): today the entry dispatches no successor,
so the committed state is the delivery's.  When SM10.1 flips
`contextRestoreSeamLive` this proof must instead compose the selection
soundness of `scheduleLocalSuccessor` — a successor is drawn from the core's
run queue, which the faulting thread is not on — the same obligation the
syscall seam's `vacatedCore_next_syscall_rejected` carries. -/
theorem faultEntryStep_not_dispatchable (lctx : LabelingContext) (st : SystemState)
    (ectx : ExceptionContext) (w : FaultRegisterWindow)
    (coreId : UInt64) (tid : SeLe4n.ThreadId) (h : coreId.toNat < numCores)
    (hCur : st.scheduler.currentOnCore ⟨coreId.toNat, h⟩ = some tid)
    (hFault : (faultOfExceptionContext ectx).isSome) :
    ¬ dispatchableOnCore (faultEntryStep lctx st ectx w coreId).2 tid ⟨coreId.toNat, h⟩ := by
  unfold faultEntryStep
  rw [dif_pos h]
  cases hF : faultOfExceptionContext ectx with
  | none => rw [hF] at hFault; exact absurd hFault (by simp)
  | some f =>
      simp only [hCur, PriorityInheritance.scheduleLocalSuccessorLive_inert]
      exact faultDeliverOnCoreChecked_not_dispatchable lctx _ tid f _ _

end SeLe4n.Kernel
