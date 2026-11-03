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
import SeLe4n.Kernel.IPC.CrossCore.InterruptDelivery
import SeLe4n.Kernel.Scheduler.PriorityInheritance.PerCore
import SeLe4n.Kernel.Scheduler.ActivateThread
import SeLe4n.Kernel.SyscallSchedContainment
import SeLe4n.Platform.FFI

/-!
# WS-ZA ZA6.32 — the device-interrupt kernel entry

`trap.rs::handle_irq_per_core` takes every IRQ exception; the timer PPI and
the reschedule SGI have their own entries, and every shared peripheral
interrupt (`Architecture.deviceInterruptLine`) enters here
(`@[export lean_handle_interrupt]`), after the HAL acknowledged it at the
CPU interface and wrote its end of interrupt.  The entry runs seL4's
`handleInterrupt` on the executing core (`interruptEntryStep`,
`handleInterruptOnCore`): the bound handler's notification signalled and the
line masked until the handler acknowledges it, or a line no handler is bound
to masked.  The mask reaches the distributor as the physical write the step
records (`PhysicalWrite.setInterruptMask`), performed after the commit as
every entry performs the writes its step owes.  A woken thread queued on any
core wakes that core: the raised flags are fired as every entry fires them.

## ZA3.1's form

The raw core id is decoded once and an id naming no core enters nothing.
Inside the one atomic step the entry saves the interrupted thread's frame,
runs the step through its bracket (`interruptBracket`, which is the step),
settles the core's residency and activates its thread, and reads the restore
target's parts, the current-thread code, the raised flags and the two
ledgers off the committed state as words.  What it commits is the raw-id
composition every carry is stated over (`interruptEntryCommitted_eq`).

## The footprint

`declaredLockSetForInterrupt` declares the table write lock and the run queues
of the executing core and, at a line a handler is bound to, of the cores the
signal wakes onto (`interruptRunCores`; the cores the `.notificationSignal`
syscall declares at that notification, `notificationSignalBoundWriteSet`).  The
executing core's queue is there because the entry settles the core's residency
and activates its thread after the step, as seL4's `handleInterrupt` is
followed by `schedule()` and `activateThread()` under the one kernel lock.  The
mask writes no object, run queue or replenish queue, so the signal's coverage
is the step's (`interruptEntryStep_coversWrites`), and the settle and the
activation are covered by the two locks the footprint always names
(`interruptEntryTail_coversWrites`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId LockSet LockKey BracketSpec)

/-! ### The footprint -/

/-- A footprint covering a step covers it followed by a write that keeps the
object store and the scheduler. -/
theorem footprintCoversWrites_of_frame {S : LockSet} {st mid post : SystemState}
    (h : footprintCoversWrites S st mid) (hO : post.objects = mid.objects)
    (hS : post.scheduler = mid.scheduler) : footprintCoversWrites S st post := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun hA oid hB => ?_, fun d hd => ?_, fun d hd => ?_⟩
  · rw [hO]; exact h1 hA oid hB
  · rw [hS]; exact h2 d hd
  · rw [hS]; exact h3 d hd

/-- **The run queues the interrupt entry declares**: the executing core's,
and at a line a handler is bound to the cores the signal wakes onto. -/
def interruptRunCores (st : SystemState) (c : CoreId) (line : Nat) : List CoreId :=
  c :: match st.irqHandlers[(⟨line⟩ : SeLe4n.Irq)]? with
    | some ntfn => notificationSignalBoundWriteSet st ntfn
    | none => []

/-- **The footprint the interrupt entry declares**: the table write lock and
the run queues `interruptRunCores` names; nothing for an id naming no core or
a line that is no device line, on which the step commits nothing. -/
def declaredLockSetForInterrupt (coreId intId : UInt64) : SystemState → Option LockSet :=
  fun st => (Concurrency.coreIdOfUInt64? coreId).bind fun c =>
    if Architecture.deviceInterruptLine intId.toNat then
      LockSet.ofList? (schedFootprintOfCores (interruptRunCores st c intId.toNat) [])
    else none

/-- A declared footprint is the one of the decoded core, at a device line. -/
theorem declaredLockSetForInterrupt_some {coreId intId : UInt64} {st : SystemState}
    {S : LockSet} (hS : declaredLockSetForInterrupt coreId intId st = some S) :
    ∃ c, Concurrency.coreIdOfUInt64? coreId = some c ∧
      Architecture.deviceInterruptLine intId.toNat = true ∧
      S.pairs = schedFootprintOfCores (interruptRunCores st c intId.toNat) [] := by
  unfold declaredLockSetForInterrupt at hS
  cases hc : Concurrency.coreIdOfUInt64? coreId with
  | none => rw [hc] at hS; cases hS
  | some c =>
    rw [hc] at hS
    simp only [Option.bind_some] at hS
    cases hd : Architecture.deviceInterruptLine intId.toNat with
    | false => rw [hd] at hS; cases hS
    | true =>
      rw [hd] at hS
      exact ⟨c, rfl, rfl, LockSet.ofList?_pairs hS⟩

/-- **The interrupt step's writes are inside the footprint it declares**: the
signal's own coverage (`schedLockSet_notificationSignalBoundOnCore_coversWrites`)
carried through the mask, which writes no object and no scheduler field. -/
theorem interruptEntryStep_coversWrites (coreId intId : UInt64) (st : SystemState)
    (S : LockSet) (hInv : st.objects.invExt)
    (hS : declaredLockSetForInterrupt coreId intId st = some S) :
    footprintCoversWrites S st (interruptEntryStep st coreId intId) := by
  obtain ⟨c, hc, hd, hP⟩ := declaredLockSetForInterrupt_some hS
  rw [interruptEntryStep_device st coreId intId c hc hd]
  unfold handleInterruptOnCore
  unfold interruptRunCores at hP
  cases hH : st.irqHandlers[(⟨intId.toNat⟩ : SeLe4n.Irq)]? with
  | none =>
    exact footprintCoversWrites_of_frame (footprintCoversWrites_refl S st) rfl rfl
  | some ntfn =>
    rw [hH] at hP
    exact footprintCoversWrites_of_frame
      (footprintCoversWrites_of_confined S _ [] st _ hP
        ((notificationSignalBoundOnCore_confinedToCores ntfn _ c st hInv).mono
          (fun _ h => List.mem_cons_of_mem _ h))
        (fun d _ => notificationSignalBoundOnCore_replenishQueueOnCore _ _ c st d)) rfl rfl

/-- The declared footprint names the table write lock… -/
theorem declaredLockSetForInterrupt_objStore {coreId intId : UInt64} {st : SystemState}
    {S : LockSet} (hS : declaredLockSetForInterrupt coreId intId st = some S) :
    (LockKey.objStore, Concurrency.AccessMode.write) ∈ S.pairs := by
  obtain ⟨_, _, _, hP⟩ := declaredLockSetForInterrupt_some hS
  rw [hP]; exact List.mem_cons_self

/-- …and the executing core's run queue. -/
theorem declaredLockSetForInterrupt_runQueue {coreId intId : UInt64} {st : SystemState}
    {S : LockSet} (hS : declaredLockSetForInterrupt coreId intId st = some S) (c : CoreId)
    (hc : Concurrency.coreIdOfUInt64? coreId = some c) :
    (LockKey.runQueue c, Concurrency.AccessMode.write) ∈ S.pairs := by
  obtain ⟨c', hc', _, hP⟩ := declaredLockSetForInterrupt_some hS
  rw [hc] at hc'; cases hc'
  rw [hP, mem_schedFootprintOfCores_iff]
  exact .inr (.inl ⟨c, List.mem_cons_self, rfl⟩)

/-- **The interrupt entry's bracket**: the footprint
`declaredLockSetForInterrupt` declares, the step, and its coverage as the
proof field.  Inlined, with `BracketSpec.run`, so the entry runs the step's own
application and the record is never built at runtime. -/
@[inline] def interruptBracket (coreId intId : UInt64) : BracketSpec Unit where
  declared := declaredLockSetForInterrupt coreId intId
  step := fun s => ((), interruptEntryStep s coreId intId)
  inv := fun s => s.objects.invExt
  covers := fun st S hInv hS => interruptEntryStep_coversWrites coreId intId st S hInv hS

/-- What the entry executes is the step: `rfl`, because `BracketSpec.run` is
the step. -/
theorem interruptBracket_run (coreId intId : UInt64) (st : SystemState) :
    (interruptBracket coreId intId).run st = ((), interruptEntryStep st coreId intId) := rfl

/-! ### The entry -/

/-- **WS-ZA ZA6.32: the device-interrupt kernel entry.**  The C-callable seam
(`@[export lean_handle_interrupt]`) `trap.rs::handle_irq_per_core` invokes,
inside `with_kernel_entry` and behind the per-core `lean_ready` gate, for a
shared peripheral interrupt it acknowledged.  Saves the interrupted thread's
frame, runs seL4's `handleInterrupt` on the executing core through its bracket,
settles the core's residency and activates its thread in one atomic step;
then performs the writes the step owes (the line's mask among them), fires
the raised flags, emits the instruction-cache maintenance, releases a
switched-out FP/SIMD owner, stages the restore and records the core's current
thread.  See the module docstring. -/
@[export lean_handle_interrupt]
def interruptEntry (coreId intId : UInt64) : BaseIO Unit :=
  match Concurrency.coreIdOfUInt64? coreId with
  | none => pure ()
  | some c => do
    let frame ← Platform.FFI.ffiTrapContext
    let (raised, kind, context, tableBase, asid, code, writes, icache) ←
      Platform.FFI.modifyGetKernelState (fun st0 =>
        let st := Architecture.saveCapturedTrapFrame st0 c frame
        let pending0 := reschedulePendingSnapshot st
        let mid := ((interruptBracket coreId intId).run st).2
        let pending := mid.scheduler.reschedulePending
        let post := activateThreadOnCore (PriorityInheritance.settleResidencyOnCore mid c) c
        (((pending0.raised pending).union (pending.raised post.scheduler.reschedulePending),
          Architecture.restoreCommitKindOnCore post c, Architecture.restoreContextOnCore post c,
          Architecture.restoreTableBaseOnCore post c, Architecture.restoreAsidOnCore post c,
          post.scheduler.currentCode.get c, post.drainedPhysicalWrites,
          post.pendingIcacheMaintenance),
          Architecture.clearIcacheMaintenance (Architecture.clearPhysicalWrites post)))
    Platform.FFI.completePhysicalWrites writes
    Concurrency.fireRaisedReschedules raised
    Platform.FFI.completeIcacheMaintenance icache
    Concurrency.releaseSwitchedFpOwnerOnCore c
    Platform.FFI.restoreTrapFrameParts kind context tableBase asid
    Concurrency.recordCommittedCurrentThreadHw (some (c, SeLe4n.ThreadId.ofOptCode code))

/-- Structural marker: `interruptEntry` unfolds to the atomic commit of the
saved, bracketed and activated step, then the writes, the flags, the
instruction-cache maintenance, the FP/SIMD release, the restore and the
current-thread record.  A refactor that drops the commit, the bracket, the
mask's write or the flags, or adds an effect the verified step does not
describe, breaks this marker at elaboration; with the `@[export]` attribute
(which `trap.rs`'s `lean_handle_interrupt` extern resolves against), the
`build.rs` trap-path scanner and `scripts/check_kernel_entry_exports.py`, the
seam cannot regress silently. -/
theorem interruptEntry_def (coreId intId : UInt64) :
    interruptEntry coreId intId =
      (match Concurrency.coreIdOfUInt64? coreId with
      | none => pure ()
      | some c => do
        let frame ← Platform.FFI.ffiTrapContext
        let (raised, kind, context, tableBase, asid, code, writes, icache) ←
          Platform.FFI.modifyGetKernelState (fun st0 =>
            let st := Architecture.saveCapturedTrapFrame st0 c frame
            let pending0 := reschedulePendingSnapshot st
            let mid := ((interruptBracket coreId intId).run st).2
            let pending := mid.scheduler.reschedulePending
            let post := activateThreadOnCore (PriorityInheritance.settleResidencyOnCore mid c) c
            (((pending0.raised pending).union (pending.raised post.scheduler.reschedulePending),
              Architecture.restoreCommitKindOnCore post c, Architecture.restoreContextOnCore post c,
              Architecture.restoreTableBaseOnCore post c, Architecture.restoreAsidOnCore post c,
              post.scheduler.currentCode.get c, post.drainedPhysicalWrites,
              post.pendingIcacheMaintenance),
              Architecture.clearIcacheMaintenance (Architecture.clearPhysicalWrites post)))
        Platform.FFI.completePhysicalWrites writes
        Concurrency.fireRaisedReschedules raised
        Platform.FFI.completeIcacheMaintenance icache
        Concurrency.releaseSwitchedFpOwnerOnCore c
        Platform.FFI.restoreTrapFrameParts kind context tableBase asid
        Concurrency.recordCommittedCurrentThreadHw (some (c, SeLe4n.ThreadId.ofOptCode code))) :=
  rfl

/-- **The state the interrupt entry writes back is the one its carries are
stated over.**  On the core the id names, the entry's per-core save, step,
settle and activation are the raw-id composition every carry of the entry is
stated over (`interruptEntryState_runQueueEntryStage` and its siblings), so
each carry holds of what the entry commits. -/
theorem interruptEntryCommitted_eq (st0 : SystemState) (coreId intId : UInt64) (c : CoreId)
    (frame : Option Architecture.InFlightContext)
    (hc : Concurrency.coreIdOfUInt64? coreId = some c) :
    Architecture.clearIcacheMaintenance (Architecture.clearPhysicalWrites
      (activateThreadOnCore (PriorityInheritance.settleResidencyOnCore
        ((interruptBracket coreId intId).run (Architecture.saveCapturedTrapFrame st0 c frame)).2
          c) c)) =
    Architecture.clearIcacheMaintenance (Architecture.clearPhysicalWrites
      (activateThreadAt (PriorityInheritance.settleResidencyAt
        (interruptEntryStep (Concurrency.saveCapturedTrapFrameAt st0 coreId frame) coreId intId)
          coreId) coreId)) := by
  simp only [interruptBracket_run, Concurrency.saveCapturedTrapFrameAt,
    PriorityInheritance.settleResidencyAt, activateThreadAt, hc]

end SeLe4n.Kernel
