-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.API
import SeLe4n.Kernel.Architecture.InterruptDispatch
import SeLe4n.Kernel.Architecture.Fault
import SeLe4n.Kernel.IPC.CrossCore.Fault
import SeLe4n.Kernel.IPC.Invariant.FaultProgress

/-!
# AG3-C (FINDING-04): ARM64 Exception Model

> **STATUS: staged for H3 hardware binding** (AN7-D.6 / PLT-M07).  This
> module is wired into `SeLe4n.Platform.Staged` so every CI run verifies
> it compiles.  See `docs/spec/SELE4N_SPEC.md` §8.15 for the activation
> roadmap.

Models the ARM64 exception vector table and exception dispatch. ARM64 defines
4 exception types × 4 execution states = 16 vector entries. The kernel's
`syscallEntry` is currently a pure function call; this module wraps it in the
hardware exception dispatch path so that SVC instructions route through the
proper exception classification pipeline.

## Exception Types

- **Synchronous**: SVC (syscall), data abort, instruction abort, alignment faults
- **IRQ**: Standard interrupt request (routed to interrupt dispatch, AG3-D)
- **FIQ**: Fast interrupt request (not used by seL4, returns `.notSupported`)
- **SError**: System error / asynchronous external abort (returns `.hardwareFault`)

## ESR_EL1 Classification

The Exception Syndrome Register (ESR_EL1) encodes the exception class in
bits [31:26]. This module classifies the EC field to route synchronous
exceptions to the appropriate handler.

## AG3-F: Exception Level Model

Models ARM64 privilege levels EL0 (user) and EL1 (kernel). The exception
dispatch path sets the appropriate level on entry/exit.

## AJ-M08 / H-01: Orphaned Module Status

This module is implemented and proven but not yet imported into the main
kernel execution path. The `dispatchException` function routes SVC
instructions to `syscallEntry` (API.lean), but an import cycle prevents
direct integration (ExceptionModel imports API, which cannot import
ExceptionModel back). See §8.15.1 of SELE4N_SPEC.md for the activation
roadmap. Hardware-integration activation closed by AN9-F (SVC FFI wiring,
DEF-R-HAL-L14).
-/

namespace SeLe4n.Kernel.Architecture

open SeLe4n
open SeLe4n.Model
open SeLe4n.Kernel.Concurrency

-- ============================================================================
-- AG3-C-i: Core type definitions
-- ============================================================================

/-- AG3-C: ARM64 exception type (4 categories). -/
inductive ExceptionType where
  | synchronous
  | irq
  | fiq
  | serror
  deriving Repr, DecidableEq

/-- AG3-C: Exception source — which execution state generated the exception. -/
inductive ExceptionSource where
  | currentElSp0     -- Current EL with SP_EL0
  | currentElSpX     -- Current EL with SP_ELx
  | lowerElAArch64   -- Lower EL using AArch64
  | lowerElAArch32   -- Lower EL using AArch32
  deriving Repr, DecidableEq

-- WS-RR RR4.3: `SynchronousExceptionClass`, `ExceptionContext`,
-- `extractExceptionClass` and `classifySynchronousException` now live in
-- `SeLe4n/Kernel/Architecture/Fault.lean`, which this module imports.  They
-- moved down because the IPC fault path has to classify an exception and this
-- module sits above `Kernel.API`; both files are in
-- `SeLe4n.Kernel.Architecture`, so every existing consumer sees the names
-- unchanged.

/-! ## AK5-F.4: TrapFrame layout contract (model side)

The Rust HAL's `TrapFrame` (rust/sele4n-hal/src/trap.rs) carries a saved
snapshot of the ARM64 register state across the exception boundary. AK5-F
extended the layout from 272 to 288 bytes to include read-only snapshots of
`ESR_EL1` (offset 272) and `FAR_EL1` (offset 280) so nested exceptions can
no longer corrupt the outer handler's syndrome view.

The `trapFrameLayout` structure below is metadata only — Lean does not
execute the layout — but it documents the binary contract the Rust side
must uphold. Any future schema change to `TrapFrame` must update this
structure and the corresponding `#[repr(C, align(16))] TrapFrame` struct in
lockstep; the Rust compile-time `offset_of!` asserts in `trap.rs` provide
the machine-checked enforcement on the Rust side. -/

/-- AK5-F.4: Contract for the offsets of each logical field inside the
    Rust HAL `TrapFrame`. Units are bytes. -/
structure TrapFrameLayout where
  /-- Total size of the trap frame in bytes. -/
  size : Nat
  /-- Offset of the general-purpose register file (x0..x30). -/
  gprsOffset : Nat
  /-- Offset of the saved `SP_EL0`. -/
  sp_el0_offset : Nat
  /-- Offset of the saved `ELR_EL1`. -/
  elr_el1_offset : Nat
  /-- Offset of the saved `SPSR_EL1`. -/
  spsr_el1_offset : Nat
  /-- AK5-F: Offset of the `ESR_EL1` snapshot (NEW, was not in the layout
      before AK5-F). -/
  esr_el1_offset : Nat
  /-- AK5-F: Offset of the `FAR_EL1` snapshot (NEW, was not in the layout
      before AK5-F). -/
  far_el1_offset : Nat
  deriving Repr, DecidableEq

/-- AK5-F.4: The Rust `TrapFrame` layout contract (288-byte, 16-byte-
    aligned) the HAL upholds.

    Rust-side enforcement: `const _: () = assert!(...)` in
    `rust/sele4n-hal/src/trap.rs` checks each offset at compile time.
    Changing any offset here requires the corresponding Rust assertion
    to be updated or the build breaks. -/
def trapFrameLayout : TrapFrameLayout :=
  { size := 288
    gprsOffset := 0
    sp_el0_offset := 248
    elr_el1_offset := 256
    spsr_el1_offset := 264
    esr_el1_offset := 272
    far_el1_offset := 280 }

/-- AK5-F.4: Sanity theorem that the declared offsets are consistent with
    the total size — each field occupies the byte range up to the next
    field's offset, and the final field fits inside the total size. -/
theorem trapFrameLayout_offsets_monotone :
    trapFrameLayout.gprsOffset ≤ trapFrameLayout.sp_el0_offset ∧
    trapFrameLayout.sp_el0_offset ≤ trapFrameLayout.elr_el1_offset ∧
    trapFrameLayout.elr_el1_offset ≤ trapFrameLayout.spsr_el1_offset ∧
    trapFrameLayout.spsr_el1_offset ≤ trapFrameLayout.esr_el1_offset ∧
    trapFrameLayout.esr_el1_offset ≤ trapFrameLayout.far_el1_offset ∧
    trapFrameLayout.far_el1_offset + 8 ≤ trapFrameLayout.size := by
  decide

/-- AK5-F.4: EXACT-fit theorem — the declared offsets use the full 288
    bytes without gaps. Each header field (SP_EL0, ELR_EL1, SPSR_EL1,
    ESR_EL1, FAR_EL1) occupies 8 bytes; the GPR array occupies
    `31 × 8 = 248` bytes starting at offset 0. Any introduction of a
    hidden gap (e.g., someone re-adding `A` padding for a 16-byte-aligned
    field) would fail this theorem. -/
theorem trapFrameLayout_exact_fit :
    trapFrameLayout.gprsOffset = 0 ∧
    trapFrameLayout.sp_el0_offset = trapFrameLayout.gprsOffset + 31 * 8 ∧
    trapFrameLayout.elr_el1_offset = trapFrameLayout.sp_el0_offset + 8 ∧
    trapFrameLayout.spsr_el1_offset = trapFrameLayout.elr_el1_offset + 8 ∧
    trapFrameLayout.esr_el1_offset = trapFrameLayout.spsr_el1_offset + 8 ∧
    trapFrameLayout.far_el1_offset = trapFrameLayout.esr_el1_offset + 8 ∧
    trapFrameLayout.size = trapFrameLayout.far_el1_offset + 8 := by
  decide

/-- AK5-F.4: AK5-F extended the trap frame by exactly 16 bytes (two
    `UInt64` fields: ESR_EL1 + FAR_EL1). Historical size was 272. -/
theorem trapFrameLayout_extended_by_16 :
    trapFrameLayout.size = 272 + 16 := by decide

/-- AK5-F.4: The trap frame is 16-byte aligned (matches Rust
    `#[repr(C, align(16))]` on `TrapFrame`) — ensures stack-discipline
    compatibility with AArch64's 16-byte SP alignment requirement. -/
theorem trapFrameLayout_size_16_aligned :
    trapFrameLayout.size % 16 = 0 := by decide

-- ============================================================================
-- AG3-F (H3-ARCH-05): Exception Level Model
-- ============================================================================

/-- AG3-F: ARM64 exception level. EL2 (hypervisor) and EL3 (secure monitor)
    are out of scope for the H3 hardware binding — seL4 runs at EL1. -/
inductive ExceptionLevel where
  | el0   -- User mode
  | el1   -- Kernel mode
  deriving Repr, DecidableEq

/-- AG3-F: Determine the current exception level from SPSR.
    SPSR_EL1 bits [3:0] encode the target EL on exception return.
    EL0: M[3:0] = 0b0000, EL1: M[3:0] = 0b0100 or 0b0101. -/
def exceptionLevelFromSpsr (spsr : UInt64) : ExceptionLevel :=
  let mBits := spsr &&& 0xF
  if mBits = 0 then .el0 else .el1

/-- AG3-F: Determine exception level from exception source.
    Exceptions from lower EL (AArch64/AArch32) came from EL0 (user).
    Exceptions from current EL came from EL1 (kernel). -/
def exceptionLevelFromSource (source : ExceptionSource) : ExceptionLevel :=
  match source with
  | .lowerElAArch64 => .el0
  | .lowerElAArch32 => .el0
  | .currentElSp0   => .el1
  | .currentElSpX   => .el1

/-- AG3-F: Privilege check — system register access requires EL1. -/
def canAccessSystemRegisters (level : ExceptionLevel) : Bool :=
  match level with
  | .el1 => true
  | .el0 => false

/-- AG3-F: Privilege check — privileged instruction execution requires EL1. -/
def canExecutePrivileged (level : ExceptionLevel) : Bool :=
  match level with
  | .el1 => true
  | .el0 => false

-- ============================================================================
-- AG3-C-iii/iv: Exception dispatch functions
-- ============================================================================

/-- WS-RR RR4.21: the `KernelError` an **unattributable** fault is reported as.

A fault taken on a core with no current thread cannot be delivered — there is
no faulting thread to block and no `faultHandler` to resolve — so it is
reported to the trap layer.  Reporting the fault's own kind keeps the
diagnostic informative and keeps `KernelError.vmFault` / `.userException`
reachable: they stop being what an abort *returns to a user thread* (the
pre-RR4 defect) and become what the kernel says about a fault it could not
attribute. -/
def unhandledFaultError : Fault → KernelError
  | .vmFault _ _ _     => .vmFault
  | .capFault _ _ _    => .invalidCapability
  | .unknownSyscall _  => .invalidSyscallNumber
  | .userException _ _ => .userException

/-- AG3-C, rewired by **WS-RR RR4.21**: dispatch a synchronous exception.

* **SVC** → `syscallEntry`, the syscall path.  Unchanged.
* **Everything else** → the fault is classified out of the syndrome registers
  (`faultOfExceptionContext`) and **delivered to the faulting thread's fault
  handler** (`faultDeliverOnCore`), which blocks the thread awaiting the
  handler's reply or, fail-closed, suspends it.

This retires the pre-RR4 arms, which returned `.error .vmFault` /
`.error .userException` as *pure errors with no state change*: the faulting
thread stayed runnable, and the trap path's `eret` put it straight back on the
instruction that faulted.  A user thread touching an unmapped page wedged its
core forever.  It was not exploitable at `v0.34.3` only because nothing
booted — which is the wrong moment to discover it.

Deliberately landed **after** RR4.17–RR4.20: this is the sub-task that makes
the delivery reachable, and a live kernel transition must not land ahead of
its own invariant surface.  The preservation
(`faultDeliverOnCore_preserves_ipcInvariantFull`), progress
(`faultDeliverOnCore_not_dispatchable`) and non-interference
(`faultDeliverOnCoreChecked_*`) theorems all predate this wiring.

The result carries the optional cross-core SGI the delivery surfaced (the
handler's home core, when the handler was woken elsewhere) — the runtime fires
it after the state commit, exactly as the syscall seam does.

**Both arms here are the *unchecked* transitions, and that is not the live
contract.**  This wrapper takes no `LabelingContext`, so its SVC arm calls
`syscallEntry` and its fault arms call `faultDeliverOnCore` — internally
symmetric, and a model of the dispatch *shape* rather than of the kernel's
enforcement.  The live seams gate: the SVC path runs `syscallEntryChecked`
through `Platform.FFI.syscallDispatchFromAbi`, and the fault path runs
`faultDeliverOnCoreChecked` through `Kernel/FaultEntry.lean`, each reading the
deployment context from `Platform.FFI.getKernelLabelingContext`.  New code must
not read this module's arms as evidence that a fault is delivered without a flow
check.

**Unattributable faults.**  A core with no current thread has no user thread to
deliver to, so the fault is reported to the trap layer as an error rather than
delivered — and the error is the *fault's own kind*
(`unhandledFaultError`), not a generic `.illegalState`, so the trap layer's
diagnostic says what actually happened.  That arm is a kernel-side fault (the
core was idle, or the kernel itself faulted); there is no thread to contain, so
reporting is the fail-closed answer.  `faultOfExceptionContext` is `none` only
for the SVC class, which this match has already routed away. -/
def dispatchSynchronousException (ectx : ExceptionContext) (st : SystemState)
    (executingCore : CoreId := bootCoreId) :
    Except KernelError (Option (CoreId × SgiKind) × SystemState) :=
  match classifySynchronousException ectx with
  | .svc =>
      match syscallEntry arm64DefaultLayout st.machine.registerCount st with
      | .error e => .error e
      | .ok ((), st') => .ok (none, st')
  | .dataAbort | .instrAbort | .pcAlignment | .spAlignment | .unknownReason =>
      match faultOfExceptionContext ectx with
      | none => .error .illegalState
      | some f =>
          match st.scheduler.currentOnCore executingCore with
          | none => .error (unhandledFaultError f)
          | some tid =>
              let fctx := faultContextOfThread st tid ectx.elr ectx.spsr
              let delivered := Kernel.faultDeliverOnCore st tid f fctx executingCore
              .ok (delivered.2.sgi, delivered.1)

/-- AG3-C/AG3-D: Top-level exception dispatch.
    Routes by exception type:
    - Synchronous: Classify and dispatch via `dispatchSynchronousException`
    - IRQ: Dispatch via `interruptDispatchSequence` (AG3-D)
    - FIQ: Not supported by seL4
    - SError: Hardware fault
    The `rawIntId` parameter is only used for IRQ exceptions (read from GICC_IAR).

    WS-RR RR4.21: the result carries the synchronous path's optional cross-core
    SGI; the IRQ path surfaces none of its own here (the per-core IRQ handler
    fires its own). -/
def dispatchException (etype : ExceptionType) (ectx : ExceptionContext)
    (rawIntId : Nat := 0)
    (st : SystemState) (executingCore : CoreId := bootCoreId) :
    Except KernelError (Option (CoreId × SgiKind) × SystemState) :=
  match etype with
  | .synchronous => dispatchSynchronousException ectx st executingCore
  | .irq =>
      match interruptDispatchSequence st rawIntId with
      | .error e => .error e
      | .ok ((), st') => .ok (none, st')
  | .fiq => .error .notSupported
  | .serror => .error .hardwareFault

-- ============================================================================
-- AG3-C-vi: Preservation theorem
-- ============================================================================

/-- AG3-C: FIQ dispatch always returns `.notSupported`. -/
theorem dispatchException_fiq (ectx : ExceptionContext) (n : Nat) (st : SystemState)
    (c : CoreId) : dispatchException .fiq ectx n st c = .error .notSupported := rfl

/-- AG3-C: SError dispatch always returns `.hardwareFault`. -/
theorem dispatchException_serror (ectx : ExceptionContext) (n : Nat) (st : SystemState)
    (c : CoreId) : dispatchException .serror ectx n st c = .error .hardwareFault := rfl

/-- AG3-C: Synchronous SVC exception dispatches to `syscallEntry` — and to
nothing else: the SVC class is the one arm RR4.21 left alone, because an `SVC`
is a syscall, not a fault. -/
theorem dispatchException_svc (ectx : ExceptionContext) (n : Nat) (st : SystemState)
    (c : CoreId) (hSvc : classifySynchronousException ectx = .svc) :
    dispatchException .synchronous ectx n st c =
      (match syscallEntry arm64DefaultLayout st.machine.registerCount st with
       | .error e => .error e
       | .ok ((), st') => .ok (none, st')) := by
  simp [dispatchException, dispatchSynchronousException, hSvc]

/-- AG3-D: IRQ dispatch delegates to `interruptDispatchSequence`. -/
theorem dispatchException_irq (ectx : ExceptionContext) (rawIntId : Nat)
    (st : SystemState) (c : CoreId) :
    dispatchException .irq ectx rawIntId st c =
      (match interruptDispatchSequence st rawIntId with
       | .error e => .error e
       | .ok ((), st') => .ok (none, st')) := rfl

/-- **WS-RR RR4.21**: a data abort **delivers a VM fault**, it does not return
one.  The pre-RR4 statement of this theorem was
`… = .error .vmFault` — a pure error, no state change, and a thread left
runnable at the faulting instruction.  This is what replaces it. -/
theorem dispatchSynchronousException_dataAbort (ectx : ExceptionContext)
    (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (hCls : classifySynchronousException ectx = .dataAbort)
    (hCur : st.scheduler.currentOnCore c = some tid) :
    dispatchSynchronousException ectx st c =
      .ok ((Kernel.faultDeliverOnCore st tid (.vmFault ectx.far ectx.esr false)
              (faultContextOfThread st tid ectx.elr ectx.spsr) c).2.sgi,
           (Kernel.faultDeliverOnCore st tid (.vmFault ectx.far ectx.esr false)
              (faultContextOfThread st tid ectx.elr ectx.spsr) c).1) := by
  simp only [dispatchSynchronousException, hCls,
    faultOfExceptionContext_dataAbort ectx hCls, hCur]

/-- **WS-RR RR4.21**: an instruction abort delivers a **prefetch** VM fault —
the flag that tells the handler to map an executable page rather than a data
page. -/
theorem dispatchSynchronousException_instrAbort (ectx : ExceptionContext)
    (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (hCls : classifySynchronousException ectx = .instrAbort)
    (hCur : st.scheduler.currentOnCore c = some tid) :
    dispatchSynchronousException ectx st c =
      .ok ((Kernel.faultDeliverOnCore st tid (.vmFault ectx.far ectx.esr true)
              (faultContextOfThread st tid ectx.elr ectx.spsr) c).2.sgi,
           (Kernel.faultDeliverOnCore st tid (.vmFault ectx.far ectx.esr true)
              (faultContextOfThread st tid ectx.elr ectx.spsr) c).1) := by
  simp only [dispatchSynchronousException, hCls,
    faultOfExceptionContext_instrAbort ectx hCls, hCur]

/-- **WS-RR RR4.21**: a data abort on a core with **no current thread** is
reported as `.vmFault` rather than delivered — the arm that keeps that
`KernelError` variant reachable, now meaning "a VM fault the kernel could not
attribute to a thread" rather than "a VM fault handed back to the thread that
took it". -/
theorem dispatchSynchronousException_dataAbort_unattributable (ectx : ExceptionContext)
    (st : SystemState) (c : CoreId)
    (hCls : classifySynchronousException ectx = .dataAbort)
    (hIdle : st.scheduler.currentOnCore c = none) :
    dispatchSynchronousException ectx st c = .error .vmFault := by
  simp only [dispatchSynchronousException, hCls,
    faultOfExceptionContext_dataAbort ectx hCls, hIdle, unhandledFaultError]

/-- **WS-RR RR4.21**: and an alignment fault on an idle core is reported as
`.userException`, symmetrically. -/
theorem dispatchSynchronousException_alignment_unattributable (ectx : ExceptionContext)
    (st : SystemState) (c : CoreId)
    (hCls : classifySynchronousException ectx = .pcAlignment)
    (hIdle : st.scheduler.currentOnCore c = none) :
    dispatchSynchronousException ectx st c = .error .userException := by
  simp only [dispatchSynchronousException, faultOfExceptionContext, hCls, hIdle,
    unhandledFaultError]

/-- **WS-RR RR4.21 (the negative that matters)**: no synchronous exception
other than `SVC` leaves the state unchanged.  The pre-RR4 abort and alignment
arms did exactly that — `.error` with the pre-state intact — and the trap
layer's `eret` then returned the thread to the instruction that faulted.

Stated over the *faulting thread's dispatchability* rather than over the
result value, because that is the property the livelock needs: whatever the
delivery decided, the thread is not runnable on the core it faulted on. -/
theorem dispatchSynchronousException_nonSvc_thread_not_dispatchable
    (ectx : ExceptionContext) (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (sgi? : Option (CoreId × SgiKind)) (st' : SystemState)
    (hCls : classifySynchronousException ectx ≠ .svc)
    (hCur : st.scheduler.currentOnCore c = some tid)
    (hStep : dispatchSynchronousException ectx st c = .ok (sgi?, st')) :
    ¬ SeLe4n.Kernel.dispatchableOnCore st' tid c := by
  have hFault : (faultOfExceptionContext ectx).isSome :=
    faultOfExceptionContext_isSome_of_ne_svc ectx hCls
  unfold dispatchSynchronousException at hStep
  cases hC : classifySynchronousException ectx with
  | svc => exact absurd hC hCls
  | dataAbort | instrAbort | pcAlignment | spAlignment | unknownReason =>
      rw [hC] at hStep
      simp only at hStep
      cases hF : faultOfExceptionContext ectx with
      | none => rw [hF] at hStep; exact absurd hStep (by simp)
      | some f =>
          rw [hF, hCur] at hStep
          simp only at hStep
          have hEq : (Kernel.faultDeliverOnCore st tid f
              (faultContextOfThread st tid ectx.elr ectx.spsr) c).1 = st' :=
            (congrArg Prod.snd (Except.ok.inj hStep))
          rw [← hEq]
          exact SeLe4n.Kernel.faultDeliverOnCore_not_dispatchable st tid f _ c

-- ============================================================================
-- AG5-G: Interrupt-disabled region enforcement
-- ============================================================================

/-!
## AG5-G: Kernel Exception Entry Interrupt Semantics

On ARM64, exception entry automatically masks IRQ (PSTATE.I = 1). The kernel
runs with interrupts disabled throughout all kernel operations. This is
enforced at the hardware level:

1. **SVC (syscall)**: User → EL1 transition masks IRQ via PSTATE save/restore
2. **IRQ**: Hardware masks further IRQs on entry to the IRQ vector
3. **ERET**: Restores PSTATE.I from SPSR_EL1, re-enabling IRQ for user mode

### Operations requiring interrupts disabled

**Always disabled** (entire kernel transition is atomic w.r.t. interrupts):
- Scheduler transitions (`schedule`, `handleYield`, `timerTick`)
- PIP propagation (`propagatePriorityInheritance`, `revertPriorityInheritance`)
- Endpoint queue mutations (`endpointSendDual`, `endpointReceiveDual`)
- Donation chain operations (`applyCallDonation`, `returnDonation`)
- Notification signal/wait (`notificationSignal`, `notificationWait`)

**Can re-enable** (future, none currently):
- Long-running operations would use `withInterruptsDisabled` for critical
  sections with periodic re-enablement. No current kernel operation requires
  this pattern.

### Atomicity guarantee

The `timerTick` and `handleInterrupt` operations preserve the interrupt-disabled
invariant: if entered with `interruptsEnabled = false`, the state remains
`interruptsEnabled = false` on exit. This follows from the structure of kernel
operations, which only modify `objects`, `scheduler`, `services`, etc. —
none toggle `machine.interruptsEnabled`.
-/

/-- AG5-G: `saveOutgoingContext` preserves `interruptsEnabled`.
    Context save only modifies `objects` (writes register context to TCB). -/
theorem saveOutgoingContext_preserves_interruptsEnabled (st : SystemState) :
    (saveOutgoingContext st).machine.interruptsEnabled = st.machine.interruptsEnabled := by
  unfold saveOutgoingContext
  split
  · rfl
  · split <;> simp_all

/-- AG5-G: `restoreIncomingContext` preserves `interruptsEnabled`.
    Context restore only modifies `machine.regs`, not `machine.interruptsEnabled`. -/
theorem restoreIncomingContext_preserves_interruptsEnabled
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (restoreIncomingContext st tid).machine.interruptsEnabled =
    st.machine.interruptsEnabled := by
  unfold restoreIncomingContext
  split <;> simp_all

/-- AG5-G: `setCurrentThread` preserves `interruptsEnabled`.
    Only modifies `scheduler.current`. -/
theorem setCurrentThread_preserves_interruptsEnabled
    (tid : Option SeLe4n.ThreadId) (st : SystemState) :
    ∀ st', setCurrentThread tid st = .ok ((), st') →
    st'.machine.interruptsEnabled = st.machine.interruptsEnabled := by
  intro st' hStep
  unfold setCurrentThread at hStep
  simp at hStep; rw [← hStep]

/-- AG5-G: `interruptDispatchSequence` for spurious interrupts preserves
    interrupt-disabled state (state is unchanged). -/
theorem interruptDispatchSequence_preserves_interruptsEnabled_spurious
    (st : SystemState) (rawIntId : Nat)
    (hSpurious : rawIntId ≥ spuriousInterruptThreshold) :
    ∀ st', interruptDispatchSequence st rawIntId = .ok ((), st') →
    st'.machine.interruptsEnabled = st.machine.interruptsEnabled := by
  intro st' hStep
  rw [interruptDispatchSequence_spurious st rawIntId hSpurious] at hStep
  simp at hStep; exact hStep.symm ▸ rfl

/-- AG5-G: `chooseThread` preserves `interruptsEnabled`.
    `chooseThread` is a pure lookup — it returns the input state unchanged. -/
theorem chooseThread_preserves_interruptsEnabled (st : SystemState) :
    ∀ result st', chooseThread st = .ok (result, st') →
    st'.machine.interruptsEnabled = st.machine.interruptsEnabled := by
  intro result st' hStep
  unfold chooseThread at hStep
  split at hStep <;> simp_all

/-- AG5-G: `setCurrentThread` preserves `interruptsEnabled` (unwrapped form).
    Unlike the `Kernel`-monad form, this extracts the preservation directly. -/
private theorem setCurrentThread_preserves_ie
    (tid : Option SeLe4n.ThreadId) (st : SystemState) (st' : SystemState)
    (h : setCurrentThread tid st = .ok ((), st')) :
    st'.machine.interruptsEnabled = st.machine.interruptsEnabled := by
  unfold setCurrentThread at h; simp at h; rw [← h]

/-- AG5-G: `schedule` preserves `interruptsEnabled`.
    `schedule` composes `chooseThread` (state unchanged), `saveOutgoingContext`
    (preserves), struct updates to `scheduler` (preserves), `restoreIncomingContext`
    (preserves), and `setCurrentThread` (preserves). -/
theorem schedule_preserves_interruptsEnabled (st : SystemState) :
    ∀ st', schedule st = .ok ((), st') →
    st'.machine.interruptsEnabled = st.machine.interruptsEnabled := by
  intro st' hStep
  unfold schedule at hStep
  -- Case split on chooseThread result
  split at hStep
  · -- chooseThread error
    simp at hStep
  · -- chooseThread returned (none, st₁)
    rename_i st₁ _
    -- Path: saveOutgoingContext st₁ → setCurrentThread none
    have hIE := setCurrentThread_preserves_ie none (saveOutgoingContext st₁) st' hStep
    rw [hIE, saveOutgoingContext_preserves_interruptsEnabled]
    exact (chooseThread_preserves_interruptsEnabled st none st₁ (by assumption)).symm ▸ rfl
  · -- chooseThread returned (some tid, st₁)
    rename_i tid st₁ _
    split at hStep
    · -- TCB found
      split at hStep
      · -- Domain check passed: saveOutgoing → dequeue → restoreIncoming → setCurrentThread
        -- The state chain preserves machine.interruptsEnabled at each step
        -- since only scheduler.runQueue and objects are modified
        have hIE := setCurrentThread_preserves_ie (some tid) _ st' hStep
        rw [hIE]
        simp [restoreIncomingContext_preserves_interruptsEnabled,
              saveOutgoingContext_preserves_interruptsEnabled]
        exact (chooseThread_preserves_interruptsEnabled st (some tid) st₁ (by assumption)).symm ▸ rfl
      · simp at hStep
    · simp at hStep

/-- AG5-G: `timerTick` preserves `interruptsEnabled`.
    All three paths (no current thread, time-slice not expired, time-slice
    expired → schedule) preserve the interrupt state. -/
theorem timerTick_preserves_interruptsEnabled (st : SystemState) :
    ∀ st', timerTick st = .ok ((), st') →
    st'.machine.interruptsEnabled = st.machine.interruptsEnabled := by
  intro st' hStep
  unfold timerTick at hStep
  split at hStep
  · -- No current thread: { st with machine := tick st.machine }
    simp at hStep; rw [← hStep]; exact tick_preserves_interruptsEnabled st.machine
  · -- Current thread exists
    split at hStep
    · -- TCB found
      split at hStep
      · -- Time-slice expired → schedule on modified state
        have hSched := schedule_preserves_interruptsEnabled _ st' hStep
        simp at hSched
        rw [hSched]; exact tick_preserves_interruptsEnabled st.machine
      · -- Time-slice not expired
        simp at hStep; rw [← hStep]; exact tick_preserves_interruptsEnabled st.machine
    · simp at hStep

/-- AG5-G: `handleInterrupt` for the timer path preserves `interruptsEnabled`.
    Proven by reducing to `timerTick` via `handleInterrupt` dispatch and
    applying `timerTick_preserves_interruptsEnabled`. -/
theorem handleInterrupt_timer_preserves_interruptsEnabled (st : SystemState) :
    ∀ st', handleInterrupt st timerInterruptId = .ok ((), st') →
    st'.machine.interruptsEnabled = st.machine.interruptsEnabled := by
  intro st' hStep
  have hReduce : handleInterrupt st timerInterruptId = timerTick st := by
    unfold handleInterrupt; simp [timerInterruptId]
  rw [hReduce] at hStep
  exact timerTick_preserves_interruptsEnabled st st' hStep

-- ============================================================================
-- AN6-F (CX-M04): archInvariantBundle interruptsEnabled composition
-- ============================================================================

/-- AN6-F (CX-M04): Composition bundle packaging the eight individual
`_preserves_interruptsEnabled` theorems (AG5-G) into a single
discoverable artifact. Each field quantifies the corresponding op's
IE-preservation property under its natural signature; callers wanting
the "all-eight" bundle at once project the relevant field rather than
re-threading eight theorem applications.

Component map:

| # | Field | Underlying theorem (AG5-G) |
|---|-------|----------------------------|
| 1 | `saveOutgoing` | `saveOutgoingContext_preserves_interruptsEnabled` |
| 2 | `restoreIncoming` | `restoreIncomingContext_preserves_interruptsEnabled` |
| 3 | `setCurrent` | `setCurrentThread_preserves_interruptsEnabled` |
| 4 | `dispatchSpurious` | `interruptDispatchSequence_preserves_interruptsEnabled_spurious` |
| 5 | `chooseThread` | `chooseThread_preserves_interruptsEnabled` |
| 6 | `schedule` | `schedule_preserves_interruptsEnabled` |
| 7 | `timerTick` | `timerTick_preserves_interruptsEnabled` |
| 8 | `handleInterruptTimer` | `handleInterrupt_timer_preserves_interruptsEnabled` |

The structure is `Prop`-valued so it can be projected without
ungrouping closures in proof scripts: e.g.
`(archInvariant_interruptsEnabled_all_eight_bundle st).schedule`
gives the schedule-specific preservation statement. -/
structure InterruptsEnabledPreservationBundle (st : SystemState) : Prop where
  saveOutgoing :
    (saveOutgoingContext st).machine.interruptsEnabled = st.machine.interruptsEnabled
  restoreIncoming : ∀ (tid : SeLe4n.ThreadId),
    (restoreIncomingContext st tid).machine.interruptsEnabled =
      st.machine.interruptsEnabled
  setCurrent : ∀ (tid : Option SeLe4n.ThreadId) (st' : SystemState),
    setCurrentThread tid st = .ok ((), st') →
    st'.machine.interruptsEnabled = st.machine.interruptsEnabled
  dispatchSpurious : ∀ (rawIntId : Nat),
    rawIntId ≥ spuriousInterruptThreshold →
    ∀ (st' : SystemState),
    interruptDispatchSequence st rawIntId = .ok ((), st') →
    st'.machine.interruptsEnabled = st.machine.interruptsEnabled
  chooseThread' : ∀ (result : Option SeLe4n.ThreadId) (st' : SystemState),
    chooseThread st = .ok (result, st') →
    st'.machine.interruptsEnabled = st.machine.interruptsEnabled
  schedule' : ∀ (st' : SystemState),
    schedule st = .ok ((), st') →
    st'.machine.interruptsEnabled = st.machine.interruptsEnabled
  timerTick' : ∀ (st' : SystemState),
    timerTick st = .ok ((), st') →
    st'.machine.interruptsEnabled = st.machine.interruptsEnabled
  handleInterruptTimer : ∀ (st' : SystemState),
    handleInterrupt st timerInterruptId = .ok ((), st') →
    st'.machine.interruptsEnabled = st.machine.interruptsEnabled

/-- AN6-F (CX-M04): Composition witness — every `SystemState` inhabits the
bundle, since each field is a theorem already proven in this file. -/
theorem archInvariant_interruptsEnabled_all_eight_bundle (st : SystemState) :
    InterruptsEnabledPreservationBundle st :=
  { saveOutgoing := saveOutgoingContext_preserves_interruptsEnabled st
    restoreIncoming := restoreIncomingContext_preserves_interruptsEnabled st
    setCurrent := fun tid st' h => setCurrentThread_preserves_interruptsEnabled tid st st' h
    dispatchSpurious := interruptDispatchSequence_preserves_interruptsEnabled_spurious st
    chooseThread' := chooseThread_preserves_interruptsEnabled st
    schedule' := schedule_preserves_interruptsEnabled st
    timerTick' := timerTick_preserves_interruptsEnabled st
    handleInterruptTimer := handleInterrupt_timer_preserves_interruptsEnabled st }

end SeLe4n.Kernel.Architecture
