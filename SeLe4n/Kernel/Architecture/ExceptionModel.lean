/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.API
import SeLe4n.Kernel.Architecture.InterruptDispatch

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
DEF-R-HAL-L14) per docs/audits/AUDIT_v0.30.6_WORKSTREAM_PLAN.md §12.
-/

namespace SeLe4n.Kernel.Architecture

open SeLe4n
open SeLe4n.Model

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

/-- AG3-C: Synchronous exception class (derived from ESR_EL1 EC field). -/
inductive SynchronousExceptionClass where
  | svc             -- SVC instruction (syscall)
  | dataAbort       -- Data abort
  | instrAbort      -- Instruction abort
  | pcAlignment     -- PC alignment fault
  | spAlignment     -- SP alignment fault
  | unknownReason   -- Unclassified synchronous exception
  deriving Repr, DecidableEq

/-- AG3-C: Exception context — captures the ARM64 exception registers
    saved on exception entry. All values are `UInt64` matching the
    hardware register width. -/
structure ExceptionContext where
  /-- ESR_EL1: Exception Syndrome Register -/
  esr : UInt64
  /-- ELR_EL1: Exception Link Register (return address) -/
  elr : UInt64
  /-- SPSR_EL1: Saved Program Status Register -/
  spsr : UInt64
  /-- FAR_EL1: Fault Address Register -/
  far : UInt64
  deriving Repr, DecidableEq

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
-- AG3-C-ii: ESR classification function
-- ============================================================================

/-- AG3-C: Extract the Exception Class (EC) field from ESR_EL1.
    EC is bits [31:26] — a 6-bit field identifying the exception reason. -/
def extractExceptionClass (esr : UInt64) : UInt64 :=
  (esr >>> 26) &&& 0x3F

/-- AG3-C: Classify a synchronous exception from the ESR_EL1 EC field.
    Maps ARM64 exception class codes to our model's classification:
    - EC 0x15: SVC from AArch64 (syscall)
    - EC 0x24/0x25: Data abort (from lower/current EL)
    - EC 0x20/0x21: Instruction abort (from lower/current EL)
    - EC 0x22: PC alignment fault
    - EC 0x26: SP alignment fault
    - All others: Unknown/unmodeled -/
def classifySynchronousException (ectx : ExceptionContext) : SynchronousExceptionClass :=
  let ec := extractExceptionClass ectx.esr
  if ec = 0x15 then .svc
  else if ec = 0x24 || ec = 0x25 then .dataAbort
  else if ec = 0x20 || ec = 0x21 then .instrAbort
  else if ec = 0x22 then .pcAlignment
  else if ec = 0x26 then .spAlignment
  else .unknownReason

/-- AG3-C: Classification is total — every ESR value produces a valid class. -/
theorem classifySynchronousException_total (ectx : ExceptionContext) :
    ∃ cls, classifySynchronousException ectx = cls :=
  ⟨_, rfl⟩

-- ============================================================================
-- AG3-C-iii/iv: Exception dispatch functions
-- ============================================================================

/-- AG3-C: Dispatch a synchronous exception.
    Routes based on ESR classification:
    - SVC: Extract syscall via `syscallEntry` (the existing entry point)
    - Data/Instruction abort: VM fault error
    - Alignment faults, unknown: User exception error -/
def dispatchSynchronousException (ectx : ExceptionContext)
    (st : SystemState) : Except KernelError (Unit × SystemState) :=
  match classifySynchronousException ectx with
  | .svc => syscallEntry arm64DefaultLayout st.machine.registerCount st
  | .dataAbort => .error .vmFault
  | .instrAbort => .error .vmFault
  | .pcAlignment => .error .userException
  | .spAlignment => .error .userException
  | .unknownReason => .error .userException

/-- AG3-C/AG3-D: Top-level exception dispatch.
    Routes by exception type:
    - Synchronous: Classify and dispatch via `dispatchSynchronousException`
    - IRQ: Dispatch via `interruptDispatchSequence` (AG3-D)
    - FIQ: Not supported by seL4
    - SError: Hardware fault
    The `rawIntId` parameter is only used for IRQ exceptions (read from GICC_IAR). -/
def dispatchException (etype : ExceptionType) (ectx : ExceptionContext)
    (rawIntId : Nat := 0)
    (st : SystemState) : Except KernelError (Unit × SystemState) :=
  match etype with
  | .synchronous => dispatchSynchronousException ectx st
  | .irq => interruptDispatchSequence st rawIntId
  | .fiq => .error .notSupported
  | .serror => .error .hardwareFault

-- ============================================================================
-- AG3-C-vi: Preservation theorem
-- ============================================================================

/-- AG3-C: FIQ dispatch always returns `.notSupported`. -/
theorem dispatchException_fiq (ectx : ExceptionContext) (n : Nat) (st : SystemState) :
    dispatchException .fiq ectx n st = .error .notSupported := rfl

/-- AG3-C: SError dispatch always returns `.hardwareFault`. -/
theorem dispatchException_serror (ectx : ExceptionContext) (n : Nat) (st : SystemState) :
    dispatchException .serror ectx n st = .error .hardwareFault := rfl

/-- AG3-C: Synchronous SVC exception dispatches to `syscallEntry`. -/
theorem dispatchException_svc (ectx : ExceptionContext) (n : Nat) (st : SystemState)
    (hSvc : classifySynchronousException ectx = .svc) :
    dispatchException .synchronous ectx n st =
    syscallEntry arm64DefaultLayout st.machine.registerCount st := by
  simp [dispatchException, dispatchSynchronousException, hSvc]

/-- AG3-D: IRQ dispatch delegates to `interruptDispatchSequence`. -/
theorem dispatchException_irq (ectx : ExceptionContext) (rawIntId : Nat) (st : SystemState) :
    dispatchException .irq ectx rawIntId st =
    interruptDispatchSequence st rawIntId := rfl

/-- AG3-C: Data abort exceptions return `.vmFault`. -/
theorem dispatchSynchronousException_dataAbort (ectx : ExceptionContext)
    (st : SystemState)
    (hCls : classifySynchronousException ectx = .dataAbort) :
    dispatchSynchronousException ectx st = .error .vmFault := by
  simp [dispatchSynchronousException, hCls]

/-- AG3-C: Instruction abort exceptions return `.vmFault`. -/
theorem dispatchSynchronousException_instrAbort (ectx : ExceptionContext)
    (st : SystemState)
    (hCls : classifySynchronousException ectx = .instrAbort) :
    dispatchSynchronousException ectx st = .error .vmFault := by
  simp [dispatchSynchronousException, hCls]

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
