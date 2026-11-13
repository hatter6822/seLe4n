-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.API
import SeLe4n.Kernel.IPC.Operations
import SeLe4n.Kernel.IPC.CrossCore.InterruptDelivery

/-!
# AG3-D (FINDING-06): Interrupt Dispatch Model

Models the ARM64 interrupt dispatch path: acknowledge → dispatch → EOI.
Integrates with the GIC-400 interrupt controller on Raspberry Pi 5.

## Interrupt Flow

1. **Acknowledge**: Read GICC_IAR to get the interrupt ID (INTID)
2. **Dispatch**: Route to handler based on INTID, on the executing core
   - Timer interrupt (PPI 30) → `timerTickOnCore`
   - Any other line → `handleInterruptOnCore` (the bound handler's
     notification signalled and the line masked; an unbound line masked)
3. **End-of-Interrupt**: Write GICC_EOIR to signal completion

## GIC-400 Interrupt ID Space

- INTIDs 0–15: SGIs (Software Generated Interrupts)
- INTIDs 16–31: PPIs (Private Peripheral Interrupts)
- INTIDs 32–319: SPIs (Shared Peripheral Interrupts; BCM2712 wires 288)
- INTIDs 1020–1023: Special (spurious)
-/

namespace SeLe4n.Kernel.Architecture

open SeLe4n
open SeLe4n.Model
open SeLe4n.Kernel

-- ============================================================================
-- AG3-D-i: Types and constants
-- ============================================================================

/-- AG3-D: GIC-400 interrupt ID for RPi5 (BCM2712).
    Bounded to 320 INTIDs (0–319): SGIs (0–15), PPIs (16–31), SPIs (32–319).
    This bound is the BCM2712's distributor configuration: 288 SPIs, the
    highest wired one being UARTA at SPI 276 (INTID 308) in Linux's
    `bcm2712.dtsi` (`SeLe4n.Platform.RPi5.gicSpiCount`; the RPi5 contract's
    `irqLineSupported` admits exactly `Fin (gicSpiCount + 32)`, which
    `tests/InterruptDispatchSuite.lean` holds equal to this type).  QEMU
    `virt`'s 256 SPIs (INTIDs 32–287) fit inside it.  The GIC-400
    architecture admits up to 480 SPIs; a future multi-platform build would
    parameterize this bound. -/
abbrev InterruptId := Fin 320

/-- AG3-D: Non-secure physical timer PPI (INTID 30). -/
def timerInterruptId : InterruptId := ⟨30, by omega⟩

/-- AG3-D: Spurious interrupt threshold. INTIDs ≥ 1020 are spurious
    (returned by GICC_IAR when no pending interrupt exists). -/
def spuriousInterruptThreshold : Nat := 1020

-- ============================================================================
-- AG3-D-ii: Acknowledge and EOI operations
-- ============================================================================

/-- AK3-C (A-H02 / HIGH): Distinguish failure modes in `acknowledgeInterrupt`.

    Prior to AK3-C, `acknowledgeInterrupt` returned `Option` which lost the
    distinction between:
    - **Spurious** (INTID ≥ 1020 per GIC-400 spec) — NO EOI per spec; writing
      EOIR for a spurious INTID is harmless but unnecessary.
    - **OutOfRange** (INTID ∈ [320, 1020)) — legal INTID space on the GIC but
      unsupported on RPi5's BCM2712 (only 320 INTIDs). Hardware errata or
      SMP races can deliver such IAR values. **Must still EOI** to complete
      the interrupt cycle and avoid GIC lockup.
    - **Erratum** (valid INTID but handler fails) — see `interruptDispatchSequence`.

    This distinction is what enables the AK3-C safety property: EOI is
    always emitted unless the interrupt was spurious. -/
inductive AckError where
  | spurious                       -- INTID ≥ 1020 — skip EOI per GIC spec
  | outOfRange (rawIntId : Nat)    -- INTID ∈ [320, 1020) — emit EOI, no dispatch
  deriving Repr, DecidableEq

/-- AK3-C (A-H02 / HIGH): Acknowledge an interrupt by reading the interrupt
    ID. Models reading GICC_IAR. Now returns `Except AckError InterruptId`
    to distinguish spurious from out-of-range failures so the dispatch
    sequence can enforce the "EOI unless spurious" invariant. -/
def acknowledgeInterrupt (rawIntId : Nat) :
    Except AckError InterruptId :=
  if rawIntId ≥ spuriousInterruptThreshold then .error .spurious
  else if h : rawIntId < 320 then .ok ⟨rawIntId, h⟩
  else .error (.outOfRange rawIntId)

/-- AG3-D / AK3-L (A-M10 / MEDIUM): End-of-interrupt signal. Models writing
    GICC_EOIR.

    Previously a pure no-op; AK3-L threads the EOI through the shadow
    `MachineState.eoiPending` audit trail so the proof layer can detect
    missing EOI writes. The hardware-level EOI effect is still modeled as
    no state change in the shadow page tables / register file; only the
    audit trail is updated. -/
def endOfInterrupt (st : SystemState) (intId : InterruptId) : SystemState :=
  { st with machine :=
    { st.machine with
      eoiPending := st.machine.eoiPending.filter (· != intId.val) } }

/-- AK3-L (A-M10 / MEDIUM): Mark an INTID as pending-EOI at the audit layer.
    Called at acknowledge time. -/
def ackInterruptAudit (st : SystemState) (rawIntId : Nat) : SystemState :=
  { st with machine :=
    { st.machine with
      eoiPending := rawIntId :: st.machine.eoiPending } }

/-- AK3-L: Kernel-exit invariant — on every kernel-exit path (syscall return,
    interrupt return), there must be no pending EOI. Any acknowledged
    interrupt must have had its EOI emitted before returning to user mode.

    This predicate is a model-layer safety net; the Rust HAL enforces the
    corresponding hardware-level invariant via the EOI-or-spurious dispatch
    logic in `rust/sele4n-hal/src/gic.rs` (AK3-C.4). -/
def eoiPendingEmpty (st : SystemState) : Prop :=
  st.machine.eoiPending = []

/-- AK3-L: `ackInterruptAudit` prepends the raw INTID to `eoiPending`. -/
theorem ackInterruptAudit_eoiPending (st : SystemState) (n : Nat) :
    (ackInterruptAudit st n).machine.eoiPending = n :: st.machine.eoiPending := rfl

/-- AK3-L: `endOfInterrupt` filters out the target INTID from `eoiPending`. -/
theorem endOfInterrupt_eoiPending (st : SystemState) (intId : InterruptId) :
    (endOfInterrupt st intId).machine.eoiPending =
    st.machine.eoiPending.filter (· != intId.val) := rfl

/-- AK3-L: Ack followed by EOI on the same INTID, with the original
    `eoiPending` empty, yields empty `eoiPending`. This is the round-trip
    closure property that formalises "every ack has a matching EOI" under
    the model-layer assumption that the handler does not touch the audit
    trail. -/
theorem ack_eoi_round_trip_empty (st : SystemState) (intId : InterruptId)
    (hEmpty : eoiPendingEmpty st) :
    eoiPendingEmpty (endOfInterrupt (ackInterruptAudit st intId.val) intId) := by
  unfold eoiPendingEmpty at *
  rw [endOfInterrupt_eoiPending, ackInterruptAudit_eoiPending, hEmpty]
  simp

-- ============================================================================
-- AG3-D-iii: Interrupt handler dispatch
-- ============================================================================

/-- AG3-D: Handle a single interrupt by ID on the executing core `c`, as the
kernel's live entries do (WS-ZA ZA6.37):
    - Timer interrupt (PPI 30): the per-core tick (`timerTickOnCore`), the one
      the live timer entry runs.
    - Any other line: seL4's `handleInterrupt` on core `c`
      (`handleInterruptOnCore`): a line at IRQSignal whose interrupt node slot
      holds a notification capability has that notification signalled with the
      capability's badge (`irqBinding?`, seL4's `IRQSignal`) and is masked
      until `seL4_IRQHandler_Ack`; an unbound line is masked, as seL4's
      `handleInterrupt` masks a line with no handler.

    Design notes:
    - The tick runs with no `withOutgoingContextChecked` guard because the
      timer interrupt is a hardware event, not a user-initiated syscall. Context save is
      the responsibility of the exception entry path in ExceptionModel, not
      the interrupt handler. This matches seL4's design where `handleInterrupt`
      is called after exception context has already been saved.
    - The handler is total: neither arm refuses, so the dispatch's absorbing
      of handler errors (AI2-A, H-03) has nothing left to absorb. -/
def handleInterrupt (st : SystemState) (c : Concurrency.CoreId) (intId : InterruptId) :
    SystemState :=
  if intId = timerInterruptId then timerTickOnCore st c
  else handleInterruptOnCore st c intId.val

-- ============================================================================
-- AG3-D-iv: Full dispatch sequence
-- ============================================================================

/-- AK3-C (A-H02 / HIGH) + AK3-L (A-M10 / MEDIUM) + AN8-C (H-19): Full
    interrupt dispatch sequence: **acknowledge → EOI → handle**.

    # AN8-C (H-19) ordering rationale

    The sequence was previously `ack → handle → EOI`. Under the Rust
    HAL's `panic = "abort"` profile, a handler panic would leave the
    INTID in an "active" state on the GIC even though the kernel
    itself had halted. To eliminate that class structurally, the HAL
    (`rust/sele4n-hal/src/gic.rs::dispatch_irq`) now emits EOI BEFORE
    the handler body runs. This Lean model is updated in lockstep so
    the proof layer mirrors hardware reality.

    GIC-400 §3.1 permits emitting EOI after IAR read but before the
    handler runs, provided the handler does not re-trigger its own
    INTID during execution. The registered handlers (timer PPI 30 and
    logged unknown IRQs) all satisfy this by construction; see
    `handle_irq` in the HAL for the per-handler re-entrancy contract.

    Per GIC-400 spec + AI2-A (H-03) + AK3-C + AK3-L audit trail + AN8-C:
    - Successful ack: record ack in `eoiPending`, IMMEDIATELY EOI
      (filters `eoiPending`), then run the handler on the post-EOI
      state, on the executing core `c`.  The handler is total, so the
      interrupt cycle closes at EOI time whatever it does.
    - Spurious interrupt (INTID ≥ 1020): no EOI per GIC spec; no ack
      record, no state change.
    - Out-of-range INTID (∈ [320, 1020)): **EOI is still emitted at HAL
      layer** to close the GIC interrupt cycle; at the Lean layer no
      handler dispatch and no audit-trail change because no valid
      `InterruptId : Fin 320` can be constructed. The hardware HAL
      writes the raw IAR value to EOIR — see
      `rust/sele4n-hal/src/gic.rs` (AK3-C.4).

    The audit trail (`ackInterruptAudit` push + `endOfInterrupt` filter)
    formalises the "EOI matches ack" invariant at the model layer. Under
    normal flow (successful dispatch), `eoiPending` is empty on kernel
    exit (AK3-L `eoiPendingEmpty` predicate). The new AN8-C order
    strengthens this: `eoiPending` is already empty when the handler
    body executes, so the handler cannot observe a state in which an
    unacknowledged EOI is pending for the INTID it's servicing. -/
def interruptDispatchSequence (st : SystemState) (c : Concurrency.CoreId) (rawIntId : Nat) :
    Except KernelError (Unit × SystemState) :=
  match acknowledgeInterrupt rawIntId with
  | .ok intId =>
    -- AK3-L: record the ack in the audit trail before dispatch.
    let stAck := ackInterruptAudit st intId.val
    -- AN8-C.2 (H-19): EOI fires BEFORE the handler body so a panicking
    -- or long-running handler cannot leave the INTID active on the GIC.
    let stEoi := endOfInterrupt stAck intId
    .ok ((), handleInterrupt stEoi c intId)
  | .error .spurious =>
    -- AK3-C: spurious — no EOI per GIC-400 spec, no audit entry
    .ok ((), st)
  | .error (.outOfRange _) =>
    -- AK3-C: out-of-range — no handler dispatch at Lean layer; HAL emits
    -- EOI with raw IAR value. No audit-trail change at Lean layer because
    -- no `InterruptId : Fin 320` witness can be produced.
    .ok ((), st)

-- ============================================================================
-- AG3-D-vi: Preservation theorems
-- ============================================================================

/-- AG3-D / AK3-C: Spurious interrupts preserve state unchanged. No EOI
    emitted per GIC-400 spec. -/
theorem interruptDispatchSequence_spurious (st : SystemState) (c : Concurrency.CoreId)
    (rawIntId : Nat) (hSpurious : rawIntId ≥ spuriousInterruptThreshold) :
    interruptDispatchSequence st c rawIntId = .ok ((), st) := by
  simp [interruptDispatchSequence, acknowledgeInterrupt, hSpurious]

/-- AK3-C (A-H02 / HIGH): Out-of-range INTIDs preserve Lean-layer state;
    the HAL emits EOI with the raw IAR value to prevent GIC lockup. -/
theorem interruptDispatchSequence_outOfRange (st : SystemState) (c : Concurrency.CoreId)
    (rawIntId : Nat)
    (hInRange : rawIntId < spuriousInterruptThreshold)
    (hOutOfRange : ¬(rawIntId < 320)) :
    interruptDispatchSequence st c rawIntId = .ok ((), st) := by
  have hNot : ¬(spuriousInterruptThreshold ≤ rawIntId) := Nat.not_le.mpr hInRange
  simp only [interruptDispatchSequence, acknowledgeInterrupt,
             if_neg hNot, dif_neg hOutOfRange]

/-- AG3-D / AK3-L: End-of-interrupt preserves all non-machine state.
    Prior to AK3-L this was a literal no-op; now it filters
    `machine.eoiPending` but leaves all other fields unchanged. -/
theorem endOfInterrupt_non_machine_eq (st : SystemState) (intId : InterruptId) :
    (endOfInterrupt st intId).objects = st.objects ∧
    (endOfInterrupt st intId).scheduler = st.scheduler := by
  unfold endOfInterrupt
  exact ⟨rfl, rfl⟩

/-- AK3-L (A-M10 / MEDIUM): After `endOfInterrupt intId`, the INTID is
    provably absent from the `eoiPending` audit trail. -/
theorem endOfInterrupt_removes_from_eoiPending
    (st : SystemState) (intId : InterruptId) :
    intId.val ∉ (endOfInterrupt st intId).machine.eoiPending := by
  unfold endOfInterrupt
  simp only
  intro hMem
  have := List.mem_filter.mp hMem
  simp at this

/-- AG3-D: an unbound device line is masked, and nothing else is written, as
seL4's `handleInterrupt` masks a line with no handler (WS-ZA ZA6.37: the
reference dispatch refused it with `.invalidIrq` until the dispatch ran the
live entry's handler). -/
theorem handleInterrupt_unmapped (st : SystemState) (c : Concurrency.CoreId)
    (intId : InterruptId)
    (hNotTimer : intId ≠ timerInterruptId)
    (hNoHandler : irqBinding? st intId.val = none) :
    handleInterrupt st c intId = setInterruptLineMask st intId.val true := by
  simp [handleInterrupt, handleInterruptOnCore, hNotTimer, hNoHandler]

/-- AG3-D: a bound device line signals its handler's notification on core `c`
and is masked until acknowledged. -/
theorem handleInterrupt_bound (st : SystemState) (c : Concurrency.CoreId)
    (intId : InterruptId) (ntfn : SeLe4n.ObjId) (badge : SeLe4n.Badge)
    (hNotTimer : intId ≠ timerInterruptId)
    (hHandler : irqBinding? st intId.val = some (ntfn, badge)) :
    handleInterrupt st c intId =
      setInterruptLineMask (interruptSignal ntfn badge c st) intId.val true := by
  simp [handleInterrupt, handleInterruptOnCore, hNotTimer, hHandler]

/-- AI2-A (H-03) + AK3-C (A-H02 / HIGH) + AN8-C (H-19):
    `interruptDispatchSequence` always succeeds at the Kernel layer.  The
    handler is total; spurious interrupts skip EOI per GIC spec; out-of-range
    INTIDs use the HAL's raw-IAR EOI path.

    The key safety invariant — "EOI is emitted unless spurious" — is
    captured by `interruptDispatchSequence_eoi_unless_spurious` below.
    AN8-C strengthens this to "EOI is emitted BEFORE the handler body
    runs unless spurious". -/
theorem interruptDispatchSequence_always_ok (st : SystemState) (c : Concurrency.CoreId)
    (rawIntId : Nat) :
    ∃ st', interruptDispatchSequence st c rawIntId = .ok ((), st') := by
  unfold interruptDispatchSequence
  cases acknowledgeInterrupt rawIntId with
  | error e =>
    cases e with
    | spurious => exact ⟨st, rfl⟩
    | outOfRange _ => exact ⟨st, rfl⟩
  | ok intId => exact ⟨_, rfl⟩

/-- AK3-C.3 (A-H02 / HIGH) + AN8-C (H-19): `eoiEmitted` — captures the
    proof-layer invariant that `endOfInterrupt` was invoked for a given
    INTID during a dispatch sequence on core `c`. At the Lean model level,
    `endOfInterrupt` filters the shadow `machine.eoiPending` audit trail;
    the hardware-level EOI is emitted by the Rust HAL (AK3-C.4).

    # Three disjuncts (post-AN8-C)

    1. `stOut = endOfInterrupt st intId` — EOI is the identity transition
       from the starting state. Preserved for backward compatibility with
       callers that reasoned about the pre-AN8-C ordering.
    2. `∃ stInner, stOut = endOfInterrupt stInner intId` — EOI was the
       last step, for some intermediate state. Matches the pre-AN8-C
       `ack → handle → EOI` ordering.
    3. `∃ stInner, stOut = handleInterrupt (endOfInterrupt stInner intId) c
       intId` — EOI happened before the handler, which produced `stOut`.
       Matches the AN8-C `ack → EOI → handle` order. -/
def eoiEmitted (c : Concurrency.CoreId) (intId : InterruptId) (st stOut : SystemState) : Prop :=
  stOut = endOfInterrupt st intId ∨
  (∃ stInner, stOut = endOfInterrupt stInner intId) ∨
  (∃ stInner, stOut = handleInterrupt (endOfInterrupt stInner intId) c intId)

/-- AK3-C.3 (A-H02 / HIGH) + AN8-C (H-19): EOI is emitted unless the
    interrupt was spurious.

    Formalizes the GIC-400 safety property: every acknowledged interrupt
    must have a matching EOI to avoid GIC lockup. Only truly spurious
    (INTID ≥ 1020) interrupts skip EOI; out-of-range INTIDs skip the
    Lean-layer EOI path because the HAL emits directly from the raw IAR
    value.  Under the `ack → EOI → handle` ordering the handler observes
    the post-EOI state (the third disjunct of `eoiEmitted`). -/
theorem interruptDispatchSequence_eoi_unless_spurious
    (st stOut : SystemState) (c : Concurrency.CoreId) (rawIntId : Nat)
    (hStep : interruptDispatchSequence st c rawIntId = .ok ((), stOut)) :
    acknowledgeInterrupt rawIntId = .error .spurious ∨
    acknowledgeInterrupt rawIntId = .error (.outOfRange rawIntId) ∨
    ∃ intId, eoiEmitted c intId st stOut := by
  unfold interruptDispatchSequence at hStep
  cases hAck : acknowledgeInterrupt rawIntId with
  | error e =>
    cases e with
    | spurious => left; rfl
    | outOfRange n =>
      right; left
      have : n = rawIntId := by
        unfold acknowledgeInterrupt at hAck
        split at hAck
        · simp at hAck
        · split at hAck
          · simp at hAck
          · simp at hAck; exact hAck.symm
      subst this; rfl
  | ok intId =>
    right; right
    refine ⟨intId, ?_⟩
    rw [hAck] at hStep
    simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
    exact Or.inr (Or.inr ⟨ackInterruptAudit st intId.val, hStep.symm⟩)

/-- AN8-C.2 (H-19): The `interruptDispatchSequence` semantics embed the
    `ack → EOI → handle` ordering: whenever the handler is invoked for a
    given INTID, its input state is `endOfInterrupt` applied to the
    ack-audit state — i.e. the INTID has already been retired from
    `machine.eoiPending` by the time the handler body runs.

    Combined with the hardware-level HAL contract in
    `rust/sele4n-hal/src/gic.rs::dispatch_irq`, this formalises the GIC-400
    §3.1 ordering that eliminates the "handler panic leaves INTID active"
    class of failure modes. -/
theorem interruptDispatchSequence_eoi_before_handler
    (st : SystemState) (c : Concurrency.CoreId) (rawIntId : Nat) (intId : InterruptId)
    (hAck : acknowledgeInterrupt rawIntId = .ok intId) :
    ∀ stOut, interruptDispatchSequence st c rawIntId = .ok ((), stOut) →
      stOut = handleInterrupt (endOfInterrupt (ackInterruptAudit st intId.val) intId) c intId := by
  intro stOut hStep
  unfold interruptDispatchSequence at hStep
  rw [hAck] at hStep
  simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
  exact hStep.symm

-- ============================================================================
-- AG5-E: Timer interrupt handler (model-level binding)
-- ============================================================================

/-- AG5-E: Timer interrupt handler on core `c` — the model-level function the
    Rust HAL's timer interrupt path calls via FFI (AG7).

    Composes:
    1. Acknowledge timer interrupt (modeled as identity — hardware-level)
    2. Run the per-core tick (`timerTickOnCore`), the live timer entry's
    3. Reprogram comparator (modeled as identity — hardware-level)

    Steps 1 and 3 are hardware operations with no kernel state effect, so
    this handler inherits every `timerTickOnCore` theorem. -/
def timerInterruptHandler (c : Concurrency.CoreId) : Kernel Unit :=
  fun st => .ok ((), timerTickOnCore st c)

/-- AG5-E: the timer interrupt handler is the per-core tick. -/
theorem timerInterruptHandler_eq_timerTickOnCore (c : Concurrency.CoreId) (st : SystemState) :
    timerInterruptHandler c st = .ok ((), timerTickOnCore st c) := rfl

/-- AG5-E: Timer interrupt handler dispatched via handleInterrupt
    when INTID = timerInterruptId (30). -/
theorem handleInterrupt_timer (st : SystemState) (c : Concurrency.CoreId) :
    handleInterrupt st c timerInterruptId = timerTickOnCore st c := by
  simp [handleInterrupt]

-- ============================================================================
-- AK3-M (A-L1..A-L9): LOW-tier architecture batch documentation
-- ============================================================================

/-!
## AK3-M: Architecture LOW-tier findings (batch documentation)

The v0.29.0 audit identified nine LOW-tier architecture findings that are
documented here rather than code-remediated per the plan's §6.AK3-M
disposition:

- **A-L1** `exceptionLevelFromSpsr` collapses EL2/EL3 → EL1. RPi5 has EL2
  present in hardware but the kernel never enters it; the collapse is
  accurate for the model and will be revisited if a hypervisor pathway is
  ever added. See `ExceptionModel.lean`.

- **A-L2** `memoryMap.find?` returns first match. The memory map is already
  invariant-constrained to `noOverlappingRegions` in boot; find-first
  therefore agrees with find-unique. See `Model/State.lean`.

- **A-L3** Hardcoded MAIR indices (0 for normal, 2 for device). These are
  already named via `MemoryAttribute.deviceNGnRnE` etc. in the HAL; the
  shadow model uses the numeric indices intentionally to match hardware.

- **A-L4** `acknowledgeInterrupt` silent truncation of INTID bits. Resolved
  by AK3-C — the new `AckError` inductive distinguishes spurious /
  out-of-range / handled with no truncation.

- **A-L5** `decodeCapPtr.isWord64Dec` proof-level invariant. Retired by
  WS-SX SX1.3: a register is a 64-bit word, so `decodeCapPtr` reads the word as
  the address and has no bound to check.

- **A-L6** Timer 64-bit wraparound. At 54 MHz, the CNTPCT_EL0 counter wraps
  at 2^64 / 54M ≈ 1.08 × 10^10 years. Not material to any realistic
  system lifetime.

- **A-L7** `contextSwitchState` does not perform TLB/ASID maintenance.
  Closed by AN9-D (suspendThread atomicity / context-switch bracket,
  DEF-C-M04), where the Rust HAL emits the required TLBI and DSB sequences
  before loading TTBR0.

- **A-L8** `BumpAllocator` off-by-one analysis. Audit found no actual
  off-by-one; documented in `VSpaceARMv8.lean:BumpAllocator.allocate`.

- **A-L9** `validateIpcBufferAddress` 4 KiB granule assumption. Documented
  in `IpcBufferValidation.lean` — the `ipcBuffer_within_page` theorem
  formalizes the 4 KiB / 512-byte relationship.

These items are either:
- Non-issues (the semantics are correct as-is),
- Resolved by related higher-tier fixes (A-L4 → AK3-C),
- Deferred to AN9-D with clear technical scope (A-L7 context-switch
  TLB/ASID maintenance).
-/

end SeLe4n.Kernel.Architecture
