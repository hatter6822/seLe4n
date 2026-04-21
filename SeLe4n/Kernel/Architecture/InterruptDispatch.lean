/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.API
import SeLe4n.Kernel.IPC.Operations

/-!
# AG3-D (FINDING-06): Interrupt Dispatch Model

Models the ARM64 interrupt dispatch path: acknowledge → dispatch → EOI.
Integrates with the GIC-400 interrupt controller on Raspberry Pi 5.

## Interrupt Flow

1. **Acknowledge**: Read GICC_IAR to get the interrupt ID (INTID)
2. **Dispatch**: Route to handler based on INTID
   - Timer interrupt (PPI 30) → `timerTick`
   - Mapped IRQ → `notificationSignal` to registered handler
   - Unmapped IRQ → error
3. **End-of-Interrupt**: Write GICC_EOIR to signal completion

## GIC-400 Interrupt ID Space

- INTIDs 0–15: SGIs (Software Generated Interrupts)
- INTIDs 16–31: PPIs (Private Peripheral Interrupts)
- INTIDs 32–223: SPIs (Shared Peripheral Interrupts)
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
    Bounded to 224 INTIDs (0–223): SGIs (0–15), PPIs (16–31), SPIs (32–223).
    This bound is RPi5/BCM2712-specific. The GIC-400 architecture supports
    up to 480 INTIDs, but BCM2712 only implements 192 SPIs (32–223).
    A future multi-platform build would parameterize this bound. -/
abbrev InterruptId := Fin 224

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
    - **OutOfRange** (INTID ∈ [224, 1020)) — legal INTID space on the GIC but
      unsupported on RPi5's BCM2712 (only 224 INTIDs). Hardware errata or
      SMP races can deliver such IAR values. **Must still EOI** to complete
      the interrupt cycle and avoid GIC lockup.
    - **Erratum** (valid INTID but handler fails) — see `interruptDispatchSequence`.

    This distinction is what enables the AK3-C safety property: EOI is
    always emitted unless the interrupt was spurious. -/
inductive AckError where
  | spurious                       -- INTID ≥ 1020 — skip EOI per GIC spec
  | outOfRange (rawIntId : Nat)    -- INTID ∈ [224, 1020) — emit EOI, no dispatch
  deriving Repr, DecidableEq

/-- AK3-C (A-H02 / HIGH): Acknowledge an interrupt by reading the interrupt
    ID. Models reading GICC_IAR. Now returns `Except AckError InterruptId`
    to distinguish spurious from out-of-range failures so the dispatch
    sequence can enforce the "EOI unless spurious" invariant. -/
def acknowledgeInterrupt (rawIntId : Nat) :
    Except AckError InterruptId :=
  if rawIntId ≥ spuriousInterruptThreshold then .error .spurious
  else if h : rawIntId < 224 then .ok ⟨rawIntId, h⟩
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

/-- AG3-D: Handle a single interrupt by ID.
    Routes based on interrupt type:
    - Timer interrupt (PPI 30): Delegate to `timerTick`
    - Mapped IRQ: Deliver notification via `notificationSignal`
    - Unmapped IRQ: Return `.invalidIrq` error

    Design notes:
    - Uses `timerTick` (not `timerTickChecked`) because the timer interrupt
      is a hardware event, not a user-initiated syscall. Context save is
      the responsibility of the exception entry path in ExceptionModel, not
      the interrupt handler. This matches seL4's design where `handleInterrupt`
      is called after exception context has already been saved.
    - Badge is derived from the INTID value via `Badge.ofNatMasked`. In seL4,
      badges are configured per-IRQ-handler at bind time. This simplification
      is sufficient for the abstract model; the hardware binding phase (AG5)
      will add per-handler badge configuration.
    - AI2-A (H-03): EOI is always sent regardless of handler outcome to
      prevent GIC lockup. Handler errors are non-fatal — the interrupt was
      acknowledged and EOI must complete the cycle. This matches Linux's
      unconditional EOI pattern. -/
def handleInterrupt (st : SystemState) (intId : InterruptId) :
    Except KernelError (Unit × SystemState) :=
  if intId = timerInterruptId then
    timerTick st
  else
    let irq : Irq := ⟨intId.val⟩
    match st.irqHandlers[irq]? with
    | some handlerId =>
        -- Deliver signal to the notification object bound to this IRQ
        notificationSignal handlerId (Badge.ofNatMasked intId.val) st
    | none => .error .invalidIrq

-- ============================================================================
-- AG3-D-iv: Full dispatch sequence
-- ============================================================================

/-- AK3-C (A-H02 / HIGH) + AK3-L (A-M10 / MEDIUM): Full interrupt dispatch
    sequence: acknowledge → handle → EOI.

    Per GIC-400 spec + AI2-A (H-03) + AK3-C + AK3-L audit trail:
    - Successful ack + successful handler: record ack in `eoiPending`,
      handle, then EOI (which filters out of `eoiPending`)
    - Successful ack + handler error ("erratum"): record ack, then EOI
      (prevents GIC lockup; error absorbed)
    - Spurious interrupt (INTID ≥ 1020): no EOI per GIC spec; no ack
      record, no state change
    - Out-of-range INTID (∈ [224, 1020)): **EOI is still emitted at HAL
      layer** to close the GIC interrupt cycle; at the Lean layer no
      handler dispatch and no audit-trail change because no valid
      `InterruptId : Fin 224` can be constructed. The hardware HAL
      writes the raw IAR value to EOIR — see
      `rust/sele4n-hal/src/gic.rs` (AK3-C.4).

    The audit trail (`ackInterruptAudit` push + `endOfInterrupt` filter)
    formalises the "EOI matches ack" invariant at the model layer. Under
    normal flow (successful dispatch), `eoiPending` is empty on kernel
    exit (AK3-L `eoiPendingEmpty` predicate). -/
def interruptDispatchSequence (st : SystemState) (rawIntId : Nat) :
    Except KernelError (Unit × SystemState) :=
  match acknowledgeInterrupt rawIntId with
  | .ok intId =>
    -- AK3-L: record the ack in the audit trail before dispatch
    let stAck := ackInterruptAudit st intId.val
    match handleInterrupt stAck intId with
    | .ok ((), st') => .ok ((), endOfInterrupt st' intId)
    | .error _ =>
      -- AI2-A (H-03): EOI fires on erratum; interrupt was acknowledged
      .ok ((), endOfInterrupt stAck intId)
  | .error .spurious =>
    -- AK3-C: spurious — no EOI per GIC-400 spec, no audit entry
    .ok ((), st)
  | .error (.outOfRange _) =>
    -- AK3-C: out-of-range — no handler dispatch at Lean layer; HAL emits
    -- EOI with raw IAR value. No audit-trail change at Lean layer because
    -- no `InterruptId : Fin 224` witness can be produced.
    .ok ((), st)

-- ============================================================================
-- AG3-D-vi: Preservation theorems
-- ============================================================================

/-- AG3-D / AK3-C: Spurious interrupts preserve state unchanged. No EOI
    emitted per GIC-400 spec. -/
theorem interruptDispatchSequence_spurious (st : SystemState) (rawIntId : Nat)
    (hSpurious : rawIntId ≥ spuriousInterruptThreshold) :
    interruptDispatchSequence st rawIntId = .ok ((), st) := by
  simp [interruptDispatchSequence, acknowledgeInterrupt, hSpurious]

/-- AK3-C (A-H02 / HIGH): Out-of-range INTIDs preserve Lean-layer state;
    the HAL emits EOI with the raw IAR value to prevent GIC lockup. -/
theorem interruptDispatchSequence_outOfRange (st : SystemState) (rawIntId : Nat)
    (hInRange : rawIntId < spuriousInterruptThreshold)
    (hOutOfRange : ¬(rawIntId < 224)) :
    interruptDispatchSequence st rawIntId = .ok ((), st) := by
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

/-- AG3-D: Unmapped IRQ returns `.invalidIrq`. -/
theorem handleInterrupt_unmapped (st : SystemState) (intId : InterruptId)
    (hNotTimer : intId ≠ timerInterruptId)
    (hNoHandler : st.irqHandlers[(⟨intId.val⟩ : Irq)]? = none) :
    handleInterrupt st intId = .error .invalidIrq := by
  unfold handleInterrupt
  simp [hNotTimer, hNoHandler]

/-- AI2-A (H-03) + AK3-C (A-H02 / HIGH): `interruptDispatchSequence` always
    succeeds at the Kernel layer. Handler errors are absorbed (EOI emitted);
    spurious interrupts skip EOI per GIC spec; out-of-range INTIDs use the
    HAL's raw-IAR EOI path.

    The key safety invariant — "EOI is emitted unless spurious" — is
    captured by `interruptDispatchSequence_eoi_unless_spurious` below. -/
theorem interruptDispatchSequence_always_ok (st : SystemState) (rawIntId : Nat) :
    ∃ st', interruptDispatchSequence st rawIntId = .ok ((), st') := by
  simp only [interruptDispatchSequence]
  cases hAck : acknowledgeInterrupt rawIntId with
  | error e =>
    cases e with
    | spurious => exact ⟨st, rfl⟩
    | outOfRange _ => exact ⟨st, rfl⟩
  | ok intId =>
    simp only []
    -- AK3-L: dispatch passes `ackInterruptAudit st intId.val` to handler
    cases hHandle : handleInterrupt (ackInterruptAudit st intId.val) intId with
    | ok val => exact ⟨endOfInterrupt val.2 intId, by rfl⟩
    | error e => exact ⟨endOfInterrupt (ackInterruptAudit st intId.val) intId, by rfl⟩

/-- AK3-C.3 (A-H02 / HIGH): `eoiEmitted` — captures the proof-layer
    invariant that `endOfInterrupt` was invoked for a given INTID during a
    dispatch sequence. At the Lean model level, `endOfInterrupt` is a no-op
    (the EOI is hardware-level); this predicate witnesses the model-level
    intent. Substantive binding comes from the Rust HAL in AK3-C.4. -/
def eoiEmitted (intId : InterruptId) (st stOut : SystemState) : Prop :=
  stOut = endOfInterrupt st intId ∨
  ∃ stInner, stOut = endOfInterrupt stInner intId

/-- AK3-C.3 (A-H02 / HIGH): EOI is emitted unless the interrupt was spurious.
    Formalizes the GIC-400 safety property: every acknowledged interrupt
    (regardless of handler outcome) must have a matching EOI to avoid
    GIC lockup. Only truly spurious (INTID ≥ 1020) interrupts skip EOI;
    out-of-range INTIDs skip the Lean-layer EOI path because the HAL emits
    directly from the raw IAR value. -/
theorem interruptDispatchSequence_eoi_unless_spurious
    (st stOut : SystemState) (rawIntId : Nat)
    (hStep : interruptDispatchSequence st rawIntId = .ok ((), stOut)) :
    acknowledgeInterrupt rawIntId = .error .spurious ∨
    acknowledgeInterrupt rawIntId = .error (.outOfRange rawIntId) ∨
    ∃ intId, eoiEmitted intId st stOut := by
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
    simp only at hStep
    -- AK3-L: dispatch now uses `ackInterruptAudit st intId.val` as the
    -- state fed to the handler. The `eoiEmitted` predicate accepts either
    -- a direct `endOfInterrupt st` (erratum path, via right-exists) or
    -- `endOfInterrupt stInner` for some inner state (handler-success path).
    cases hHandle : handleInterrupt (ackInterruptAudit st intId.val) intId with
    | ok val =>
      rw [hHandle] at hStep
      simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
      right; exact ⟨val.2, hStep.2.symm⟩
    | error e =>
      rw [hHandle] at hStep
      simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
      right; exact ⟨ackInterruptAudit st intId.val, hStep.2.symm⟩

-- ============================================================================
-- AG5-E: Timer interrupt handler (model-level binding)
-- ============================================================================

/-- AG5-E: Timer interrupt handler — the model-level function that the
    Rust HAL's timer interrupt path calls via FFI (AG7).

    Composes:
    1. Acknowledge timer interrupt (modeled as identity — hardware-level)
    2. Execute `timerTick` to advance the model timer
    3. Reprogram comparator (modeled as identity — hardware-level)

    Steps 1 and 3 are hardware operations with no kernel state effect.
    The only state-affecting operation is `timerTick`, which is the existing
    scheduler tick function. This handler therefore inherits all `timerTick`
    preservation theorems automatically.

    Note: uses `timerTick` (not `timerTickWithBudget`) to match the seL4
    design where the basic timer tick is the hardware interrupt handler's
    responsibility. Budget-aware processing is a higher-level scheduler
    concern handled in the full `timerTickWithBudget` path. -/
def timerInterruptHandler : Kernel Unit :=
  fun st => timerTick st

/-- AG5-E: Timer interrupt handler is equivalent to `timerTick`.
    This allows all existing `timerTick` preservation theorems to be
    reused directly for the timer interrupt path. -/
theorem timerInterruptHandler_eq_timerTick :
    timerInterruptHandler = timerTick := rfl

/-- AG5-E: Timer interrupt handler dispatched via handleInterrupt
    when INTID = timerInterruptId (30). -/
theorem handleInterrupt_timer (st : SystemState) :
    handleInterrupt st timerInterruptId = timerTick st := by
  unfold handleInterrupt
  simp [timerInterruptId]

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

- **A-L5** `decodeCapPtr.isWord64Dec` proof-level invariant. Documented at
  the `CPtr` type level; no runtime-observable effect because CPtr construction
  already guarantees word-boundedness.

- **A-L6** Timer 64-bit wraparound. At 54 MHz, the CNTPCT_EL0 counter wraps
  at 2^64 / 54M ≈ 1.08 × 10^10 years. Not material to any realistic
  system lifetime.

- **A-L7** `contextSwitchState` does not perform TLB/ASID maintenance.
  Recorded as a post-1.0 H3 hardware-integration hardening candidate
  (related: DEF-A-M04 TLB+cache composition in
  docs/audits/AUDIT_v0.29.0_DEFERRED.md); the Rust HAL emits the required
  TLBI and DSB sequences before loading TTBR0.

- **A-L8** `BumpAllocator` off-by-one analysis. Audit found no actual
  off-by-one; documented in `VSpaceARMv8.lean:BumpAllocator.allocate`.

- **A-L9** `validateIpcBufferAddress` 4 KiB granule assumption. Documented
  in `IpcBufferValidation.lean` — the `ipcBuffer_within_page` theorem
  formalizes the 4 KiB / 512-byte relationship.

These items are either:
- Non-issues (the semantics are correct as-is),
- Resolved by related higher-tier fixes (A-L4 → AK3-C),
- Recorded as post-1.0 hardening candidates with clear technical scope
  (A-L7 context-switch TLB/ASID maintenance; see DEF-A-M04 in
  docs/audits/AUDIT_v0.29.0_DEFERRED.md).
-/

end SeLe4n.Kernel.Architecture
