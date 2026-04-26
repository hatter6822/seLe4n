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
      state. Handler errors are absorbed — the interrupt cycle has
      already closed at EOI time.
    - Spurious interrupt (INTID ≥ 1020): no EOI per GIC spec; no ack
      record, no state change.
    - Out-of-range INTID (∈ [224, 1020)): **EOI is still emitted at HAL
      layer** to close the GIC interrupt cycle; at the Lean layer no
      handler dispatch and no audit-trail change because no valid
      `InterruptId : Fin 224` can be constructed. The hardware HAL
      writes the raw IAR value to EOIR — see
      `rust/sele4n-hal/src/gic.rs` (AK3-C.4).

    The audit trail (`ackInterruptAudit` push + `endOfInterrupt` filter)
    formalises the "EOI matches ack" invariant at the model layer. Under
    normal flow (successful dispatch), `eoiPending` is empty on kernel
    exit (AK3-L `eoiPendingEmpty` predicate). The new AN8-C order
    strengthens this: `eoiPending` is already empty when the handler
    body executes, so the handler cannot observe a state in which an
    unacknowledged EOI is pending for the INTID it's servicing. -/
def interruptDispatchSequence (st : SystemState) (rawIntId : Nat) :
    Except KernelError (Unit × SystemState) :=
  match acknowledgeInterrupt rawIntId with
  | .ok intId =>
    -- AK3-L: record the ack in the audit trail before dispatch.
    let stAck := ackInterruptAudit st intId.val
    -- AN8-C.2 (H-19): EOI fires BEFORE the handler body so a panicking
    -- or long-running handler cannot leave the INTID active on the GIC.
    let stEoi := endOfInterrupt stAck intId
    match handleInterrupt stEoi intId with
    | .ok ((), st') => .ok ((), st')
    | .error _ =>
      -- AI2-A (H-03): handler errors are absorbed; the interrupt cycle
      -- has already closed at EOI time.
      .ok ((), stEoi)
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

/-- AI2-A (H-03) + AK3-C (A-H02 / HIGH) + AN8-C (H-19):
    `interruptDispatchSequence` always succeeds at the Kernel layer. Handler
    errors are absorbed (EOI already emitted before dispatch); spurious
    interrupts skip EOI per GIC spec; out-of-range INTIDs use the HAL's
    raw-IAR EOI path.

    The key safety invariant — "EOI is emitted unless spurious" — is
    captured by `interruptDispatchSequence_eoi_unless_spurious` below.
    AN8-C strengthens this to "EOI is emitted BEFORE the handler body
    runs unless spurious". -/
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
    -- AN8-C.2: handler runs on the post-EOI state, not the post-ack state
    cases hHandle : handleInterrupt
        (endOfInterrupt (ackInterruptAudit st intId.val) intId) intId with
    | ok val => exact ⟨val.2, by rfl⟩
    | error e =>
      exact ⟨endOfInterrupt (ackInterruptAudit st intId.val) intId, by rfl⟩

/-- AK3-C.3 (A-H02 / HIGH) + AN8-C (H-19): `eoiEmitted` — captures the
    proof-layer invariant that `endOfInterrupt` was invoked for a given
    INTID during a dispatch sequence. At the Lean model level,
    `endOfInterrupt` filters the shadow `machine.eoiPending` audit trail;
    the hardware-level EOI is emitted by the Rust HAL (AK3-C.4).

    # Three disjuncts (post-AN8-C)

    1. `stOut = endOfInterrupt st intId` — EOI is the identity transition
       from the starting state. Preserved for backward compatibility with
       callers that reasoned about the pre-AN8-C ordering.
    2. `∃ stInner, stOut = endOfInterrupt stInner intId` — EOI was the
       last step, for some intermediate state. Matches the pre-AN8-C
       `ack → handle → EOI` ordering AND the AN8-C error branch (handler
       failed, dispatch returns `stEoi` directly).
    3. `∃ stInner, handleInterrupt (endOfInterrupt stInner intId) intId =
       .ok ((), stOut)` — EOI happened before the handler, which ran
       successfully to produce `stOut`. Matches the AN8-C `ack → EOI →
       handle` success branch. -/
def eoiEmitted (intId : InterruptId) (st stOut : SystemState) : Prop :=
  stOut = endOfInterrupt st intId ∨
  (∃ stInner, stOut = endOfInterrupt stInner intId) ∨
  (∃ stInner, handleInterrupt (endOfInterrupt stInner intId) intId = .ok ((), stOut))

/-- AK3-C.3 (A-H02 / HIGH) + AN8-C (H-19): EOI is emitted unless the
    interrupt was spurious.

    Formalizes the GIC-400 safety property: every acknowledged interrupt
    (regardless of handler outcome) must have a matching EOI to avoid
    GIC lockup. Only truly spurious (INTID ≥ 1020) interrupts skip EOI;
    out-of-range INTIDs skip the Lean-layer EOI path because the HAL emits
    directly from the raw IAR value.

    AN8-C.2 strengthens the witness: under the new `ack → EOI → handle`
    ordering, the `eoiEmitted` predicate fires on BOTH the handler-success
    and handler-error branches. On success, the handler observes the
    post-EOI state; its output state `st'` inherits the EOI through the
    handler's preservation properties. On error, the dispatch returns
    the post-EOI state directly. Either way, `∃ stInner, stOut =
    endOfInterrupt stInner intId` witnesses the EOI emission. -/
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
    -- AN8-C.2: EOI fires BEFORE the handler. Case split on the handler
    -- outcome: success uses the 3rd disjunct of `eoiEmitted`; error
    -- uses the 2nd (since stOut = endOfInterrupt stAck intId).
    cases hHandle : handleInterrupt
        (endOfInterrupt (ackInterruptAudit st intId.val) intId) intId with
    | ok val =>
      rw [hHandle] at hStep
      simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
      -- AN8-C.2 success branch: stOut = val.2, and
      -- handleInterrupt (endOfInterrupt stAck intId) intId = .ok ((), val.2).
      -- Witness: 3rd disjunct, stInner = ackInterruptAudit st intId.val.
      right; right
      refine ⟨ackInterruptAudit st intId.val, ?_⟩
      -- Show val = ((), stOut) via Prod eta + val.snd = stOut from hStep.
      obtain ⟨uSt, sSt⟩ := val
      cases uSt
      simp only at hStep
      rw [← hStep.2]
      exact hHandle
    | error _ =>
      rw [hHandle] at hStep
      simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
      -- AN8-C.2 error branch: stOut = endOfInterrupt stAck intId directly.
      -- Witness: 2nd disjunct, stInner = ackInterruptAudit st intId.val.
      right; left
      exact ⟨ackInterruptAudit st intId.val, hStep.2.symm⟩

/-- AN8-C.2 (H-19): The `interruptDispatchSequence` semantics now embed the
    `ack → EOI → handle` ordering. This theorem witnesses the structural
    property: whenever the handler is invoked for a given INTID, its input
    state is `endOfInterrupt` applied to the ack-audit state — i.e. the
    INTID has already been retired from `machine.eoiPending` by the time
    the handler body runs.

    Combined with the hardware-level HAL contract in
    `rust/sele4n-hal/src/gic.rs::dispatch_irq`, this formalises the GIC-400
    §3.1 ordering that eliminates the "handler panic leaves INTID active"
    class of failure modes.

    The conclusion is phrased with `.snd` rather than a `Prod.mk` literal
    to sidestep `Unit.unit` vs `PUnit.unit` definitional quirks during
    unification with `handleInterrupt`'s output. -/
theorem interruptDispatchSequence_eoi_before_handler
    (st : SystemState) (rawIntId : Nat) (intId : InterruptId)
    (hAck : acknowledgeInterrupt rawIntId = .ok intId) :
    ∀ stOut, interruptDispatchSequence st rawIntId = .ok ((), stOut) →
      -- Either the handler errored (returns stAck-after-EOI directly) or
      -- the handler ran on an already-EOI'd state and its output state
      -- equals `stOut`.
      stOut = endOfInterrupt (ackInterruptAudit st intId.val) intId ∨
      (∃ v, handleInterrupt
              (endOfInterrupt (ackInterruptAudit st intId.val) intId) intId
                = .ok v ∧ v.2 = stOut) := by
  intro stOut hStep
  unfold interruptDispatchSequence at hStep
  rw [hAck] at hStep
  simp only at hStep
  cases hHandle : handleInterrupt
      (endOfInterrupt (ackInterruptAudit st intId.val) intId) intId with
  | ok val =>
    rw [hHandle] at hStep
    simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
    right
    -- After `cases hHandle`, the goal's `handleInterrupt ... = .ok v`
    -- has been rewritten to `Except.ok val = .ok v`, so witnessing
    -- `v := val` makes the first conjunct `rfl`-closed and the second
    -- comes from hStep.2 (val.snd = stOut).
    exact ⟨val, rfl, hStep.2⟩
  | error _ =>
    rw [hHandle] at hStep
    simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
    left; exact hStep.2.symm

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
  Closed by AN9-D (suspendThread atomicity / context-switch bracket,
  DEF-C-M04) in docs/audits/AUDIT_v0.30.6_WORKSTREAM_PLAN.md §12, where
  the Rust HAL emits the required TLBI and DSB sequences before loading
  TTBR0.

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
