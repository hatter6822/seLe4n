-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/
import SeLe4n.Kernel.IPC.CrossCore.NotificationBind
import SeLe4n.Kernel.Architecture.InterruptMask
import SeLe4n.Kernel.Concurrency.Runtime

/-!
# WS-ZA ZA6.32 — a device interrupt, delivered on a core

seL4's `handleInterrupt` (`src/kernel/interrupt.c`, GICv2 build) on a line the
interrupt controller acknowledged:

* `IRQSignal` — a handler is bound: the handler's notification is signalled
  (`sendSignal`), then the line is masked (`maskInterrupt(true, irq)`) until the
  handler acknowledges it (`invokeIRQHandler_AckIRQ`, `Architecture.irqHandlerAck`);
* `IRQInactive` — no handler is bound: the line is masked, so a line nobody
  serves stops interrupting.

The step here is that function on core `c` (`handleInterruptOnCore`): the
model's handler table (`SystemState.irqHandlers`) names the notification, and
the signal is the per-core bound-aware signal the `.notificationSignal` syscall
runs (`notificationSignalBoundOnCore`), so a waiter on another core is woken
there.  A signal the notification cannot take (no notification at the bound
object) leaves the state as it was, as seL4 prints `Undelivered IRQ` and
delivers nothing, and the line is masked either way.

The entry's raw form (`interruptEntryStep`) decodes the core and the line the
HAL passes: an id naming no core, or a line that is no device line
(`Architecture.deviceInterruptLine`), enters nothing.  The HAL never passes a
spurious INTID (`≥ 1020`, seL4's `handleSpuriousIRQ`, no EOI) or one past the
distributor's lines (EOI'd without dispatch); the decode makes either inert
if it did.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

/-- **seL4's `handleInterrupt` on core `c`**: the bound handler's notification
signalled and the line masked, or, with no handler bound, the line masked. -/
def handleInterruptOnCore (st : SystemState) (c : CoreId) (line : Nat) : SystemState :=
  match st.irqHandlers[(⟨line⟩ : SeLe4n.Irq)]? with
  | some ntfn =>
      Architecture.setInterruptLineMask
        (notificationSignalBoundOnCore ntfn (SeLe4n.Badge.ofNatMasked line) c st).1 line true
  | none => Architecture.setInterruptLineMask st line true

/-- **The interrupt entry's step**, over the raw core id and INTID the HAL
passes: inert unless the id names a core and the INTID a device line. -/
def interruptEntryStep (st : SystemState) (coreId intId : UInt64) : SystemState :=
  match Concurrency.coreIdOfUInt64? coreId with
  | none => st
  | some c =>
      if Architecture.deviceInterruptLine intId.toNat then handleInterruptOnCore st c intId.toNat
      else st

/-! ### The step's shape -/

/-- An id naming no core enters nothing. -/
theorem interruptEntryStep_invalid_core (st : SystemState) (coreId intId : UInt64)
    (h : Concurrency.coreIdOfUInt64? coreId = none) : interruptEntryStep st coreId intId = st := by
  simp [interruptEntryStep, h]

/-- A line that is no device line enters nothing. -/
theorem interruptEntryStep_not_device (st : SystemState) (coreId intId : UInt64)
    (h : Architecture.deviceInterruptLine intId.toNat = false) :
    interruptEntryStep st coreId intId = st := by
  unfold interruptEntryStep
  cases Concurrency.coreIdOfUInt64? coreId <;> simp [h]

/-- On a core and a device line the step is `handleInterruptOnCore`. -/
theorem interruptEntryStep_device (st : SystemState) (coreId intId : UInt64) (c : CoreId)
    (hc : Concurrency.coreIdOfUInt64? coreId = some c)
    (h : Architecture.deviceInterruptLine intId.toNat = true) :
    interruptEntryStep st coreId intId = handleInterruptOnCore st c intId.toNat := by
  simp [interruptEntryStep, hc, h]

/-- **Every state the step reaches is `P`** when the state it starts from is,
the signal's is and the mask keeps `P`: the one case split every frame below
is an instance of. -/
theorem handleInterruptOnCore_of {P : SystemState → Prop} (st : SystemState) (c : CoreId)
    (line : Nat)
    (hMask : ∀ s, P s → P (Architecture.setInterruptLineMask s line true))
    (hSt : P st)
    (hSig : ∀ ntfn, st.irqHandlers[(⟨line⟩ : SeLe4n.Irq)]? = some ntfn →
      P (notificationSignalBoundOnCore ntfn (SeLe4n.Badge.ofNatMasked line) c st).1) :
    P (handleInterruptOnCore st c line) := by
  unfold handleInterruptOnCore
  cases h : st.irqHandlers[(⟨line⟩ : SeLe4n.Irq)]? with
  | none => exact hMask _ hSt
  | some ntfn => exact hMask _ (hSig ntfn h)

/-- …and the raw step's. -/
theorem interruptEntryStep_of {P : SystemState → Prop} (st : SystemState) (coreId intId : UInt64)
    (hSt : P st) (hStep : ∀ c, Concurrency.coreIdOfUInt64? coreId = some c →
      Architecture.deviceInterruptLine intId.toNat = true →
      P (handleInterruptOnCore st c intId.toNat)) :
    P (interruptEntryStep st coreId intId) := by
  unfold interruptEntryStep
  cases hc : Concurrency.coreIdOfUInt64? coreId with
  | none => exact hSt
  | some c =>
    dsimp only
    cases hd : Architecture.deviceInterruptLine intId.toNat with
    | false => simpa using hSt
    | true => simpa using hStep c hc hd

/-- The step leaves the line masked. -/
theorem handleInterruptOnCore_masks (st : SystemState) (c : CoreId) (line : Nat) :
    (handleInterruptOnCore st c line).machine.irqLineMasked line = true := by
  unfold handleInterruptOnCore
  split <;> simp

/-- The step keeps the object store's invariant. -/
theorem handleInterruptOnCore_preserves_objects_invExt (st : SystemState) (c : CoreId)
    (line : Nat) (h : st.objects.invExt) : (handleInterruptOnCore st c line).objects.invExt :=
  handleInterruptOnCore_of (P := fun s => s.objects.invExt) st c line
    (fun s hs => by simpa using hs) h
    (fun ntfn _ => notificationSignalBoundOnCore_preserves_objects_invExt _ _ _ st h)

/-- …and so does the raw step. -/
theorem interruptEntryStep_preserves_objects_invExt (st : SystemState) (coreId intId : UInt64)
    (h : st.objects.invExt) : (interruptEntryStep st coreId intId).objects.invExt :=
  interruptEntryStep_of (P := fun s => s.objects.invExt) st coreId intId h
    (fun c _ _ => handleInterruptOnCore_preserves_objects_invExt st c _ h)

/-- No core's replenish queue moves. -/
theorem handleInterruptOnCore_replenishQueueOnCore (st : SystemState) (c d : CoreId)
    (line : Nat) :
    (handleInterruptOnCore st c line).scheduler.replenishQueueOnCore d =
      st.scheduler.replenishQueueOnCore d :=
  handleInterruptOnCore_of
    (P := fun s => s.scheduler.replenishQueueOnCore d = st.scheduler.replenishQueueOnCore d)
    st c line (fun s hs => by simpa using hs) rfl
    (fun ntfn _ => notificationSignalBoundOnCore_replenishQueueOnCore _ _ _ st d)

end SeLe4n.Kernel
