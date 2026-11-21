-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/
import SeLe4n.Kernel.API
import SeLe4n.Kernel.IPC.CrossCore.DeliveredInPlace
import SeLe4n.Kernel.IPC.Invariant.SignalWakeLinkFrame
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
line's interrupt node slot names the notification and its badge
(`Architecture.irqBinding?`: the line at `IRQSignal`, `SystemState.irqSignalLines`,
and a notification capability with the send right in its node slot), and
the signal is the one the `.notificationSignal` syscall's arm performs
(`interruptSignal`): the per-core bound-aware signal
(`notificationSignalBoundOnCore`), so a waiter on another core is woken there,
then the woken bound receiver's reply stash cleared; the wake itself writes the
badge into the badge register of the thread it wakes, as seL4's `sendSignal`
does.  A signal the notification cannot take
(no notification at the bound object) leaves the state as it was, as seL4
prints `Undelivered IRQ` and delivers nothing, and the line is masked either
way.

The entry's raw form (`interruptEntryStep`) decodes the core and the line the
HAL passes: an id naming no core, or a line that is no device line of this
board (`Architecture.deviceInterruptLine`: an SPI below the board's line count,
`MachineState.interruptLineCount`, as seL4's `Arch_checkIRQ` bounds a line by
`maxIRQ`), enters nothing and writes nothing.  The HAL never passes a
spurious INTID (`≥ 1020`, seL4's `handleSpuriousIRQ`, no EOI) or one past the
distributor's lines (EOI'd without dispatch); the decode makes either inert
if it did.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

/-- **The interrupt's signal**, as the `.notificationSignal` syscall's arm
leaves the state (`dispatchWithCapChecked`): seL4-MCS `sendSignal`
(`sendSignalOnCore`), the bound-aware per-core signal and then the donation of
the notification's scheduling context to the thread it woke, under seL4's
guard (`maybeDonateSchedContext`), as seL4's `handleInterrupt` signals through
`sendSignal`.  The wake writes the badge into the woken thread's badge register
and drops a woken bound receiver's reply stash itself (`TCB.signalWoken`,
`TCB.signalBoundWoken`).  A signal the notification refuses leaves the state as
the signal does, unchanged. -/
def interruptSignal (ntfn : SeLe4n.ObjId) (badge : SeLe4n.Badge) (c : CoreId)
    (st : SystemState) : SystemState :=
  (sendSignalOnCore ntfn badge c st).1

/-- `interruptSignal` restated, the fallback of its compiled form (a separate
definition, so the `@[csimp]` replacement does not reach the fallback). -/
def interruptSignalGeneral (ntfn : SeLe4n.ObjId) (badge : SeLe4n.Badge) (c : CoreId)
    (st : SystemState) : SystemState :=
  (sendSignalOnCore ntfn badge c st).1

/-- **The interrupt's signal as compiled**: a signal that wakes its
notification's head waiter, with no bound receiver and every write in its slot
(`signalWakesInPlace`), makes its writes in place (`performSignalWoken`), as the
`.notificationSignal`
syscall's arm does (`notificationSignalCheckedArmR`); a signal whose bound
thread is blocked receiving, every write of its removal in its slot
(`queueRemoveInPlace`), wakes that thread with the badge in its badge register
(`performSignalBoundDelivered`); each wake is followed by the compiled donation
to the thread it woke (`maybeDonateSchedContextFast`); a signal with neither a
bound receiver nor a waiter wakes no thread, so donates nothing, and is the
signal's own state; every other signal runs the specification. -/
@[inline] def interruptSignalImpl (ntfn : SeLe4n.ObjId) (badge : SeLe4n.Badge) (c : CoreId)
    (st : SystemState) : SystemState :=
  if (boundDeliveryTarget? st ntfn).isNone then
    match st.getNotification? ntfn with
    | some n =>
        match n.waitHeadCode with
        | k + 1 =>
            if signalWakesInPlace st ntfn ⟨k⟩ then
              maybeDonateSchedContextFast
                (performSignalWoken st ntfn ⟨k⟩ (ntfnSuccessorCode st ⟨k⟩) badge c) ntfn.val k
            else interruptSignalGeneral ntfn badge c st
        | 0 => (notificationSignalBoundOnCore ntfn badge c st).1
    | none => interruptSignalGeneral ntfn badge c st
  else
    -- No waiter: a bound thread blocked receiving takes the badge.
    match st.getNotification? ntfn with
    | some n =>
        match n.waitHeadCode, n.boundTCBCode with
        | 0, k + 1 =>
            match st.getTcb? ⟨k⟩ with
            | some tcb =>
                if tcb.ipcStateCode = 1 then
                  match st.getEndpoint? ⟨tcb.ipcObjectCode⟩ with
                  | some ep =>
                      if queueRemoveInPlace st ⟨tcb.ipcObjectCode⟩ true ⟨k⟩ ep tcb then
                        maybeDonateSchedContextFast
                          (performSignalBoundDelivered c ⟨k⟩ ⟨tcb.ipcObjectCode⟩ ep tcb badge st)
                          ntfn.val k
                      else interruptSignalGeneral ntfn badge c st
                  | _ => interruptSignalGeneral ntfn badge c st
                else interruptSignalGeneral ntfn badge c st
            | _ => interruptSignalGeneral ntfn badge c st
        | _, _ => interruptSignalGeneral ntfn badge c st
    | none => interruptSignalGeneral ntfn badge c st

@[csimp] theorem interruptSignal_eq_impl : @interruptSignal = @interruptSignalImpl := by
  funext ntfn badge c st
  have hG : interruptSignalGeneral ntfn badge c st = interruptSignal ntfn badge c st := rfl
  unfold interruptSignalImpl
  split
  · next hBound =>
    simp only [Option.isNone_iff_eq_none] at hBound
    split
    · next n hN =>
      split
      · next k hK =>
        split
        · next hW =>
          have hNo : st.objects.noResizeDue := by
            simp only [signalWakesInPlace, Bool.and_eq_true] at hW
            exact RobinHood.RHTable.noResizeDue_of_findsInPlace hW.1.1.2
          have hHead : n.waitHead = some ⟨k⟩ := by
            rw [← Notification.ofOptCode_waitHeadCode, hK]; rfl
          have hWk : signalWokenThread? st ntfn = some ⟨k⟩ := by
            simp only [signalWokenThread?, hBound, hN, Option.bind_some, hHead]
          simp only [interruptSignal, sendSignalOnCore, notificationSignalBoundOnCore, hBound,
            notificationSignalOnCore_eq_impl, notificationSignalOnCoreImpl, hN, hHead, hW,
            ↓reduceIte, Option.map_none, donateToSignalled, hWk]
          rw [← optCode_ntfnSuccessor?, ← signalWoken_eq_perform, maybeDonateSchedContextFast_eq]
        · exact hG
      · next hK =>
        have hHead : n.waitHead = none := by
          rw [← Notification.ofOptCode_waitHeadCode, hK]; rfl
        have hWk : signalWokenThread? st ntfn = none := by
          simp only [signalWokenThread?, hBound, hN, Option.bind_some, hHead]
        unfold interruptSignal
        rw [sendSignalOnCore_fst]
        split <;> first | rfl | simp only [donateToSignalled, hWk]
    · exact hG
  · split
    · next n hN =>
      split
      · next k hK0 hB =>
        split
        · next tcb hTT0 =>
          have hTT := (SystemState.getTcb?_eq_some_iff _ _ _).mp hTT0
          split
          · next hSt =>
            split
            · next ep hE0 =>
              have hE := (SystemState.getEndpoint?_eq_some_iff _ _ _).mp hE0
              split
              · next hQ =>
                have hBT := boundDeliveryTarget?_of_codes st ntfn n k tcb hN hK0 hB hTT hSt
                have hS := notificationSignalBoundOnCore_bound_eq ntfn badge c st ⟨k⟩
                  ⟨tcb.ipcObjectCode⟩ ep tcb hBT hE hTT hQ
                have hWk : signalWokenThread? st ntfn = some ⟨k⟩ := by
                  simp only [signalWokenThread?, hBT]
                simp only [interruptSignal, sendSignalOnCore, hS, donateToSignalled, hWk]
                rw [maybeDonateSchedContextFast_eq]
                rfl
              · exact hG
            all_goals exact hG
          · exact hG
        all_goals exact hG
      all_goals exact hG
    · exact hG

/-- **seL4's `handleInterrupt` on core `c`**: the bound handler's notification
signalled (`interruptSignal`, the badge written into the thread it wakes) and
the line masked, or, with no handler bound, the line masked. -/
def handleInterruptOnCore (st : SystemState) (c : CoreId) (line : Nat) : SystemState :=
  match Architecture.irqBinding? st line with
  | some (ntfn, badge) =>
      Architecture.setInterruptLineMask (interruptSignal ntfn badge c st) line true
  | none => Architecture.setInterruptLineMask st line true

/-- **The interrupt entry's step**, over the raw core id and INTID the HAL
passes: inert unless the id names a core and the INTID a device line. -/
def interruptEntryStep (st : SystemState) (coreId intId : UInt64) : SystemState :=
  match Concurrency.coreIdOfUInt64? coreId with
  | none => st
  | some c =>
      if Architecture.deviceInterruptLine st intId.toNat then handleInterruptOnCore st c intId.toNat
      else st

/-! ### The step's shape -/

/-- An id naming no core enters nothing. -/
theorem interruptEntryStep_invalid_core (st : SystemState) (coreId intId : UInt64)
    (h : Concurrency.coreIdOfUInt64? coreId = none) : interruptEntryStep st coreId intId = st := by
  simp [interruptEntryStep, h]

/-- A line that is no device line enters nothing. -/
theorem interruptEntryStep_not_device (st : SystemState) (coreId intId : UInt64)
    (h : Architecture.deviceInterruptLine st intId.toNat = false) :
    interruptEntryStep st coreId intId = st := by
  unfold interruptEntryStep
  cases Concurrency.coreIdOfUInt64? coreId <;> simp [h]

/-- **A line the board does not have enters nothing**: an INTID at or past the
board's line count (`MachineState.interruptLineCount`) is refused before any
write, as seL4's `Arch_checkIRQ` refuses one above `maxIRQ`. -/
theorem interruptEntryStep_off_board (st : SystemState) (coreId intId : UInt64)
    (h : st.machine.interruptLineCount ≤ intId.toNat) :
    interruptEntryStep st coreId intId = st := by
  apply interruptEntryStep_not_device
  simp only [Architecture.deviceInterruptLine, Architecture.deviceInterruptLineUnder,
    Bool.and_eq_false_iff, decide_eq_false_iff_not, Nat.not_lt]
  exact .inl (.inr h)

/-- On a core and a device line the step is `handleInterruptOnCore`. -/
theorem interruptEntryStep_device (st : SystemState) (coreId intId : UInt64) (c : CoreId)
    (hc : Concurrency.coreIdOfUInt64? coreId = some c)
    (h : Architecture.deviceInterruptLine st intId.toNat = true) :
    interruptEntryStep st coreId intId = handleInterruptOnCore st c intId.toNat := by
  simp [interruptEntryStep, hc, h]

/-- **Every state the step reaches is `P`** when the state it starts from is,
the signal's is and the mask keeps `P`: the one case split every frame below
is an instance of. -/
theorem handleInterruptOnCore_of {P : SystemState → Prop} (st : SystemState) (c : CoreId)
    (line : Nat)
    (hMask : ∀ s, P s → P (Architecture.setInterruptLineMask s line true))
    (hSt : P st)
    (hSig : ∀ ntfn badge, Architecture.irqBinding? st line = some (ntfn, badge) →
      P (interruptSignal ntfn badge c st)) :
    P (handleInterruptOnCore st c line) := by
  unfold handleInterruptOnCore
  cases h : Architecture.irqBinding? st line with
  | none => exact hMask _ hSt
  | some p => obtain ⟨ntfn, badge⟩ := p; exact hMask _ (hSig ntfn badge h)

/-- …and the raw step's. -/
theorem interruptEntryStep_of {P : SystemState → Prop} (st : SystemState) (coreId intId : UInt64)
    (hSt : P st) (hStep : ∀ c, Concurrency.coreIdOfUInt64? coreId = some c →
      Architecture.deviceInterruptLine st intId.toNat = true →
      P (handleInterruptOnCore st c intId.toNat)) :
    P (interruptEntryStep st coreId intId) := by
  unfold interruptEntryStep
  cases hc : Concurrency.coreIdOfUInt64? coreId with
  | none => exact hSt
  | some c =>
    dsimp only
    cases hd : Architecture.deviceInterruptLine st intId.toNat with
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
    (fun ntfn _ _ => (sendSignalOnCore_preserves_objects_invExt _ _ _ st h))

/-- …and so does the raw step. -/
theorem interruptEntryStep_preserves_objects_invExt (st : SystemState) (coreId intId : UInt64)
    (h : st.objects.invExt) : (interruptEntryStep st coreId intId).objects.invExt :=
  interruptEntryStep_of (P := fun s => s.objects.invExt) st coreId intId h
    (fun c _ _ => handleInterruptOnCore_preserves_objects_invExt st c _ h)

end SeLe4n.Kernel
