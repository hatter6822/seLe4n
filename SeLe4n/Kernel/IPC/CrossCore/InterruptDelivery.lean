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
then the woken bound receiver's reply stash cleared and the badge staged into
the saved registers of the thread it woke, as seL4's `sendSignal` writes the
badge register of the thread it wakes.  A signal the notification cannot take
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
leaves the state (`dispatchWithCapChecked`): the bound-aware per-core signal,
then the woken bound receiver's reply stash cleared
(`clearWokenReceiverStash`) and the badge frame staged into the woken thread's
saved registers (`stageWokenDelivery`), the bound receiver's and the
notification's head waiter's.  A signal the notification refuses leaves the
state as the signal does, unchanged. -/
def interruptSignal (ntfn : SeLe4n.ObjId) (badge : SeLe4n.Badge) (c : CoreId)
    (st : SystemState) : SystemState :=
  match notificationSignalBoundOnCore ntfn badge c st with
  | (s1, .ok _) =>
      match clearWokenReceiverStash ((boundDeliveryTarget? st ntfn).map (·.1)) s1 with
      | .ok ((), s2) =>
          Architecture.stageWokenDelivery
            (Architecture.stageWokenDelivery s2 ((boundDeliveryTarget? st ntfn).map (·.1)) 0)
            (notificationSignalWaiter? st ntfn) 0
      | .error _ => s1
  | (s1, .error _) => s1

/-- **Every state the signal reaches is `P`** when the signal's own state is,
and the staged state is from each stash clear that succeeds: the one case
split every frame of the signal below is an instance of. -/
theorem interruptSignal_of {P : SystemState → Prop} (ntfn : SeLe4n.ObjId)
    (badge : SeLe4n.Badge) (c : CoreId) (st : SystemState)
    (hSig : P (notificationSignalBoundOnCore ntfn badge c st).1)
    (hStage : ∀ r s2, notificationSignalBoundOnCore ntfn badge c st =
        ((notificationSignalBoundOnCore ntfn badge c st).1, .ok r) →
      clearWokenReceiverStash ((boundDeliveryTarget? st ntfn).map (·.1))
        (notificationSignalBoundOnCore ntfn badge c st).1 = .ok ((), s2) →
      P (Architecture.stageWokenDelivery
        (Architecture.stageWokenDelivery s2 ((boundDeliveryTarget? st ntfn).map (·.1)) 0)
        (notificationSignalWaiter? st ntfn) 0)) :
    P (interruptSignal ntfn badge c st) := by
  unfold interruptSignal
  rcases hR : notificationSignalBoundOnCore ntfn badge c st with ⟨s1, _ | r⟩
  · rw [hR] at hSig; exact hSig
  · rw [hR] at hSig hStage
    dsimp only at hSig hStage ⊢
    split
    · next s2 hC => exact hStage r s2 rfl hC
    · exact hSig

/-- `interruptSignal` restated, the fallback of its compiled form. -/
def interruptSignalGeneral (ntfn : SeLe4n.ObjId) (badge : SeLe4n.Badge) (c : CoreId)
    (st : SystemState) : SystemState :=
  match notificationSignalBoundOnCore ntfn badge c st with
  | (s1, .ok _) =>
      match clearWokenReceiverStash ((boundDeliveryTarget? st ntfn).map (·.1)) s1 with
      | .ok ((), s2) =>
          Architecture.stageWokenDelivery
            (Architecture.stageWokenDelivery s2 ((boundDeliveryTarget? st ntfn).map (·.1)) 0)
            (notificationSignalWaiter? st ntfn) 0
      | .error _ => s1
  | (s1, .error _) => s1

/-- **The interrupt's signal as compiled**: a signal that wakes its
notification's head waiter, with no bound receiver and every write in its slot
(`signalWakesInPlace`), writes the badge frame straight into the waiter's saved
registers (`performSignalWokenDelivered`), as the `.notificationSignal`
syscall's arm does (`notificationSignalCheckedArmR`); a signal whose bound
thread is blocked receiving, every write of its removal in its slot
(`queueRemoveInPlace`), delivers the badge frame to that thread
(`performSignalBoundDelivered`); a signal with neither a bound receiver nor a
waiter wakes no thread, so it clears no stash and stages nothing, and is the
signal's own state; every other signal runs the specification. -/
@[inline] def interruptSignalImpl (ntfn : SeLe4n.ObjId) (badge : SeLe4n.Badge) (c : CoreId)
    (st : SystemState) : SystemState :=
  if (boundDeliveryTarget? st ntfn).isNone then
    match st.getNotification? ntfn with
    | some n =>
        match n.waitHeadCode with
        | k + 1 =>
            if signalWakesInPlace st ntfn ⟨k⟩ then
              performSignalWokenDelivered st ntfn ⟨k⟩ (ntfnSuccessorCode st ⟨k⟩) badge c
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
                        performSignalBoundDelivered c ⟨k⟩ ⟨tcb.ipcObjectCode⟩ ep tcb badge st
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
          simp only [interruptSignal, notificationSignalBoundOnCore, hBound,
            notificationSignalOnCore_eq_impl, notificationSignalOnCoreImpl, hN, hHead, hW,
            ↓reduceIte, Option.map_none, clearWokenReceiverStash,
            Architecture.stageWokenDelivery_none, notificationSignalWaiter?]
          rw [← optCode_ntfnSuccessor?, ← signalWoken_eq_delivered _ _ _ _ _ _ hNo]
        · exact hG
      · next hK =>
        have hHead : n.waitHead = none := by
          rw [← Notification.ofOptCode_waitHeadCode, hK]; rfl
        have hW : notificationSignalWaiter? st ntfn = none := by
          simp only [notificationSignalWaiter?, hN, hHead]
        simp only [interruptSignal, hBound, hW, Option.map_none, clearWokenReceiverStash,
          Architecture.stageWokenDelivery_none]
        split <;> next h => rw [h]
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
                have hNo : st.objects.noResizeDue := by
                  have hQ' := hQ
                  unfold queueRemoveInPlace at hQ'
                  simp only [Bool.and_eq_true] at hQ'
                  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, hFE⟩, -⟩, -⟩, -⟩, -⟩ := hQ'
                  exact RobinHood.RHTable.noResizeDue_of_findsInPlace hFE
                have hWait := notificationSignalWaiter?_of_boundDeliveryTarget st ntfn ⟨k⟩
                  ⟨tcb.ipcObjectCode⟩ hBT
                rw [← hG]
                unfold interruptSignalGeneral
                rw [notificationSignalBoundOnCore_bound_eq ntfn badge c st ⟨k⟩ ⟨tcb.ipcObjectCode⟩
                  ep tcb hBT hE hTT hQ]
                simp only [hBT, Option.map_some, clearWokenReceiverStash_eq_pure, hWait,
                  Architecture.stageWokenDelivery_none]
                rw [signalBound_eq_writes _ _ _ _ _ _ _ hNo]
                rfl
              · exact hG
            all_goals exact hG
          · exact hG
        all_goals exact hG
      all_goals exact hG
    · exact hG

/-- **seL4's `handleInterrupt` on core `c`**: the bound handler's notification
signalled (`interruptSignal`, the badge staged into the thread it wakes) and
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
    (fun ntfn _ _ => interruptSignal_of (P := fun s => s.objects.invExt) ntfn _ c st
      (notificationSignalBoundOnCore_preserves_objects_invExt _ _ _ st h)
      (fun _ s2 _ hC => stageWokenDelivery_preserves_objects_invExt _ _ _
        (stageWokenDelivery_preserves_objects_invExt _ _ _
          (clearWokenReceiverStash_preserves_objects_invExt _ _ ((), s2)
            (notificationSignalBoundOnCore_preserves_objects_invExt _ _ _ st h) hC))))

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
    (fun ntfn _ _ => interruptSignal_of
      (P := fun s => s.scheduler.replenishQueueOnCore d = st.scheduler.replenishQueueOnCore d)
      ntfn _ c st (notificationSignalBoundOnCore_replenishQueueOnCore _ _ _ st d)
      (fun _ s2 _ hC => by
        dsimp only
        rw [Architecture.stageWokenDelivery_scheduler_eq,
          Architecture.stageWokenDelivery_scheduler_eq,
          clearWokenReceiverStash_scheduler_eq _ _ ((), s2) hC]
        exact notificationSignalBoundOnCore_replenishQueueOnCore _ _ _ st d))

end SeLe4n.Kernel
