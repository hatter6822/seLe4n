-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Architecture.HardwareTables

/-!
# WS-ZA ZA6.32 — an interrupt line's state, mask and node

seL4 masks an interrupt line at the interrupt controller in two places: the
interrupt entry masks a line it delivers to a notification until the handler
acknowledges it (`handleInterrupt`'s `IRQSignal` arm, then
`invokeIRQHandler_AckIRQ`), and it masks a line no handler is bound to
(`IRQInactive`).  The mask is machine state (`MachineState.setIrqLineMask`,
seL4's `irq_masks`), and the controller is told by the physical write the step
records (`PhysicalWrite.setInterruptMask`), which the committing entry performs
after the commit, as it performs every other write the step owes.

The acknowledge is `irqHandlerAck`, the operation behind the `.irqHandlerAck`
syscall on an interrupt-handler capability (`CapTarget.irqHandler`).
-/

namespace SeLe4n.Kernel.Architecture

open SeLe4n.Model

/-- The interrupt lines the model names: the 320 the BCM2712 distributor
serves (`InterruptId`), and the five mask words hold. -/
def modelInterruptLineCount : Nat := 320

/-- **The lines a device raises on a board of `count` lines**: the shared
peripheral interrupts, INTIDs 32 up to the board's line count (and inside the
model's).  An SGI (0–15) is the kernel's own inter-core signal and a PPI
(16–31) is a line banked per core, which the distributor enables and disables
on the core that writes the register; neither is a line one handler capability
names for the whole machine, so neither is delivered, masked or acknowledged
here.  A line at or past the board's count is no line the board has: seL4's
`Arch_checkIRQ` refuses an IRQ above `maxIRQ` before anything is written. -/
@[inline] def deviceInterruptLineUnder (count line : Nat) : Bool :=
  32 ≤ line && line < count && line < modelInterruptLineCount

/-- **The lines a device raises on this machine**: `deviceInterruptLineUnder`
at the board's line count, which the boot installs from the bound machine
configuration (`MachineState.interruptLineCount`,
`MachineConfig.interruptLineCount`). -/
@[inline] def deviceInterruptLine (st : SystemState) (line : Nat) : Bool :=
  deviceInterruptLineUnder st.machine.interruptLineCount line

/-! ### The interrupt node

seL4 keeps, for every interrupt line, one capability slot the kernel owns
(`intStateIRQNode`; in the abstract specification `interrupt_irq_node irq`, a
CNode of one slot per line).  `seL4_IRQHandler_SetNotification` copies a
notification capability into the line's slot as a derivation child of the
capability it copied (`cteInsert`), `seL4_IRQHandler_Clear` deletes it
(`cteDeleteOne`), and the interrupt entry signals the notification the slot's
capability names with that capability's badge.  Here each line's node is a
CNode of one slot at a reserved object id, `irqNodeId line`, installed by the
boot for every line the board has; no capability names one
(`isIrqNodeObjId`, refused by the capability resolution).  The ids live with
the state (`SeLe4n.Model.irqNodeId`), so the information-flow projection reads
them. -/

/-- **Whether a capability names an interrupt node** (an object or slot capability
whose object is one). -/
@[inline] def capTargetsIrqNode (count : Nat) (cap : Capability) : Bool :=
  match cap.target with
  | .object oid => isIrqNodeObjId count oid
  | .cnodeSlot cnode _ => isIrqNodeObjId count cnode
  | _ => false

/-- **The binding line `line` signals**, seL4's `handleInterrupt` on a line at
`IRQSignal`: the notification its node slot's capability names and that
capability's badge, when the capability is a notification capability with the
send right; none on a line at `IRQInactive`, or whose slot holds no such
capability (seL4's "undelivered" interrupt, masked all the same). -/
@[inline] def irqBinding? (st : SystemState) (line : Nat) : Option (SeLe4n.ObjId × SeLe4n.Badge) :=
  if st.irqSignalLines.mem line then
    match st.lookupSlotCap (irqNodeAddr line) with
    | some cap =>
        match cap.target with
        | .object n =>
            if cap.hasRight .write then
              match st.getObject? n with
              | some (.notification _) =>
                  some (n, if cap.badged then cap.badgeWord else SeLe4n.Badge.zero)
              | _ => none
            else none
        | _ => none
    | none => none
  else none

/-- A bound line's notification is a notification. -/
theorem irqBinding?_notification {st : SystemState} {line : Nat} {n : SeLe4n.ObjId}
    {b : SeLe4n.Badge} (h : irqBinding? st line = some (n, b)) :
    ∃ ntfn, st.getObject? n = some (.notification ntfn) := by
  unfold irqBinding? at h
  split at h
  · split at h
    · split at h
      · split at h
        · split at h
          · next ntfn hN => cases h; exact ⟨ntfn, hN⟩
          · cases h
        · cases h
      · cases h
    · cases h
  · cases h

/-- **Line `line` masked (`masked = true`) or unmasked at the interrupt
controller**: the machine's mask written and the controller's write recorded. -/
def setInterruptLineMask (st : SystemState) (line : Nat) (masked : Bool) : SystemState :=
  recordPhysicalWrites { st with machine := st.machine.setIrqLineMask line masked }
    [.setInterruptMask line masked]

/-- The mask reads back what was written. -/
@[simp] theorem setInterruptLineMask_irqLineMasked (st : SystemState) (line : Nat)
    (masked : Bool) :
    (setInterruptLineMask st line masked).machine.irqLineMasked line = masked :=
  MachineState.irqLineMasked_setIrqLineMask_self _ _ _

/-- The write the controller is owed is recorded after the writes already owed. -/
@[simp] theorem setInterruptLineMask_pendingPhysicalWrites (st : SystemState) (line : Nat)
    (masked : Bool) :
    (setInterruptLineMask st line masked).pendingPhysicalWrites =
      st.pendingPhysicalWrites ++ [.setInterruptMask line masked] := by
  unfold setInterruptLineMask
  rw [recordPhysicalWrites_pending]
  rfl

/-- The mask writes no object. -/
@[simp] theorem setInterruptLineMask_objects (st : SystemState) (line : Nat) (masked : Bool) :
    (setInterruptLineMask st line masked).objects = st.objects := rfl

/-- …and no scheduler field. -/
@[simp] theorem setInterruptLineMask_scheduler (st : SystemState) (line : Nat) (masked : Bool) :
    (setInterruptLineMask st line masked).scheduler = st.scheduler := rfl

/-- **seL4's `setIRQState`**: line `line` put at `IRQSignal` (`signal`) or at
`IRQInactive`, and masked at the controller exactly when it is inactive. -/
def setIrqLineSignal (st : SystemState) (line : Nat) (signal : Bool) : SystemState :=
  setInterruptLineMask { st with irqSignalLines := st.irqSignalLines.set line signal } line (!signal)

/-- The line's state reads back what was written. -/
@[simp] theorem setIrqLineSignal_mem (st : SystemState) {line : Nat} (signal : Bool)
    (h : line < InterruptLineSet.capacity) :
    (setIrqLineSignal st line signal).irqSignalLines.mem line = signal := by
  simp [setIrqLineSignal, setInterruptLineMask, recordPhysicalWrites_irqSignalLines, h]

/-- …and the mask is set exactly when the line goes inactive. -/
@[simp] theorem setIrqLineSignal_irqLineMasked (st : SystemState) (line : Nat) (signal : Bool) :
    (setIrqLineSignal st line signal).machine.irqLineMasked line = !signal := by
  simp [setIrqLineSignal]

/-- The state write writes no object. -/
@[simp] theorem setIrqLineSignal_objects (st : SystemState) (line : Nat) (signal : Bool) :
    (setIrqLineSignal st line signal).objects = st.objects := rfl

/-- …and no scheduler field. -/
@[simp] theorem setIrqLineSignal_scheduler (st : SystemState) (line : Nat) (signal : Bool) :
    (setIrqLineSignal st line signal).scheduler = st.scheduler := rfl

/-- **seL4's `invokeIRQHandler_AckIRQ`**: the line the handler capability names
unmasked at the controller.  A line that is no device line is refused
(`deviceInterruptLine`, a line inside the board's count), so a capability
naming one acknowledges nothing and writes nothing. -/
def irqHandlerAck (line : Nat) : Kernel Unit := fun st =>
  if deviceInterruptLine st line then .ok ((), setInterruptLineMask st line false)
  else .error .invalidIrq

/-- The acknowledge leaves the line unmasked. -/
theorem irqHandlerAck_unmasks {line : Nat} {st st' : SystemState}
    (h : irqHandlerAck line st = .ok ((), st')) : st'.machine.irqLineMasked line = false := by
  unfold irqHandlerAck at h
  split at h
  · cases h; simp
  · cases h

/-- **A line the board does not have is refused**, and the state is not
written: an acknowledge of a line at or past the board's line count is
`.invalidIrq`. -/
theorem irqHandlerAck_refuses_off_board {line : Nat} {st : SystemState}
    (h : st.machine.interruptLineCount ≤ line) :
    irqHandlerAck line st = .error .invalidIrq := by
  have hN : deviceInterruptLine st line = false := by
    simp only [deviceInterruptLine, deviceInterruptLineUnder, Bool.and_eq_false_iff,
      decide_eq_false_iff_not, Nat.not_lt]
    exact .inl (.inr h)
  simp [irqHandlerAck, hN]

/-- The acknowledge's state is the mask's. -/
theorem irqHandlerAck_ok {line : Nat} {st st' : SystemState}
    (h : irqHandlerAck line st = .ok ((), st')) : st' = setInterruptLineMask st line false := by
  unfold irqHandlerAck at h
  split at h
  · cases h; rfl
  · cases h

end SeLe4n.Kernel.Architecture
