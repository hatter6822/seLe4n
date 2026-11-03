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
# WS-ZA ZA6.32 — masking an interrupt line

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
serves (`InterruptId`). -/
def interruptLineCount : Nat := 320

/-- **The lines a device raises**: the shared peripheral interrupts, INTIDs 32
to 319.  An SGI (0–15) is the kernel's own inter-core signal and a PPI (16–31)
is a line banked per core, which the distributor enables and disables on the
core that writes the register; neither is a line one handler capability names
for the whole machine, so neither is delivered, masked or acknowledged here. -/
@[inline] def deviceInterruptLine (line : Nat) : Bool :=
  32 ≤ line && line < interruptLineCount

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

/-- **seL4's `invokeIRQHandler_AckIRQ`**: the line the handler capability names
unmasked at the controller.  A line that is no device line is refused
(`deviceInterruptLine`), so a capability naming one acknowledges nothing. -/
def irqHandlerAck (line : Nat) : Kernel Unit := fun st =>
  if deviceInterruptLine line then .ok ((), setInterruptLineMask st line false)
  else .error .invalidIrq

/-- The acknowledge leaves the line unmasked. -/
theorem irqHandlerAck_unmasks {line : Nat} {st st' : SystemState}
    (h : irqHandlerAck line st = .ok ((), st')) : st'.machine.irqLineMasked line = false := by
  unfold irqHandlerAck at h
  split at h
  · cases h; simp
  · cases h

/-- The acknowledge's state is the mask's. -/
theorem irqHandlerAck_ok {line : Nat} {st st' : SystemState}
    (h : irqHandlerAck line st = .ok ((), st')) : st' = setInterruptLineMask st line false := by
  unfold irqHandlerAck at h
  split at h
  · cases h; rfl
  · cases h

end SeLe4n.Kernel.Architecture
