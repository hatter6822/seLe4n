-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Capability.FrameFinalise
import SeLe4n.Kernel.Architecture.InterruptMask

/-!
# WS-ZA ZA6.32 — the interrupt-control and interrupt-handler invocations

seL4's interrupt interface, over the interrupt nodes the boot installs (one
CNode of one slot per line, `SeLe4n.Model.irqNodeId`):

* `irqControlGet` — `seL4_IRQControl_Get`: a line the board has
  (`Arch_checkIRQ`) and that no handler holds (`isIRQActive`) is put at
  `IRQSignal` and its handler capability is issued into an empty slot, as a
  derivation child of the interrupt-control capability (`cteInsert`), so a
  revocation of that capability reaches every handler it issued.
* `irqHandlerSetNotification` — `seL4_IRQHandler_SetNotification`: the line's
  node slot emptied (`cteDeleteOne`) and a copy of a notification capability
  with the send right inserted there, as a derivation child of the capability
  it copies (`cteInsert`).
* `irqHandlerClear` — `seL4_IRQHandler_Clear`: the node slot emptied.

The handler's last capability's delete ends the line (`retireIrqNode`,
`finaliseCap`'s `deletingIRQHandler` and `deletedIRQHandler`): a handler
capability names its line's node (`Capability.namedObject`), so the final
delete empties the node's slot first and then retires the node, which puts the
line at `IRQInactive`.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- **The line checks of `seL4_IRQControl_Get`**, read before any write:
`.invalidIrq` for a line that is no device line of the board (`Arch_checkIRQ`)
or that has no interrupt node, and `.revocationRequired` for a line a handler
already holds (`isIRQActive`, seL4's `RevokeFirst`). -/
@[inline] def irqControlLineRefusal (st : SystemState) (line : Nat) : Option KernelError :=
  if !Architecture.deviceInterruptLine st line then some .invalidIrq
  else if (st.getCNode? (irqNodeId line)).isNone then some .invalidIrq
  else if st.irqSignalLines.mem line then some .revocationRequired
  else none

/-- **`seL4_IRQControl_Get`'s checks**, read before any write: the line
checks (`irqControlLineRefusal`) and the destination's (`cspaceDstAdmitted`, an
addressable empty slot of a CNode, seL4's `ensureEmptySlot`). -/
@[inline] def irqControlGetAdmitted (st : SystemState) (dst : CSpaceAddr) (line : Nat) : Bool :=
  (irqControlLineRefusal st line).isNone && cspaceDstAdmitted dst st

/-- **`seL4_IRQControl_Get`'s writes**, in place: the line put at `IRQSignal`
(`setIRQState`), then the handler capability installed at `dst` as a derivation
child of the interrupt-control capability's slot `control` (`cteInsert`). -/
def irqControlGetPerform (control dst : CSpaceAddr) (line : Nat) (st : SystemState) :
    SystemState :=
  cspaceInstallPerform control dst (Capability.irqHandlerOf line) .mint
    (Architecture.setIrqLineSignal st line true)

/-- **`seL4_IRQControl_Get`**: the checks, then the line put at `IRQSignal`,
the handler capability inserted at `dst`, and the derivation edge from the
interrupt-control capability's slot `control` recorded (`cteInsert`), so a
revocation of that capability reaches every handler it issued. -/
def irqControlGet (control dst : CSpaceAddr) (line : Nat) : Kernel Unit :=
  fun st =>
    match irqControlLineRefusal st line with
    | some e => .error e
    | none =>
      match cspaceInsertSlot dst (Capability.irqHandlerOf line)
          (Architecture.setIrqLineSignal st line true) with
      | .error e => .error e
      | .ok ((), st') => .ok ((), st'.cdtAddChild control dst .mint)

/-- An admitted issue is its in-place writes. -/
theorem irqControlGet_of_admitted {control dst : CSpaceAddr} {line : Nat} {st : SystemState}
    (h : irqControlGetAdmitted st dst line = true) :
    irqControlGet control dst line st = .ok ((), irqControlGetPerform control dst line st) := by
  unfold irqControlGetAdmitted at h
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at h
  obtain ⟨hR, hD⟩ := h
  have hD' : cspaceDstAdmitted dst (Architecture.setIrqLineSignal st line true) = true := by
    unfold cspaceDstAdmitted at hD ⊢
    simpa [SystemState.getCNode?, SystemState.getObject?] using hD
  simp only [irqControlGet, hR, cspaceInsertSlot_of_admitted hD', irqControlGetPerform,
    cspaceInstallPerform]

/-- **Whether a capability may be bound to an interrupt line**: a notification
capability carrying the send right (seL4's `isNotificationCap` and
`capNtfnCanSend` in `decodeIRQHandlerInvocation`). -/
@[inline] def irqNotificationCapAdmitted (st : SystemState) (cap : Capability) : Bool :=
  match cap.target with
  | .object n => cap.hasRight .write && (st.getNotification? n).isSome
  | _ => false

/-- **`seL4_IRQHandler_SetNotification`**: the capability in `src` (the
notification capability the caller named) bound to line `line`: refused unless it
is a notification capability with the send right and the line has its node;
then the node slot emptied by the finalising delete every slot delete is
(`cspaceDeleteSlotZombie`, seL4's `cteDeleteOne`), and the capability copied
there as a derivation child of `src` (`cteInsert`). -/
def irqHandlerSetNotification (executingCore : Concurrency.CoreId) (line : Nat)
    (src : CSpaceAddr) : Kernel Unit :=
  fun st =>
    match st.lookupSlotCap src with
    | none => .error .invalidCapability
    | some cap =>
      if !irqNotificationCapAdmitted st cap then .error .invalidCapability
      else if !cnodeInvoked (irqNodeId line) st then .error .objectNotFound
      else
        match cspaceDeleteSlotZombie executingCore (irqNodeAddr line) st with
        | .error e => .error e
        | .ok ((), st1) => cspaceCopy src (irqNodeAddr line) st1

/-- **`seL4_IRQHandler_Clear`**: the line's node slot emptied by the finalising
delete (`cspaceDeleteSlotZombie`, seL4's `cteDeleteOne`), so the line signals
nothing until a notification is set again. -/
def irqHandlerClear (executingCore : Concurrency.CoreId) (line : Nat) : Kernel Unit :=
  fun st =>
    if !cnodeInvoked (irqNodeId line) st then .error .objectNotFound
    else cspaceDeleteSlotZombie executingCore (irqNodeAddr line) st

end SeLe4n.Kernel
