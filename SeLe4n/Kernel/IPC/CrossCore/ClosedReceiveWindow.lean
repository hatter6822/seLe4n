-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.CrossCore.DeliveredInPlace
import SeLe4n.Kernel.IPC.DualQueue.WithCaps
import SeLe4n.Kernel.IPC.CrossCore.EndpointCallInPlace

/-!
# A rendezvous whose receiver can take no capability

seL4's `transferCaps` transfers nothing to a receiver with no IPC buffer: the
caps-unwrapped bits and the extra-caps count it reports are both zero, and no
slot is written.  The specification reads the receiver's side of the transfer
from the pre-state (`receiverCapTarget?`), and a receiver whose buffer the
kernel cannot write has none (`receiveWindowClosed`): the transfer is then the
identity on the state and reports nothing (`receiveTransferCaps_of_windowClosed`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- **Can the receiver take no capability?**  `r` has no IPC buffer the kernel
may write (or is no thread), so a capability transfer to it transfers none. -/
def receiveWindowClosed (st : SystemState) (r : SeLe4n.ThreadId) : Bool :=
  (receiverCapTarget? st r).isNone

/-- **A transfer to a receiver that can take no capability is the identity and
reports none.** -/
theorem receiveTransferCaps_of_windowClosed
    (req : Option (SeLe4n.ObjId × Array SeLe4n.CPtr × Nat)) (endpointId : SeLe4n.ObjId)
    (st : SystemState) :
    receiveTransferCaps req endpointId none st = .ok ({ results := #[] }, st) := by
  unfold receiveTransferCaps
  rcases req with _ | ⟨sroot, addrs, depth⟩
  · rfl
  · simp only []
    split <;> rfl

/-- The closed window, as the target the specification reads. -/
theorem receiverCapTarget?_of_windowClosed {st : SystemState} {r : SeLe4n.ThreadId}
    (h : receiveWindowClosed st r = true) : receiverCapTarget? st r = none :=
  Option.isNone_iff_eq_none.mp h

end SeLe4n.Kernel
