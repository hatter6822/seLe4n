-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Lifecycle.Operations.RetypeWrappers
import SeLe4n.Kernel.Lifecycle.Operations.CarvedObjectErase
import SeLe4n.Kernel.Lifecycle.Operations.UntypedReset
import SeLe4n.Kernel.Lifecycle.Operations.RetypePerform
import SeLe4n.Kernel.Lifecycle.Operations.SetSpace

/-!
# `Lifecycle.Operations` hub

A thin re-export hub over the lifecycle child modules:

| Child module                                 | Subject matter                                                                 |
|----------------------------------------------|--------------------------------------------------------------------------------|
| `Operations.Cleanup`                         | `lifecycleRetypeAuthority`, `removeThreadFromQueue`, `spliceOutMidQueueNode`, `removeFromAll{Endpoint,Notification}Queues`, `cleanupDonatedSchedContext`, `cleanupTcbReferences` |
| `Operations.CleanupPreservation`             | Cleanup-primitive preservation theorems, `detachCNodeSlots`, `lifecyclePreRetypeCleanup`, `lifecycleCleanupPipeline` — the destroy-path cleanup a capability's finalisation will call |
| `Operations.ScrubAndUntyped`                 | the object-identifier address-space guard, the carve (`CarveRequest`, `retypeFromUntyped`) + capacity / alignment / freshness / atomicity / error-path theorems |
| `Operations.RetypeWrappers`                  | A released ASID's shootdown round, and the carve-scrub discharge |
| `Operations.CarvedObjectErase`               | The store's erase of a carved object (`retireCarvedObject`), which the final-delete retire runs |
| `Operations.UntypedReset`, `RetypePerform`, `SetSpace` | The reset (seL4's `resetUntypedCap`), the carve's dispatch-level entry, and the space-slot write |

**WS-ZA ZA5.4 part 14**: there is no in-place retype.  Every kernel object is
carved from an untyped at its free index (`untypedRetypeObject`), so the
`Internal` namespace that hid the bypass primitive is gone, and with it the
consumer allowlist that fenced it.
-/

namespace SeLe4n.Kernel

end SeLe4n.Kernel
