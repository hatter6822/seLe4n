/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.DualQueue.Core
import SeLe4n.Kernel.IPC.DualQueue.Transport
import SeLe4n.Kernel.IPC.DualQueue.WithCaps
import SeLe4n.Kernel.IPC.Operations.Timeout

/-! # IPC Dual-Queue — Re-export Hub

Decomposed into:
- **Core**: Dual-queue endpoint operations (storeTcbQueueLinks, endpointQueuePopHead,
  endpointQueueEnqueue, endpointQueueRemove).
- **Transport**: Transport lemmas proving scheduler/object/endpoint/notification
  backward preservation for all dual-queue primitives.
- **Timeout**: Z6 timeout-driven IPC unblocking (timeoutThread, timeoutAwareReceive).
- **WithCaps**: IPC cap transfer wrappers (M-D01/WS-M3) — compose existing
  dual-queue operations with `ipcUnwrapCaps` for capability transfer during
  rendezvous.

**AN3-F (IPC LOW #4) re-export policy.**  This hub re-exports every IPC
dual-queue module.  The sibling hub `SeLe4n.Kernel.IPC.Operations`
re-exports the core operation family plus `Donation.Primitives` (per
AN3-A / H-01), but deliberately does NOT re-export
`SeLe4n.Kernel.IPC.Operations.Donation` (the transport-dependent
donation wrappers) because doing so would reintroduce the
`Operations -> Donation -> Transport -> Core -> Operations` import
cycle closed by AI4-A.  Consumers that want the transport-dependent
donation wrappers (`endpointCallWithDonation`, etc.) must import
`SeLe4n.Kernel.IPC.Operations.Donation` directly — this is a
prescriptive policy, not an accidental omission.  New IPC modules
must honour the hub symmetry by exporting their primitives through
`Operations` (if transport-independent) or through `DualQueue` /
direct import (if transport-dependent).
-/
