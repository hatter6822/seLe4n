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

/-! # IPC Dual-Queue — Re-export Hub

Decomposed into:
- **Core**: Dual-queue endpoint operations (storeTcbQueueLinks, endpointQueuePopHead,
  endpointQueueEnqueue, endpointQueueRemoveDual).
- **Transport**: Transport lemmas proving scheduler/object/endpoint/notification
  backward preservation for all dual-queue primitives.
- **WithCaps**: IPC cap transfer wrappers (M-D01/WS-M3) — compose existing
  dual-queue operations with `ipcUnwrapCaps` for capability transfer during
  rendezvous.
-/
