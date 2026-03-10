import SeLe4n.Kernel.IPC.DualQueue.Core
import SeLe4n.Kernel.IPC.DualQueue.Transport

/-! # IPC Dual-Queue — Re-export Hub

Decomposed into:
- **Core**: Dual-queue endpoint operations (storeTcbQueueLinks, endpointQueuePopHead,
  endpointQueueEnqueue, endpointQueueRemoveDual).
- **Transport**: Transport lemmas proving scheduler/object/endpoint/notification
  backward preservation for all dual-queue primitives.
-/
