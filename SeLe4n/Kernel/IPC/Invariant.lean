/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.Invariant.Defs
import SeLe4n.Kernel.IPC.Invariant.EndpointPreservation
import SeLe4n.Kernel.IPC.Invariant.CallReplyRecv
import SeLe4n.Kernel.IPC.Invariant.NotificationPreservation
import SeLe4n.Kernel.IPC.Invariant.QueueNoDup
import SeLe4n.Kernel.IPC.Invariant.QueueMembership
import SeLe4n.Kernel.IPC.Invariant.QueueNextBlocking
import SeLe4n.Kernel.IPC.Invariant.Structural

/-! # IPC Invariant Preservation — Re-export Hub

Decomposed into:
- **Defs**: Core invariant definitions (ipcInvariant, ipcInvariantFull,
  dualQueueSystemInvariant, ipcSchedulerContractPredicates, notification
  well-formedness, notification waiter consistency).
- **EndpointPreservation**: endpointReply, endpointSendDual, endpointReceiveDual,
  and endpointQueueRemoveDual invariant preservation proofs.
- **CallReplyRecv**: endpointCall and endpointReplyRecv compound operation
  invariant preservation proofs.
- **NotificationPreservation**: notificationSignal and notificationWait
  invariant preservation proofs.
- **Structural**: WS-H5 intrusive dual-queue structural invariants,
  contextMatchesCurrent preservation, allPendingMessagesBounded preservation,
  and ipcInvariantFull composition theorems.
-/
