/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.Operations.Endpoint
import SeLe4n.Kernel.IPC.Operations.SchedulerLemmas
import SeLe4n.Kernel.IPC.Operations.CapTransfer
-- Note: Donation.lean is NOT re-exported here to avoid import cycles.
-- It imports Transport.lean which depends on this module.
-- Import SeLe4n.Kernel.IPC.Operations.Donation directly where needed.

/-! # IPC Operations — Re-export Hub

Decomposed into:
- **Endpoint**: Core IPC operations (removeRunnable, ensureRunnable,
  storeTcbIpcState, storeTcbIpcStateAndMessage, storeTcbPendingMessage,
  endpoint send/receive/reply, notification signal/wait) and notification
  transport lemmas.
- **SchedulerLemmas**: Scheduler preservation lemmas for removeRunnable and
  ensureRunnable, plus supporting lemmas for storeTcbIpcStateAndMessage and
  storeTcbPendingMessage.
- **CapTransfer**: IPC capability transfer operations (M-D01/WS-M3) —
  `ipcUnwrapCaps` batch operation with Grant-right gate.
-/
