/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.Operations.Endpoint
import SeLe4n.Kernel.IPC.Operations.SchedulerLemmas

/-! # IPC Operations — Re-export Hub

Decomposed into:
- **Endpoint**: Core IPC operations (removeRunnable, ensureRunnable,
  storeTcbIpcState, storeTcbIpcStateAndMessage, storeTcbPendingMessage,
  endpoint send/receive/reply, notification signal/wait) and notification
  transport lemmas.
- **SchedulerLemmas**: Scheduler preservation lemmas for removeRunnable and
  ensureRunnable, plus supporting lemmas for storeTcbIpcStateAndMessage and
  storeTcbPendingMessage.
-/
