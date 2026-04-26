-- SPDX-License-Identifier: GPL-3.0-or-later
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
import SeLe4n.Kernel.IPC.Operations.Donation.Primitives

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
- **Donation.Primitives** (AN3-A / H-01): transport-independent donation
  helpers (`applyCallDonation`, `applyReplyDonation`, plus all
  `*_scheduler_eq` / `*_machine_eq` / `*_atomicRegion` preservation theorems
  and server-binding witnesses). This is the symmetric counterpart to
  Timeout/WithCaps re-exports — `Donation.Primitives` depends only on
  `Endpoint.lean`, so adding it to the hub does NOT reintroduce the
  `Operations -> Donation -> Transport -> Core -> Operations` cycle.

The transport-dependent donation wrappers
(`endpointCallWithDonation`, `endpointReplyWithDonation`,
`endpointReplyRecvWithDonation`) remain in
`SeLe4n.Kernel.IPC.Operations.Donation` and are importable directly from
consumers that need them; they are NOT re-exported here by design (see
AN3-A in `docs/dev_history/audits/AUDIT_v0.30.6_WORKSTREAM_PLAN.md` §6).
-/
