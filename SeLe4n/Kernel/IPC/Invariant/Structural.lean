-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.Invariant.Structural.QueueNextTransport
import SeLe4n.Kernel.IPC.Invariant.Structural.StoreObjectFrame
import SeLe4n.Kernel.IPC.Invariant.Structural.DualQueueMembership
import SeLe4n.Kernel.IPC.Invariant.Structural.PerOperation

/-! # IPC Structural Preservation — Re-Export Hub (AN3-C)

Post-AN3-C, the former 7626-line `Structural.lean` has been split into
four child modules under `SeLe4n.Kernel.IPC.Invariant.Structural.*`
(see plan §6 / AN3-C of `docs/dev_history/audits/AUDIT_v0.30.6_WORKSTREAM_PLAN.md`):

* `QueueNextTransport` — intrusive-queue basics + `storeObject` /
  `ensure/removeRunnable` / `storeTcbQueueLinks` frame lemmas
* `StoreObjectFrame` — per-op `dualQueueSystemInvariant`,
  `contextMatchesCurrent`, and `allPendingMessagesBounded` frames
* `DualQueueMembership` — composed `ipcInvariantFull` witnesses,
  V3-K/J queue-membership preservation, WithCaps `ipcInvariantFull`
* `PerOperation` — M3-E4 WithCaps `dualQueueSystemInvariant` cluster
  and V3-G/V3-G4 per-operation preservation witnesses

All four are re-exported here so every legacy consumer that does
`import SeLe4n.Kernel.IPC.Invariant.Structural` keeps compiling without
changes.  No theorem was renamed, reordered, or reproven; the split is
purely a file-boundary operation.
-/
