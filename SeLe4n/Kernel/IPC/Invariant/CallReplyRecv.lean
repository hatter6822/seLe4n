-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.Invariant.CallReplyRecv.Call
import SeLe4n.Kernel.IPC.Invariant.CallReplyRecv.ReplyRecv

/-! # CallReplyRecv Preservation — Re-Export Hub (AN3-D)

Split per AN3-D (IPC-M04 / Theme 4.7):
* `Call` — `endpointCall` preservation witnesses
* `ReplyRecv` — `endpointReplyRecv`, `endpointReply`, `endpointCallWithCaps`
  preservation witnesses + `endpointCall_preserves_objects_invExt`

All theorems preserved unchanged; no renames, no reorderings.
-/
