-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Capability.Invariant.Preservation.BadgeIpcCapsAndCdtMaps

/-!
# AN4-F.3 (CAP-M03): `Capability.Invariant.Preservation` hub

This module is a thin re-export hub after the AN4-F.3 split of the former
monolithic 2464-LOC `Preservation.lean`. All preservation theorems now live
in six child modules — each owning a semantically coherent slice of the
former file — and the original public API is preserved byte-for-byte:

| Child module                              | Subject matter                                                            |
|-------------------------------------------|---------------------------------------------------------------------------|
| `Preservation.Insert`                     | `cspaceLookupSlot` / `cspaceInsertSlot` / `cspaceMint` base preservation  |
| `Preservation.Delete`                     | `cspaceDeleteSlotCore` / `cspaceDeleteSlot` / `cspaceRevoke` base         |
| `Preservation.CopyMoveMutate`             | `cspaceCopy` / `cspaceMove` / `cspaceMintWithCdt` / `cspaceMutate`        |
| `Preservation.Revoke`                     | `processRevokeNode` + `cspaceRevokeCdt` (+ strict/streaming variants)     |
| `Preservation.EndpointReplyAndLifecycle`  | `endpointReply` + `coreIpcInvariantBundle` + `lifecycleRetypeObject` / `lifecycleRevokeDeleteRetype` preservation cluster |
| `Preservation.BadgeIpcCapsAndCdtMaps`     | Mint/Mutate badge preservation + `ipcTransferSingleCap` / `ipcUnwrapCaps` variants + `cdtMapsConsistent` preservation + CDT composition witnesses |

The children form a linear import chain
(`Insert ← Delete ← CopyMoveMutate ← Revoke ← EndpointReplyAndLifecycle ←
BadgeIpcCapsAndCdtMaps`). The hub re-exports the tail of that chain so
every downstream consumer sees the union of all preservation theorems.

**Migration discipline**: theorem names, statements, proofs, and relative
ordering are unchanged across the split. Private helpers were promoted to
public at file-boundary scope so sibling children can reference them
without re-proving. The promotion is the only structural change — the
proof surface is byte-identical to the pre-split file.
-/

namespace SeLe4n.Kernel

end SeLe4n.Kernel
