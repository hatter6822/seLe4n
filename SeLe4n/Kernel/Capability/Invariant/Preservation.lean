-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Capability.Invariant.Preservation.Revoke
import SeLe4n.Kernel.Capability.Invariant.Preservation.ThreadSpaceCopy
import SeLe4n.Kernel.Capability.Invariant.Preservation.Carve
import SeLe4n.Kernel.Capability.Invariant.Preservation.ZombieTermination
import SeLe4n.Kernel.Capability.Invariant.Preservation.MappingRecords
import SeLe4n.Kernel.Capability.Invariant.Preservation.SetSpaceMappingRecords

/-!
# AN4-F.3 (CAP-M03): `Capability.Invariant.Preservation` hub

This module is a thin re-export hub after the AN4-F.3 split of the former
monolithic 2464-LOC `Preservation.lean`. All preservation theorems now live
in its child modules — each owning a semantically coherent slice of the
former file — and the original public API is preserved byte-for-byte:

| Child module                              | Subject matter                                                            |
|-------------------------------------------|---------------------------------------------------------------------------|
| `Preservation.Insert`                     | `cspaceLookupSlot` / `cspaceInsertSlot` / `cspaceMint` base preservation  |
| `Preservation.Delete`                     | `cspaceDeleteSlotCore` / `cspaceDeleteSlot` / `cspaceRevoke` base         |
| `Preservation.CopyMoveMutate`             | `cspaceCopy` / `cspaceMove` / `cspaceMintWithCdt` / `cspaceMutate`        |
| `Preservation.EndpointReplyAndLifecycle`  | `endpointReply` + `coreIpcInvariantBundle` preservation cluster |
| `Preservation.BadgeIpcCapsAndCdtMaps` | Mint/Mutate badge preservation + `ipcTransferSingleCap` / `ipcUnwrapCaps` variants + CDT composition witnesses |
| `Preservation.Revoke`                     | the finalising delete and `cteRevoke` loop: bundle preservation and the revocation's completeness |
| `Preservation.ThreadSpaceCopy`            | setting a thread's space (`copyThreadSpaces`): each space slot's delete, copy and derivation edge |
| `Preservation.Carve`                      | the untyped carve (`retypeFromUntyped`, `untypedRetypeObject`): the carved object's store, the free-index write, the install and its `.retype` edge |
| `Preservation.ZombieTermination`          | the zombie loop's passes end within `zombieFuel` on every state the capability invariants hold in (`zombiePasses_end`) |
| `Preservation.MappingRecords`             | the finalising delete, the revocation and the zombie delete keep every live mapping recorded (`cspaceDeleteSlotFinalising_preserves_liveMappingsRecorded`) |
| `Preservation.SetSpaceMappingRecords`     | the thread-space set keeps every live mapping recorded (`copyThreadSpacesZombie_preserves_liveMappingsRecorded`): no thread's space slot records a mapping |

The children form a linear import chain
(`Insert ← Delete ← CopyMoveMutate ← EndpointReplyAndLifecycle ←
BadgeIpcCapsAndCdtMaps ← Revoke`), with `ThreadSpaceCopy` and `ZombieTermination` on
`Revoke`, `MappingRecords` on `Revoke`, `Carve` on `ThreadSpaceCopy` and
`SetSpaceMappingRecords` on `ThreadSpaceCopy` and `MappingRecords`. The hub
re-exports the tails of that chain, `ThreadSpaceCopy`, `Carve`, `ZombieTermination`,
`MappingRecords` and `SetSpaceMappingRecords`, so every downstream
consumer sees the union of all preservation theorems.

**Migration discipline**: theorem names, statements, proofs, and relative
ordering are unchanged across the split. Private helpers were promoted to
public at file-boundary scope so sibling children can reference them
without re-proving. The promotion is the only structural change — the
proof surface is byte-identical to the pre-split file.
-/

namespace SeLe4n.Kernel

end SeLe4n.Kernel
