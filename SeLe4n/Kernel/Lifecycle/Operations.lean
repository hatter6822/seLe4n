-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Lifecycle.Operations.RetypeWrappers

/-!
# AN4-G.5 (LIF-M05): `Lifecycle.Operations` hub

This module is a thin re-export hub after the AN4-G.5 split of the former
monolithic 1600-LOC `Operations.lean`. All lifecycle retype-path
primitives, preservation theorems, and production wrappers now live in
four child modules:

| Child module                                 | Subject matter                                                                 |
|----------------------------------------------|--------------------------------------------------------------------------------|
| `Operations.Cleanup`                         | `lifecycleRetypeAuthority`, `removeThreadFromQueue`, `spliceOutMidQueueNode`, `removeFromAll{Endpoint,Notification}Queues`, `cleanupDonatedSchedContext`, `cleanupTcbReferences` |
| `Operations.CleanupPreservation`             | Cleanup-primitive preservation theorems, `detachCNodeSlots`, `lifecyclePreRetypeCleanup`, `lifecycleCleanupPipeline` (AN4-G.2), `Internal.lifecycleRetypeObject` (AN4-A), `lifecycleRevokeDeleteRetype` |
| `Operations.ScrubAndUntyped`                 | `scrubObjectMemory` + frame theorems, `retypeFromUntyped` def + capacity / freshness / atomicity / error-path theorems |
| `Operations.RetypeWrappers`                  | Production entry points: `lifecycleRetypeWithCleanup`, WS-K-D dispatch helpers, `lifecycleRetypeDirect*` variants |

The children form a linear import chain
(`Cleanup ← CleanupPreservation ← ScrubAndUntyped ← RetypeWrappers`). The
hub re-exports the tail so every downstream consumer sees the union of
all lifecycle operations and proofs.

**Migration discipline**: theorem names, statements, and relative order
are unchanged across the split. One proof — `removeFromAllEndpointQueues_preserves`
— was rewritten to apply `RHTable.fold_preserves` directly against a
bundled triple invariant (`scheduler ∧ lifecycle ∧ serviceRegistry`
equalities) instead of the former `epFold` helper that relied on
syntactic `let ep' : Endpoint := ...` pattern matching. The rewrite
eliminated a cross-file elaboration fragility where `unfold` through
an imported sibling module reshaped the `let` binder into `have` and
broke the subsequent `rw`. Every other theorem is moved byte-identically.
Private helpers were promoted to public at file-boundary scope so
sibling children can reference them without re-proving. The `Internal`
namespace (AN4-A) is defined in `CleanupPreservation` where
`lifecycleRetypeObject` is declared; `ScrubAndUntyped` and
`RetypeWrappers` re-enable the bare name via `open Internal` as allowed
by `scripts/lifecycle_internal_allowlist.txt`.
-/

namespace SeLe4n.Kernel

end SeLe4n.Kernel
