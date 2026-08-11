/-
  seLe4n — the hardware context-restore seam flag.

  WS-SM SM8.B (PR #861 review round 29).

  This module exists only to hold one `Bool` low enough in the import graph
  that every consumer can read the *same* one.

  It was defined in `Scheduler/PriorityInheritance/PerCore.lean`, which the
  `SchedContext` per-core operations cannot import: the edge closes a cycle
  through `Kernel.API` / `Model.FreezeProofs` / `Platform.Boot`.  The tempting
  workaround — a second literal at the second site — is exactly the defect
  round 20 fixed, where a guard and the register describing it carried
  independent copies and could drift.  A flag whose whole purpose is to be
  flipped once, everywhere, in one commit must have one definition, so the
  definition moves down instead of being duplicated.

  Deliberately importless.  Anything this module imported could later grow an
  edge back to a consumer and reintroduce the cycle it exists to avoid.
-/
prelude
import Init.Prelude

namespace SeLe4n.Kernel.PriorityInheritance

/-- WS-SM SM8.B (PR #861 review round 20): **is the hardware context-restore
seam live?**

`false` until SM9.E, and the single source of truth for that fact — the
`contextRestoreWired` register (`Scheduler/PriorityInheritance/PerCore.lean`)
reads it rather than carrying its own literals, as do the two live guards
`scheduleLocalSuccessorLive` and the `.schedContextUnbind` local reschedule, so
none of them can drift and the flip is one constant.

Three things must land together before it becomes `true`, and none of them fits
a non-interference cut: a `VSpaceRoot → TTBR0` binding (the model carries an
ASID and an abstract `VAddr → PAddr` table, not a translation-table physical
base), a full outgoing-frame save (`writeFfiRegistersToTcb` spills only x0..x5
and x7, so `regsOnCore` is stale for x6, x8..x30, SP and PC), and per-core
staging (the kernel-entry lock closes in `dispatch_svc` before the trap handler
would install). -/
def contextRestoreSeamLive : Bool := false

end SeLe4n.Kernel.PriorityInheritance
