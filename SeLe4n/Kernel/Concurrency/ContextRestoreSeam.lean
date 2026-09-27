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

`false` until SM10.1, and the single source of truth for that fact — the
`contextRestoreWired` register (`Scheduler/PriorityInheritance/PerCore.lean`)
reads it rather than carrying its own literals, as do the **three** live
guards, so none of them can drift and the flip is one constant:

* `scheduleLocalSuccessorLive` — the vacated-core successor;
* `resumeThreadOnCoreLive` — the local `.tcbResume` dispatch;
* `priorityRescheduleOnCoreLive` — the local preemption point behind
  `.tcbSetPriority` / `.tcbSetMCPriority`.

The `.schedContextUnbind` reschedule is **deliberately ungated**, and was
briefly listed here in error (PR #861 review round 37).  Round 28 asked for the
gate and round 33 showed it recreates the round-15 defect: `schedContextUnbind`
clears the executing core's `current` slot *in order to* force a reschedule, so
suppressing the tail leaves a core with no successor and nothing to resolve it.
A gate is only sound where the state it leaves behind is coherent — a gated
resume leaves the thread `.Ready` and queued, which the next tick resolves; a
gated unbind leaves half a transaction.

Three things must land before it becomes `true`, and none of them fits a
non-interference cut: a `VSpaceRoot → TTBR0` binding — landed at WS-BP BP7.2
(`v0.36.15`: each carved root owns a table page, the physical-write ledger keeps
the tables in memory, and `Platform.FFI.installThreadTranslation` installs one);
a full outgoing-frame save — landed at WS-BP BP7.3 (`v0.36.16`: every state-
committing trap entry saves `x0`–`x30`, `SP`, `PC` and `PSTATE` into the core's
bank and the current thread's context, `Architecture.saveTrapFrameOnCore`); and
per-core staging (the kernel-entry lock closes in `dispatch_svc` before the trap
handler would install) — landed at WS-BP BP7.4 (`v0.36.17`: the caller's result
is staged into its saved context before any local reschedule,
`Architecture.stageCallerReturn`, and every entry hands the HAL what its core
resumes, `Platform.FFI.restoreTrapFrameLive`, which reads this constant).  With
the three in place, what the flip waits on is BP7.5 and the trap arms (BP7.6). -/
def contextRestoreSeamLive : Bool := false

end SeLe4n.Kernel.PriorityInheritance
