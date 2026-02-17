import SeLe4n

open SeLe4n.Model

namespace SeLe4n.Testing

/--
Testing-only permissive runtime contract fixture.

This contract is intentionally broad to exercise success branches in adapter traces
and MUST NOT be imported by production kernel modules.
-/
def runtimeContractAcceptAll : SeLe4n.Kernel.Architecture.RuntimeBoundaryContract :=
  {
    timerMonotonic := fun st st' => st.machine.timer ≤ st'.machine.timer
    registerContextStable := fun _ _ => True
    memoryAccessAllowed := fun _ _ => True
    timerMonotonicDecidable := by
      intro st st'
      infer_instance
    registerContextStableDecidable := by
      intro st st'
      infer_instance
    memoryAccessAllowedDecidable := by
      intro st addr
      infer_instance
  }

/--
Testing-only restrictive runtime contract fixture.

This contract intentionally denies all runtime paths so tests can assert explicit
error branches in adapter semantics.
-/
def runtimeContractDenyAll : SeLe4n.Kernel.Architecture.RuntimeBoundaryContract :=
  {
    timerMonotonic := fun _ _ => False
    registerContextStable := fun _ _ => False
    memoryAccessAllowed := fun _ _ => False
    timerMonotonicDecidable := by
      intro st st'
      infer_instance
    registerContextStableDecidable := by
      intro st st'
      infer_instance
    memoryAccessAllowedDecidable := by
      intro st addr
      infer_instance
  }

end SeLe4n.Testing
