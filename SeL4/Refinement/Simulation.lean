import SeL4.Execution.Step
import SeL4.Spec.Objects
import SeL4.Spec.Capabilities
import SeL4.Spec.IPC

namespace SeL4
namespace Refinement
open Model
open Execution
open Spec

/-- Aggregate invariant used for early refinement proofs. -/
def KernelInvariant (s : KernelState) : Prop :=
  ObjectsWellFormed s ∧ CapabilitySafe s ∧ IPCQueuesConsistent s

/-- Simulation theorem statement placeholder (to be completed incrementally). -/
theorem step_preserves_invariant
    (s : KernelState)
    (c : Syscall)
    (hInv : KernelInvariant s)
    : match step s c with
      | .ok s' => KernelInvariant s'
      | .blocked s' => KernelInvariant s'
      | .invalidCapability => True
      | .invalidEndpoint => True := by
  cases c <;> simp [step, KernelInvariant] at *

end Refinement
end SeL4
