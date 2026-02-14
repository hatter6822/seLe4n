import SeL4.Refinement.Simulation

namespace SeL4
namespace Proofs
open Model
open Refinement

/-- Initial reusable theorem exposing the global invariant frame. -/
theorem invariant_of_empty_state :
    KernelInvariant Model.KernelState.empty := by
  unfold KernelInvariant Spec.ObjectsWellFormed Spec.CapabilitySafe Spec.IPCQueuesConsistent
  simp [Model.KernelState.empty]

end Proofs
end SeL4
