import SeL4.Model.KernelState

namespace SeL4
namespace Spec
open Model

/-- Object invariants expected from the abstract object graph. -/
def ObjectsWellFormed (s : KernelState) : Prop :=
  (∀ tcb, tcb ∈ s.runnableQueue → (s.threads tcb).isSome) ∧
  (s.threads s.currentThread).isSome

end Spec
end SeL4
