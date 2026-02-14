import SeL4.Model.KernelState

namespace SeL4
namespace Model

/-- Return codes for the abstract syscall semantics. -/
inductive SyscallResult where
  | ok (state : KernelState)
  | blocked (state : KernelState)
  | invalidCapability
  | invalidEndpoint
  deriving Repr

end Model
end SeL4
