import SeL4.Model.Syscall

namespace SeL4
namespace Execution
open Model

/-- Placeholder for a pure state transition relation for syscalls. -/
def step (state : KernelState) (call : Syscall) : SyscallResult :=
  match call with
  | .yield =>
      SyscallResult.ok {
        state with
        runnableQueue := state.runnableQueue ++ [state.currentThread]
      }
  | .send endpoint _ =>
      match state.endpoints endpoint with
      | none => .invalidEndpoint
      | some _ => .blocked state
  | .recv endpoint =>
      match state.endpoints endpoint with
      | none => .invalidEndpoint
      | some _ => .blocked state
  | .mintCap _ _ => .ok state

end Execution
end SeL4
