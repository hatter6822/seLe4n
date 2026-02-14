import SeL4.Model.KernelState

namespace SeL4
namespace Spec
open Model

/-- IPC consistency invariant between endpoint queues and blocked thread states. -/
def IPCQueuesConsistent (s : KernelState) : Prop :=
  ∀ endpointId endpoint,
    s.endpoints endpointId = some endpoint →
      (∀ tid, tid ∈ endpoint.sendQueue →
        ∃ tcb, s.threads tid = some tcb ∧ tcb.status = .blockedOnSend endpointId) ∧
      (∀ tid, tid ∈ endpoint.recvQueue →
        ∃ tcb, s.threads tid = some tcb ∧ tcb.status = .blockedOnReceive endpointId)

end Spec
end SeL4
