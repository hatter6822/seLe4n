import SeL4.Model.Types

namespace SeL4
namespace Model

/-- Scheduling state for a thread. -/
inductive ThreadStatus where
  | running
  | ready
  | blockedOnReceive (endpoint : EndpointId)
  | blockedOnSend (endpoint : EndpointId)
  deriving DecidableEq, Repr

structure ThreadControlBlock where
  priority : Nat
  status : ThreadStatus
  messageRegisters : List Nat
  deriving DecidableEq, Repr

structure EndpointState where
  sendQueue : List ThreadId
  recvQueue : List ThreadId
  deriving DecidableEq, Repr

structure CNodeState where
  slots : CapabilitySlot → Capability

/-- Top-level abstract kernel state for the executable specification. -/
structure KernelState where
  currentThread : ThreadId
  runnableQueue : List ThreadId
  threads : ThreadId → Option ThreadControlBlock
  endpoints : EndpointId → Option EndpointState
  cnodes : CNodeId → Option CNodeState

namespace KernelState

def empty : KernelState := {
  currentThread := 0
  runnableQueue := []
  threads := fun _ => none
  endpoints := fun _ => none
  cnodes := fun _ => none
}

end KernelState
end Model
end SeL4
