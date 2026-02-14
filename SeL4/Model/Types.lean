namespace SeL4
namespace Model

abbrev ThreadId : Type := Nat
abbrev EndpointId : Type := Nat
abbrev NotificationId : Type := Nat
abbrev CNodeId : Type := Nat
abbrev CapabilitySlot : Type := Nat

/-- Rights attached to a capability. -/
inductive Rights where
  | read
  | write
  | grant
  deriving DecidableEq, Repr

/-- Capability references to kernel objects. -/
inductive Capability where
  | nullCap
  | threadCap (tid : ThreadId)
  | endpointCap (eid : EndpointId) (rights : List Rights)
  | notificationCap (nid : NotificationId)
  | cnodeCap (cid : CNodeId)
  deriving DecidableEq, Repr

/-- User-facing system call surface we model initially. -/
inductive Syscall where
  | send (endpoint : EndpointId) (message : List Nat)
  | recv (endpoint : EndpointId)
  | yield
  | mintCap (srcCNode : CNodeId) (srcSlot : CapabilitySlot)
  deriving DecidableEq, Repr

end Model
end SeL4
