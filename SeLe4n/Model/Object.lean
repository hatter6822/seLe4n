import SeLe4n.Prelude

namespace SeLe4n.Model

inductive AccessRight where
  | read
  | write
  | grant
  | grantReply
  deriving Repr, DecidableEq

/-- The addressable target of a capability in the abstract object universe. -/
inductive CapTarget where
  | object (id : SeLe4n.ObjId)
  | cnodeSlot (cnode : SeLe4n.ObjId) (slot : SeLe4n.Slot)
  deriving Repr, DecidableEq

structure Capability where
  target : CapTarget
  rights : List AccessRight
  badge : Option SeLe4n.Badge := none
  deriving Repr, DecidableEq

namespace Capability

def hasRight (cap : Capability) (right : AccessRight) : Bool :=
  right ∈ cap.rights

end Capability

/-- Minimal per-thread IPC scheduler-visible status for M3.5 handshake scaffolding.

This is intentionally narrow: only endpoint-local blocking states needed to model one deterministic
waiting-thread handshake story. -/
inductive ThreadIpcState where
  | ready
  | blockedOnSend (endpoint : SeLe4n.ObjId)
  | blockedOnReceive (endpoint : SeLe4n.ObjId)
  deriving Repr, DecidableEq

structure TCB where
  tid : SeLe4n.ThreadId
  priority : SeLe4n.Priority
  domain : SeLe4n.DomainId
  cspaceRoot : SeLe4n.ObjId
  vspaceRoot : SeLe4n.ObjId
  ipcBuffer : SeLe4n.VAddr
  ipcState : ThreadIpcState := .ready
  deriving Repr, DecidableEq

inductive EndpointState where
  | idle
  | send
  | receive
  deriving Repr, DecidableEq

structure Endpoint where
  state : EndpointState
  queue : List SeLe4n.ThreadId
  waitingReceiver : Option SeLe4n.ThreadId := none
  deriving Repr, DecidableEq

structure CNode where
  guard : Nat
  radix : Nat
  slots : List (SeLe4n.Slot × Capability)
  deriving Repr, DecidableEq

namespace CNode

def empty : CNode :=
  { guard := 0, radix := 0, slots := [] }

def lookup (node : CNode) (slot : SeLe4n.Slot) : Option Capability :=
  (node.slots.find? (fun entry => entry.fst = slot)).map Prod.snd

def insert (node : CNode) (slot : SeLe4n.Slot) (cap : Capability) : CNode :=
  let slots := (slot, cap) :: node.slots.filter (fun entry => entry.fst ≠ slot)
  { node with slots }

def remove (node : CNode) (slot : SeLe4n.Slot) : CNode :=
  { node with slots := node.slots.filter (fun entry => entry.fst ≠ slot) }

/-- Local revoke helper for the current modeled slice.

This keeps the authority-bearing source slot while deleting sibling slots in the same CNode that
name the same capability target. Full cross-CNode revoke requires an explicit derivation graph and
is intentionally deferred. -/
def revokeTargetLocal (node : CNode) (sourceSlot : SeLe4n.Slot) (target : CapTarget) : CNode :=
  {
    node with
      slots := node.slots.filter (fun entry => entry.fst = sourceSlot ∨ entry.snd.target ≠ target)
  }

theorem lookup_remove_eq_none (node : CNode) (slot : SeLe4n.Slot) :
    (node.remove slot).lookup slot = none := by
  unfold remove lookup
  simp

theorem lookup_revokeTargetLocal_source_eq_lookup
    (node : CNode)
    (sourceSlot : SeLe4n.Slot)
    (target : CapTarget) :
    (node.revokeTargetLocal sourceSlot target).lookup sourceSlot = node.lookup sourceSlot := by
  unfold revokeTargetLocal lookup
  have hPred :
      (fun entry : SeLe4n.Slot × Capability =>
        (decide (entry.fst = sourceSlot) || !decide (entry.snd.target = target)) &&
          decide (entry.fst = sourceSlot)) =
      (fun entry : SeLe4n.Slot × Capability => decide (entry.fst = sourceSlot)) := by
    funext entry
    by_cases hEq : entry.fst = sourceSlot <;> simp [hEq]
  simp [hPred]

end CNode

inductive KernelObject where
  | tcb (t : TCB)
  | endpoint (e : Endpoint)
  | cnode (c : CNode)
  deriving Repr, DecidableEq

inductive KernelObjectType where
  | tcb
  | endpoint
  | cnode
  deriving Repr, DecidableEq

namespace KernelObject

def objectType : KernelObject → KernelObjectType
  | .tcb _ => .tcb
  | .endpoint _ => .endpoint
  | .cnode _ => .cnode

end KernelObject

/-- Construct a capability that names an object directly. -/
def makeObjectCap (id : SeLe4n.ObjId) (rights : List AccessRight) : Capability :=
  { target := .object id, rights }

end SeLe4n.Model
