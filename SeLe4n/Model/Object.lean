import SeLe4n.Prelude

namespace SeLe4n.Model

inductive AccessRight where
  | read
  | write
  | grant
  deriving Repr, DecidableEq

structure Capability where
  target : SeLe4n.ObjId
  rights : List AccessRight
  badge : Option SeLe4n.Badge := none
  deriving Repr, DecidableEq

structure TCB where
  tid : SeLe4n.ThreadId
  priority : SeLe4n.Priority
  domain : SeLe4n.DomainId
  cspaceRoot : SeLe4n.ObjId
  vspaceRoot : SeLe4n.ObjId
  deriving Repr, DecidableEq

structure Endpoint where
  queue : List SeLe4n.ThreadId
  deriving Repr, DecidableEq

structure CNode where
  slots : SeLe4n.Slot → Option Capability

instance : Repr CNode where
  reprPrec _ _ := "CNode(<function>)"

inductive KernelObject where
  | tcb (t : TCB)
  | endpoint (e : Endpoint)
  | cnode (c : CNode)
  deriving Repr

end SeLe4n.Model
