import SeLe4.Prelude

namespace SeLe4.Model

inductive AccessRight where
  | read
  | write
  | grant
  deriving Repr, DecidableEq

structure Capability where
  target : SeLe4.ObjId
  rights : List AccessRight
  badge : Option Nat := none
  deriving Repr, DecidableEq

structure TCB where
  tid : SeLe4.ThreadId
  priority : SeLe4.Priority
  domain : SeLe4.DomainId
  cspaceRoot : SeLe4.ObjId
  vspaceRoot : SeLe4.ObjId
  deriving Repr, DecidableEq

structure Endpoint where
  queue : List SeLe4.ThreadId
  deriving Repr, DecidableEq

structure CNode where
  slots : Nat → Option Capability

instance : Repr CNode where
  reprPrec _ _ := "CNode(<function>)"

inductive KernelObject where
  | tcb (t : TCB)
  | endpoint (e : Endpoint)
  | cnode (c : CNode)
  deriving Repr

end SeLe4.Model
