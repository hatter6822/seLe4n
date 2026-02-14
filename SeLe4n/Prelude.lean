namespace SeLe4n

/-- Identifier for objects in the global kernel object store. -/
abbrev ObjId := Nat

/-- Identifier for threads (TCBs). -/
abbrev ThreadId := Nat

/-- Scheduling domain identifier. -/
abbrev DomainId := Nat

/-- Scheduling priority level. -/
abbrev Priority := Nat

/-- Interrupt request line identifier. -/
abbrev Irq := Nat

/-- Capability-space pointer value. -/
abbrev CPtr := Nat

/-- Slot index within a CNode. -/
abbrev Slot := Nat

/-- Endpoint or notification badge value. -/
abbrev Badge := Nat

/-- Address-space identifier. -/
abbrev ASID := Nat

/-- Virtual-memory address in the abstract model. -/
abbrev VAddr := Nat

/-- Physical-memory address in the abstract model. -/
abbrev PAddr := Nat

/-- A tiny state/error monad used for executable kernel skeletons. -/
abbrev KernelM (σ ε α : Type) := σ → Except ε (α × σ)

namespace KernelM

def pure {σ ε α : Type} (a : α) : KernelM σ ε α :=
  fun s => Except.ok (a, s)

def bind {σ ε α β : Type} (m : KernelM σ ε α) (f : α → KernelM σ ε β) : KernelM σ ε β :=
  fun s =>
    match m s with
    | .error e => .error e
    | .ok (a, s') => f a s'

instance {σ ε : Type} : Monad (KernelM σ ε) where
  pure := pure
  bind := bind

end KernelM

end SeLe4n
