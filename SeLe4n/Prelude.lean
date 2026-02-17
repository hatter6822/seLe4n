namespace SeLe4n

/-- Identifier for objects in the global kernel object store. -/
structure ObjId where
  val : Nat
deriving DecidableEq, Repr, Inhabited

namespace ObjId

/-- Constructor helper kept explicit for migration ergonomics. -/
@[inline] def ofNat (n : Nat) : ObjId := ⟨n⟩

/-- Projection helper kept explicit for migration ergonomics. -/
@[inline] def toNat (id : ObjId) : Nat := id.val

instance instOfNat (n : Nat) : OfNat ObjId n where
  ofNat := ⟨n⟩

instance : ToString ObjId where
  toString id := toString id.toNat

end ObjId

/-- Identifier for threads (TCBs). -/
structure ThreadId where
  val : Nat
deriving DecidableEq, Repr, Inhabited

namespace ThreadId

/-- Constructor helper kept explicit for migration ergonomics. -/
@[inline] def ofNat (n : Nat) : ThreadId := ⟨n⟩

/-- Projection helper kept explicit for migration ergonomics. -/
@[inline] def toNat (id : ThreadId) : Nat := id.val

/-- Explicit conversion used at object-store boundaries. -/
@[inline] def toObjId (id : ThreadId) : ObjId := ObjId.ofNat id.toNat

instance instOfNat (n : Nat) : OfNat ThreadId n where
  ofNat := ⟨n⟩

instance : ToString ThreadId where
  toString tid := toString tid.toNat

end ThreadId

/-- Scheduling domain identifier. -/
abbrev DomainId := Nat

/-- Scheduling priority level. -/
abbrev Priority := Nat

/-- Interrupt request line identifier. -/
abbrev Irq := Nat

/-- Capability-space pointer value. -/
structure CPtr where
  val : Nat
deriving DecidableEq, Repr, Inhabited

namespace CPtr

/-- Constructor helper kept explicit for migration ergonomics. -/
@[inline] def ofNat (n : Nat) : CPtr := ⟨n⟩

/-- Projection helper kept explicit for migration ergonomics. -/
@[inline] def toNat (ptr : CPtr) : Nat := ptr.val

instance instOfNat (n : Nat) : OfNat CPtr n where
  ofNat := ⟨n⟩

instance : ToString CPtr where
  toString ptr := toString ptr.toNat

end CPtr

/-- Slot index within a CNode. -/
structure Slot where
  val : Nat
deriving DecidableEq, Repr, Inhabited

namespace Slot

/-- Constructor helper kept explicit for migration ergonomics. -/
@[inline] def ofNat (n : Nat) : Slot := ⟨n⟩

/-- Projection helper kept explicit for migration ergonomics. -/
@[inline] def toNat (slot : Slot) : Nat := slot.val

instance instOfNat (n : Nat) : OfNat Slot n where
  ofNat := ⟨n⟩

instance : ToString Slot where
  toString slot := toString slot.toNat

end Slot

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
