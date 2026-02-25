/-!
# Typed Identifiers

## Sentinel ID convention (H-06, WS-E3)

All identifier types (`ObjId`, `ThreadId`, `DomainId`, `Priority`, `Irq`,
`ServiceId`, `CPtr`, `Slot`, `Badge`, `ASID`) derive `Inhabited`, which
produces a default value of `⟨0⟩`. This is an intentional design decision:

- **ID 0 is reserved as the sentinel (default) value** for all identifier types.
- Kernel operations MUST NOT assign ID 0 to live objects. The bootstrap state
  builder enforces this by starting object allocation at ID 1.
- The `Inhabited` instances are retained for Lean framework compatibility
  (e.g., `Array.get!`, `HashMap.find!`, default structure fields). Removing
  them would require pervasive API changes with no safety benefit, since the
  sentinel convention achieves the same goal.
- Future work (WS-E6/L-04) may add runtime validation to `ThreadId.toObjId`
  and similar conversions to reject sentinel values at API boundaries.
-/

namespace SeLe4n

/-- Identifier for objects in the global kernel object store.
H-06 (WS-E3): Value 0 is a reserved sentinel; see module-level docstring. -/
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

/-- H-06 (WS-E3): An identifier is valid (non-sentinel) when its raw value is nonzero. -/
def ObjId.valid (id : ObjId) : Prop := id.val ≠ 0

/-- H-06: The Inhabited default is the sentinel value 0. -/
theorem ObjId.sentinel_val : (default : ObjId).val = 0 := rfl

/-- Identifier for threads (TCBs).
H-06 (WS-E3): Value 0 is a reserved sentinel; see Prelude module-level docstring. -/
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

/-- H-09 (WS-E3): ThreadId → ObjId is injective. Two thread identifiers that
map to the same object identifier must be equal. This is used in IPC-scheduler
contract proofs to ensure that storeTcbIpcState at one thread ID does not
corrupt the TCB observed at a different thread ID. -/
theorem ThreadId.toObjId_injective (t1 t2 : ThreadId)
    (h : t1.toObjId = t2.toObjId) : t1 = t2 := by
  cases t1 with | mk v1 => cases t2 with | mk v2 =>
  simp [ThreadId.toObjId, ThreadId.toNat, ObjId.ofNat] at h
  subst h; rfl

/-- Scheduling domain identifier. -/
structure DomainId where
  val : Nat
deriving DecidableEq, Repr, Inhabited

namespace DomainId

/-- Constructor helper kept explicit for migration ergonomics. -/
@[inline] def ofNat (n : Nat) : DomainId := ⟨n⟩

/-- Projection helper kept explicit for migration ergonomics. -/
@[inline] def toNat (id : DomainId) : Nat := id.val

instance instOfNat (n : Nat) : OfNat DomainId n where
  ofNat := ⟨n⟩

instance : ToString DomainId where
  toString id := toString id.toNat

end DomainId

/-- Scheduling priority level. -/
structure Priority where
  val : Nat
deriving DecidableEq, Repr, Inhabited

namespace Priority

/-- Constructor helper kept explicit for migration ergonomics. -/
@[inline] def ofNat (n : Nat) : Priority := ⟨n⟩

/-- Projection helper kept explicit for migration ergonomics. -/
@[inline] def toNat (prio : Priority) : Nat := prio.val

instance instOfNat (n : Nat) : OfNat Priority n where
  ofNat := ⟨n⟩

instance : ToString Priority where
  toString prio := toString prio.toNat

end Priority

/-- Interrupt request line identifier. -/
structure Irq where
  val : Nat
deriving DecidableEq, Repr, Inhabited

namespace Irq

/-- Constructor helper kept explicit for migration ergonomics. -/
@[inline] def ofNat (n : Nat) : Irq := ⟨n⟩

/-- Projection helper kept explicit for migration ergonomics. -/
@[inline] def toNat (irq : Irq) : Nat := irq.val

instance instOfNat (n : Nat) : OfNat Irq n where
  ofNat := ⟨n⟩

instance : ToString Irq where
  toString irq := toString irq.toNat

end Irq

/-- Identifier for graph-level services in the orchestration layer. -/
structure ServiceId where
  val : Nat
deriving DecidableEq, Repr, Inhabited

namespace ServiceId

/-- Constructor helper kept explicit for migration ergonomics. -/
@[inline] def ofNat (n : Nat) : ServiceId := ⟨n⟩

/-- Projection helper kept explicit for migration ergonomics. -/
@[inline] def toNat (id : ServiceId) : Nat := id.val

instance instOfNat (n : Nat) : OfNat ServiceId n where
  ofNat := ⟨n⟩

instance : ToString ServiceId where
  toString id := toString id.toNat

end ServiceId

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
structure Badge where
  val : Nat
deriving DecidableEq, Repr, Inhabited

namespace Badge

/-- Constructor helper kept explicit for migration ergonomics. -/
@[inline] def ofNat (n : Nat) : Badge := ⟨n⟩

/-- Projection helper kept explicit for migration ergonomics. -/
@[inline] def toNat (badge : Badge) : Nat := badge.val

instance instOfNat (n : Nat) : OfNat Badge n where
  ofNat := ⟨n⟩

instance : ToString Badge where
  toString badge := toString badge.toNat

end Badge

/-- Address-space identifier. -/
structure ASID where
  val : Nat
deriving DecidableEq, Repr, Inhabited

namespace ASID

/-- Constructor helper kept explicit for migration ergonomics. -/
@[inline] def ofNat (n : Nat) : ASID := ⟨n⟩

/-- Projection helper kept explicit for migration ergonomics. -/
@[inline] def toNat (asid : ASID) : Nat := asid.val

instance instOfNat (n : Nat) : OfNat ASID n where
  ofNat := ⟨n⟩

instance : ToString ASID where
  toString asid := toString asid.toNat

end ASID

/-- Virtual-memory address in the abstract model. -/
structure VAddr where
  val : Nat
deriving DecidableEq, Repr, Inhabited

namespace VAddr

/-- Constructor helper kept explicit for migration ergonomics. -/
@[inline] def ofNat (n : Nat) : VAddr := ⟨n⟩

/-- Projection helper kept explicit for migration ergonomics. -/
@[inline] def toNat (addr : VAddr) : Nat := addr.val

instance instOfNat (n : Nat) : OfNat VAddr n where
  ofNat := ⟨n⟩

instance : ToString VAddr where
  toString addr := toString addr.toNat

end VAddr

/-- Physical-memory address in the abstract model. -/
structure PAddr where
  val : Nat
deriving DecidableEq, Repr, Inhabited

namespace PAddr

/-- Constructor helper kept explicit for migration ergonomics. -/
@[inline] def ofNat (n : Nat) : PAddr := ⟨n⟩

/-- Projection helper kept explicit for migration ergonomics. -/
@[inline] def toNat (addr : PAddr) : Nat := addr.val

instance instOfNat (n : Nat) : OfNat PAddr n where
  ofNat := ⟨n⟩

instance : ToString PAddr where
  toString addr := toString addr.toNat

end PAddr

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
