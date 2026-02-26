namespace SeLe4n

/-! ## H-06/WS-E3: Identifier sentinel convention

All identifier types (`ObjId`, `ThreadId`, `CPtr`, `Slot`, `DomainId`, `Badge`,
`ServiceId`, `ASID`, `VAddr`, `PAddr`) derive `Inhabited`, which generates a
default instance of `⟨0⟩`. To prevent silent use of this magic value from
causing aliasing with real kernel objects:

**Convention:** ID value 0 is **reserved as a sentinel** meaning "unallocated"
or "invalid". Kernel operations must never store a real object, thread, or
service at ID 0. This mirrors seL4's convention where capability pointer 0
(`seL4_CapNull`) is the null capability. The `isReserved` predicate on
`ObjId`, `ThreadId`, and `ServiceId` identifies the sentinel value. -/

/-- Identifier for objects in the global kernel object store.
    Value 0 is reserved as sentinel (H-06/WS-E3). -/
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

/-- H-06/WS-E3: ID 0 is the reserved sentinel value. -/
@[inline] def isReserved (id : ObjId) : Bool := id.val = 0

/-- H-06/WS-E3: The sentinel ObjId (value 0). -/
@[inline] def sentinel : ObjId := ⟨0⟩

/-- H-06/WS-E3: An identifier is valid (non-sentinel) when its raw value is nonzero. -/
def valid (id : ObjId) : Prop := id.val ≠ 0

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

/-- Explicit conversion used at object-store boundaries.

**L-04/WS-E6 design note:** This conversion is intentionally unchecked (pure
identity mapping on the underlying `Nat`). Validation of the resulting `ObjId`
is deferred to the object-store lookup boundary (`lookupObject`), which returns
`.error .objectNotFound` when no object exists at the target ID. This is safe
because:
1. `ThreadId.toObjId_injective` guarantees no aliasing between distinct thread IDs.
2. The sentinel convention (H-06) ensures ID 0 is never a valid store target.
3. All kernel operations that consume `toObjId` immediately follow with a
   `lookupObject` or pattern match that validates the object exists and is a TCB.

See `ThreadId.toObjId_preserves_sentinel` for the sentinel-preservation proof. -/
@[inline] def toObjId (id : ThreadId) : ObjId := ObjId.ofNat id.toNat

instance instOfNat (n : Nat) : OfNat ThreadId n where
  ofNat := ⟨n⟩

instance : ToString ThreadId where
  toString tid := toString tid.toNat

/-- H-06/WS-E3: ID 0 is the reserved sentinel value. -/
@[inline] def isReserved (id : ThreadId) : Bool := id.val = 0

/-- H-06/WS-E3: The sentinel ThreadId (value 0). -/
@[inline] def sentinel : ThreadId := ⟨0⟩

/-- L-04/WS-E6: Checked conversion that validates the thread ID is non-sentinel
before producing an ObjId. Returns `none` for the reserved sentinel (ID 0). -/
@[inline] def toObjIdChecked (id : ThreadId) : Option ObjId :=
  if id.isReserved then none else some (id.toObjId)

end ThreadId

/-- H-09/WS-E3: ThreadId → ObjId is injective. Two thread identifiers that
map to the same object identifier must be equal. This is used in IPC-scheduler
contract proofs to ensure that storeTcbIpcState at one thread ID does not
corrupt the TCB observed at a different thread ID. -/
theorem ThreadId.toObjId_injective (t1 t2 : ThreadId)
    (h : t1.toObjId = t2.toObjId) : t1 = t2 := by
  cases t1 with | mk v1 => cases t2 with | mk v2 =>
  simp [ThreadId.toObjId, ThreadId.toNat, ObjId.ofNat] at h
  subst h; rfl

/-- L-04/WS-E6: The sentinel ThreadId maps to the sentinel ObjId. -/
theorem ThreadId.toObjId_preserves_sentinel :
    ThreadId.sentinel.toObjId = ObjId.sentinel := rfl

/-- L-04/WS-E6: A non-sentinel ThreadId maps to a non-sentinel ObjId. -/
theorem ThreadId.toObjId_valid_of_not_reserved (tid : ThreadId)
    (h : tid.isReserved = false) :
    tid.toObjId.isReserved = false := by
  simp [ThreadId.isReserved] at h
  simp [ThreadId.toObjId, ThreadId.toNat, ObjId.ofNat, ObjId.isReserved, h]

/-- L-04/WS-E6: `toObjIdChecked` returns `some` exactly when the ID is non-sentinel. -/
theorem ThreadId.toObjIdChecked_some_iff (tid : ThreadId) :
    tid.toObjIdChecked.isSome = true ↔ tid.isReserved = false := by
  unfold ThreadId.toObjIdChecked ThreadId.isReserved
  by_cases h : tid.val = 0 <;> simp [h]

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

/-- H-06/WS-E3: ID 0 is the reserved sentinel value. -/
@[inline] def isReserved (id : ServiceId) : Bool := id.val = 0

/-- H-06/WS-E3: The sentinel ServiceId (value 0). -/
@[inline] def sentinel : ServiceId := ⟨0⟩

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

/-- WS-E4 preparation: CPtr 0 corresponds to seL4_CapNull (null capability pointer).
    Sentinel infrastructure parallels ObjId/ThreadId/ServiceId. -/
@[inline] def isReserved (ptr : CPtr) : Bool := ptr.val = 0

/-- The null capability pointer (CPtr 0), analogous to seL4_CapNull. -/
@[inline] def sentinel : CPtr := ⟨0⟩

theorem default_eq_sentinel : (default : CPtr) = CPtr.sentinel := rfl

theorem sentinel_isReserved : CPtr.sentinel.isReserved = true := rfl

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

/-- L-03/WS-E6: Read the current state without modifying it. -/
def get {σ ε : Type} : KernelM σ ε σ :=
  fun s => .ok (s, s)

/-- L-03/WS-E6: Replace the current state entirely. -/
def set {σ ε : Type} (s : σ) : KernelM σ ε Unit :=
  fun _ => .ok ((), s)

/-- L-03/WS-E6: Apply a pure transformation to the current state. -/
def modify {σ ε : Type} (f : σ → σ) : KernelM σ ε Unit :=
  fun s => .ok ((), f s)

/-- L-03/WS-E6: Lift an `Except` computation into `KernelM`, propagating errors. -/
def liftExcept {σ ε α : Type} (e : Except ε α) : KernelM σ ε α :=
  fun s =>
    match e with
    | .ok a => .ok (a, s)
    | .error err => .error err

/-- L-03/WS-E6: Raise an error, aborting the computation. -/
def throw {σ ε α : Type} (err : ε) : KernelM σ ε α :=
  fun _ => .error err

-- L-03/WS-E6: Monad helper correctness theorems

theorem get_eq (s : σ) : @get σ ε s = .ok (s, s) := rfl

theorem set_eq (s s' : σ) : @set σ ε s' s = .ok ((), s') := rfl

theorem modify_eq (f : σ → σ) (s : σ) : @modify σ ε f s = .ok ((), f s) := rfl

theorem liftExcept_ok (a : α) (s : σ) :
    @liftExcept σ ε α (.ok a) s = .ok (a, s) := rfl

theorem liftExcept_error (err : ε) (s : σ) :
    @liftExcept σ ε α (.error err) s = .error err := rfl

theorem throw_eq (err : ε) (s : σ) :
    @throw σ ε α err s = .error err := rfl

end KernelM

-- ============================================================================
-- H-06/WS-E3: Sentinel identity theorems
-- ============================================================================

/-- The default `ObjId` is the reserved sentinel (value 0). -/
theorem ObjId.default_eq_sentinel : (default : ObjId) = ObjId.sentinel := rfl

/-- The default `ThreadId` is the reserved sentinel (value 0). -/
theorem ThreadId.default_eq_sentinel : (default : ThreadId) = ThreadId.sentinel := rfl

/-- The sentinel ObjId is reserved. -/
theorem ObjId.sentinel_isReserved : ObjId.sentinel.isReserved = true := rfl

/-- The sentinel ThreadId is reserved. -/
theorem ThreadId.sentinel_isReserved : ThreadId.sentinel.isReserved = true := rfl

/-- H-06/WS-E3: An ObjId is valid iff it is not reserved. -/
theorem ObjId.valid_iff_not_reserved (id : ObjId) :
    id.valid ↔ id.isReserved = false := by
  simp [ObjId.valid, ObjId.isReserved]

/-- The default `ServiceId` is the reserved sentinel (value 0). -/
theorem ServiceId.default_eq_sentinel : (default : ServiceId) = ServiceId.sentinel := rfl

/-- The sentinel ServiceId is reserved. -/
theorem ServiceId.sentinel_isReserved : ServiceId.sentinel.isReserved = true := rfl

end SeLe4n
