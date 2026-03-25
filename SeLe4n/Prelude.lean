/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import Std.Data.HashMap
import Std.Data.HashSet
import SeLe4n.Kernel.RobinHood.Bridge

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

/-- WS-G1: Hash instance for HashMap/HashSet keying. Delegates to Nat hash.
    BEq is already provided by DecidableEq via instBEqOfDecidableEq. -/
@[inline] instance : Hashable ObjId where
  hash a := hash a.val

namespace ObjId

/-- Constructor helper kept explicit for migration ergonomics. -/
@[inline] def ofNat (n : Nat) : ObjId := ⟨n⟩

/-- Projection helper kept explicit for migration ergonomics. -/
@[inline] def toNat (id : ObjId) : Nat := id.val

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

/-- WS-G1: Hash instance for HashMap/HashSet keying. Delegates to Nat hash.
    BEq is already provided by DecidableEq via instBEqOfDecidableEq. -/
@[inline] instance : Hashable ThreadId where
  hash a := hash a.val

namespace ThreadId

/-- WS-H12b: Extensionality theorem for ThreadId. -/
theorem ext {a b : ThreadId} (h : a.val = b.val) : a = b := by
  cases a; cases b; simp_all

/-- Constructor helper kept explicit for migration ergonomics. -/
@[inline] def ofNat (n : Nat) : ThreadId := ⟨n⟩

/-- Projection helper kept explicit for migration ergonomics. -/
@[inline] def toNat (id : ThreadId) : Nat := id.val

/-- L-04/WS-E6: Explicit conversion used at object-store boundaries.

**Design note (deferred validation):** This conversion is unchecked — it does
not verify that the resulting `ObjId` actually maps to a TCB in the object store.
Validation is intentionally deferred to the store-access boundary: callers that
retrieve a `KernelObject` via `st.objects tid.toObjId` immediately pattern-match
on `.tcb tcb`, so invalid IDs are caught deterministically at use site. This
avoids carrying an extra proof obligation through every intermediate function.
See `ThreadId.toObjId_injective` for the injectivity proof that ensures two
distinct thread IDs cannot alias the same object.

**S1-C: Trust boundary documentation.** `ThreadId.toObjId` is an identity
mapping (`ObjId.ofNat id.toNat`) — it performs no validation, bounds checking,
or type verification. Callers **must** verify the returned `ObjId` references a
TCB by pattern-matching on `.tcb tcb` after the object store lookup. Failure to
check the object kind after `toObjId` would allow a thread ID to alias a non-TCB
object, violating type safety. The checked variant `toObjIdChecked` additionally
rejects the sentinel value (ID 0). -/
@[inline] def toObjId (id : ThreadId) : ObjId := ObjId.ofNat id.toNat

instance : ToString ThreadId where
  toString tid := toString tid.toNat

/-- H-06/WS-E3: ID 0 is the reserved sentinel value. -/
@[inline] def isReserved (id : ThreadId) : Bool := id.val = 0

/-- H-06/WS-E3: The sentinel ThreadId (value 0). -/
@[inline] def sentinel : ThreadId := ⟨0⟩

/-- L-04/WS-E6: Checked variant of `toObjId` that rejects sentinel thread IDs.
Returns `none` for the reserved sentinel (value 0). -/
@[inline] def toObjIdChecked (id : ThreadId) : Option ObjId :=
  if id.isReserved then .none else .some (id.toObjId)

/-- L-04/WS-E6: `toObjIdChecked` agrees with `toObjId` on non-sentinel inputs. -/
theorem toObjIdChecked_eq_some_of_not_reserved (id : ThreadId)
    (hNotRes : id.isReserved = false) :
    id.toObjIdChecked = some id.toObjId := by
  simp [toObjIdChecked, hNotRes]

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

/-- Scheduling domain identifier. -/
structure DomainId where
  val : Nat
deriving DecidableEq, Repr, Inhabited

/-- WS-G1: Hash instance for HashMap/HashSet keying. Delegates to Nat hash.
    BEq is already provided by DecidableEq via instBEqOfDecidableEq. -/
@[inline] instance : Hashable DomainId where
  hash a := hash a.val

namespace DomainId

/-- Constructor helper kept explicit for migration ergonomics. -/
@[inline] def ofNat (n : Nat) : DomainId := ⟨n⟩

/-- Projection helper kept explicit for migration ergonomics. -/
@[inline] def toNat (id : DomainId) : Nat := id.val

instance : ToString DomainId where
  toString id := toString id.toNat

end DomainId

/-- Scheduling priority level. -/
structure Priority where
  val : Nat
deriving DecidableEq, Repr, Inhabited

/-- WS-G1: Hash instance for HashMap/HashSet keying. Delegates to Nat hash.
    BEq is already provided by DecidableEq via instBEqOfDecidableEq. -/
@[inline] instance : Hashable Priority where
  hash a := hash a.val

namespace Priority

/-- Constructor helper kept explicit for migration ergonomics. -/
@[inline] def ofNat (n : Nat) : Priority := ⟨n⟩

/-- Projection helper kept explicit for migration ergonomics. -/
@[inline] def toNat (prio : Priority) : Nat := prio.val

instance : ToString Priority where
  toString prio := toString prio.toNat

end Priority

/-- M-03/WS-E6: Scheduling deadline for EDF (Earliest Deadline First) tie-breaking.
A deadline of 0 means "no deadline set" (infinite deadline, lowest urgency among
threads with deadlines). Nonzero values represent relative urgency: lower values
are more urgent. This convention makes the type total without requiring `Option Nat`
and preserves backward compatibility (all existing TCBs default to deadline 0). -/
structure Deadline where
  val : Nat
deriving DecidableEq, Repr, Inhabited

/-- WS-G1: Hash instance for HashMap/HashSet keying. Delegates to Nat hash.
    BEq is already provided by DecidableEq via instBEqOfDecidableEq. -/
@[inline] instance : Hashable Deadline where
  hash a := hash a.val

namespace Deadline

@[inline] def ofNat (n : Nat) : Deadline := ⟨n⟩
@[inline] def toNat (d : Deadline) : Nat := d.val

instance : ToString Deadline where
  toString d := toString d.toNat

/-- The default deadline (no deadline set). -/
@[inline] def none : Deadline := ⟨0⟩

/-- An immediate deadline (most urgent). -/
@[inline] def immediate : Deadline := ⟨1⟩

end Deadline

/-- Interrupt request line identifier. -/
structure Irq where
  val : Nat
deriving DecidableEq, Repr, Inhabited

/-- WS-G1: Hash instance for HashMap/HashSet keying. Delegates to Nat hash.
    BEq is already provided by DecidableEq via instBEqOfDecidableEq. -/
@[inline] instance : Hashable Irq where
  hash a := hash a.val

namespace Irq

/-- Constructor helper kept explicit for migration ergonomics. -/
@[inline] def ofNat (n : Nat) : Irq := ⟨n⟩

/-- Projection helper kept explicit for migration ergonomics. -/
@[inline] def toNat (irq : Irq) : Nat := irq.val

instance : ToString Irq where
  toString irq := toString irq.toNat

end Irq

/-- Identifier for graph-level services in the orchestration layer. -/
structure ServiceId where
  val : Nat
deriving DecidableEq, Repr, Inhabited

/-- WS-G1: Hash instance for HashMap/HashSet keying. Delegates to Nat hash.
    BEq is already provided by DecidableEq via instBEqOfDecidableEq. -/
@[inline] instance : Hashable ServiceId where
  hash a := hash a.val

namespace ServiceId

/-- Constructor helper kept explicit for migration ergonomics. -/
@[inline] def ofNat (n : Nat) : ServiceId := ⟨n⟩

/-- Projection helper kept explicit for migration ergonomics. -/
@[inline] def toNat (id : ServiceId) : Nat := id.val

instance : ToString ServiceId where
  toString id := toString id.toNat

/-- H-06/WS-E3: ID 0 is the reserved sentinel value. -/
@[inline] def isReserved (id : ServiceId) : Bool := id.val = 0

/-- H-06/WS-E3: The sentinel ServiceId (value 0). -/
@[inline] def sentinel : ServiceId := ⟨0⟩

end ServiceId

/-- Identifier for interface specifications in the service registry. -/
structure InterfaceId where
  val : Nat
deriving DecidableEq, Repr, Inhabited

@[inline] instance : Hashable InterfaceId where
  hash a := hash a.val

namespace InterfaceId

@[inline] def ofNat (n : Nat) : InterfaceId := ⟨n⟩
@[inline] def toNat (id : InterfaceId) : Nat := id.val

instance : ToString InterfaceId where
  toString id := toString id.toNat

@[inline] def isReserved (id : InterfaceId) : Bool := id.val = 0
@[inline] def sentinel : InterfaceId := ⟨0⟩

/-- Round-trip: ofNat then toNat is identity. -/
theorem toNat_ofNat (n : Nat) : (InterfaceId.ofNat n).toNat = n := rfl

/-- Round-trip: toNat then ofNat is identity. -/
theorem ofNat_toNat (id : InterfaceId) : InterfaceId.ofNat id.toNat = id := by
  cases id; rfl

end InterfaceId

/-- Capability-space pointer value. -/
structure CPtr where
  val : Nat
deriving DecidableEq, Repr, Inhabited

/-- WS-G1: Hash instance for HashMap/HashSet keying. Delegates to Nat hash.
    BEq is already provided by DecidableEq via instBEqOfDecidableEq. -/
@[inline] instance : Hashable CPtr where
  hash a := hash a.val

namespace CPtr

/-- Constructor helper kept explicit for migration ergonomics. -/
@[inline] def ofNat (n : Nat) : CPtr := ⟨n⟩

/-- Projection helper kept explicit for migration ergonomics. -/
@[inline] def toNat (ptr : CPtr) : Nat := ptr.val

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

/-- WS-G1: Hash instance for HashMap/HashSet keying. Delegates to Nat hash.
    BEq is already provided by DecidableEq via instBEqOfDecidableEq. -/
@[inline] instance : Hashable Slot where
  hash a := hash a.val

namespace Slot

/-- Constructor helper kept explicit for migration ergonomics. -/
@[inline] def ofNat (n : Nat) : Slot := ⟨n⟩

/-- Projection helper kept explicit for migration ergonomics. -/
@[inline] def toNat (slot : Slot) : Nat := slot.val

instance : ToString Slot where
  toString slot := toString slot.toNat

end Slot

/-- WS-F5/D1a: Machine word width in bits. ARM64 target = 64.
    Badge values and notification bitmasks are bounded to this width. -/
def machineWordBits : Nat := 64

/-- WS-F5/D1a: Maximum value representable in one machine word. -/
def machineWordMax : Nat := 2 ^ machineWordBits

/-- R7-C/L-03: Predicate asserting a natural number fits in one machine word.
    Hardware registers, virtual addresses, and physical addresses are 64-bit
    values. This predicate is used as a refinement in invariants — the underlying
    types keep `Nat` for proof ergonomics, but hardware-bound operations should
    ensure `isWord64` holds. -/
@[inline] def isWord64 (n : Nat) : Prop := n < machineWordMax

/-- R7-C/L-03: Decidable `isWord64` check for runtime use. -/
@[inline] def isWord64Dec (n : Nat) : Bool := n < machineWordMax

/-- R7-C/L-03: `isWord64Dec` reflects `isWord64`. -/
theorem isWord64Dec_iff (n : Nat) : isWord64Dec n = true ↔ isWord64 n := by
  simp [isWord64Dec, isWord64]

/-- Endpoint or notification badge value.
    WS-F5/D1a: Values are logically bounded to `machineWordBits` (64) bits.
    The `valid` predicate asserts word-boundedness; `ofNatMasked` enforces it
    at construction. -/
structure Badge where
  val : Nat
deriving DecidableEq, Repr, Inhabited

/-- WS-G1: Hash instance for HashMap/HashSet keying. Delegates to Nat hash.
    BEq is already provided by DecidableEq via instBEqOfDecidableEq. -/
@[inline] instance : Hashable Badge where
  hash a := hash a.val

namespace Badge

/-- Projection helper kept explicit for migration ergonomics. -/
@[inline] def toNat (badge : Badge) : Nat := badge.val

/-- WS-F5/D1a: A badge is valid if its value fits in one machine word. -/
@[inline] def valid (badge : Badge) : Prop := badge.val < machineWordMax

/-- WS-F5/D1a: Decidable validity check for runtime use. -/
@[inline] def isValid (badge : Badge) : Bool := badge.val < machineWordMax

/-- WS-F5/D1a: Construct a badge with word-size truncation, matching seL4's
    silent word-truncation semantics on 64-bit platforms. -/
@[inline] def ofNatMasked (n : Nat) : Badge := ⟨n % machineWordMax⟩

/-- WS-F5/D1b: Bitwise OR combiner for badge accumulation. Masks the result
    to machine word size, matching seL4 notification signal semantics. -/
@[inline] def bor (a b : Badge) : Badge := ofNatMasked (a.val ||| b.val)

/-- WS-F5/D1a: `ofNatMasked` always produces a valid badge. -/
theorem ofNatMasked_valid (n : Nat) : (ofNatMasked n).valid := by
  simp [ofNatMasked, valid, machineWordMax]
  exact Nat.mod_lt n (by decide)

/-- WS-F5/D1b: `bor` preserves validity — OR of two word-bounded values
    is word-bounded. -/
theorem bor_valid (a b : Badge) : (bor a b).valid :=
  ofNatMasked_valid (a.val ||| b.val)

/-- WS-F5/D1b: Badge OR is commutative. -/
theorem bor_comm (a b : Badge) : bor a b = bor b a := by
  simp [bor, ofNatMasked, Nat.or_comm]

/-- WS-F5/D1b: Badge OR is idempotent. -/
theorem bor_idempotent (a : Badge) : bor a a = ofNatMasked a.val := by
  simp [bor, Nat.or_self]

/-- R6-B: `ofNatMasked` with a small literal that fits in one word is
    identity — the modulus is a no-op. -/
theorem ofNatMasked_lt_eq {n : Nat} (h : n < machineWordMax) :
    (ofNatMasked n).val = n := by
  unfold ofNatMasked machineWordMax machineWordBits
  exact Nat.mod_eq_of_lt h

instance : ToString Badge where
  toString badge := toString badge.toNat

end Badge

/-- Address-space identifier. -/
structure ASID where
  val : Nat
deriving DecidableEq, Repr, Inhabited

/-- WS-G1: Hash instance for HashMap/HashSet keying. Delegates to Nat hash.
    BEq is already provided by DecidableEq via instBEqOfDecidableEq. -/
@[inline] instance : Hashable ASID where
  hash a := hash a.val

namespace ASID

/-- Constructor helper kept explicit for migration ergonomics. -/
@[inline] def ofNat (n : Nat) : ASID := ⟨n⟩

/-- Projection helper kept explicit for migration ergonomics. -/
@[inline] def toNat (asid : ASID) : Nat := asid.val

/-- U2-G/U-H08: An ASID is valid for a given config if it lies within [0, maxASID).
    ARM64 uses 16-bit ASIDs (maxASID = 65536). -/
@[inline] def isValidForConfig (asid : ASID) (maxASID : Nat) : Bool := asid.val < maxASID

/-- U2-G/U-H08: Propositional version of ASID config validation. -/
@[inline] def validForConfig (asid : ASID) (maxASID : Nat) : Prop := asid.val < maxASID

instance : ToString ASID where
  toString asid := toString asid.toNat

end ASID

/-- Virtual-memory address in the abstract model. -/
structure VAddr where
  val : Nat
deriving DecidableEq, Repr, Inhabited

/-- WS-G1: Hash instance for HashMap/HashSet keying. Delegates to Nat hash.
    BEq is already provided by DecidableEq via instBEqOfDecidableEq. -/
@[inline] instance : Hashable VAddr where
  hash a := hash a.val

namespace VAddr

/-- Constructor helper kept explicit for migration ergonomics. -/
@[inline] def ofNat (n : Nat) : VAddr := ⟨n⟩

/-- Projection helper kept explicit for migration ergonomics. -/
@[inline] def toNat (addr : VAddr) : Nat := addr.val

/-- R7-C/L-03: A virtual address is valid if it fits in one machine word. -/
@[inline] def valid (addr : VAddr) : Prop := isWord64 addr.val

/-- R7-C/L-03: Decidable validity check for runtime use. -/
@[inline] def isValid (addr : VAddr) : Bool := isWord64Dec addr.val

/-- U2-A/U-H06: ARM64 canonical address bound — 48-bit virtual address space.
    ARMv8-A with 4-level page tables supports [0, 2^48) for user-space addresses. -/
def canonicalBound : Nat := 2^48

/-- U2-A/U-H06: A virtual address is canonical if it lies within [0, 2^48).
    Non-canonical addresses would fault on ARM64 hardware. -/
@[inline] def isCanonical (addr : VAddr) : Bool := addr.val < canonicalBound

/-- U2-A/U-H06: Propositional version of canonical address check. -/
@[inline] def canonical (addr : VAddr) : Prop := addr.val < canonicalBound

instance : ToString VAddr where
  toString addr := toString addr.toNat

end VAddr

/-- Physical-memory address in the abstract model. -/
structure PAddr where
  val : Nat
deriving DecidableEq, Repr, Inhabited

/-- WS-G1: Hash instance for HashMap/HashSet keying. Delegates to Nat hash.
    BEq is already provided by DecidableEq via instBEqOfDecidableEq. -/
@[inline] instance : Hashable PAddr where
  hash a := hash a.val

namespace PAddr

/-- Constructor helper kept explicit for migration ergonomics. -/
@[inline] def ofNat (n : Nat) : PAddr := ⟨n⟩

/-- Projection helper kept explicit for migration ergonomics. -/
@[inline] def toNat (addr : PAddr) : Nat := addr.val

/-- R7-C/L-03: A physical address is valid if it fits in one machine word. -/
@[inline] def valid (addr : PAddr) : Prop := isWord64 addr.val

/-- R7-C/L-03: Decidable validity check for runtime use. -/
@[inline] def isValid (addr : PAddr) : Bool := isWord64Dec addr.val

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

-- ============================================================================
-- L-03/WS-E6: Standard monad helpers for KernelM
-- ============================================================================

namespace KernelM

/-- L-03/WS-E6: Read the current state. -/
def get {σ ε : Type} : KernelM σ ε σ :=
  fun s => .ok (s, s)

/-- L-03/WS-E6: Replace the entire state. -/
def set {σ ε : Type} (s : σ) : KernelM σ ε Unit :=
  fun _ => .ok ((), s)

/-- L-03/WS-E6: Modify the state with a pure function. -/
def modify {σ ε : Type} (f : σ → σ) : KernelM σ ε Unit :=
  fun s => .ok ((), f s)

/-- L-03/WS-E6: Lift an `Except` into the monad (fail on error). -/
def liftExcept {σ ε α : Type} (e : Except ε α) : KernelM σ ε α :=
  fun s =>
    match e with
    | .ok a => .ok (a, s)
    | .error err => .error err

/-- L-03/WS-E6: Fail with an error. -/
def throw {σ ε α : Type} (err : ε) : KernelM σ ε α :=
  fun _ => .error err

-- L-03: Correctness theorems for monad helpers

theorem get_returns_state {σ ε : Type} (s : σ) :
    @get σ ε s = .ok (s, s) := rfl

theorem set_replaces_state {σ ε : Type} (s s' : σ) :
    @set σ ε s' s = .ok ((), s') := rfl

theorem modify_applies_function {σ ε : Type} (f : σ → σ) (s : σ) :
    @modify σ ε f s = .ok ((), f s) := rfl

theorem liftExcept_ok {σ ε α : Type} (a : α) (s : σ) :
    @liftExcept σ ε α (.ok a) s = .ok (a, s) := rfl

theorem liftExcept_error {σ ε α : Type} (err : ε) (s : σ) :
    @liftExcept σ ε α (.error err) s = .error err := rfl

theorem throw_errors {σ ε α : Type} (err : ε) (s : σ) :
    @KernelM.throw σ ε α err s = .error err := rfl

-- WS-H14b: LawfulMonad instance for KernelM

/-- WS-H14b: Left identity — `pure a >>= f = f a`. -/
theorem pure_bind_law {σ ε α β : Type} (a : α) (f : α → KernelM σ ε β) :
    bind (pure a) f = f a := rfl

/-- WS-H14b: Right identity — `m >>= pure = m`. -/
theorem bind_pure_law {σ ε α : Type} (m : KernelM σ ε α) :
    bind m pure = m := by
  funext s
  simp only [bind, pure]
  cases m s with
  | error e => rfl
  | ok p => rfl

/-- WS-H14b: Associativity — `(m >>= f) >>= g = m >>= (fun x => f x >>= g)`. -/
theorem bind_assoc_law {σ ε α β γ : Type}
    (m : KernelM σ ε α) (f : α → KernelM σ ε β) (g : β → KernelM σ ε γ) :
    bind (bind m f) g = bind m (fun x => bind (f x) g) := by
  funext s
  simp only [bind]
  cases m s with
  | error e => rfl
  | ok p => rfl

instance instLawfulMonad {σ ε : Type} : LawfulMonad (KernelM σ ε) where
  map_const := by intros; rfl
  id_map f := by
    show bind f (pure ∘ id) = f
    exact bind_pure_law f
  seqLeft_eq f g := by
    funext s
    simp only [bind, pure, SeqLeft.seqLeft, Seq.seq, Functor.map, Function.comp]
    cases f s with
    | error e => rfl
    | ok p => cases g p.2 <;> rfl
  seqRight_eq f g := by
    funext s
    simp only [bind, pure, SeqRight.seqRight, Seq.seq, Functor.map, Function.comp]
    cases f s with
    | error e => rfl
    | ok p => simp only [Function.const, id]; cases g p.2 <;> rfl
  pure_seq f x := by show bind (pure f) (fun g => bind x (fun a => pure (g a))) = bind x (fun a => pure (f a)); rfl
  bind_pure_comp f x := by show bind x (fun a => pure (f a)) = bind x (pure ∘ f); rfl
  bind_map f g := by
    show bind f (fun h => bind g (fun b => pure (h b))) =
         bind f (fun h => bind g (fun b => pure (h b))); rfl
  pure_bind a f := rfl
  bind_assoc m f g := bind_assoc_law m f g

end KernelM

-- ============================================================================
-- S1-K: MonadStateOf and MonadExceptOf instances for KernelM
-- ============================================================================

/-- S1-K: `MonadStateOf` instance for `KernelM`, enabling generic monadic
    state operations (`MonadStateOf.get`, `MonadStateOf.set`, `MonadStateOf.modifyGet`).
    This allows `KernelM` to compose with generic monadic combinators that
    require state access through the typeclass interface. -/
instance {ε : Type} : MonadStateOf σ (KernelM σ ε) where
  get := fun s => .ok (s, s)
  set s := fun _ => .ok ((), s)
  modifyGet f := fun s => let (a, s') := f s; .ok (a, s')

/-- S1-K: `MonadExceptOf` instance for `KernelM`, enabling generic monadic
    error handling (`MonadExceptOf.throw`, `MonadExceptOf.tryCatch`).
    This allows `KernelM` to compose with generic error-handling combinators. -/
instance {σ : Type} : MonadExceptOf ε (KernelM σ ε) where
  throw err := fun _ => .error err
  tryCatch m handler := fun s =>
    match m s with
    | .ok res => .ok res
    | .error err => handler err s

-- ============================================================================
-- WS-G2: LawfulHashable instances for HashMap/HashSet proof support
-- ============================================================================

instance : LawfulHashable ObjId where
  hash_eq _ _ h := by cases eq_of_beq h; rfl

instance : LawfulHashable ThreadId where
  hash_eq _ _ h := by cases eq_of_beq h; rfl

instance : LawfulHashable DomainId where
  hash_eq _ _ h := by cases eq_of_beq h; rfl

instance : LawfulHashable Priority where
  hash_eq _ _ h := by cases eq_of_beq h; rfl

instance : LawfulHashable Deadline where
  hash_eq _ _ h := by cases eq_of_beq h; rfl

instance : LawfulHashable Irq where
  hash_eq _ _ h := by cases eq_of_beq h; rfl

instance : LawfulHashable ServiceId where
  hash_eq _ _ h := by cases eq_of_beq h; rfl

instance : LawfulHashable CPtr where
  hash_eq _ _ h := by cases eq_of_beq h; rfl

instance : LawfulHashable Slot where
  hash_eq _ _ h := by cases eq_of_beq h; rfl

instance : LawfulHashable Badge where
  hash_eq _ _ h := by cases eq_of_beq h; rfl

instance : LawfulHashable ASID where
  hash_eq _ _ h := by cases eq_of_beq h; rfl

instance : LawfulHashable VAddr where
  hash_eq _ _ h := by cases eq_of_beq h; rfl

instance : LawfulHashable PAddr where
  hash_eq _ _ h := by cases eq_of_beq h; rfl

-- ============================================================================
-- WS-H14a: EquivBEq and LawfulBEq instances for typed identifiers
-- ============================================================================

instance : EquivBEq ObjId := ⟨⟩
instance : EquivBEq ThreadId := ⟨⟩
instance : EquivBEq DomainId := ⟨⟩
instance : EquivBEq Priority := ⟨⟩
instance : EquivBEq Deadline := ⟨⟩
instance : EquivBEq Irq := ⟨⟩
instance : EquivBEq ServiceId := ⟨⟩
instance : EquivBEq CPtr := ⟨⟩
instance : EquivBEq Slot := ⟨⟩
instance : EquivBEq Badge := ⟨⟩
instance : EquivBEq ASID := ⟨⟩
instance : EquivBEq VAddr := ⟨⟩
instance : EquivBEq PAddr := ⟨⟩

instance : LawfulBEq ObjId where
  eq_of_beq h := eq_of_beq h
  rfl := beq_self_eq_true _
instance : LawfulBEq ThreadId where
  eq_of_beq h := eq_of_beq h
  rfl := beq_self_eq_true _
instance : LawfulBEq DomainId where
  eq_of_beq h := eq_of_beq h
  rfl := beq_self_eq_true _
instance : LawfulBEq Priority where
  eq_of_beq h := eq_of_beq h
  rfl := beq_self_eq_true _
instance : LawfulBEq Deadline where
  eq_of_beq h := eq_of_beq h
  rfl := beq_self_eq_true _
instance : LawfulBEq Irq where
  eq_of_beq h := eq_of_beq h
  rfl := beq_self_eq_true _
instance : LawfulBEq ServiceId where
  eq_of_beq h := eq_of_beq h
  rfl := beq_self_eq_true _
instance : LawfulBEq CPtr where
  eq_of_beq h := eq_of_beq h
  rfl := beq_self_eq_true _
instance : LawfulBEq Slot where
  eq_of_beq h := eq_of_beq h
  rfl := beq_self_eq_true _
instance : LawfulBEq Badge where
  eq_of_beq h := eq_of_beq h
  rfl := beq_self_eq_true _
instance : LawfulBEq ASID where
  eq_of_beq h := eq_of_beq h
  rfl := beq_self_eq_true _
instance : LawfulBEq VAddr where
  eq_of_beq h := eq_of_beq h
  rfl := beq_self_eq_true _
instance : LawfulBEq PAddr where
  eq_of_beq h := eq_of_beq h
  rfl := beq_self_eq_true _

-- ============================================================================
-- WS-G2: HashSet bridge lemmas for algorithm-local proof ergonomics
-- (HashMap lemmas removed in Q2 — all state maps now use RHTable/KMap)
-- ============================================================================

/-- WS-G2: Bridge lemma for `HashSet.contains` on empty. -/
theorem HashSet_contains_empty {α : Type} [BEq α] [Hashable α]
    {a : α} : (∅ : Std.HashSet α).contains a = false :=
  Std.DHashMap.contains_empty

/-- WS-G8: Bridge lemma — `HashSet.contains` after `insert` characterization.
`Std.HashSet.contains_insert` gives `(s.insert a).contains b = (a == b || s.contains b)`. -/
theorem HashSet_contains_insert_iff {α : Type} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]
    (s : Std.HashSet α) (a b : α) :
    (s.insert a).contains b = true ↔ b = a ∨ s.contains b = true := by
  rw [Std.HashSet.contains_insert]
  simp only [Bool.or_eq_true]
  constructor
  · rintro (h | h)
    · left; exact (eq_of_beq h).symm
    · right; exact h
  · rintro (rfl | h)
    · left; simp
    · right; exact h

/-- WS-G8: Bridge lemma — negative `HashSet.contains` after `insert`. -/
theorem HashSet_not_contains_insert {α : Type} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]
    (s : Std.HashSet α) (a b : α) :
    (s.insert a).contains b = false ↔ b ≠ a ∧ s.contains b = false := by
  rw [Std.HashSet.contains_insert]
  simp only [Bool.or_eq_false_iff]
  constructor
  · rintro ⟨hab, hc⟩
    exact ⟨fun heq => by subst heq; simp at hab, hc⟩
  · rintro ⟨hne, hc⟩
    refine ⟨?_, hc⟩
    cases h : (a == b)
    · rfl
    · exact absurd ((eq_of_beq h).symm) hne

/-- WS-G8: `HashSet.insert` self-membership. -/
theorem HashSet_contains_insert_self {α : Type} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]
    (s : Std.HashSet α) (a : α) :
    (s.insert a).contains a = true := by
  rw [Std.HashSet.contains_insert]; simp

-- ============================================================================
-- Q2-A: RHTable bridge lemmas for universal migration
-- Re-export Bridge.lean theorems under naming conventions used by downstream
-- proofs. These provide drop-in replacements for the HashMap lemmas above.
-- ============================================================================

open SeLe4n.Kernel.RobinHood in
/-- Q2-A: Lookup in empty RHTable returns none. -/
theorem RHTable_get?_empty {α β : Type} [BEq α] [Hashable α]
    (cap : Nat) (hPos : 0 < cap) {a : α} :
    (RHTable.empty cap hPos : RHTable α β).get? a = none :=
  RHTable.getElem?_empty cap hPos a

open SeLe4n.Kernel.RobinHood in
/-- Q2-A: After inserting key `k` with value `v`, lookup returns `some v`. -/
theorem RHTable_get?_insert_self {α β : Type} [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) (v : β) (hExt : t.invExt) :
    (t.insert k v).get? k = some v :=
  RHTable.getElem?_insert_self t k v hExt

open SeLe4n.Kernel.RobinHood in
/-- Q2-A: Inserting key `k` does not affect lookups of other keys. -/
theorem RHTable_get?_insert_ne {α β : Type} [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k k' : α) (v : β) (hNe : ¬(k == k') = true)
    (hExt : t.invExt) :
    (t.insert k v).get? k' = t.get? k' :=
  RHTable.getElem?_insert_ne t k k' v hNe hExt

open SeLe4n.Kernel.RobinHood in
/-- Q2-A: After erasing key `k`, lookup returns `none`. -/
theorem RHTable_get?_erase_self {α β : Type} [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) (hExt : t.invExt) :
    (t.erase k).get? k = none :=
  RHTable.getElem?_erase_self t k hExt

open SeLe4n.Kernel.RobinHood in
/-- Q2-A: Erasing key `k` does not affect lookups of other keys. -/
theorem RHTable_get?_erase_ne {α β : Type} [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k k' : α) (hNe : ¬(k == k') = true)
    (hExt : t.invExt) (hSize : t.size < t.capacity) :
    (t.erase k).get? k' = t.get? k' :=
  RHTable.getElem?_erase_ne t k k' hNe hExt hSize

open SeLe4n.Kernel.RobinHood in
/-- Q2-A: Combined insert lookup characterization.
    Provides `if k == a then some v else t.get? a` for insert lookups. -/
theorem RHTable_getElem?_insert {α β : Type} [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) (v : β) (hExt : t.invExt) (a : α) :
    (t.insert k v).get? a = if k == a then some v else t.get? a := by
  by_cases h : (k == a) = true
  · simp only [h, ite_true]
    have hka : a = k := (eq_of_beq h).symm; subst hka
    exact RHTable.getElem?_insert_self t a v hExt
  · simp only [show (k == a) = false from Bool.eq_false_iff.mpr h]
    exact RHTable.getElem?_insert_ne t k a v h hExt

open SeLe4n.Kernel.RobinHood in
/-- Q2-A: Combined erase lookup characterization.
    Provides `if k == a then none else t.get? a` for erase lookups. -/
theorem RHTable_getElem?_erase {α β : Type} [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) (hExt : t.invExt) (hSize : t.size < t.capacity) (a : α) :
    (t.erase k).get? a = if k == a then none else t.get? a := by
  by_cases h : (k == a) = true
  · simp only [h, ite_true]
    have hka : a = k := (eq_of_beq h).symm; subst hka
    exact RHTable.getElem?_erase_self t a hExt
  · simp only [show (k == a) = false from Bool.eq_false_iff.mpr h]
    exact RHTable.getElem?_erase_ne t k a h hExt hSize

open SeLe4n.Kernel.RobinHood in
/-- Q2-A: Membership is equivalent to `get?` returning `some`. -/
theorem RHTable_contains_iff_get_some {α β : Type} [BEq α] [Hashable α]
    (t : RHTable α β) (k : α) :
    t.contains k = true ↔ (t.get? k).isSome = true := by
  simp [RHTable.contains]

open SeLe4n.Kernel.RobinHood in
/-- Q2-A: Not contained iff get? returns none. -/
theorem RHTable_not_contains_iff_get_none {α β : Type} [BEq α] [Hashable α]
    (t : RHTable α β) (k : α) :
    t.contains k = false ↔ t.get? k = none := by
  simp [RHTable.contains]

open SeLe4n.Kernel.RobinHood in
/-- Q2-A: Bracket notation `t[k]?` is definitionally `t.get? k` for RHTable.
    This simp lemma allows rewrite lemmas stated in terms of `.get?` to fire
    on goals containing bracket notation. -/
theorem RHTable_getElem?_eq_get? {α β : Type} [BEq α] [Hashable α]
    (t : RHTable α β) (k : α) : t[k]? = t.get? k := rfl

open SeLe4n.Kernel.RobinHood in
/-- Q2-A: Contains after insert self. -/
theorem RHTable_contains_insert_self {α β : Type} [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) (v : β) (hExt : t.invExt) :
    (t.insert k v).contains k = true := by
  simp [RHTable.contains, RHTable_get?_insert_self t k v hExt]

open SeLe4n.Kernel.RobinHood in
/-- Q2-A: Contains after erase self. -/
theorem RHTable_contains_erase_self {α β : Type} [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) (hExt : t.invExt) :
    (t.erase k).contains k = false := by
  simp [RHTable.contains, RHTable_get?_erase_self t k hExt]

open SeLe4n.Kernel.RobinHood in
/-- Q2-A: Insert preserves invExt. -/
theorem RHTable_insert_preserves_invExt {α β : Type} [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) (v : β) (hExt : t.invExt) :
    (t.insert k v).invExt :=
  t.insert_preserves_invExt k v hExt

open SeLe4n.Kernel.RobinHood in
/-- Q2-A: Erase preserves invExt. -/
theorem RHTable_erase_preserves_invExt {α β : Type} [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) (hExt : t.invExt)
    (hSize : t.size < t.capacity) :
    (t.erase k).invExt :=
  t.erase_preserves_invExt k hExt hSize

open SeLe4n.Kernel.RobinHood in
/-- Q2-A: Empty table satisfies invExt. -/
theorem RHTable_empty_invExt {α β : Type} [BEq α] [Hashable α]
    (cap : Nat) (hPos : 0 < cap) :
    (RHTable.empty cap hPos : RHTable α β).invExt :=
  RHTable.empty_invExt cap hPos

open SeLe4n.Kernel.RobinHood in
/-- Q2-A: Filter preserves invExt. -/
theorem RHTable_filter_preserves_invExt {α β : Type} [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (f : α → β → Bool) (hExt : t.invExt) :
    (t.filter f).invExt :=
  RHTable.filter_preserves_invExt t f hExt

open SeLe4n.Kernel.RobinHood in
/-- Q2-A: Filter preserves key when predicate is true for that key. -/
theorem RHTable_filter_preserves_key {α β : Type} [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (f : α → β → Bool) (k : α)
    (hTrue : ∀ (k' : α) (v : β), (k' == k) = true → f k' v = true)
    (hExt : t.invExt) :
    (t.filter f).get? k = t.get? k :=
  RHTable.filter_preserves_key t f k hTrue hExt

open SeLe4n.Kernel.RobinHood in
/-- Q2-A: Filter idempotence at a key. -/
theorem RHTable_filter_filter_getElem? {α β : Type} [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (f : α → β → Bool) (k : α)
    (hExt : t.invExt) :
    ((t.filter f).filter f).get? k = (t.filter f).get? k :=
  RHTable.filter_filter_getElem? t f k hExt

open SeLe4n.Kernel.RobinHood in
/-- Q2-A: Inserting a key increases table size by at most 1. -/
theorem RHTable_size_insert_bound {α β : Type} [BEq α] [Hashable α]
    (t : RHTable α β) (k : α) (v : β) (hwf : t.WF) :
    (t.insert k v).size ≤ t.size + 1 :=
  RHTable.size_insert_le t k v hwf

open SeLe4n.Kernel.RobinHood in
/-- Q2-A: Erasing a key does not increase table size. -/
theorem RHTable_size_erase_bound {α β : Type} [BEq α] [Hashable α]
    (t : RHTable α β) (k : α) :
    (t.erase k).size ≤ t.size :=
  RHTable.size_erase_le t k

open SeLe4n.Kernel.RobinHood in
/-- Q2-A: Fold preserves a property through all entries. -/
theorem RHTable_fold_preserves {α β γ : Type} [BEq α] [Hashable α]
    (t : RHTable α β) (init : γ) (f : γ → α → β → γ)
    (P : γ → Prop) (hInit : P init)
    (hStep : ∀ acc k v, P acc → P (f acc k v)) :
    P (t.fold init f) :=
  RHTable.fold_preserves t init f P hInit hStep

-- ============================================================================
-- WS-G9: List.foldl HashSet bridge lemmas for observable-set precomputation
-- ============================================================================

/-- WS-G9: If `s.contains a = true`, then after folding any list with conditional
inserts, `a` remains in the set. Monotonicity of HashSet.insert under foldl. -/
theorem List.foldl_preserves_contains {α : Type} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]
    (p : α → Bool) (xs : List α) (s : Std.HashSet α) {a : α}
    (hContains : s.contains a = true) :
    (xs.foldl (fun acc x => if p x then acc.insert x else acc) s).contains a = true := by
  induction xs generalizing s with
  | nil => exact hContains
  | cons x xs ih =>
    simp only [List.foldl_cons]
    split
    · exact ih (s.insert x) (by rw [Std.HashSet.contains_insert]; simp [hContains])
    · exact ih s hContains

/-- WS-G9: If `a` is not in the list `xs`, then folding conditional inserts does
not change whether `a` is in the set. -/
theorem List.foldl_not_contains_when_absent {α : Type} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]
    (p : α → Bool) (xs : List α) (s : Std.HashSet α) {a : α}
    (hNotIn : a ∉ xs) :
    (xs.foldl (fun acc x => if p x then acc.insert x else acc) s).contains a =
      s.contains a := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    have hNe : a ≠ x := fun h => hNotIn (h ▸ List.Mem.head xs)
    have hNotInXs : a ∉ xs := fun h => hNotIn (List.Mem.tail x h)
    split
    · rw [ih (s.insert x) hNotInXs]
      rw [Std.HashSet.contains_insert]
      simp [Ne.symm hNe]
    · exact ih s hNotInXs

/-- WS-G9: If `p a = false`, then folding with conditional inserts guarded by `p`
preserves `a`'s containment status. Whether `a` is in the list or not, `p a = false`
prevents any insertion of `a`, so the final `contains a` equals `s.contains a`. -/
theorem List.foldl_preserves_when_pred_false {α : Type} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]
    (p : α → Bool) (xs : List α) (s : Std.HashSet α) {a : α}
    (hPa : p a = false) :
    (xs.foldl (fun acc x => if p x then acc.insert x else acc) s).contains a =
      s.contains a := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    by_cases hEq : x = a
    · -- x = a: since p a = false, the if-branch doesn't insert, leaving s unchanged
      subst hEq
      split
      · rename_i hContra; rw [hPa] at hContra; exact absurd hContra (by decide)
      · exact ih s
    · -- x ≠ a: whether or not x is inserted, a's membership is unchanged
      split
      · -- p x = true: x is inserted; a ≠ x so a remains unchanged
        rw [ih (s.insert x), Std.HashSet.contains_insert]
        simp [beq_false_of_ne hEq]
      · -- p x = false: nothing inserted
        exact ih s

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

-- ============================================================================
-- WS-H14d: Identifier roundtrip and injectivity proofs
-- ============================================================================

/-- WS-H14d: ObjId roundtrip — construct then project. -/
theorem ObjId.toNat_ofNat (n : Nat) : (ObjId.ofNat n).toNat = n := rfl
/-- WS-H14d: ObjId roundtrip — project then reconstruct. -/
theorem ObjId.ofNat_toNat (id : ObjId) : ObjId.ofNat id.toNat = id := rfl
/-- WS-H14d: ObjId injectivity. -/
theorem ObjId.ofNat_injective {n₁ n₂ : Nat} (h : ObjId.ofNat n₁ = ObjId.ofNat n₂) : n₁ = n₂ := by
  cases h; rfl
/-- WS-H14d: ObjId extensionality. -/
theorem ObjId.ext {a b : ObjId} (h : a.val = b.val) : a = b := by
  cases a; cases b; simp_all

/-- WS-H14d: ThreadId roundtrip — construct then project. -/
theorem ThreadId.toNat_ofNat (n : Nat) : (ThreadId.ofNat n).toNat = n := rfl
/-- WS-H14d: ThreadId roundtrip — project then reconstruct. -/
theorem ThreadId.ofNat_toNat (id : ThreadId) : ThreadId.ofNat id.toNat = id := rfl
/-- WS-H14d: ThreadId injectivity. -/
theorem ThreadId.ofNat_injective {n₁ n₂ : Nat} (h : ThreadId.ofNat n₁ = ThreadId.ofNat n₂) : n₁ = n₂ := by
  cases h; rfl

/-- WS-H14d: DomainId roundtrip — construct then project. -/
theorem DomainId.toNat_ofNat (n : Nat) : (DomainId.ofNat n).toNat = n := rfl
/-- WS-H14d: DomainId roundtrip — project then reconstruct. -/
theorem DomainId.ofNat_toNat (id : DomainId) : DomainId.ofNat id.toNat = id := rfl
/-- WS-H14d: DomainId injectivity. -/
theorem DomainId.ofNat_injective {n₁ n₂ : Nat} (h : DomainId.ofNat n₁ = DomainId.ofNat n₂) : n₁ = n₂ := by
  cases h; rfl
/-- WS-H14d: DomainId extensionality. -/
theorem DomainId.ext {a b : DomainId} (h : a.val = b.val) : a = b := by
  cases a; cases b; simp_all

/-- WS-H14d: Priority roundtrip — construct then project. -/
theorem Priority.toNat_ofNat (n : Nat) : (Priority.ofNat n).toNat = n := rfl
/-- WS-H14d: Priority roundtrip — project then reconstruct. -/
theorem Priority.ofNat_toNat (p : Priority) : Priority.ofNat p.toNat = p := rfl
/-- WS-H14d: Priority injectivity. -/
theorem Priority.ofNat_injective {n₁ n₂ : Nat} (h : Priority.ofNat n₁ = Priority.ofNat n₂) : n₁ = n₂ := by
  cases h; rfl
/-- WS-H14d: Priority extensionality. -/
theorem Priority.ext {a b : Priority} (h : a.val = b.val) : a = b := by
  cases a; cases b; simp_all

/-- WS-H14d: Deadline roundtrip — construct then project. -/
theorem Deadline.toNat_ofNat (n : Nat) : (Deadline.ofNat n).toNat = n := rfl
/-- WS-H14d: Deadline roundtrip — project then reconstruct. -/
theorem Deadline.ofNat_toNat (d : Deadline) : Deadline.ofNat d.toNat = d := rfl
/-- WS-H14d: Deadline injectivity. -/
theorem Deadline.ofNat_injective {n₁ n₂ : Nat} (h : Deadline.ofNat n₁ = Deadline.ofNat n₂) : n₁ = n₂ := by
  cases h; rfl
/-- WS-H14d: Deadline extensionality. -/
theorem Deadline.ext {a b : Deadline} (h : a.val = b.val) : a = b := by
  cases a; cases b; simp_all

/-- WS-H14d: Irq roundtrip — construct then project. -/
theorem Irq.toNat_ofNat (n : Nat) : (Irq.ofNat n).toNat = n := rfl
/-- WS-H14d: Irq roundtrip — project then reconstruct. -/
theorem Irq.ofNat_toNat (irq : Irq) : Irq.ofNat irq.toNat = irq := rfl
/-- WS-H14d: Irq injectivity. -/
theorem Irq.ofNat_injective {n₁ n₂ : Nat} (h : Irq.ofNat n₁ = Irq.ofNat n₂) : n₁ = n₂ := by
  cases h; rfl
/-- WS-H14d: Irq extensionality. -/
theorem Irq.ext {a b : Irq} (h : a.val = b.val) : a = b := by
  cases a; cases b; simp_all

/-- WS-H14d: ServiceId roundtrip — construct then project. -/
theorem ServiceId.toNat_ofNat (n : Nat) : (ServiceId.ofNat n).toNat = n := rfl
/-- WS-H14d: ServiceId roundtrip — project then reconstruct. -/
theorem ServiceId.ofNat_toNat (id : ServiceId) : ServiceId.ofNat id.toNat = id := rfl
/-- WS-H14d: ServiceId injectivity. -/
theorem ServiceId.ofNat_injective {n₁ n₂ : Nat} (h : ServiceId.ofNat n₁ = ServiceId.ofNat n₂) : n₁ = n₂ := by
  cases h; rfl
/-- WS-H14d: ServiceId extensionality. -/
theorem ServiceId.ext {a b : ServiceId} (h : a.val = b.val) : a = b := by
  cases a; cases b; simp_all

/-- WS-H14d: CPtr roundtrip — construct then project. -/
theorem CPtr.toNat_ofNat (n : Nat) : (CPtr.ofNat n).toNat = n := rfl
/-- WS-H14d: CPtr roundtrip — project then reconstruct. -/
theorem CPtr.ofNat_toNat (ptr : CPtr) : CPtr.ofNat ptr.toNat = ptr := rfl
/-- WS-H14d: CPtr injectivity. -/
theorem CPtr.ofNat_injective {n₁ n₂ : Nat} (h : CPtr.ofNat n₁ = CPtr.ofNat n₂) : n₁ = n₂ := by
  cases h; rfl
/-- WS-H14d: CPtr extensionality. -/
theorem CPtr.ext {a b : CPtr} (h : a.val = b.val) : a = b := by
  cases a; cases b; simp_all

/-- WS-H14d: Slot roundtrip — construct then project. -/
theorem Slot.toNat_ofNat (n : Nat) : (Slot.ofNat n).toNat = n := rfl
/-- WS-H14d: Slot roundtrip — project then reconstruct. -/
theorem Slot.ofNat_toNat (slot : Slot) : Slot.ofNat slot.toNat = slot := rfl
/-- WS-H14d: Slot injectivity. -/
theorem Slot.ofNat_injective {n₁ n₂ : Nat} (h : Slot.ofNat n₁ = Slot.ofNat n₂) : n₁ = n₂ := by
  cases h; rfl
/-- WS-H14d: Slot extensionality. -/
theorem Slot.ext {a b : Slot} (h : a.val = b.val) : a = b := by
  cases a; cases b; simp_all

/-- R6-B: Badge.ofNatMasked roundtrip — construct then project (mod). -/
theorem Badge.toNat_ofNatMasked (n : Nat) :
    (Badge.ofNatMasked n).toNat = n % machineWordMax := rfl
/-- R6-B: Badge.ofNatMasked of a valid badge is identity. -/
theorem Badge.ofNatMasked_toNat (b : Badge) (h : b.valid) :
    Badge.ofNatMasked b.toNat = b := by
  unfold Badge.ofNatMasked Badge.toNat Badge.valid machineWordMax machineWordBits at *
  exact congrArg Badge.mk (Nat.mod_eq_of_lt h)
/-- WS-H14d: Badge injectivity (val-level). -/
theorem Badge.val_injective {a b : Badge} (h : a.val = b.val) : a = b := by
  cases a; cases b; simp_all
/-- WS-H14d: Badge extensionality. -/
theorem Badge.ext {a b : Badge} (h : a.val = b.val) : a = b := by
  cases a; cases b; simp_all

/-- WS-H14d: ASID roundtrip — construct then project. -/
theorem ASID.toNat_ofNat (n : Nat) : (ASID.ofNat n).toNat = n := rfl
/-- WS-H14d: ASID roundtrip — project then reconstruct. -/
theorem ASID.ofNat_toNat (asid : ASID) : ASID.ofNat asid.toNat = asid := rfl
/-- WS-H14d: ASID injectivity. -/
theorem ASID.ofNat_injective {n₁ n₂ : Nat} (h : ASID.ofNat n₁ = ASID.ofNat n₂) : n₁ = n₂ := by
  cases h; rfl
/-- WS-H14d: ASID extensionality. -/
theorem ASID.ext {a b : ASID} (h : a.val = b.val) : a = b := by
  cases a; cases b; simp_all

/-- WS-H14d: VAddr roundtrip — construct then project. -/
theorem VAddr.toNat_ofNat (n : Nat) : (VAddr.ofNat n).toNat = n := rfl
/-- WS-H14d: VAddr roundtrip — project then reconstruct. -/
theorem VAddr.ofNat_toNat (addr : VAddr) : VAddr.ofNat addr.toNat = addr := rfl
/-- WS-H14d: VAddr injectivity. -/
theorem VAddr.ofNat_injective {n₁ n₂ : Nat} (h : VAddr.ofNat n₁ = VAddr.ofNat n₂) : n₁ = n₂ := by
  cases h; rfl
/-- WS-H14d: VAddr extensionality. -/
theorem VAddr.ext {a b : VAddr} (h : a.val = b.val) : a = b := by
  cases a; cases b; simp_all

/-- WS-H14d: PAddr roundtrip — construct then project. -/
theorem PAddr.toNat_ofNat (n : Nat) : (PAddr.ofNat n).toNat = n := rfl
/-- WS-H14d: PAddr roundtrip — project then reconstruct. -/
theorem PAddr.ofNat_toNat (addr : PAddr) : PAddr.ofNat addr.toNat = addr := rfl
/-- WS-H14d: PAddr injectivity. -/
theorem PAddr.ofNat_injective {n₁ n₂ : Nat} (h : PAddr.ofNat n₁ = PAddr.ofNat n₂) : n₁ = n₂ := by
  cases h; rfl
/-- WS-H14d: PAddr extensionality. -/
theorem PAddr.ext {a b : PAddr} (h : a.val = b.val) : a = b := by
  cases a; cases b; simp_all

-- ============================================================================
-- WS-H14f: Sentinel predicate completion
-- ============================================================================

/-- WS-H14f: ThreadId validity — nonzero value. -/
def ThreadId.valid (id : ThreadId) : Prop := id.val ≠ 0

/-- WS-H14f: ThreadId valid iff not reserved. -/
theorem ThreadId.valid_iff_not_reserved (id : ThreadId) :
    id.valid ↔ id.isReserved = false := by
  simp [ThreadId.valid, ThreadId.isReserved]

/-- WS-H14f: The sentinel ThreadId is not valid. -/
theorem ThreadId.sentinel_not_valid : ¬ ThreadId.sentinel.valid := by
  simp [ThreadId.valid, ThreadId.sentinel]

/-- WS-H14f: ServiceId validity — nonzero value. -/
def ServiceId.valid (id : ServiceId) : Prop := id.val ≠ 0

/-- WS-H14f: ServiceId valid iff not reserved. -/
theorem ServiceId.valid_iff_not_reserved (id : ServiceId) :
    id.valid ↔ id.isReserved = false := by
  simp [ServiceId.valid, ServiceId.isReserved]

/-- WS-H14f: The sentinel ServiceId is not valid. -/
theorem ServiceId.sentinel_not_valid : ¬ ServiceId.sentinel.valid := by
  simp [ServiceId.valid, ServiceId.sentinel]

/-- WS-H14f: CPtr validity — nonzero value. -/
def CPtr.valid (ptr : CPtr) : Prop := ptr.val ≠ 0

/-- WS-H14f: CPtr valid iff not reserved. -/
theorem CPtr.valid_iff_not_reserved (ptr : CPtr) :
    ptr.valid ↔ ptr.isReserved = false := by
  simp [CPtr.valid, CPtr.isReserved]

/-- WS-H14f: The sentinel CPtr is not valid. -/
theorem CPtr.sentinel_not_valid : ¬ CPtr.sentinel.valid := by
  simp [CPtr.valid, CPtr.sentinel]

/-- WS-H14f: The sentinel ObjId is not valid. -/
theorem ObjId.sentinel_not_valid : ¬ ObjId.sentinel.valid := by
  simp [ObjId.valid, ObjId.sentinel]

end SeLe4n
