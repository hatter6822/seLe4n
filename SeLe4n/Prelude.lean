import Std.Data.HashMap
import Std.Data.HashSet

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

/-- WS-G1: Hash instance for HashMap/HashSet keying. Delegates to Nat hash.
    BEq is already provided by DecidableEq via instBEqOfDecidableEq. -/
@[inline] instance : Hashable ThreadId where
  hash a := hash a.val

namespace ThreadId

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
distinct thread IDs cannot alias the same object. -/
@[inline] def toObjId (id : ThreadId) : ObjId := ObjId.ofNat id.toNat

instance instOfNat (n : Nat) : OfNat ThreadId n where
  ofNat := ⟨n⟩

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

instance instOfNat (n : Nat) : OfNat DomainId n where
  ofNat := ⟨n⟩

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

instance instOfNat (n : Nat) : OfNat Priority n where
  ofNat := ⟨n⟩

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

instance instOfNat (n : Nat) : OfNat Deadline n where
  ofNat := ⟨n⟩

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

instance instOfNat (n : Nat) : OfNat Irq n where
  ofNat := ⟨n⟩

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

/-- WS-G1: Hash instance for HashMap/HashSet keying. Delegates to Nat hash.
    BEq is already provided by DecidableEq via instBEqOfDecidableEq. -/
@[inline] instance : Hashable CPtr where
  hash a := hash a.val

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

/-- WS-G1: Hash instance for HashMap/HashSet keying. Delegates to Nat hash.
    BEq is already provided by DecidableEq via instBEqOfDecidableEq. -/
@[inline] instance : Hashable Slot where
  hash a := hash a.val

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

/-- WS-G1: Hash instance for HashMap/HashSet keying. Delegates to Nat hash.
    BEq is already provided by DecidableEq via instBEqOfDecidableEq. -/
@[inline] instance : Hashable Badge where
  hash a := hash a.val

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

/-- WS-G1: Hash instance for HashMap/HashSet keying. Delegates to Nat hash.
    BEq is already provided by DecidableEq via instBEqOfDecidableEq. -/
@[inline] instance : Hashable ASID where
  hash a := hash a.val

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

/-- WS-G1: Hash instance for HashMap/HashSet keying. Delegates to Nat hash.
    BEq is already provided by DecidableEq via instBEqOfDecidableEq. -/
@[inline] instance : Hashable VAddr where
  hash a := hash a.val

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

/-- WS-G1: Hash instance for HashMap/HashSet keying. Delegates to Nat hash.
    BEq is already provided by DecidableEq via instBEqOfDecidableEq. -/
@[inline] instance : Hashable PAddr where
  hash a := hash a.val

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

end KernelM

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
-- WS-G2: HashMap/HashSet bridge lemmas for proof ergonomics
-- ============================================================================

/-- WS-G2: Bridge lemma for `HashMap.get?` after `insert`. Maps to the underlying
    `DHashMap.Const.get?_insert` for types with `EquivBEq` and `LawfulHashable`. -/
theorem HashMap_get?_insert {α β : Type} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {m : Std.HashMap α β} {k a : α} {v : β} :
    (m.insert k v).get? a = if k == a then some v else m.get? a :=
  Std.DHashMap.Const.get?_insert

/-- WS-G2: Bridge lemma for `HashMap.get?` on empty. -/
theorem HashMap_get?_empty {α β : Type} [BEq α] [Hashable α]
    {a : α} : (∅ : Std.HashMap α β).get? a = none :=
  Std.DHashMap.Const.get?_empty

/-- WS-G2: Bridge lemma for `HashMap.get?` after `erase`. -/
theorem HashMap_get?_erase {α β : Type} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {m : Std.HashMap α β} {k a : α} :
    (m.erase k).get? a = if k == a then none else m.get? a :=
  Std.DHashMap.Const.get?_erase

/-- WS-G2: Bridge lemma for `HashMap[k]?` after `insert` (getElem? notation).
    Matches goals where `simp` has normalized `.get?` to `[k]?`. -/
theorem HashMap_getElem?_insert {α β : Type} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {m : Std.HashMap α β} {k a : α} {v : β} :
    (m.insert k v)[a]? = if k == a then some v else m[a]? :=
  Std.HashMap.getElem?_insert

/-- WS-G2: Bridge lemma for `HashMap[k]?` on empty (getElem? notation). -/
theorem HashMap_getElem?_empty {α β : Type} [BEq α] [Hashable α]
    {a : α} : (∅ : Std.HashMap α β)[a]? = none :=
  Std.HashMap.getElem?_empty

/-- WS-G2: Bridge lemma for `HashMap[k]?` after `erase` (getElem? notation). -/
theorem HashMap_getElem?_erase {α β : Type} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {m : Std.HashMap α β} {k a : α} :
    (m.erase k)[a]? = if k == a then none else m[a]? :=
  Std.HashMap.getElem?_erase

/-- WS-G2: Equate `HashMap[k]?` (getElem?) and `.get?` — use explicitly, not
    as `@[simp]` (conflicts with `Std.HashMap.get?_eq_getElem?`). -/
theorem HashMap_getElem?_eq_get? {α β : Type} [BEq α] [Hashable α]
    (m : Std.HashMap α β) (k : α) : m[k]? = m.get? k := rfl

/-- WS-G2: Equate `.get?` and `HashMap[k]?` — use explicitly in rewrites. -/
theorem HashMap_get?_eq_getElem? {α β : Type} [BEq α] [Hashable α]
    (m : Std.HashMap α β) (k : α) : m.get? k = m[k]? := rfl

/-- WS-G5: Bridge lemma for `HashMap.filter` key preservation.
When the filter predicate `f` is guaranteed to return `true` for key `k`
(and any BEq-equivalent key), `filter` does not remove `k`'s entry.

This bridges over the dependent `Option.pfilter` that `Std.HashMap.getElem?_filter`
produces, which is difficult to work with directly due to the membership proof
in `getKey`. -/
theorem HashMap_filter_preserves_key
    {α β : Type _} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (m : Std.HashMap α β) (f : α → β → Bool) (k : α)
    (hTrue : ∀ (k' : α) (v : β), (k' == k) = true → f k' v = true) :
    (m.filter f)[k]? = m[k]? := by
  simp only [Std.HashMap.getElem?_filter]
  suffices h : ∀ (o : Option β) (p : (a : β) → o = some a → Bool),
      (∀ a (h : o = some a), p a h = true) → o.pfilter p = o by
    apply h
    intro a ha
    have hMem : k ∈ m := Std.HashMap.mem_iff_isSome_getElem?.mpr (by simp [ha])
    exact hTrue _ _ (Std.HashMap.getKey_beq hMem)
  intro o p hp
  cases o with
  | none => rfl
  | some v => simp [hp]

/-- WS-G5: Lookup-level filter idempotency for HashMap.
For a predicate that ignores the key (depends only on the value),
double-filtering is lookup-equivalent to single-filtering.

This avoids the need for structural `HashMap.filter_filter` (which is
unavailable in Lean 4.28.0's Std library due to `AssocList.filter`
internal bucket-ordering differences). -/
theorem HashMap_filter_filter_getElem?
    {α β : Type _} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (m : Std.HashMap α β) (f : α → β → Bool) (k : α) :
    ((m.filter f).filter f)[k]? = (m.filter f)[k]? := by
  by_cases hMem : k ∈ m.filter f
  · -- k is in m.filter f; the value there already satisfies f,
    -- so the second filter preserves the same entry.
    have ⟨_, hF⟩ := Std.HashMap.mem_filter.mp hMem
    have hMemFF : k ∈ (m.filter f).filter f := by
      rw [Std.HashMap.mem_filter]
      refine ⟨hMem, ?_⟩
      rw [Std.HashMap.getKey_filter]
      rw [Std.HashMap.getElem_filter]
      exact hF
    have h1 := Std.HashMap.getElem?_eq_some_getElem hMemFF
    have h2 := Std.HashMap.getElem?_eq_some_getElem hMem
    have h3 : ((m.filter f).filter f)[k] = (m.filter f)[k] :=
      Std.HashMap.getElem_filter
    rw [h1, h2, h3]
  · -- k ∉ m.filter f ⇒ k ∉ (m.filter f).filter f ⇒ both sides are none
    have hNotMemFF : k ∉ (m.filter f).filter f :=
      fun h => hMem (Std.HashMap.mem_of_mem_filter h)
    rw [Std.HashMap.getElem?_eq_none hNotMemFF,
        Std.HashMap.getElem?_eq_none hMem]

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

end SeLe4n
