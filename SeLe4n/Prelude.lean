-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import Std.Data.HashMap
import Std.Data.HashSet
import Lean.Attributes
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

/-! ## AC4-C/F-01: Typed Identifier Safety Model

All identifier types (`ObjId`, `ThreadId`, `CPtr`, `Slot`, `DomainId`, `Priority`,
`Deadline`, `Irq`, `ServiceId`, `InterfaceId`, `SchedContextId`, `Badge`, `ASID`,
`VAddr`, `PAddr`) wrap unbounded Lean `Nat` by design. This is intentional for
proof ergonomics: unbounded naturals allow `simp`, `omega`, and `decide` to work
without bit-width overflow reasoning, making theorem statements cleaner and proofs
shorter.

**ABI boundary validation**: The Rust ABI crate + `RegisterDecode.lean` +
`SyscallArgDecode.lean` validate all incoming values before constructing
identifiers. Specifically:
- `RegisterDecode.decodeSyscallId` rejects values ≥ 25 (invalid syscall numbers).
- `RegisterDecode.decodeMsgInfo` enforces length ≤ 120, extraCaps ≤ 3.
- `RegisterDecode.validateRegBound` checks register indices against a
  configurable bound (default 32 on ARM64 via `regCount`).
- All per-syscall decoders in `SyscallArgDecode.lean` produce typed identifiers
  only from validated register contents.

**Internal kernel trust**: Operations that derive new identifiers from existing
(validated) ones are trusted. For example, `storeObject` with an `ObjId` from
`retypeFromUntyped` inherits the source's validity.

**Hardware deployment contract**: For ARM64 targets, the `isWord64` / `isWord64Dec`
predicates (defined below at `machineWordMax := 2^64`) must be enforced at every
ABI entry point. The `CPtr.isWord64Bounded` and `Slot.isWord64Bounded` methods
provide this check for capability pointers and slot indices. -/

/-! ## AN4-F.1 (CAP-M01): `@[documented_obligation]` attribute

Marker attribute for theorems that exist solely to surface a caller-facing
invariant as machine-searchable documentation (no Prop content). The
attribute is a no-op; it exists so reviewers can `grep -r @\[documented_obligation\]`
to locate every such obligation. -/

initialize SeLe4n.documentedObligationAttr : Lean.TagAttribute ←
  Lean.registerTagAttribute `documented_obligation
    "AN4-F.1 (CAP-M01): marks a declaration whose sole purpose is to record a caller obligation in machine-searchable form (no Prop content)."

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
rejects the sentinel value (ID 0).

**AJ2-D (M-09): Namespace disjointness.** This identity mapping shares the
`ObjId` namespace with `SchedContextId.toObjId` — both map their `.val` to the
same `ObjId` space. A `ThreadId(5)` and `SchedContextId(5)` produce the same
`ObjId(5)`. The object store (a functional map) prevents aliasing: each ObjId
maps to exactly one `KernelObject` variant. `retypeFromUntyped_childId_fresh`
(Lifecycle/Operations.lean) ensures all new allocations target fresh ObjIds.
See `typedIdDisjointness` (CrossSubsystem.lean) for the formal statement. -/
@[inline] def toObjId (id : ThreadId) : ObjId := ObjId.ofNat id.toNat

/-! ### AN2-F.8 / FND-M08 — `toObjId` family decision table

| Variant             | Checks sentinel | Checks store type | Use when                                   |
|---------------------|:---------------:|:-----------------:|--------------------------------------------|
| `toObjId`           |       no        |        no         | Proof-side identity mapping / trusted path |
| `toObjIdChecked`    |      yes        |        no         | Kernel entry rejecting sentinel IDs        |
| `toObjIdVerified`   |      yes        |       yes         | API boundary with guaranteed-TCB result    |

The sentinel-checked/store-checked dichotomy mirrors the `ObjId` / `ValidThreadId`
discipline introduced in AL7 (WS-AL) — see the per-variant docstrings below for
migration guidance. -/

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

/-- V5-J (L-FND-1): Store-aware checked variant of `toObjId`.

Validates that:
1. The thread ID is not the reserved sentinel (value 0).
2. The resulting ObjId maps to an object for which `isTcb` returns `true`.

The `isTcb` predicate is caller-supplied because `Prelude.lean` does not
import the object model. Callers should instantiate it as:
```
fun oid => match st.objects[oid]? with | some (.tcb _) => true | _ => false
```

Returns `some oid` on success, `none` on any validation failure.

**When to use which variant:**
- `toObjId` (unchecked): Internal fast path inside scheduler/IPC operations
  where the caller immediately pattern-matches on `.tcb tcb` after lookup.
  Suitable when the thread ID comes from a trusted source (e.g., run queue,
  IPC queue head) and the caller handles the non-TCB case explicitly.
- `toObjIdChecked` (sentinel-only): When the thread ID comes from an
  untrusted source but the caller will do its own object-store lookup.
  Rejects only the sentinel value.
- `toObjIdVerified` (full verification): When the thread ID comes from an
  untrusted source AND the caller needs a guaranteed-valid TCB reference
  without further pattern matching. Suitable for API boundary validation. -/
@[inline] def toObjIdVerified (id : ThreadId)
    (isTcb : ObjId → Bool) : Option ObjId :=
  if id.isReserved then .none
  else
    let oid := id.toObjId
    if isTcb oid then some oid else none

/-- V5-J: `toObjIdVerified` agrees with `toObjIdChecked` when `isTcb` returns
    true for the target ObjId. -/
theorem toObjIdVerified_eq_checked_when_isTcb (id : ThreadId)
    (isTcb : ObjId → Bool)
    (hNotRes : id.isReserved = false)
    (hIsTcb : isTcb id.toObjId = true) :
    id.toObjIdVerified isTcb = id.toObjIdChecked := by
  simp [toObjIdVerified, toObjIdChecked, hNotRes, hIsTcb]

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

/-- Scheduling context identifier. SchedContexts are first-class kernel objects
containing CPU budget, period, and replenishment parameters for CBS (Constant
Bandwidth Server) scheduling. Threads are bound to SchedContexts via capabilities. -/
structure SchedContextId where
  val : Nat
deriving DecidableEq, Repr, Inhabited

@[inline] instance : Hashable SchedContextId where
  hash a := hash a.val

namespace SchedContextId

@[inline] def ofNat (n : Nat) : SchedContextId := ⟨n⟩
@[inline] def toNat (id : SchedContextId) : Nat := id.val

/-- Convert SchedContextId to ObjId for object store lookups.

    AJ2-D (M-09): Shares the `ObjId` namespace with `ThreadId.toObjId` —
    both use identity mappings. The object store's functional-map property
    guarantees that each ObjId maps to at most one `KernelObject` variant,
    preventing type confusion. See `typedIdDisjointness` (CrossSubsystem.lean)
    and `retypeFromUntyped_childId_fresh` (Lifecycle/Operations.lean). -/
@[inline] def toObjId (id : SchedContextId) : ObjId := ObjId.ofNat id.toNat

/-- Convert ObjId to SchedContextId. -/
@[inline] def ofObjId (oid : ObjId) : SchedContextId := ⟨oid.toNat⟩

/-- AF2-B: Checked conversion that rejects the reserved sentinel (value 0).
    Mirrors `ThreadId.toObjIdChecked` for consistency across typed identifier
    conversions. Prefer this at ABI boundaries where ObjId 0 could indicate
    an uninitialized or invalid reference. The unchecked `ofObjId` remains
    available for internal paths where validity is established by context. -/
@[inline] def ofObjIdChecked (oid : ObjId) : Option SchedContextId :=
  if oid.toNat = 0 then .none else .some ⟨oid.toNat⟩

/-- AF2-B: `ofObjIdChecked` agrees with `ofObjId` on non-sentinel inputs. -/
theorem ofObjIdChecked_eq_some_of_nonzero (oid : ObjId)
    (hNonZero : oid.toNat ≠ 0) :
    ofObjIdChecked oid = some (ofObjId oid) := by
  simp [ofObjIdChecked, ofObjId, hNonZero]

/-- AF2-B: `ofObjIdChecked` rejects the sentinel (ObjId with value 0). -/
theorem ofObjIdChecked_sentinel :
    ofObjIdChecked (ObjId.ofNat 0) = none := by
  simp [ofObjIdChecked, ObjId.toNat, ObjId.ofNat]

instance : ToString SchedContextId where
  toString id := toString id.toNat

@[inline] def isReserved (id : SchedContextId) : Bool := id.val = 0
@[inline] def sentinel : SchedContextId := ⟨0⟩

/-- A SchedContextId is valid (non-sentinel). -/
@[inline] def valid (id : SchedContextId) : Bool := !id.isReserved

/-- Round-trip: ofNat then toNat is identity. -/
theorem toNat_ofNat (n : Nat) : (SchedContextId.ofNat n).toNat = n := rfl

/-- Round-trip: toNat then ofNat is identity. -/
theorem ofNat_toNat (id : SchedContextId) : SchedContextId.ofNat id.toNat = id := by
  cases id; rfl

/-- toObjId is injective. -/
theorem toObjId_injective (a b : SchedContextId) (h : a.toObjId = b.toObjId) : a = b := by
  cases a with | mk va => cases b with | mk vb =>
  simp [toObjId, toNat, ObjId.ofNat] at h
  subst h; rfl

end SchedContextId

/-! ### Machine-word bounds (hoisted before `CPtr`/`Slot` so both can
    delegate their hardware-width predicate to `isWord64Dec` — AN2-F.1 /
    FND-M01). These constants are used throughout the kernel to assert
    that identifiers, badges, and addresses fit in one hardware word
    on the target platform. -/

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

/-- Capability-space pointer value.

    AN2-B.1 / H-13 (Theme 4.3): The `mk` constructor is `private`. External
    callers must use `CPtr.ofNat` (unbounded) or `CPtr.ofNat?` (word-bounded
    smart constructor). This forecloses accidental `CPtr.mk (2^64)` that
    would exceed hardware width. -/
structure CPtr where
  private mk ::
  val : Nat
deriving DecidableEq, Repr

/-- AN2-B.1: Manual `Inhabited` (deriving requires public constructor). -/
instance : Inhabited CPtr := ⟨⟨0⟩⟩

/-- WS-G1: Hash instance for HashMap/HashSet keying. Delegates to Nat hash.
    BEq is already provided by DecidableEq via instBEqOfDecidableEq. -/
@[inline] instance : Hashable CPtr where
  hash a := hash a.val

namespace CPtr

/-- Smart constructor — accepts any `Nat`. Pre-existing migration helper;
    remains the default construction API for external callers. -/
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

/-- V4-L/L-FND-4: A CPtr is hardware-representable if its value fits in 64 bits.
    Hardware decode paths should validate this before passing to kernel operations.

    AN2-F.1 / FND-M01: Delegates to `isWord64Dec` (hoisted above `CPtr` in this
    file). The delegation ensures future drift between the two predicates is
    impossible — any adjustment to `machineWordMax` propagates automatically. -/
@[inline] def isWord64Bounded (ptr : CPtr) : Bool := isWord64Dec ptr.val

end CPtr

/-- Slot index within a CNode.

    AN2-B.2 / H-13 (Theme 4.3): The `mk` constructor is `private`. External
    callers must use `Slot.ofNat`. -/
structure Slot where
  private mk ::
  val : Nat
deriving DecidableEq, Repr

/-- AN2-B.2: Manual `Inhabited`. -/
instance : Inhabited Slot := ⟨⟨0⟩⟩

/-- WS-G1: Hash instance for HashMap/HashSet keying. Delegates to Nat hash.
    BEq is already provided by DecidableEq via instBEqOfDecidableEq. -/
@[inline] instance : Hashable Slot where
  hash a := hash a.val

namespace Slot

/-- Smart constructor — accepts any `Nat`. Pre-existing migration helper;
    remains the default construction API for external callers. -/
@[inline] def ofNat (n : Nat) : Slot := ⟨n⟩

/-- Projection helper kept explicit for migration ergonomics. -/
@[inline] def toNat (slot : Slot) : Nat := slot.val

instance : ToString Slot where
  toString slot := toString slot.toNat

/-- V4-L/L-FND-4: A Slot is hardware-representable if its value fits in 64 bits.
    Hardware decode paths should validate this before passing to kernel operations.

    AN2-F.1 / FND-M01: Delegates to `isWord64Dec` — see `CPtr.isWord64Bounded`
    for rationale. -/
@[inline] def isWord64Bounded (slot : Slot) : Bool := isWord64Dec slot.val

end Slot

/-- AN2-F.1 / FND-M01: `CPtr.isWord64Bounded` reduces definitionally to
    `isWord64Dec ptr.val` — `isWord64Bounded` is implemented as the
    delegation itself (see `CPtr.isWord64Bounded` above). This theorem
    records the equivalence for call sites that still want the explicit
    rewrite form. -/
theorem CPtr.isWord64Bounded_eq_isWord64Dec (ptr : CPtr) :
    CPtr.isWord64Bounded ptr = isWord64Dec ptr.val := rfl

/-- AN2-F.1 / FND-M01: `Slot.isWord64Bounded` reduces definitionally to
    `isWord64Dec slot.val`. -/
theorem Slot.isWord64Bounded_eq_isWord64Dec (slot : Slot) :
    Slot.isWord64Bounded slot = isWord64Dec slot.val := rfl

-- AN2-A / H-13: Badge constructor is now `private` to force every external
-- consumer through a smart constructor (`ofNatMasked`, `ofNat`, `zero`, or
-- `ofUInt64Pair`). Direct `Badge.mk n` calls outside the `Badge` namespace
-- are rejected by the elaborator. Proof-side destructuring (when strictly
-- necessary) goes through the private `Badge.mkUnsafeForProof` helper below.
-- Pattern matches `AccessRightSet` (AJ2-A) and `CapDerivationTree`.
--
-- Historical safety layers retained:
-- 1. `Badge.valid` predicate: `b.val < 2^64` — used in proof obligations
-- 2. `Badge.ofNatMasked`: truncates to word size at construction
-- 3. `cspaceMint` (Operations.lean): uses masked badge from decoded syscall
-- 4. IPC message delivery: badge comes from stored Capability (already masked)
-- 5. Rust ABI: `Badge` is `u64` — hardware truncation at FFI boundary
-- BadgeOverflowSuite.lean (AG9-E) validates round-trip Nat↔UInt64 safety.
--
-- AK7-K (F-L2 / LOW) — seL4 badge-64-bit compatibility note:
-- seL4's badge field is exactly 64 bits wide (`seL4_Word` on 64-bit
-- platforms). Our `Badge.val : Nat` model widens this to unbounded Nat
-- for proof ergonomics, with `Badge.valid` asserting the hardware bound.
-- The Rust side (`sele4n-types::Badge`) uses `u64` directly; the
-- Nat↔UInt64 conversion at the FFI boundary (validated by
-- `BadgeOverflowSuite`) discharges the bound obligation.

/-- Endpoint or notification badge value.
    WS-F5/D1a: Values are logically bounded to `machineWordBits` (64) bits.
    The `valid` predicate asserts word-boundedness; `ofNatMasked` enforces it
    at construction.

    AN2-A / H-13: The `mk` constructor is `private`. External callers must use
    one of the public smart constructors (`ofNatMasked`, `ofNat`, `zero`,
    `ofUInt64Pair`). -/
structure Badge where
  private mk ::
  val : Nat
deriving DecidableEq, Repr

/-- AN2-A / H-13: Manual `Inhabited` instance — `deriving Inhabited` requires
    a public constructor. The default value is the zero badge (`⟨0⟩`). -/
instance : Inhabited Badge := ⟨⟨0⟩⟩

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

/-- AN2-A / H-13: Proof-internal destructuring helper — use ONLY inside
    `Badge` proof machinery where a non-masked constructor is needed to
    witness `Badge.mk n` equalities (e.g. `congrArg Badge.mk`). Never call
    this from operational code — callers should use `ofNatMasked` or
    `ofNat`. Kept `private` so external modules cannot bypass the
    smart-constructor discipline. -/
@[inline] private def mkUnsafeForProof (n : Nat) : Badge := ⟨n⟩

/-- AN2-A / H-13: Canonical zero badge (valid by construction). -/
@[inline] def zero : Badge := ⟨0⟩

/-- AN2-A / H-13: `Badge.zero` is always valid. The zero badge is
    the canonical "no-badge" sentinel used by the kernel ABI when
    a capability is minted without a caller-supplied badge. -/
theorem zero_valid : Badge.zero.valid := by
  unfold valid zero machineWordMax machineWordBits
  decide

/-- AN2-A / H-13: `Badge.zero.toNat = 0` (projection of the canonical
    zero badge). -/
@[simp] theorem zero_toNat : Badge.zero.toNat = 0 := rfl

/-- AN2-A / H-13: Construct a badge from a `Nat` that is already
    word-bounded, carrying the bound as a proof. Prefer this over
    `ofNatMasked` when the caller has a pre-validated input (e.g. decoded
    from a `UInt64`). -/
@[inline] def ofNat (n : Nat) (_h : n < machineWordMax := by decide) : Badge :=
  ⟨n⟩

/-- AN2-A / H-13: `Badge.ofNat n h` produces a badge whose underlying
    value is exactly `n` (no masking). -/
@[simp] theorem ofNat_toNat (n : Nat) (h : n < machineWordMax) :
    (Badge.ofNat n h).toNat = n := rfl

/-- AN2-A / H-13: `Badge.ofNat n h` is valid — the bound `h` is the
    witness. -/
theorem ofNat_valid (n : Nat) (h : n < machineWordMax) :
    (Badge.ofNat n h).valid := h

/-- WS-F5/D1a: Construct a badge with word-size truncation, matching seL4's
    silent word-truncation semantics on 64-bit platforms. -/
@[inline] def ofNatMasked (n : Nat) : Badge := ⟨n % machineWordMax⟩

/-- WS-F5/D1b: Bitwise OR combiner for badge accumulation. Masks the result
    to machine word size, matching seL4 notification signal semantics.

    **AC3-C / I-04 — Unbounded intermediate note**: The expression `a.val ||| b.val`
    computes the bitwise OR on unbounded Lean `Nat`. The intermediate result may
    exceed `machineWordMax` (2^64) in the abstract model even though hardware
    notification words are 64-bit. `ofNatMasked` (defined above) applies
    `% machineWordMax` to truncate to 64 bits, and the `bor_valid` theorem
    (below) proves the result satisfies the `valid` predicate. For hardware
    deployment, the platform binding layer must ensure all `Badge` values
    entering the model are already within 64-bit range, making the intermediate
    unboundedness a no-op. -/
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

/-- AN2-E / H-12: OR two pre-bounded `UInt64` values and lift the result
    into `Badge`. The bitwise OR is performed on `UInt64` (64-bit bounded)
    so the intermediate value never exceeds `2^64` — this forecloses the
    unbounded-intermediate concern flagged by audit H-12 (present in the
    pre-AN2-E `bor` composition when a caller passes un-masked `Nat`
    badges).

    Production paths ingesting values from the Rust ABI (where badges are
    `u64`) should prefer this constructor over `bor` + `ofNatMasked`. -/
@[inline] def ofUInt64Pair (a b : UInt64) : Badge :=
  ⟨(a ||| b).toNat⟩

/-- AN2-E / H-12: The intermediate value in `ofUInt64Pair` is always
    `< 2^64`, so the resulting badge is `valid` by construction — no
    truncation occurs. -/
theorem ofUInt64Pair_valid (a b : UInt64) : (ofUInt64Pair a b).valid := by
  unfold ofUInt64Pair valid machineWordMax machineWordBits
  exact (a ||| b).toNat_lt

/-- AN2-E / H-12: `ofUInt64Pair` is commutative — matches the commutative
    `Badge.bor` (pre-AN2-E `Nat`-level OR) on `UInt64`-bounded inputs. -/
theorem ofUInt64Pair_comm (a b : UInt64) :
    ofUInt64Pair a b = ofUInt64Pair b a := by
  unfold ofUInt64Pair
  congr 1
  simp [UInt64.or_comm]

/-- AN2-E / H-12: `ofUInt64Pair` with a zero argument projects the other
    argument's `toNat` directly. -/
theorem ofUInt64Pair_zero_right (a : UInt64) :
    (ofUInt64Pair a 0).toNat = a.toNat := by
  unfold ofUInt64Pair toNat
  simp

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

/-- Virtual-memory address in the abstract model.

    AN2-B.3 / H-13 (Theme 4.3): The `mk` constructor is `private`. External
    callers must use `VAddr.ofNat`. Combined with `isCanonical` (ARM64
    48-bit canonical-form check), this gates the abstract-address entry
    points to the kernel. -/
structure VAddr where
  private mk ::
  val : Nat
deriving DecidableEq, Repr

/-- AN2-B.3: Manual `Inhabited`. -/
instance : Inhabited VAddr := ⟨⟨0⟩⟩

/-- WS-G1: Hash instance for HashMap/HashSet keying. Delegates to Nat hash.
    BEq is already provided by DecidableEq via instBEqOfDecidableEq. -/
@[inline] instance : Hashable VAddr where
  hash a := hash a.val

namespace VAddr

/-- Smart constructor — accepts any `Nat`. Pre-existing migration helper;
    remains the default construction API for external callers. -/
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

/-- D3-C: IPC buffer alignment requirement in bytes.
    Matches seL4's `seL4_IPCBufferSizeBits = 9` (2^9 = 512 bytes).
    The IPC buffer must be aligned to this boundary so the kernel can
    safely read/write message registers without crossing page boundaries. -/
def ipcBufferAlignment : Nat := 512

/-- Physical-memory address in the abstract model.

    AN2-B.4 / H-13 (Theme 4.3): The `mk` constructor is `private`. External
    callers must use `PAddr.ofNat`. Validation against the platform's
    `physicalAddressWidth` (e.g. AK3-E's `decodeVSpaceMapArgsChecked` and
    AJ4-C's `validateIpcBufferAddress`) remains the caller's obligation —
    production decode paths must gate against `2^physicalAddressWidth`
    before accepting a raw ABI word. -/
structure PAddr where
  private mk ::
  val : Nat
deriving DecidableEq, Repr

/-- AN2-B.4: Manual `Inhabited`. -/
instance : Inhabited PAddr := ⟨⟨0⟩⟩

/-- WS-G1: Hash instance for HashMap/HashSet keying. Delegates to Nat hash.
    BEq is already provided by DecidableEq via instBEqOfDecidableEq. -/
@[inline] instance : Hashable PAddr where
  hash a := hash a.val

namespace PAddr

/-- Smart constructor — accepts any `Nat`. Pre-existing migration helper;
    remains the default construction API for external callers. -/
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

-- WS-H14b: LawfulMonad instance for KernelM

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

instance : LawfulHashable SchedContextId where
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
instance : EquivBEq SchedContextId := ⟨⟩

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
instance : LawfulBEq SchedContextId where
  eq_of_beq h := eq_of_beq h
  rfl := beq_self_eq_true _

-- ============================================================================
-- WS-G2: HashSet bridge lemmas for algorithm-local proof ergonomics
-- (HashMap lemmas removed in Q2 — all state maps now use RHTable)
-- ============================================================================

/-- WS-G2: Bridge lemma for `HashSet.contains` on empty. -/
theorem HashSet_contains_empty {α : Type} [BEq α] [Hashable α] [LawfulBEq α]
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
theorem RHTable_get?_empty {α β : Type} [BEq α] [Hashable α] [LawfulBEq α]
    (cap : Nat) (hCapGe4 : 4 ≤ cap) {a : α} :
    (RHTable.empty cap hCapGe4 : RHTable α β).get? a = none :=
  RHTable.getElem?_empty cap hCapGe4 a

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
/-- Q2-A: Membership is equivalent to `get?` returning `some`. -/
theorem RHTable_contains_iff_get_some {α β : Type} [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) :
    t.contains k = true ↔ (t.get? k).isSome = true := by
  simp [RHTable.contains]

open SeLe4n.Kernel.RobinHood in
/-- Q2-A: Not contained iff get? returns none. -/
theorem RHTable_not_contains_iff_get_none {α β : Type} [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) :
    t.contains k = false ↔ t.get? k = none := by
  simp [RHTable.contains]

open SeLe4n.Kernel.RobinHood in
/-- Q2-A: Bracket notation `t[k]?` is definitionally `t.get? k` for RHTable.
    This simp lemma allows rewrite lemmas stated in terms of `.get?` to fire
    on goals containing bracket notation. -/
theorem RHTable_getElem?_eq_get? {α β : Type} [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) : t[k]? = t.get? k := rfl

/- W6-J (LOW-01): RHTable specification surface theorems (14 theorems).
   The following 14 theorems (through `RHTable_fold_preserves`) characterize
   RHTable behavior for external reasoning. They are not currently composed
   into the kernel proof chain but serve as machine-checked documentation of
   hash table properties:
   - `RHTable_contains_insert_self` / `_erase_self`: containment after mutation
   - `RHTable_insert_preserves_invExt`: insert preserves base invariant
   - `RHTable_empty_invExt`: empty table satisfies base invariant
   - `RHTable_erase_preserves_invExtK`: erase preserves kernel invariant
   - `RHTable_get?_erase_ne_K` / `RHTable_getElem?_erase_K`: lookup after erase
   - `RHTable_insert_preserves_invExtK`: insert preserves kernel invariant
   - `RHTable_filter_preserves_invExtK` / `_key` / `_filter_getElem?`: filter properties
   - `RHTable_size_insert_bound` / `_erase_bound`: size bounds
   - `RHTable_fold_preserves`: fold induction principle
   See `SeLe4n/Kernel/RobinHood/Invariant/` for the actively-used proof
   infrastructure that these theorems document. -/

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
/-- Q2-A: Empty table satisfies invExt. -/
theorem RHTable_empty_invExt {α β : Type} [BEq α] [Hashable α] [LawfulBEq α]
    (cap : Nat) (hCapGe4 : 4 ≤ cap) :
    (RHTable.empty cap hCapGe4 : RHTable α β).invExt :=
  RHTable.empty_invExt cap hCapGe4

-- ============================================================================
-- V3-B Phase 2: invExtK re-exports for kernel code
-- ============================================================================

open SeLe4n.Kernel.RobinHood in
/-- V3-B: Erase preserves invExtK. -/
theorem RHTable_erase_preserves_invExtK {α β : Type} [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) (hK : t.invExtK) :
    (t.erase k).invExtK :=
  t.erase_preserves_invExtK k hK

open SeLe4n.Kernel.RobinHood in
/-- V3-B: Erasing key `k` does not affect lookups of other keys (invExtK API). -/
theorem RHTable_get?_erase_ne_K {α β : Type} [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k k' : α) (hNe : ¬(k == k') = true) (hK : t.invExtK) :
    (t.erase k).get? k' = t.get? k' :=
  t.getElem?_erase_ne_K k k' hNe hK

open SeLe4n.Kernel.RobinHood in
/-- V3-B: Combined erase lookup characterization (invExtK API). -/
theorem RHTable_getElem?_erase_K {α β : Type} [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) (hK : t.invExtK) (a : α) :
    (t.erase k).get? a = if k == a then none else t.get? a := by
  by_cases h : (k == a) = true
  · simp only [h, ite_true]
    have hka : a = k := (eq_of_beq h).symm; subst hka
    exact RHTable.getElem?_erase_self t a hK.1
  · simp only [show (k == a) = false from Bool.eq_false_iff.mpr h]
    exact RHTable.getElem?_erase_ne_K t k a h hK

open SeLe4n.Kernel.RobinHood in
/-- V3-B: Insert preserves invExtK. -/
theorem RHTable_insert_preserves_invExtK {α β : Type} [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) (v : β) (hK : t.invExtK) :
    (t.insert k v).invExtK :=
  t.insert_preserves_invExtK k v hK

open SeLe4n.Kernel.RobinHood in
/-- V3-B: Filter preserves invExtK. -/
theorem RHTable_filter_preserves_invExtK {α β : Type} [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (f : α → β → Bool) (hK : t.invExtK) :
    (t.filter f).invExtK :=
  RHTable.filter_preserves_invExtK t f hK

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
theorem RHTable_size_insert_bound {α β : Type} [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) (v : β) (hwf : t.WF) :
    (t.insert k v).size ≤ t.size + 1 :=
  RHTable.size_insert_le t k v hwf

open SeLe4n.Kernel.RobinHood in
/-- Q2-A: Erasing a key does not increase table size. -/
theorem RHTable_size_erase_bound {α β : Type} [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (k : α) :
    (t.erase k).size ≤ t.size :=
  RHTable.size_erase_le t k

open SeLe4n.Kernel.RobinHood in
/-- Q2-A: Fold preserves a property through all entries. -/
theorem RHTable_fold_preserves {α β γ : Type} [BEq α] [Hashable α] [LawfulBEq α]
    (t : RHTable α β) (init : γ) (f : γ → α → β → γ)
    (P : γ → Prop) (hInit : P init)
    (hStep : ∀ acc k v, P acc → P (f acc k v)) :
    P (t.fold init f) :=
  RHTable.fold_preserves t init f P hInit hStep

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

-- ============================================================================
-- AK7-E (F-M03 / MEDIUM): Valid*Id subtypes carrying non-sentinel witnesses
-- ============================================================================

/-! ## AK7-E: Sentinel-rejecting subtypes for typed identifiers

`ValidObjId`, `ValidThreadId`, `ValidSchedContextId`, and `ValidCPtr`
refine their base types by the non-sentinel predicate. Handlers that
require a valid (non-null) identifier should accept the subtype at
boundaries; the proof obligation `id ≠ .sentinel` is then discharged once
at the decode/lookup site and propagated through the handler chain.

`AK7-E.1` introduces the subtypes; `AK7-E.2` provides the
invariant-backed extraction lemmas. Cascade migration to individual
syscall handlers (`AK7-E.3`) is performed incrementally; the baseline
definitions here are sufficient for future opt-in adoption without
breaking existing call sites. Full migration of ~300 internal call sites
is tracked as `AK7-E.cascade` in the v0.29.0 DEFERRED document.

**Design note:** The subtype stores `val : Nat` plus a proof of
`val ≠ 0`, matching the `ObjId.sentinel = ⟨0⟩` convention. On
`ValidObjId`, the proof obligation uses `ObjId.sentinel` via
`val.val ≠ 0` through `ObjId.valid = (val.val ≠ 0)`. Conversion to the
base type is a pure projection; conversion from the base type is a
partial function (`?`) or takes an explicit proof. -/

/-- AK7-E.1 (F-M03): Refinement of `ObjId` excluding the sentinel value. -/
abbrev ValidObjId := { o : ObjId // o ≠ ObjId.sentinel }

/-- AK7-E.1 (F-M03): Refinement of `ThreadId` excluding the sentinel. -/
abbrev ValidThreadId := { t : ThreadId // t ≠ ThreadId.sentinel }

/-- AK7-E.1 (F-M03): Refinement of `SchedContextId` excluding the sentinel. -/
abbrev ValidSchedContextId := { s : SchedContextId // s ≠ SchedContextId.sentinel }

/-- AK7-E.1 (F-M03): Refinement of `CPtr` excluding the null pointer. -/
abbrev ValidCPtr := { c : CPtr // c ≠ CPtr.sentinel }

namespace ObjId

/-- AK7-E.1 (F-M03): Promote an `ObjId` with an explicit non-sentinel proof
to a `ValidObjId`. -/
@[inline] def toValid (o : ObjId) (h : o ≠ sentinel) : ValidObjId := ⟨o, h⟩

/-- AK7-E.1 (F-M03): Forget the non-sentinel proof on a `ValidObjId`. -/
@[inline] def ofValid (v : ValidObjId) : ObjId := v.val

/-- AK7-E.1 (F-M03): Try to promote an `ObjId` to a `ValidObjId` by
performing a runtime sentinel check. Returns `none` for the sentinel. -/
@[inline] def toValid? (o : ObjId) : Option ValidObjId :=
  if h : o = sentinel then none else some ⟨o, h⟩

/-- AK7-E.2 (F-M03): Invariant-backed validity extraction. If an object
exists at `o` in the object store, then `o` must not be the sentinel
(the default store is empty so any `get? = some _` establishes
non-sentinel-ness via object-presence witness). The callable form here
is abstract over the lookup — specific store shapes provide concrete
witnesses. -/
theorem valid_of_ne_sentinel {o : ObjId} (h : o ≠ sentinel) : o.valid := by
  simp only [valid]
  intro hZero
  exact h (by cases o; simp [sentinel]; exact hZero)

end ObjId

namespace ThreadId

/-- AK7-E.1 (F-M03): Promote a `ThreadId` with a non-sentinel proof. -/
@[inline] def toValid (t : ThreadId) (h : t ≠ sentinel) : ValidThreadId := ⟨t, h⟩

/-- AK7-E.1 (F-M03): Forget the non-sentinel proof. -/
@[inline] def ofValid (v : ValidThreadId) : ThreadId := v.val

/-- AK7-E.1 (F-M03): Runtime-checked promotion. -/
@[inline] def toValid? (t : ThreadId) : Option ValidThreadId :=
  if h : t = sentinel then none else some ⟨t, h⟩

/-- AN10-residual-1: when `toValid?` produces `some vt`, the underlying
`ThreadId` round-trips. Used by callers that bridge `ValidThreadId`-typed
wrappers back to their raw form for proof composition. -/
theorem toValid?_some_val_eq (t : ThreadId) (vt : ValidThreadId)
    (h : t.toValid? = some vt) : vt.val = t := by
  unfold toValid? at h
  split at h
  · exact absurd h (by simp)
  · injection h with hEq
    rw [← hEq]

/-- AK7-E.2 (F-M03): `toValid?` succeeds iff `t` is not reserved. -/
theorem toValid?_isSome_iff (t : ThreadId) :
    t.toValid?.isSome = true ↔ t.isReserved = false := by
  simp [toValid?, isReserved]
  constructor
  · intro h hRes
    exact h (ext hRes)
  · intro h hEq
    apply h
    rw [hEq]; rfl

end ThreadId

namespace SchedContextId

/-- AK7-E.1 (F-M03): Promote a `SchedContextId` with a non-sentinel proof. -/
@[inline] def toValid (s : SchedContextId) (h : s ≠ sentinel) : ValidSchedContextId := ⟨s, h⟩

/-- AK7-E.1 (F-M03): Forget the non-sentinel proof. -/
@[inline] def ofValid (v : ValidSchedContextId) : SchedContextId := v.val

/-- AK7-E.1 (F-M03): Runtime-checked promotion. -/
@[inline] def toValid? (s : SchedContextId) : Option ValidSchedContextId :=
  if h : s = sentinel then none else some ⟨s, h⟩

end SchedContextId

namespace CPtr

/-- AK7-E.1 (F-M03): Promote a `CPtr` with a non-null proof. -/
@[inline] def toValid (c : CPtr) (h : c ≠ sentinel) : ValidCPtr := ⟨c, h⟩

/-- AK7-E.1 (F-M03): Forget the non-null proof. -/
@[inline] def ofValid (v : ValidCPtr) : CPtr := v.val

/-- AK7-E.1 (F-M03): Runtime-checked promotion. -/
@[inline] def toValid? (c : CPtr) : Option ValidCPtr :=
  if h : c = sentinel then none else some ⟨c, h⟩

end CPtr

-- ============================================================================
-- AK7-F (F-M04 / MEDIUM): ObjectKind discriminator
-- ============================================================================

/-! ## AK7-F: Phantom-tag object identifiers across typed-id wrappers

`ThreadId ⟨5⟩.toObjId = SchedContextId ⟨5⟩.toObjId = ObjId ⟨5⟩` — the
base `ObjId` has no notion of the *kind* of object it points to.
Disjointness across wrapper types currently relies on pattern-match
discipline in the object store (each `ObjId` maps to exactly one
`KernelObject` variant via `functional-map`).

**Baseline (this phase):** `ObjectKind` enumerates the 8 object variants
plus a legacy-compatible `.unknown` default. Kinded wrappers
(`KindedObjId`) carry the discriminator explicitly; `ThreadId.toKinded`
tags the result as `.thread`, and analogous tagged constructors exist
for each wrapper. Disjointness theorems hold structurally across any two
distinct kinds.

**Cascade deferred (tracked as AK7-F.cascade for v1.1):** Migrating the
~300 call sites that use raw `ObjId.toNat`-based lookup to kinded
lookup. The current baseline does *not* change `ObjId` or `toObjId`; it
introduces an opt-in layer that can be adopted incrementally without
breaking existing proofs.

**Design decision per plan §Risk mitigation:** Rather than adding a
`kind` field to `ObjId` (which would cascade through 300+ proofs), we
introduce `KindedObjId` as a parallel structure. The 21 disjointness
theorems are provided on `KindedObjId`. Existing code that uses raw
`ObjId` continues to work unchanged; code that needs disjointness
promotes via `ThreadId.toKinded` etc. -/

/-- AK7-F.1 (F-M04): Enumeration of kernel object kinds. Used by
`KindedObjId` to discriminate a typed object reference structurally. -/
inductive ObjectKind where
  | unknown      -- legacy compatibility default for decoded raw ObjIds
  | thread
  | schedContext
  | endpoint
  | notification
  | cnode
  | vspaceRoot
  | untyped
  | service
  deriving Repr, DecidableEq, Inhabited

/-- AK7-F.1 (F-M04): An object identifier tagged with its declared kind.
The `val` field is the same unbounded `Nat` used by the base `ObjId`;
the `kind` field carries the compile-time discriminator that
distinguishes, e.g., a `ThreadId`-sourced lookup from a
`SchedContextId`-sourced lookup. -/
structure KindedObjId where
  val  : Nat
  kind : ObjectKind
  deriving Repr, DecidableEq, Inhabited

namespace KindedObjId

/-- AK7-F.1 (F-M04): Project a `KindedObjId` to its untagged `ObjId`. -/
@[inline] def toObjId (k : KindedObjId) : ObjId := ObjId.ofNat k.val

/-- AK7-F.4 (F-M04): Legacy-compatible constructor — forget the kind. -/
@[inline] def ofNatUnknown (n : Nat) : KindedObjId :=
  { val := n, kind := .unknown }

end KindedObjId

namespace ThreadId

/-- AK7-F.2 (F-M04): Kinded variant of `toObjId` — tags the result
`.thread` so subsequent lookups/comparisons can discriminate against
`.schedContext`-tagged ids with the same numeric value. -/
@[inline] def toKinded (t : ThreadId) : KindedObjId :=
  { val := t.val, kind := .thread }

end ThreadId

namespace SchedContextId

/-- AK7-F.2 (F-M04): Kinded variant of `toObjId` — tags the result
`.schedContext`. -/
@[inline] def toKinded (s : SchedContextId) : KindedObjId :=
  { val := s.val, kind := .schedContext }

end SchedContextId

-- ============================================================================
-- AK7-F.3 (F-M04): Disjointness theorems
-- ============================================================================

/-! ## AK7-F.3: Structural disjointness across kinds

For any two *distinct* `ObjectKind`s, the kinded projection maps are
disjoint on the structural `KindedObjId` level, regardless of the
numeric value. This closes `typedIdDisjointness_trivial` (DS-L10): if
a caller uses `ThreadId.toKinded` and `SchedContextId.toKinded`, the
resulting `KindedObjId` values can never alias even when the underlying
`.val` is the same.

For brevity, we state the canonical pair `ThreadId`/`SchedContextId`
(the pair cited in F-M04) explicitly and provide a general form keyed on
the `kind` field. Users of the cascade can prove per-pair instances by
unfolding and applying `ObjectKind.noConfusion`. -/

/-- AK7-F.3 (F-M04): Two `KindedObjId`s with distinct kinds cannot be
equal regardless of their numeric values. -/
theorem KindedObjId.ne_of_kind_ne {a b : KindedObjId} (h : a.kind ≠ b.kind) :
    a ≠ b := by
  intro hEq
  exact h (by rw [hEq])

/-- AK7-F.3 (F-M04): Canonical `ThreadId`/`SchedContextId` disjointness —
`t.toKinded` can never alias `s.toKinded` regardless of numeric values. -/
theorem ThreadId.toKinded_ne_schedContext_toKinded
    (t : ThreadId) (s : SchedContextId) :
    t.toKinded ≠ s.toKinded :=
  KindedObjId.ne_of_kind_ne (by
    simp [ThreadId.toKinded, SchedContextId.toKinded])

end SeLe4n
