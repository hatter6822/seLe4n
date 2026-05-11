-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Machine
import SeLe4n.Kernel.RobinHood
import SeLe4n.Kernel.SchedContext
import SeLe4n.Model.Object.NoDupList
import SeLe4n.Model.Object.UniqueSlotMap

namespace SeLe4n.Model


/-- Stable service identity metadata for graph-level orchestration. -/
structure ServiceIdentity where
  sid : ServiceId
  backingObject : SeLe4n.ObjId
  owner : SeLe4n.ObjId
  deriving Repr, DecidableEq

/-- Declared service dependencies and isolation edges.

WS-Q1-E1: `status` field removed — runtime lifecycle state is no longer tracked
in the service graph. The capability-indexed service registry
(`SystemState.serviceRegistry`) replaces lifecycle-focused orchestration. -/
structure ServiceGraphEntry where
  identity : ServiceIdentity
  dependencies : List ServiceId
  isolatedFrom : List ServiceId
  deriving Repr, DecidableEq

inductive AccessRight where
  | read
  | write
  | grant
  -- U5-L/U-L05: `grantReply` (bit 3) is defined for spec fidelity with seL4's
  -- `seL4_CapRights_t` but has no operational effect in the current IPC model.
  -- The `.grant` right (bit 2) governs ALL grant operations including reply cap
  -- grant. In real seL4, `grantReply` permits granting reply capabilities
  -- without granting full `grant` authority. seLe4n does not yet implement this
  -- distinction because reply cap grant is implicitly allowed by the reply
  -- mechanism itself (single-use authority).
  | grantReply
  | retype        -- WS-H15c/A-42: lifecycle retype operations
  deriving Repr, DecidableEq

namespace AccessRight

/-- WS-F5/D2a: Ordinal encoding for bitmask representation. Each right maps to
    a unique bit position. -/
@[inline] def toBit : AccessRight → Nat
  | .read       => 0
  | .write      => 1
  | .grant      => 2
  | .grantReply => 3
  | .retype     => 4

/-- WS-F5/D2a: All access rights in canonical order (bit 0..4). -/
def all : List AccessRight := [.read, .write, .grant, .grantReply, .retype]

end AccessRight

/-- WS-F5/D2a: Order-independent access right set using bitmask representation.

Matches seL4's rights representation as a word-sized bitmask. Each of the 5
access rights maps to a unique bit position (0..4). Membership is a single
bit test; subset is bitwise AND comparison. Two sets with the same rights in
any order are structurally equal.

**Constructor Safety Model (AC4-B/F-02):**

- `mk` (raw constructor) is TCB-internal only. Lean 4 cannot enforce private
  constructors, so `⟨999⟩` is syntactically valid but violates `valid`.
- **Safe constructors** (each guarantees `valid` by theorem):
  - `ofNat n`: Masks to 5 bits (`n % 32`). Use for user-supplied input.
  - `mk_checked bits h`: Carries `bits < 32` witness. Use in proof contexts.
  - `ofList rs` / `singleton r` / `empty`: Compile-time-known sets.
- **Operational safety argument**: Even if `bits ≥ 32` (invalid), operations
  produce correct results for the 5 defined rights:
  - `mem` uses shift-right and bitwise AND (`(bits >>> r.toBit) &&& 1 != 0`)
    — only positions 0..4 are meaningful access rights, so high bits are
    irrelevant to membership queries.
  - `subset` uses bitwise AND — `a &&& b == a` is correct for any `Nat`.
  - `inter` returns `⟨a &&& b⟩` — AND naturally clears bits beyond `b`'s range.
  - `union` returns `⟨a ||| b⟩` — may propagate invalid high bits from either
    operand; callers requiring validity should apply `ofNat` to the result.
- **Formal proofs**: `ofNat_valid`, `mk_checked_valid`, `empty_valid`,
  `singleton_valid`, `union_valid`, `inter_valid`, `ofList_valid` collectively
  prove that all public constructors produce valid sets. AC5-E operational
  safety theorems: `inter_valid` strengthened to require only the left
  operand's validity (AND clears high bits), `subset_sound` (subset implies
  per-right inclusion via `Nat.testBit_and`), `mem_bit_bounded` (membership
  tests bounded to bits 0..4). -/
-- AJ2-A (M-10): Constructor is private — external code cannot write
-- `AccessRightSet.mk 999` to bypass the 5-bit valid predicate. All public
-- construction goes through `ofNat` (masked), `ofList`, `singleton`, `empty`,
-- or `mk_checked` (proof-carrying). Pattern established by `CapDerivationTree`
-- (Structures.lean:941).
structure AccessRightSet where
  private mk ::
  bits : Nat
deriving DecidableEq, Repr

namespace AccessRightSet

-- AJ2-A (M-10): Manual Inhabited instance — `deriving Inhabited` requires public
-- constructor. Uses `empty` (bits = 0) as the canonical default.
instance : Inhabited AccessRightSet := ⟨⟨0⟩⟩

/-- S1-G: Maximum valid bitmask value — 5 access rights use bits 0..4,
    so valid values are in `[0, 2^5)`. -/
private def maxBits : Nat := 2 ^ 5

/-- S1-G: Well-formedness predicate — a rights set is valid when its bitmask
    fits in the 5-bit rights space (bits 0..4). Values ≥ 32 have spurious
    upper bits that do not correspond to any access right. -/
@[inline] def valid (s : AccessRightSet) : Prop := s.bits < maxBits

instance (s : AccessRightSet) : Decidable s.valid :=
  inferInstanceAs (Decidable (s.bits < maxBits))

/-- S1-G: Construct a rights set from a raw `Nat`, masking to the valid 5-bit
    range. This is the safe constructor — it guarantees `valid` by construction. -/
@[inline] def ofNat (n : Nat) : AccessRightSet := ⟨n % maxBits⟩

/-- S1-G: `ofNat` always produces a valid rights set. -/
theorem ofNat_valid (n : Nat) : (ofNat n).valid := by
  simp [ofNat, valid, maxBits]
  exact Nat.mod_lt n (by decide)

/-- S1-G: `ofNat` is idempotent on valid inputs. -/
theorem ofNat_idempotent (s : AccessRightSet) (h : s.valid) :
    ofNat s.bits = s := by
  simp [ofNat, maxBits, valid] at *
  exact congrArg AccessRightSet.mk (Nat.mod_eq_of_lt h)

/-- U2-K: Proof-carrying constructor — the caller must supply evidence that
    `bits < 2^5`. Prefer `ofNat` (auto-masked) or `ofList`/`singleton` for
    convenience; use `mk_checked` only when a raw literal needs an explicit
    validity witness. -/
@[inline] def mk_checked (bits : Nat) (_h : bits < 2 ^ 5 := by decide) : AccessRightSet := ⟨bits⟩

/-- U2-K: Every `AccessRightSet` created through the public API fits in
    5 bits. This holds by construction for `mk_checked`, `ofNat`, `singleton`,
    `empty`, and `ofList`. For `union`/`inter`/`diff` the caller should derive
    validity from the inputs; this theorem serves as documentation of intent. -/
theorem mk_checked_valid (bits : Nat) (h : bits < 2 ^ 5) :
    (mk_checked bits h).valid := by
  simp [mk_checked, valid, maxBits]; exact h

/-- Y1-D: Eta reconstruction — `ofNat` on a value's bits recovers the
    original when the value is already valid (bits < 32). For proof
    contexts that need to reconstruct an `AccessRightSet` from its `.bits`
    field. -/
@[simp] theorem eta (s : AccessRightSet) (h : s.valid) : ofNat s.bits = s :=
  ofNat_idempotent s h

/-- The empty rights set (no permissions). -/
@[inline] def empty : AccessRightSet := ⟨0⟩

/-- U2-K: `empty` is valid. -/
theorem empty_valid : empty.valid := by decide

/-- Construct a rights set from a single right. -/
@[inline] def singleton (r : AccessRight) : AccessRightSet := ⟨1 <<< r.toBit⟩

/-- U2-K: `singleton` is valid for all access rights. -/
theorem singleton_valid (r : AccessRight) : (singleton r).valid := by
  cases r <;> decide

/-- WS-F5/D2a: Construct a rights set from a list of rights. Order-independent:
    `ofList [.read, .write] = ofList [.write, .read]`. -/
@[inline] def ofList (rs : List AccessRight) : AccessRightSet :=
  ⟨rs.foldl (fun acc r => acc ||| (1 <<< r.toBit)) 0⟩

/-- WS-F5/D2a: Membership test — O(1) bit check. -/
@[inline] def mem (s : AccessRightSet) (r : AccessRight) : Bool :=
  (s.bits >>> r.toBit) &&& 1 != 0

instance : Membership AccessRight AccessRightSet where
  mem s r := AccessRightSet.mem s r = true

instance (r : AccessRight) (s : AccessRightSet) : Decidable (r ∈ s) :=
  inferInstanceAs (Decidable (AccessRightSet.mem s r = true))

/-- WS-F5/D2a: Subset test — O(1) bitwise check. `a ⊆ b` iff every bit in `a`
    is also set in `b`. -/
@[inline] def subset (a b : AccessRightSet) : Bool :=
  a.bits &&& b.bits == a.bits

/-- WS-F5/D2a: Union of two rights sets (bitwise OR).
    **AC4-B note**: Returns raw `⟨bits⟩` without masking. If either operand has
    invalid high bits (`bits ≥ 32`), they propagate to the result. Callers
    requiring `valid` should use `ofNat (union a b).bits` or rely on
    `union_valid` (which requires both operands valid). -/
@[inline] def union (a b : AccessRightSet) : AccessRightSet := ⟨a.bits ||| b.bits⟩

/-- WS-F5/D2a: Intersection of two rights sets (bitwise AND).
    **AC4-B note**: Returns raw `⟨bits⟩` without masking. However, AND naturally
    clears any bit not set in both operands, so if the left operand is valid
    (`bits < 32`), the result is also valid (see `inter_valid`). -/
@[inline] def inter (a b : AccessRightSet) : AccessRightSet := ⟨a.bits &&& b.bits⟩

/-- U2-K: Union of two valid rights sets is valid (5-bit closure). -/
theorem union_valid (a b : AccessRightSet) (ha : a.valid) (hb : b.valid) :
    (union a b).valid := by
  simp only [union, valid, maxBits] at *
  exact Nat.or_lt_two_pow ha hb

/-- U2-K/AC5-E: Intersection preserves validity when at least the left operand
    is valid. Bitwise AND cannot set bits that `a` does not have, so the result
    fits in the same bit range as `a`. The right operand `b` may have arbitrary
    (even invalid) high bits — they are cleared by the AND operation.

    This is the key property that makes `subset` (which uses AND internally)
    safe even when the right operand is an invalid `AccessRightSet`. -/
theorem inter_valid (a b : AccessRightSet) (ha : a.valid) :
    (inter a b).valid := by
  simp only [inter, valid, maxBits] at *
  exact Nat.lt_of_le_of_lt Nat.and_le_left ha

/-- AC5-E: `subset` correctly tests bit-level inclusion for the 5 defined
    access rights, regardless of whether the operands satisfy `valid`.
    Bitwise AND is well-defined on all `Nat` values, so `a.subset b = true`
    implies every right in `a` is also in `b`. -/
theorem subset_sound (a b : AccessRightSet) (r : AccessRight)
    (hSub : a.subset b = true) (hMem : a.mem r = true) :
    b.mem r = true := by
  simp only [subset, mem] at *
  -- Convert beq to equality
  have hEq : a.bits &&& b.bits = a.bits := eq_of_beq hSub
  -- mem uses (bits >>> toBit) &&& 1, testBit uses 1 &&& (bits >>> toBit)
  -- Connect via Nat.and_comm
  have hMemTB : Nat.testBit a.bits r.toBit = true := by
    simp only [Nat.testBit]
    rwa [Nat.and_comm]
  have hAnd := Nat.testBit_and a.bits b.bits r.toBit
  rw [hEq] at hAnd
  rw [hMemTB] at hAnd
  have hBTB : Nat.testBit b.bits r.toBit = true := by simpa using hAnd
  simp only [Nat.testBit] at hBTB
  rwa [Nat.and_comm] at hBTB

/-- AC5-E: Membership checks are bounded by the 5 defined access rights.
    `mem` tests bit `r.toBit` where `r : AccessRight`, and `toBit` returns
    a value in `{0, 1, 2, 3, 4}`. This proves that out-of-range bit positions
    are never tested, even for invalid sets. -/
theorem mem_bit_bounded (r : AccessRight) : r.toBit < 5 := by
  cases r <;> decide

/-- U2-K/U-L03: Every `AccessRightSet` value constructed through `ofNat`, `ofList`,
    `singleton`, `empty`, or `mk_checked` satisfies the 5-bit invariant.
    This is the `isWord64` lemma requested by the workstream plan.
    Note: values constructed via raw `.mk` may violate this — callers building
    `AccessRightSet` directly from `Nat` should use `ofNat` (masked) or
    `mk_checked` (proof-carrying) instead. -/
theorem isWord5_of_valid (ars : AccessRightSet) (h : ars.valid) : ars.bits < 2 ^ 5 := h

/-- WS-F5/D2a: Convert rights set to a list (canonical order). -/
def toList (s : AccessRightSet) : List AccessRight :=
  AccessRight.all.filter s.mem

instance : ToString AccessRightSet where
  toString s := toString (s.toList.map reprStr)

/-- WS-F5/D2a: `ofList` is order-independent — permutations produce equal sets. -/
theorem ofList_comm (a b : AccessRight) (rest : List AccessRight) :
    ofList (a :: b :: rest) = ofList (b :: a :: rest) := by
  simp [ofList, List.foldl]
  congr 1
  exact Nat.or_comm (1 <<< a.toBit) (1 <<< b.toBit)

/-- T2-A (H-1): Helper — each `AccessRight.toBit` yields a value < 5, so
    `1 <<< r.toBit < maxBits` (i.e., < 32). -/
private theorem singleton_lt_maxBits (r : AccessRight) : 1 <<< r.toBit < maxBits := by
  cases r <;> simp [AccessRight.toBit, maxBits] <;> decide

/-- T2-A (H-1): Helper — bitwise OR of two values below `2^n` stays
    below `2^n`. This holds because OR cannot set bits that neither
    operand has, and both operands fit in n bits. -/
private theorem or_lt_two_pow (a b : Nat) (n : Nat) (ha : a < 2^n) (hb : b < 2^n) :
    a ||| b < 2^n :=
  Nat.or_lt_two_pow ha hb

private theorem or_lt_maxBits (a b : Nat) (ha : a < maxBits) (hb : b < maxBits) :
    a ||| b < maxBits :=
  or_lt_two_pow a b 5 ha hb

/-- T2-A (H-1): The fold body preserves `< maxBits` — accumulating one more
    singleton via OR stays within the 5-bit range. -/
private theorem foldl_or_lt_maxBits (rs : List AccessRight) (init : Nat)
    (hInit : init < maxBits) :
    rs.foldl (fun acc r => acc ||| (1 <<< r.toBit)) init < maxBits := by
  induction rs generalizing init with
  | nil => exact hInit
  | cons r rest ih =>
    simp only [List.foldl_cons]
    exact ih _ (or_lt_maxBits init (1 <<< r.toBit) hInit (singleton_lt_maxBits r))

/-- T2-A (H-1): `ofList` always produces a valid rights set.

    **Proof sketch**: `ofList` folds `(fun acc r => acc ||| (1 <<< r.toBit))`
    starting from 0. Each `1 <<< r.toBit` is < 32 (since `toBit` ∈ {0..4}),
    and bitwise OR of values < 32 stays < 32. Therefore the result fits in
    the 5-bit rights space, satisfying `valid` (`.bits < 2^5`).

    This closes finding H-1: `AccessRightSet.ofList` now has a machine-checked
    `valid` postcondition. -/
theorem ofList_valid (rs : List AccessRight) : (ofList rs).valid := by
  simp [ofList, valid]
  exact foldl_or_lt_maxBits rs 0 (by unfold maxBits; omega)

end AccessRightSet

/-- The addressable target of a capability in the abstract object universe.

WS-E4/M-12: Added `replyCap` variant for one-shot reply capabilities that
reference a specific sender's TCB, enabling bidirectional IPC. -/
inductive CapTarget where
  | object (id : SeLe4n.ObjId)
  | cnodeSlot (cnode : SeLe4n.ObjId) (slot : SeLe4n.Slot)
  | replyCap (senderTcb : SeLe4n.ThreadId)
  deriving Repr, DecidableEq

/-- WS-RC R4.A: `Inhabited CapTarget` for the `Capability` Inhabited
    derivation needed by the `UniqueSlotMap` `GetElem?` `[s]` total-access
    fallback. The chosen default is `.object SeLe4n.ObjId.sentinel`, matching
    the H-06/WS-E3 sentinel convention. -/
instance : Inhabited CapTarget := ⟨.object SeLe4n.ObjId.sentinel⟩

/-- WS-F5/D2b: Capability with order-independent rights set.
    `rights` is an `AccessRightSet` (bitmask), replacing the prior `List AccessRight`. -/
structure Capability where
  target : CapTarget
  rights : AccessRightSet
  badge : Option SeLe4n.Badge := none
  deriving Repr, DecidableEq, Inhabited

namespace Capability

/-- WS-F5/D2b: Check if a capability has a specific right. O(1) bit test. -/
def hasRight (cap : Capability) (right : AccessRight) : Bool :=
  cap.rights.mem right

/-- AK7-I (F-M07 / MEDIUM): Null capability predicate.

Returns `true` when the capability is sentinel-initialised — its target
references the reserved `ObjId.sentinel` (value 0) and carries no access
rights. This mirrors seL4's `seL4_CapNull` convention, which combines a
null object reference with the empty rights set.

**Callers:** Sensitive entry points (`cspaceInvoke`, `cspaceMint`,
`cspaceCopy`) should reject null capabilities at the ABI boundary by
combining `isNull cap = false` with the usual access-right checks. A null
capability carrying bits in the target's `cnodeSlot`/`replyCap` arms is
treated as non-null so that structural capability pointers survive the
check. -/
@[inline] def isNull (cap : Capability) : Bool :=
  match cap.target with
  | .object oid => oid.isReserved && cap.rights.bits = 0
  | _           => false

/-- AK7-I: Structural negation — a capability is NOT null when either its
target is non-object, its object id is non-sentinel, or it carries any
access right. The predicate is `Bool`-valued so callers can discharge it
with `decide`. -/
@[inline] def isNotNull (cap : Capability) : Bool := !cap.isNull

/-- AK7-I: `isNotNull` reflects `!isNull`. -/
theorem isNotNull_iff (cap : Capability) :
    cap.isNotNull = true ↔ cap.isNull = false := by
  simp [isNotNull]

/-- AK7-I: Canonical null capability. Mirrors `seL4_CapNull` — target is
`ObjId.sentinel`, rights set is empty, badge is `none`. Useful as a
default/sentinel capability for CSpace slot initialisation. -/
def null : Capability :=
  { target := .object ObjId.sentinel, rights := AccessRightSet.empty, badge := none }

/-- AK7-I: The canonical null capability satisfies `isNull`. -/
theorem null_isNull : (Capability.null).isNull = true := by
  simp [null, isNull, AccessRightSet.empty, ObjId.isReserved, ObjId.sentinel]

/-- AK7-I (F-M07 / MEDIUM): Fail-closed gate helper for capability-using
entry points. Returns `some cap` when the capability is non-null, `none`
otherwise. Callers at the syscall boundary (e.g., `cspaceInvoke`,
`cspaceMint`, `cspaceCopy`) should chain through `requireNotNull` when
accepting caller-supplied capabilities to reject `seL4_CapNull`-style
sentinel caps early.

This is an additive helper; existing code continues to compile. The
integration obligation — routing all capability-using entry points
through this gate — is tracked as AK7-I.cascade (post-1.0). -/
@[inline] def requireNotNull (cap : Capability) : Option Capability :=
  if cap.isNull then none else some cap

/-- AK7-I: `requireNotNull` returns `some cap` iff the cap is not null. -/
theorem requireNotNull_isSome_iff (cap : Capability) :
    (cap.requireNotNull).isSome = true ↔ cap.isNull = false := by
  unfold requireNotNull
  cases h : cap.isNull <;> simp

/-- AK7-I: `requireNotNull` rejects the canonical null cap. -/
theorem requireNotNull_null : (Capability.null).requireNotNull = none := by
  simp [requireNotNull, null_isNull]

/-- AK7-I: The value returned by `requireNotNull` is not null. -/
theorem requireNotNull_some_not_null {cap cap' : Capability}
    (h : cap.requireNotNull = some cap') : cap'.isNull = false := by
  unfold requireNotNull at h
  split at h
  · cases h
  · rename_i hNotNull
    cases h
    simp [hNotNull]

end Capability

-- ============================================================================
-- AL1b (WS-AL / AK7-I.cascade): `NonNullCap` subtype for type-level null-cap
-- rejection. Replaces the earlier runtime-guard approach (reverted because
-- it overloaded `.invalidCapability`).
-- ============================================================================

/-- AL1b: Subtype witnessing that a capability is not the `seL4_CapNull`
sentinel. Any function that takes `NonNullCap` as a formal argument is
guaranteed by the Lean type system that no caller can feed it a null cap —
construction of a `NonNullCap` requires a proof of `cap.isNull = false`.

This is the *type-level* discipline counterpart to `ValidThreadId`
(AK7-E baseline). Callers who need to convert a raw `Capability` must
go through `Capability.toNonNull?`, which returns `Option NonNullCap`;
on `none` the caller is forced to either propagate a `NullCapability`
error or take a different path. -/
abbrev NonNullCap := { cap : Capability // cap.isNull = false }

namespace Capability

/-- AL1b: Forget the non-null witness — project `NonNullCap` back to a
raw `Capability`. -/
@[inline] def ofNonNull (c : NonNullCap) : Capability := c.val

/-- AL1b: Construct a `NonNullCap` when the caller has a
`cap.isNull = false` witness in hand. Preferred for proof-carrying
contexts where the non-null property is already established. -/
@[inline] def toNonNull (cap : Capability) (h : cap.isNull = false) : NonNullCap :=
  ⟨cap, h⟩

/-- AL1b: Runtime-checked promotion. Returns `some ⟨cap, _⟩` when
`cap.isNull = false` and `none` otherwise. This is the canonical way a
runtime-discovered capability (e.g., the result of `cspaceLookupSlot`) is
promoted to the non-null type before being passed into an operation that
requires `NonNullCap`.

Callers that receive `none` MUST produce `KernelError.nullCapability`
(or propagate it) — the error code dedicated to this failure mode. -/
@[inline] def toNonNull? (cap : Capability) : Option NonNullCap :=
  if h : cap.isNull = false then some ⟨cap, h⟩ else none

end Capability

/-- AL1b: `toNonNull?` succeeds iff the capability is not null. -/
theorem Capability.toNonNull?_isSome_iff (cap : Capability) :
    (cap.toNonNull?).isSome = true ↔ cap.isNull = false := by
  unfold Capability.toNonNull?
  constructor
  · intro h; split at h
    · rename_i hNotNull; exact hNotNull
    · cases h
  · intro h; simp [h]

/-- AL1b: `toNonNull?` rejects the canonical null cap. -/
theorem Capability.toNonNull?_null : (Capability.null).toNonNull? = none := by
  unfold Capability.toNonNull?
  simp [null_isNull]

/-- AL1b: Projecting a `NonNullCap` back via `ofNonNull` round-trips through
`toNonNull?` — the result is `some` with the original cap. -/
theorem Capability.toNonNull?_ofNonNull (c : NonNullCap) :
    (Capability.ofNonNull c).toNonNull? = some c := by
  unfold Capability.toNonNull? Capability.ofNonNull
  simp [c.property]

/-- AL1b: Bridge lemma — if `cap.isNull = false`, then `toNonNull?` returns
`some ⟨cap, _⟩`. This is the canonical introduction pattern for callers who
have established non-nullness externally. -/
theorem Capability.toNonNull?_of_not_null
    {cap : Capability} (h : cap.isNull = false) :
    cap.toNonNull? = some ⟨cap, h⟩ := by
  unfold Capability.toNonNull?
  simp [h]

/-- AL1b: Implicit coercion `NonNullCap → Capability` via the subtype's
`.val` projection. Enables `nn.rights`, `nn.target`, `nn.badge` syntax on
`NonNullCap` values without explicit `.val` or `Capability.ofNonNull`
calls. The coercion is safe because the subtype projection is injective:
two distinct `NonNullCap`s have distinct underlying capabilities. -/
instance : CoeHead NonNullCap Capability where
  coe := Subtype.val

/-- WS-H12d/A-09: Maximum number of message registers per IPC message.
Matches seL4's `seL4_MsgMaxLength` (120 words). -/
def maxMessageRegisters : Nat := 120

/-- WS-H12d/A-09: Maximum number of extra capabilities per IPC message.
Matches seL4's `seL4_MsgMaxExtraCaps` (3 extra caps). -/
def maxExtraCaps : Nat := 3

/-- WS-E4/M-02: Structured IPC message payload for endpoint transfers.

Models seL4 message registers plus optional capability transfer and sender badge.
WS-H12d/A-09: Registers and caps are bounded `Array` types matching seL4's
`seL4_MsgMaxLength` (120) and `seL4_MsgMaxExtraCaps` (3). Bounds are enforced
at IPC send boundaries. -/
structure IpcMessage where
  /-- S4-D: Changed from `Array Nat` to `Array RegValue` for type consistency
      with the machine register model. All register values in IPC messages
      are now typed, matching the `RegValue` wrapper used throughout the
      register decode and context-switch infrastructure. -/
  registers : Array SeLe4n.RegValue
  caps : Array Capability := #[]
  badge : Option SeLe4n.Badge := none
  deriving Repr, DecidableEq

namespace IpcMessage

def empty : IpcMessage := { registers := (#[] : Array SeLe4n.RegValue), caps := #[], badge := none }

/-- WS-H12d/A-09: Predicate asserting that a message's payload respects
seL4 message-register and extra-capability bounds. -/
def bounded (msg : IpcMessage) : Prop :=
  msg.registers.size ≤ maxMessageRegisters ∧
  msg.caps.size ≤ maxExtraCaps

/-- WS-H12d/A-09: Decidable bounds check for runtime enforcement at IPC
send boundaries. Returns `true` iff the message satisfies payload bounds. -/
def checkBounds (msg : IpcMessage) : Bool :=
  msg.registers.size ≤ maxMessageRegisters &&
  msg.caps.size ≤ maxExtraCaps

theorem empty_bounded : IpcMessage.empty.bounded := by
  unfold bounded empty maxMessageRegisters maxExtraCaps
  simp [Array.size]

theorem checkBounds_iff_bounded (msg : IpcMessage) :
    msg.checkBounds = true ↔ msg.bounded := by
  unfold checkBounds bounded maxMessageRegisters maxExtraCaps
  simp [Bool.and_eq_true]

end IpcMessage

/-- M-D01: Result of attempting to unwrap a single transferred capability
into the receiver's CSpace during IPC rendezvous.

seL4 semantics: each extra cap in the message is independently unwrapped.
Failures on one cap do not abort the transfer of subsequent caps. -/
inductive CapTransferResult where
  /-- Successfully installed in the receiver's CSpace at the given CNode and slot. -/
  | installed (cnode : SeLe4n.ObjId) (slot : SeLe4n.Slot)
  /-- No empty slot available in the receiver's CNode (receiver CSpace full). -/
  | noSlot
  /-- The endpoint capability lacks the Grant right — transfer silently skipped. -/
  | grantDenied
  deriving Repr, DecidableEq

/-- M-D01: Aggregated results of unwrapping all extra capabilities in an
IPC message. One entry per cap in the original `msg.caps` array. -/
structure CapTransferSummary where
  results : Array CapTransferResult := #[]
  deriving Repr, DecidableEq

/-- WS-Z/Z6-H: Result of a timeout-aware IPC operation.
Distinguishes successful message delivery from budget-driven timeout.
Used by `timeoutAwareReceive` and related timeout-aware IPC wrappers. -/
inductive IpcTimeoutResult where
  /-- IPC completed successfully with a delivered message. -/
  | completed (msg : IpcMessage)
  /-- The thread's SchedContext budget expired while blocked — IPC timed out.
      The thread has been unblocked, removed from the endpoint queue, and
      re-enqueued in the RunQueue with a timeout error code. -/
  | timedOut
  deriving Repr, DecidableEq

/-- Per-thread IPC scheduler-visible status.

WS-E3/H-09: Endpoint-local blocking states for deterministic handshake.
WS-E4/M-12: Added `blockedOnReply` for bidirectional IPC (sender waiting for reply).
WS-H1/C-01: Added `blockedOnCall` — a Call sender blocked on the send queue carries
  this state (distinct from `blockedOnSend`) so that upon dequeue the sender
  transitions to `blockedOnReply`, not `.ready`.
WS-H1/M-02: `blockedOnReply` now carries an optional `replyTarget` recording which
  server thread is authorized to reply, preventing confused-deputy attacks. -/
inductive ThreadIpcState where
  | ready
  | blockedOnSend (endpoint : SeLe4n.ObjId)
  | blockedOnReceive (endpoint : SeLe4n.ObjId)
  | blockedOnNotification (notification : SeLe4n.ObjId)
  | blockedOnReply (endpoint : SeLe4n.ObjId) (replyTarget : Option SeLe4n.ThreadId := none)
  | blockedOnCall (endpoint : SeLe4n.ObjId)
  deriving Repr, DecidableEq

/-- V8-G1: Explicit thread lifecycle state.
Previously, thread state was inferred from queue membership and `ThreadIpcState`.
This enum makes the state machine explicit, improving debuggability and
enabling the `threadState_consistent` invariant predicate.

The 8 states correspond to the seL4 thread model:
- `Running`: Currently dispatched (is `scheduler.current`)
- `Ready`: In the run queue, eligible for scheduling
- `BlockedSend`: Blocked on endpoint send queue
- `BlockedRecv`: Blocked on endpoint receive queue
- `BlockedCall`: Blocked on endpoint call (send then wait for reply)
- `BlockedReply`: Blocked waiting for a reply after ReplyRecv (server-side)
- `BlockedNotif`: Blocked waiting for notification
- `Inactive`: Freshly created or cleaned up, not yet scheduled -/
inductive ThreadState where
  | Running
  | Ready
  | BlockedSend
  | BlockedRecv
  | BlockedCall
  | BlockedReply
  | BlockedNotif
  | Inactive
  deriving Repr, DecidableEq, Inhabited

/-- Thread Control Block.

M-03/WS-E6: `deadline` field for EDF tie-breaking. Default 0 = no deadline.
M-04/WS-E6: `timeSlice` field for preemption. Default 5 ticks per quantum.
V8-G1: `threadState` field for explicit lifecycle state machine. -/
inductive QueuePPrev where
  | endpointHead
  | tcbNext (tid : SeLe4n.ThreadId)
  deriving Repr, DecidableEq

structure TCB where
  tid : SeLe4n.ThreadId
  priority : SeLe4n.Priority
  domain : SeLe4n.DomainId
  cspaceRoot : SeLe4n.ObjId
  vspaceRoot : SeLe4n.ObjId
  ipcBuffer : SeLe4n.VAddr
  ipcState : ThreadIpcState := .ready
  /-- V8-G1: Explicit lifecycle state. Default `.Inactive` for freshly created
      threads; set to `.Ready` when enqueued, `.Running` when dispatched. -/
  threadState : ThreadState := .Inactive
  /-- M-04/WS-E6: Remaining time-slice ticks before preemption. Reset to
      `defaultTimeSlice` on expiry. Default value matches seL4's
      CONFIG_TIMER_TICK_MS-based quantum. -/
  timeSlice : Nat := 5
  /-- M-03/WS-E6: Scheduling deadline for EDF tie-breaking within same
      priority level. 0 = no deadline (lowest urgency). Lower nonzero
      values are more urgent. -/
  deadline : SeLe4n.Deadline := ⟨0⟩
  /-- WS-E4/M-01 intrusive queue linkage for endpoint dual queues.
      `none`/`none` means detached from intrusive endpoint wait queues. -/
  queuePrev : Option SeLe4n.ThreadId := none
  /-- WS-E8: pointer-to-previous-link metadata.
      `endpointHead` means this node is currently referenced by queue head;
      `tcbNext prevTid` means it is referenced by `prevTid.queueNext`.
      Cleared when detached from intrusive endpoint wait queues. -/
  queuePPrev : Option QueuePPrev := none
  queueNext : Option SeLe4n.ThreadId := none
  /-- WS-F1: Pending IPC message for transfer during endpoint rendezvous.
      Stored in the sender's TCB while blocked; transferred to the receiver
      on handshake/dequeue. `none` = no pending message. -/
  pendingMessage : Option IpcMessage := none
  /-- WS-H12c/H-03: Per-TCB register save area. The scheduler saves the
      outgoing thread's machine registers here on dispatch and restores
      the incoming thread's context from here. Zero-initialized by default.
      See `contextMatchesCurrent` in `Scheduler/Invariant.lean`. -/
  registerContext : SeLe4n.RegisterFile := default
  /-- R7-D/L-06: Capability pointer to the fault handler endpoint.
      In seL4, when a thread faults (e.g., VM fault, cap fault), the kernel
      sends a fault IPC message to the endpoint identified by this capability.
      `none` = no fault handler configured (faults are silently dropped). -/
  faultHandler : Option SeLe4n.CPtr := none
  /-- R7-D/L-06: Object ID of the bound notification object.
      In seL4, a thread may bind one notification object. Signals on the bound
      notification can wake the thread when it is waiting on an endpoint.
      `none` = no bound notification. -/
  boundNotification : Option SeLe4n.ObjId := none
  /-- WS-Z/Z1-J: Scheduling context binding. Determines whether this thread
      uses legacy TCB scheduling fields or a first-class SchedContext object.
      Default `.unbound` preserves backward compatibility. -/
  schedContextBinding : SeLe4n.Kernel.SchedContextBinding := .unbound
  /-- WS-Z/Z6-A: Timeout budget reference for IPC blocking operations.
      When a thread blocks on IPC (send/receive/call/reply), this records which
      SchedContext's budget bounds the blocking duration. When the SchedContext's
      budget expires, the thread is unblocked with a timeout error.
      `none` = no timeout (legacy unbounded blocking). Cleared on unblock.
      Invariant: `timeoutBudget = some _` implies `ipcState` is a blocking state. -/
  timeoutBudget : Option SeLe4n.SchedContextId := none
  /-- D2-A: Maximum Controlled Priority (MCP) ceiling. The maximum priority this
      thread can assign to other threads (or itself) via `setPriority`. seL4
      convention: `setPriority newPrio` requires `newPrio ≤ caller.mcp`.
      Default is maximum priority (0xFF = no restriction).

      L-12/AH5-C: **Design rationale — maximally permissive MCP default**.
      Default `0xFF` (255) allows any priority to be assigned without MCP
      restriction. This is safe because `setPriorityOp` (PriorityManagement.lean)
      enforces `newPrio ≤ caller.mcp` at the operation level — the target's own
      MCP is irrelevant to the authority check.

      seL4 divergence: seL4 uses a restrictive default (0), requiring explicit
      MCP elevation before priority assignment. seLe4n's permissive default
      simplifies boot configuration: all threads can be assigned any priority
      without a separate MCP initialization step.

      Production recommendation: set explicit MCP values during system
      initialization to enforce least-privilege priority assignment. -/
  maxControlledPriority : SeLe4n.Priority := ⟨0xFF⟩
  /-- D4-A: Priority Inheritance Protocol boost. When `some p`, the thread's
      effective scheduling priority is boosted to at least `p` regardless of
      its SchedContext binding. Set by `propagatePriorityInheritance` when
      the thread holds a pending Reply on behalf of a higher-priority client.
      Cleared by `revertPriorityInheritance` when the client is unblocked.
      Default `none` = no PIP boost (existing effective priority behavior). -/
  pipBoost : Option SeLe4n.Priority := none
  /-- AG8-A (H3-IPC-01/I-01): Explicit timeout flag replacing the fragile
      sentinel pattern (`gpr x0 = 0xFFFFFFFF ∧ ipcState = .ready`).
      Set to `true` by `timeoutThread` when a thread's IPC operation times
      out due to SchedContext budget expiry. Cleared to `false` by
      `timeoutAwareReceive` after the timeout is detected and reported.
      This eliminates the risk of sentinel collision with legitimate IPC data
      in register x0. -/
  timedOut : Bool := false
  deriving Repr

/-- WS-H12c: Manual `BEq` for `TCB`. `DecidableEq` cannot be derived because
`RegisterFile` contains a function field (`gpr : Nat → Nat`). Field-wise
comparison uses the `BEq RegisterFile` instance from `Machine.lean`.

**V7-F: WARNING — non-lawful BEq instance.** Inherits non-lawfulness from
`BEq RegisterFile` via the `registerContext` field comparison. Safe for
runtime testing but do NOT rely on `==` for propositional equality in proofs.
See `TCB.not_lawfulBEq` and `RegisterFile.not_lawfulBEq`. -/
instance : BEq TCB where
  beq a b :=
    a.tid == b.tid && a.priority == b.priority && a.domain == b.domain &&
    a.cspaceRoot == b.cspaceRoot && a.vspaceRoot == b.vspaceRoot &&
    a.ipcBuffer == b.ipcBuffer && a.ipcState == b.ipcState &&
    a.threadState == b.threadState &&
    a.timeSlice == b.timeSlice && a.deadline == b.deadline &&
    a.queuePrev == b.queuePrev && a.queuePPrev == b.queuePPrev &&
    a.queueNext == b.queueNext && a.pendingMessage == b.pendingMessage &&
    a.registerContext == b.registerContext &&
    a.faultHandler == b.faultHandler && a.boundNotification == b.boundNotification &&
    a.schedContextBinding == b.schedContextBinding &&
    a.timeoutBudget == b.timeoutBudget &&
    a.maxControlledPriority == b.maxControlledPriority &&
    a.pipBoost == b.pipBoost &&
    a.timedOut == b.timedOut

/-- AJ4-D (L-09): Detect sentinel-initialized (unconfigured) TCBs.
    Returns `true` if the TCB's identity or address-space references use
    reserved sentinel values (ID 0), indicating the TCB was freshly created
    by `objectOfTypeTag`/`objectOfKernelType` and has not been configured
    via `threadConfigureOp`. Unconfigured TCBs must NOT be scheduled. -/
@[inline] def TCB.isUnconfigured (tcb : TCB) : Bool :=
  tcb.tid.isReserved || tcb.cspaceRoot.isReserved || tcb.vspaceRoot.isReserved

/-- U2-N/U-M17: Negative `LawfulBEq` witness for `TCB`.
    `BEq TCB` is field-wise comparison including `registerContext : RegisterFile`.
    Since `RegisterFile.BEq` is not lawful (see `RegisterFile.not_lawfulBEq`),
    `TCB.BEq` inherits the same limitation. This prevents accidental use of
    `TCB` in proofs that assume `LawfulBEq`. -/
theorem TCB.not_lawfulBEq : ¬ LawfulBEq TCB := by
  intro h
  have hEq := @LawfulBEq.eq_of_beq _ _ h
  -- Construct two TCBs whose registerContext differs only on out-of-range GPR index 32
  let f₁ : SeLe4n.RegName → SeLe4n.RegValue := fun _ => ⟨0⟩
  let f₂ : SeLe4n.RegName → SeLe4n.RegValue := fun r => if r.val = 32 then ⟨1⟩ else ⟨0⟩
  let r₁ : SeLe4n.RegisterFile := { pc := ⟨0⟩, sp := ⟨0⟩, gpr := f₁ }
  let r₂ : SeLe4n.RegisterFile := { pc := ⟨0⟩, sp := ⟨0⟩, gpr := f₂ }
  let oid : SeLe4n.ObjId := ⟨0⟩
  let va : SeLe4n.VAddr := (SeLe4n.VAddr.ofNat 0)
  let t₁ : TCB := {
    tid := ⟨0⟩, priority := ⟨0⟩, domain := ⟨0⟩,
    cspaceRoot := oid, vspaceRoot := oid, ipcBuffer := va, registerContext := r₁ }
  let t₂ : TCB := {
    tid := ⟨0⟩, priority := ⟨0⟩, domain := ⟨0⟩,
    cspaceRoot := oid, vspaceRoot := oid, ipcBuffer := va, registerContext := r₂ }
  have hBeq : (t₁ == t₂) = true := by decide
  have hPropEq : t₁ = t₂ := hEq hBeq
  have hNeq : t₁.registerContext.gpr ⟨32⟩ ≠ t₂.registerContext.gpr ⟨32⟩ := by decide
  exact hNeq (by rw [hPropEq])

/-- AK7-G (F-M05 / MEDIUM): Sanctioned extensionality lemma for `TCB`.

Use this lemma instead of `==` in any proof that requires propositional
equality of TCBs. `TCB.ext` requires each structural field to match —
including the `registerContext : RegisterFile` function field — so the
proof obligation covers the same surface as `a == b = true` but without
the out-of-range-GPR trap that `TCB.not_lawfulBEq` exposes.

Companion to `RegisterFile.ext` (Machine.lean). Together they close the
proof gap cited in F-M05: non-lawful BEq remains available for test
infrastructure, while proof-critical paths derive equality via explicit
pointwise witnesses. -/
theorem TCB.ext {a b : TCB}
    (hTid : a.tid = b.tid) (hPrio : a.priority = b.priority) (hDom : a.domain = b.domain)
    (hCsp : a.cspaceRoot = b.cspaceRoot) (hVsp : a.vspaceRoot = b.vspaceRoot)
    (hBuf : a.ipcBuffer = b.ipcBuffer) (hIpc : a.ipcState = b.ipcState)
    (hTs : a.threadState = b.threadState)
    (hSlice : a.timeSlice = b.timeSlice) (hDeadline : a.deadline = b.deadline)
    (hQPrev : a.queuePrev = b.queuePrev) (hQPPrev : a.queuePPrev = b.queuePPrev)
    (hQNext : a.queueNext = b.queueNext) (hPend : a.pendingMessage = b.pendingMessage)
    (hRC : a.registerContext = b.registerContext)
    (hFh : a.faultHandler = b.faultHandler) (hBn : a.boundNotification = b.boundNotification)
    (hSc : a.schedContextBinding = b.schedContextBinding)
    (hTb : a.timeoutBudget = b.timeoutBudget)
    (hMcp : a.maxControlledPriority = b.maxControlledPriority)
    (hPip : a.pipBoost = b.pipBoost)
    (hTo : a.timedOut = b.timedOut) :
    a = b := by
  cases a; cases b
  simp at *
  exact ⟨hTid, hPrio, hDom, hCsp, hVsp, hBuf, hIpc, hTs, hSlice, hDeadline,
         hQPrev, hQPPrev, hQNext, hPend, hRC, hFh, hBn, hSc, hTb, hMcp, hPip, hTo⟩

/-- Intrusive FIFO queue metadata for endpoint wait queues.

Queue membership links are stored in the waiting TCBs (`queuePrev`/`queueNext`).
The endpoint stores only queue boundaries. -/
structure IntrusiveQueue where
  head : Option SeLe4n.ThreadId := none
  tail : Option SeLe4n.ThreadId := none
  deriving Repr, DecidableEq

/-- Endpoint object model.

WS-H12a: Endpoint structure uses only intrusive dual-queue fields.
Legacy WS-E3 fields (`state`, `queue`, `waitingReceiver`) and the
`EndpointState` type have been removed — all IPC operations use the O(1)
dual-queue path (`endpointSendDual`/`endpointReceiveDual`). -/
structure Endpoint where
  sendQ : IntrusiveQueue := {}
  receiveQ : IntrusiveQueue := {}
  deriving Repr, DecidableEq

inductive NotificationState where
  | idle
  | waiting
  | active
  deriving Repr, DecidableEq

/-- Minimal notification object model for WS-B6.

`active` stores a single pending badge, while `waiting` tracks blocked receivers.

**S4-G: `waitingThreads` representation evaluation.** An intrusive queue
(matching the endpoint dual-queue design) was evaluated and not implemented:

1. **Low cardinality.** Unlike endpoint send/receive queues which can grow to
   hundreds of threads in server workloads, notification waiting lists are
   typically short (1-3 threads). The seL4 spec notes that most notifications
   are 1:1 or 1:N with small N.

2. **No ordering requirement.** `notificationSignal` wakes the head waiter
   (`List.head?`), but seL4 does not guarantee FIFO ordering for notification
   waiters. Any waiter may be woken, so the prepend-based O(1) enqueue in
   `notificationWait` is semantically correct.

3. **O(n) cost is acceptable.** The only O(n) operation is
   `List.filter` in `removeFromAllNotificationWaitLists` (lifecycle cleanup),
   which iterates over all notifications' waiting lists during TCB deletion.
   With the expected bound of ≤8 waiters per notification (typical RPi5 core
   count), this is effectively O(1).

4. **Migration cost.** Intrusive queues require adding `notifQueuePrev`/
   `notifQueueNext` fields to TCB (6 new fields including PPrev metadata),
   duplicating the endpoint queue infrastructure for minimal benefit.

The `List` representation is retained. If future profiling reveals notification
queue pressure, migration to intrusive queues remains straightforward. -/
structure Notification where
  state : NotificationState
  /-- T5-L (M-MOD-6): Blocked waiter list. Uses `List.cons` prepend (LIFO ordering),
      matching seL4's notification wait semantics. `notificationWait` prepends the
      caller's ThreadId, and `notificationSignal` wakes via `List.head?` (most
      recently blocked waiter). This LIFO order is deliberate: seL4 does not
      guarantee FIFO for notification waiters, and prepend gives O(1) enqueue.
      Thread removal during lifecycle cleanup uses `List.filter` (O(n), acceptable
      for ≤8 waiters per notification).

      **WS-RC R4.C (DEEP-IPC-05; subsumes DEEP-IPC-01)**: the list-level
      no-duplicate property is carried **structurally** by
      `SeLe4n.NoDupList SeLe4n.ThreadId`, materialised in
      `SeLe4n/Model/Object/NoDupList.lean`. The wrapper exposes
      `val : List SeLe4n.ThreadId` plus a proof `hNodup : val.Nodup`, so
      every reachable notification has a duplicate-free waiter list by
      construction. The smart constructors `NoDupList.empty`,
      `NoDupList.consWithGuard?`, `NoDupList.filter`, and `NoDupList.tail?`
      discharge the obligation at every mutation site (`Endpoint.lean`,
      `Cleanup.lean`, `FrozenOps/Operations.lean`).  The runtime duplicate
      guard at `IPC/Operations/Endpoint.lean` is subsumed by
      `NoDupList.consWithGuard?` (which returns `none` for a duplicate and
      is consumed as `.error .alreadyWaiting`); the state-level invariant
      `SeLe4n.Kernel.uniqueWaiters` collapses to a trivial projection of
      `hNodup`. The structural-witness theorems
      `SeLe4n.Kernel.notification_waitingThreads_nodup_witness` and
      `SeLe4n.Kernel.notificationWait_runtime_check_implied_by_nodup` (in
      `IPC/Invariant/QueueNoDup.lean`) codify this closure at the proof
      surface, per the WS-RC §1.5 structural-fix policy. -/
  waitingThreads : SeLe4n.NoDupList SeLe4n.ThreadId
  pendingBadge : Option SeLe4n.Badge := none
  deriving Repr, DecidableEq

/-- WS-H13/H-01: Depth-aware CNode with compressed-path guard.

`depth` = maximum remaining CSpace depth in bits from this node to any leaf.
Each resolution step consumes `guardWidth + radixWidth` bits.
A large `guardWidth` compresses an unbranched path prefix into a single
guard comparison, avoiding chains of intermediate CNodes (Patricia-trie
optimisation matching seL4's real CSpace implementation).

`slots` is backed by `SeLe4n.UniqueSlotMap Capability` — a smart-constructor
wrapper around `RHTable Slot Capability` (the formally verified Robin Hood
hash table providing O(1) amortized lookup, insert, and delete with
machine-checked proofs).  The wrapper carries `RHTable.invExtK`
(no-duplicate-keys ∧ `size < capacity` ∧ `4 ≤ capacity`) structurally at
construction time, so the state-level `cspaceSlotUnique` invariant
collapses to a trivial projection of `hWF`.  Defined in
`SeLe4n/Model/Object/UniqueSlotMap.lean`. -/
structure CNode where
  depth      : Nat          -- maximum remaining depth in bits from this node to any leaf
  guardWidth : Nat          -- width of guard field in bits
  guardValue : Nat          -- expected guard value to match
  radixWidth : Nat          -- width of slot index in bits (2^radixWidth slots)
  slots      : SeLe4n.UniqueSlotMap Capability
  deriving Repr

/-- Maximum CSpace address width (matching ARM64 word size). -/
def maxCSpaceDepth : Nat := 64

/-- WS-F2: Child allocation record within an untyped memory region.
Each child records the object identity, its byte offset within the parent
untyped region, and its allocation size. -/
structure UntypedChild where
  objId : SeLe4n.ObjId
  offset : Nat
  size : Nat
  deriving Repr, DecidableEq

/-- WS-F2: Untyped memory object — the foundational seL4 memory safety mechanism.

Models a contiguous region of physical memory `[regionBase, regionBase + regionSize)`
from which typed kernel objects are carved via `retypeFromUntyped`. The `watermark`
tracks the next free byte offset within the region (monotonically increasing).

seL4 reference: `Untyped_D` in the abstract spec — tracks device/non-device flag,
region bounds, and a free-area pointer. Our model uses an explicit child list for
non-overlap proofs rather than relying on CSpace derivation tree ancestry. -/
structure UntypedObject where
  /-- Base physical address of the untyped region. -/
  regionBase : SeLe4n.PAddr
  /-- Total size of the region in bytes. -/
  regionSize : Nat
  /-- Next free byte offset within the region. Monotonically increasing.
      Invariant: `watermark ≤ regionSize`. -/
  watermark : Nat := 0
  /-- List of typed objects carved from this region. Each child records
      its ObjId, offset within the region, and size. -/
  children : List UntypedChild := []
  /-- Whether this untyped covers device memory (MMIO). Device untypeds
      cannot back TCBs, CNodes, or other kernel objects. -/
  isDevice : Bool := false
  /-- AN6-C.1 (H-09): parent ObjId for transitive ancestor tracking.
      `none` for top-level (boot-allocated) untypeds; `some parentId` for
      untypeds carved out by a `retypeFromUntyped` call with `.untyped`
      target. Enables the transitive `untypedAncestorRegionsDisjoint`
      invariant (AN6-C.4 in `CrossSubsystem.lean`) to walk ancestor
      chains and avoid false-overlap reports for grandparent-grandchild
      nesting. For non-`.untyped` children (e.g., TCBs, Endpoints) the
      parent relationship is irrelevant and the field is unused since
      non-untyped objects do not carry an `UntypedObject` record.

      **Default** is `none` to preserve backward compatibility with
      existing tests + fixtures that construct `UntypedObject` via named
      field syntax. Existing code that does not set `parent` defaults to
      "top-level" semantics, which is correct for boot-constructed
      untypeds and for any test that does not exercise multi-level
      retype chains. -/
  parent : Option SeLe4n.ObjId := none
  deriving Repr, DecidableEq

namespace UntypedObject

/-- Remaining free space in the untyped region. -/
def freeSpace (ut : UntypedObject) : Nat :=
  ut.regionSize - ut.watermark

/-- Check whether an allocation of `size` bytes fits within the remaining region. -/
def canAllocate (ut : UntypedObject) (size : Nat) : Bool :=
  size > 0 && ut.watermark + size ≤ ut.regionSize

/-- Allocate `size` bytes from the region, returning the updated untyped and
    the byte offset of the new allocation.

    S4-H: New children are prepended to the `children` list, creating
    reverse-chronological order (most recent allocation first). Proofs that
    traverse children must account for this ordering — in particular,
    `List.mem` witnesses are preserved across allocations since prepending
    does not remove existing elements. -/
def allocate (ut : UntypedObject) (childId : SeLe4n.ObjId) (size : Nat) :
    Option (UntypedObject × Nat) :=
  if ut.canAllocate size then
    let offset := ut.watermark
    some ({ ut with
      watermark := ut.watermark + size
      children := { objId := childId, offset := offset, size := size } :: ut.children
    }, offset)
  else
    none

/-- AK7-K (F-L14 / LOW): Allocation with an explicit positive-size
precondition. `allocateChecked size h` rejects zero-size child
allocations statically via the `h : size > 0` witness, in addition to
the `canAllocate` watermark check performed by `allocate`.

A zero-size child is not ill-formed in the abstract model (the
watermark is unchanged, the child list gains an empty-extent entry),
but it indicates a caller bug — no production syscall path allocates a
zero-size object. The checked variant surfaces this at the type level,
matching the F-L14 guard recommendation without breaking existing
callers. -/
def allocateChecked (ut : UntypedObject) (childId : SeLe4n.ObjId) (size : Nat)
    (_hPos : size > 0) : Option (UntypedObject × Nat) :=
  ut.allocate childId size

/-- AK7-K (F-L14): `allocateChecked` agrees with `allocate` on positive
sizes — it simply adds the positive-size proof obligation at the type
level without changing the body. -/
theorem allocateChecked_eq_allocate (ut : UntypedObject) (childId : SeLe4n.ObjId)
    (size : Nat) (hPos : size > 0) :
    ut.allocateChecked childId size hPos = ut.allocate childId size := rfl

/-- Reset the untyped to its initial state (revoke all children). -/
def reset (ut : UntypedObject) : UntypedObject :=
  { ut with watermark := 0, children := [] }

/-- Watermark is within region bounds. -/
def watermarkValid (ut : UntypedObject) : Prop :=
  ut.watermark ≤ ut.regionSize

/-- All children fit within the watermark (and thus within the region). -/
def childrenWithinWatermark (ut : UntypedObject) : Prop :=
  ∀ c ∈ ut.children, c.offset + c.size ≤ ut.watermark

/-- No two children overlap in the allocated region. -/
def childrenNonOverlap (ut : UntypedObject) : Prop :=
  ∀ c₁ c₂, c₁ ∈ ut.children → c₂ ∈ ut.children →
    c₁ ≠ c₂ → c₁.offset + c₁.size ≤ c₂.offset ∨ c₂.offset + c₂.size ≤ c₁.offset

/-- Children have distinct object identities. -/
def childrenUniqueIds (ut : UntypedObject) : Prop :=
  ∀ c₁ c₂, c₁ ∈ ut.children → c₂ ∈ ut.children →
    c₁.objId = c₂.objId → c₁ = c₂

/-- Combined well-formedness predicate for the untyped object. -/
def wellFormed (ut : UntypedObject) : Prop :=
  ut.watermarkValid ∧ ut.childrenWithinWatermark ∧
  ut.childrenNonOverlap ∧ ut.childrenUniqueIds

theorem empty_watermarkValid (base : SeLe4n.PAddr) (size : Nat) :
    (UntypedObject.mk base size 0 [] false none).watermarkValid := by
  simp [watermarkValid]

theorem empty_childrenWithinWatermark (base : SeLe4n.PAddr) (size : Nat) :
    (UntypedObject.mk base size 0 [] false none).childrenWithinWatermark := by
  intro c hMem
  simp at hMem

theorem empty_childrenNonOverlap (base : SeLe4n.PAddr) (size : Nat) :
    (UntypedObject.mk base size 0 [] false none).childrenNonOverlap := by
  intro c₁ c₂ hMem₁
  simp at hMem₁

theorem empty_childrenUniqueIds (base : SeLe4n.PAddr) (size : Nat) :
    (UntypedObject.mk base size 0 [] false none).childrenUniqueIds := by
  intro c₁ c₂ hMem₁
  simp at hMem₁

theorem empty_wellFormed (base : SeLe4n.PAddr) (size : Nat) :
    (UntypedObject.mk base size 0 [] false none).wellFormed :=
  ⟨empty_watermarkValid base size, empty_childrenWithinWatermark base size,
   empty_childrenNonOverlap base size, empty_childrenUniqueIds base size⟩

/-! ### AN2-F.3 / FND-M03 — `UntypedObjectValid` subtype (marker)

    A proof-carrying refinement of `UntypedObject` whose well-formedness
    has been discharged at construction time. Defined below, outside the
    `UntypedObject` namespace, so it is reachable from callers via
    `SeLe4n.Model.UntypedObjectValid` (or just `UntypedObjectValid` with
    `open SeLe4n.Model`). -/

/-- `canAllocate` being true implies the allocation fits within region bounds. -/
theorem canAllocate_implies_fits (ut : UntypedObject) (size : Nat)
    (hCan : ut.canAllocate size = true) :
    ut.watermark + size ≤ ut.regionSize := by
  simp [canAllocate] at hCan
  exact hCan.2

/-- Decomposition lemma: a successful `allocate` produces a specific updated state. -/
theorem allocate_some_iff (ut : UntypedObject) (childId : SeLe4n.ObjId) (size : Nat)
    (result : UntypedObject × Nat) :
    ut.allocate childId size = some result ↔
      ut.canAllocate size = true ∧
      result = ({ ut with
        watermark := ut.watermark + size
        children := { objId := childId, offset := ut.watermark, size := size } :: ut.children
      }, ut.watermark) := by
  constructor
  · intro h
    unfold allocate at h
    by_cases hCan : ut.canAllocate size
    · simp [hCan] at h; exact ⟨hCan, h.symm⟩
    · simp [hCan] at h
  · intro ⟨hCan, hEq⟩
    unfold allocate
    simp [hCan, hEq]

/-- After a successful `allocate`, the watermark advances by exactly `size`. -/
theorem allocate_watermark_advance (ut ut' : UntypedObject) (childId : SeLe4n.ObjId)
    (size offset : Nat) (hAlloc : ut.allocate childId size = some (ut', offset)) :
    ut'.watermark = ut.watermark + size := by
  rw [allocate_some_iff] at hAlloc
  rcases hAlloc with ⟨_, hEq⟩
  have hU := (Prod.mk.inj hEq).1
  subst hU; rfl

/-- After a successful `allocate`, the returned offset equals the pre-allocation watermark. -/
theorem allocate_offset_eq_watermark (ut ut' : UntypedObject) (childId : SeLe4n.ObjId)
    (size offset : Nat) (hAlloc : ut.allocate childId size = some (ut', offset)) :
    offset = ut.watermark := by
  rw [allocate_some_iff] at hAlloc
  exact (Prod.mk.inj hAlloc.2).2

/-- Watermark monotonicity: a successful allocation never decreases the watermark. -/
theorem allocate_watermark_monotone (ut ut' : UntypedObject) (childId : SeLe4n.ObjId)
    (size offset : Nat) (hAlloc : ut.allocate childId size = some (ut', offset)) :
    ut.watermark ≤ ut'.watermark := by
  have hAdv := allocate_watermark_advance ut ut' childId size offset hAlloc
  omega

/-- A successful allocation preserves watermark validity when the pre-state is valid. -/
theorem allocate_preserves_watermarkValid (ut ut' : UntypedObject) (childId : SeLe4n.ObjId)
    (size offset : Nat) (_hWF : ut.watermarkValid)
    (hAlloc : ut.allocate childId size = some (ut', offset)) :
    ut'.watermarkValid := by
  rw [allocate_some_iff] at hAlloc
  rcases hAlloc with ⟨hCan, hEq⟩
  have hFits := canAllocate_implies_fits ut size hCan
  have hU := (Prod.mk.inj hEq).1
  subst hU; simp [watermarkValid]; omega

/-- `allocate` does not change the region base or size. -/
theorem allocate_preserves_region (ut ut' : UntypedObject) (childId : SeLe4n.ObjId)
    (size offset : Nat) (hAlloc : ut.allocate childId size = some (ut', offset)) :
    ut'.regionBase = ut.regionBase ∧ ut'.regionSize = ut.regionSize := by
  rw [allocate_some_iff] at hAlloc
  rcases hAlloc with ⟨_, hEq⟩
  have hU := (Prod.mk.inj hEq).1
  subst hU; exact ⟨rfl, rfl⟩

/-- AK8-A (WS-AK / C-M01): `allocate` extends the children list — every
existing entry in `ut.children` is still present in `ut'.children`. Used
by the cross-untyped disjointness preservation proof to transport
child-exclusion hypotheses across the allocation step. -/
theorem allocate_children_extends (ut ut' : UntypedObject)
    (childId : SeLe4n.ObjId) (size offset : Nat)
    (hAlloc : ut.allocate childId size = some (ut', offset)) :
    ∀ c, c ∈ ut.children → c ∈ ut'.children := by
  rw [allocate_some_iff] at hAlloc
  rcases hAlloc with ⟨_, hEq⟩
  have hU := (Prod.mk.inj hEq).1; subst hU
  intro c hc; exact List.mem_cons_of_mem _ hc

/-- AK8-A (WS-AK / C-M01): `allocate` places the new child at the head of
the children list, with exact bookkeeping for `objId`, `offset`, and
`size`. This is the key structural fact used by the retype preservation
proof to show that the parent's post-state children list contains the
new child (so the parent-child pair is excluded from disjointness). -/
theorem allocate_children_new (ut ut' : UntypedObject)
    (childId : SeLe4n.ObjId) (size offset : Nat)
    (hAlloc : ut.allocate childId size = some (ut', offset)) :
    { objId := childId, offset := ut.watermark, size := size : UntypedChild }
      ∈ ut'.children := by
  rw [allocate_some_iff] at hAlloc
  rcases hAlloc with ⟨_, hEq⟩
  have hU := (Prod.mk.inj hEq).1; subst hU
  exact List.mem_cons_self ..

/-- AK8-A (WS-AK / C-M01): `allocate`'s post-state `children` list equals
the new child prepended onto the pre-state list. Combined with
`allocate_children_extends`, this exhaustively characterizes the change
to `children`. -/
theorem allocate_children_eq (ut ut' : UntypedObject)
    (childId : SeLe4n.ObjId) (size offset : Nat)
    (hAlloc : ut.allocate childId size = some (ut', offset)) :
    ut'.children =
      { objId := childId, offset := ut.watermark, size := size }
        :: ut.children := by
  rw [allocate_some_iff] at hAlloc
  rcases hAlloc with ⟨_, hEq⟩
  have hU := (Prod.mk.inj hEq).1; subst hU; rfl

/-- AK8-A (WS-AK / C-M01): A successful `allocate` witnesses that the
requested size fits within the parent's region — the new child's
`[parent.regionBase + offset, parent.regionBase + offset + size)` range
lies entirely inside `[parent.regionBase, parent.regionBase + parent.regionSize)`. -/
theorem allocate_child_fits_parent (ut ut' : UntypedObject)
    (childId : SeLe4n.ObjId) (size offset : Nat)
    (hAlloc : ut.allocate childId size = some (ut', offset)) :
    offset + size ≤ ut.regionSize := by
  rw [allocate_some_iff] at hAlloc
  rcases hAlloc with ⟨hCan, hEq⟩
  have hOffsetEq : offset = ut.watermark := (Prod.mk.inj hEq).2
  have hFits := canAllocate_implies_fits ut size hCan
  omega

/-- WS-F2: A successful allocation preserves childrenWithinWatermark.
Existing children are within the old watermark (≤ new watermark), and the new
child occupies [old_watermark, old_watermark + size] = [old_watermark, new_watermark]. -/
theorem allocate_preserves_childrenWithinWatermark (ut ut' : UntypedObject)
    (childId : SeLe4n.ObjId) (size offset : Nat)
    (hBounds : ut.childrenWithinWatermark)
    (hAlloc : ut.allocate childId size = some (ut', offset)) :
    ut'.childrenWithinWatermark := by
  rw [allocate_some_iff] at hAlloc
  rcases hAlloc with ⟨_hCan, hEq⟩
  have hU := (Prod.mk.inj hEq).1; subst hU
  intro c hMem
  simp at hMem ⊢
  rcases hMem with rfl | hOld
  · dsimp; omega
  · have := hBounds c hOld; omega

/-- WS-F2: A successful allocation preserves childrenNonOverlap, given that
existing children are within the watermark. Since the new child starts at the
old watermark and all existing children end at or before the old watermark,
no overlap is possible. -/
theorem allocate_preserves_childrenNonOverlap (ut ut' : UntypedObject)
    (childId : SeLe4n.ObjId) (size offset : Nat)
    (hNonOverlap : ut.childrenNonOverlap)
    (hBounds : ut.childrenWithinWatermark)
    (hAlloc : ut.allocate childId size = some (ut', offset)) :
    ut'.childrenNonOverlap := by
  rw [allocate_some_iff] at hAlloc
  rcases hAlloc with ⟨_hCan, hEq⟩
  have hU := (Prod.mk.inj hEq).1; subst hU
  intro c₁ c₂ hMem₁ hMem₂ hNe
  simp at hMem₁ hMem₂
  rcases hMem₁ with rfl | hOld₁ <;> rcases hMem₂ with rfl | hOld₂
  · exact absurd rfl hNe
  · -- new child vs old child: old child ends ≤ watermark = new child offset
    right; have := hBounds c₂ hOld₂; dsimp; omega
  · -- old child vs new child: old child ends ≤ watermark = new child offset
    left; have := hBounds c₁ hOld₁; dsimp; omega
  · -- two old children: by pre-condition
    exact hNonOverlap c₁ c₂ hOld₁ hOld₂ hNe

/-- WS-F2: A successful allocation preserves childrenUniqueIds, given that
the new child's ID does not collide with any existing child. -/
theorem allocate_preserves_childrenUniqueIds (ut ut' : UntypedObject)
    (childId : SeLe4n.ObjId) (size offset : Nat)
    (hUnique : ut.childrenUniqueIds)
    (hFresh : ∀ c ∈ ut.children, c.objId ≠ childId)
    (hAlloc : ut.allocate childId size = some (ut', offset)) :
    ut'.childrenUniqueIds := by
  rw [allocate_some_iff] at hAlloc
  rcases hAlloc with ⟨_hCan, hEq⟩
  have hU := (Prod.mk.inj hEq).1; subst hU
  intro c₁ c₂ hMem₁ hMem₂ hIdEq
  simp at hMem₁ hMem₂
  rcases hMem₁ with rfl | hOld₁ <;> rcases hMem₂ with rfl | hOld₂
  · rfl
  · -- new child has objId = childId, old child has objId ≠ childId
    dsimp at hIdEq; exact absurd hIdEq.symm (hFresh c₂ hOld₂)
  · dsimp at hIdEq; exact absurd hIdEq (hFresh c₁ hOld₁)
  · exact hUnique c₁ c₂ hOld₁ hOld₂ hIdEq

/-- `reset` restores watermark validity. -/
theorem reset_watermarkValid (ut : UntypedObject) : ut.reset.watermarkValid := by
  simp [reset, watermarkValid]

/-- `reset` restores full well-formedness. -/
theorem reset_wellFormed (ut : UntypedObject) : ut.reset.wellFormed := by
  refine ⟨reset_watermarkValid ut, ?_, ?_, ?_⟩
  · intro c hMem; simp [reset] at hMem
  · intro c₁ c₂ hMem₁; simp [reset] at hMem₁
  · intro c₁ c₂ hMem₁; simp [reset] at hMem₁

end UntypedObject

/-! ### AN2-F.3 / FND-M03 — `UntypedObjectValid` subtype

    A proof-carrying refinement of `UntypedObject` whose well-formedness
    has been discharged at construction time. Production paths (retype,
    capability derivation) that require a well-formed untyped region
    should accept this subtype rather than bare `UntypedObject` + a
    run-time `wellFormed` check.

    Current state (AN2-landed subset): the subtype is defined and a
    convenience `UntypedObjectValid.empty` smart constructor is provided.
    Tightening `allocate` / `retypeFromUntyped` entry signatures to take
    `UntypedObjectValid` (instead of a bare `UntypedObject`) is tracked
    as an AN2-continuation cascade — each caller needs to produce the
    `.wellFormed` witness locally, which typically reduces to the
    `crossSubsystemInvariant` / `retypeFromUntyped_capacity_gated`
    chain already present at kernel-entry boundaries. -/
def UntypedObjectValid : Type := { ut : UntypedObject // ut.wellFormed }

namespace UntypedObjectValid

/-- AN2-F.3: Project the underlying `UntypedObject`. -/
@[inline] def toUntyped (u : UntypedObjectValid) : UntypedObject := u.val

/-- AN2-F.3: Extract the well-formedness witness. -/
@[inline] def wf (u : UntypedObjectValid) : u.toUntyped.wellFormed := u.property

/-- AN2-F.3: Canonical empty constructor — a fresh untyped region at `base`
    with `size` capacity, zero children, is well-formed by `empty_wellFormed`. -/
@[inline] def empty (base : SeLe4n.PAddr) (size : Nat) : UntypedObjectValid :=
  ⟨UntypedObject.mk base size 0 [] false none, UntypedObject.empty_wellFormed base size⟩

end UntypedObjectValid

instance : CoeHead UntypedObjectValid UntypedObject := ⟨UntypedObjectValid.toUntyped⟩

-- ============================================================================
-- Syscall decode types — register-sourced syscall argument decoding
-- ============================================================================

/-- Typed syscall identifier covering the modeled syscall set.
    Maps to the syscall number register value (x7 on ARM64).
    Each variant corresponds to exactly one kernel API entry point. -/
inductive SyscallId where
  | send
  | receive
  | call
  | reply
  | cspaceMint
  | cspaceCopy
  | cspaceMove
  | cspaceDelete
  | lifecycleRetype
  | vspaceMap
  | vspaceUnmap
  | serviceRegister      -- WS-Q1-D: capability-mediated service registration
  | serviceRevoke        -- WS-Q1-D: service revocation
  | serviceQuery         -- WS-Q1-D: service lookup by capability
  | notificationSignal   -- V2-A: notification signal (badge merge / wake waiter)
  | notificationWait     -- V2-A: notification wait (consume badge / block)
  | replyRecv            -- V2-C: compound reply + receive in one transition
  | schedContextConfigure  -- Z5-D: configure SchedContext parameters
  | schedContextBind       -- Z5-D: bind thread to SchedContext
  | schedContextUnbind     -- Z5-D: unbind thread from SchedContext
  | tcbSuspend             -- D1-A: suspend a thread (transition to Inactive)
  | tcbResume              -- D1-A: resume a suspended thread (transition to Ready)
  | tcbSetPriority         -- D2-B: set thread scheduling priority (MCP-bounded)
  | tcbSetMCPriority       -- D2-B: set thread maximum controlled priority
  | tcbSetIPCBuffer        -- D3-A: set thread IPC buffer address
  deriving Repr, DecidableEq, Inhabited

namespace SyscallId

/-- Encode a syscall identifier to its numeric value for the syscall number
    register. The encoding matches the canonical ordering and is injective. -/
@[inline] def toNat : SyscallId → Nat
  | .send            => 0
  | .receive         => 1
  | .call            => 2
  | .reply           => 3
  | .cspaceMint      => 4
  | .cspaceCopy      => 5
  | .cspaceMove      => 6
  | .cspaceDelete    => 7
  | .lifecycleRetype => 8
  | .vspaceMap       => 9
  | .vspaceUnmap     => 10
  | .serviceRegister    => 11
  | .serviceRevoke      => 12
  | .serviceQuery       => 13
  | .notificationSignal => 14
  | .notificationWait   => 15
  | .replyRecv          => 16
  | .schedContextConfigure => 17
  | .schedContextBind      => 18
  | .schedContextUnbind    => 19
  | .tcbSuspend            => 20
  | .tcbResume             => 21
  | .tcbSetPriority        => 22
  | .tcbSetMCPriority      => 23
  | .tcbSetIPCBuffer       => 24

/-- Total number of modeled syscalls. -/
def count : Nat := 25

/-- Decode a natural number to a syscall identifier.
    Returns `none` for values outside the modeled set. -/
@[inline] def ofNat? : Nat → Option SyscallId
  | 0  => some .send
  | 1  => some .receive
  | 2  => some .call
  | 3  => some .reply
  | 4  => some .cspaceMint
  | 5  => some .cspaceCopy
  | 6  => some .cspaceMove
  | 7  => some .cspaceDelete
  | 8  => some .lifecycleRetype
  | 9  => some .vspaceMap
  | 10 => some .vspaceUnmap
  | 11 => some .serviceRegister
  | 12 => some .serviceRevoke
  | 13 => some .serviceQuery
  | 14 => some .notificationSignal
  | 15 => some .notificationWait
  | 16 => some .replyRecv
  | 17 => some .schedContextConfigure
  | 18 => some .schedContextBind
  | 19 => some .schedContextUnbind
  | 20 => some .tcbSuspend
  | 21 => some .tcbResume
  | 22 => some .tcbSetPriority
  | 23 => some .tcbSetMCPriority
  | 24 => some .tcbSetIPCBuffer
  | _  => none

instance : ToString SyscallId where
  toString
    | .send            => "send"
    | .receive         => "receive"
    | .call            => "call"
    | .reply           => "reply"
    | .cspaceMint      => "cspaceMint"
    | .cspaceCopy      => "cspaceCopy"
    | .cspaceMove      => "cspaceMove"
    | .cspaceDelete    => "cspaceDelete"
    | .lifecycleRetype => "lifecycleRetype"
    | .vspaceMap       => "vspaceMap"
    | .vspaceUnmap     => "vspaceUnmap"
    | .serviceRegister    => "serviceRegister"
    | .serviceRevoke      => "serviceRevoke"
    | .serviceQuery       => "serviceQuery"
    | .notificationSignal => "notificationSignal"
    | .notificationWait   => "notificationWait"
    | .replyRecv          => "replyRecv"
    | .schedContextConfigure => "schedContextConfigure"
    | .schedContextBind      => "schedContextBind"
    | .schedContextUnbind    => "schedContextUnbind"
    | .tcbSuspend            => "tcbSuspend"
    | .tcbResume             => "tcbResume"
    | .tcbSetPriority        => "tcbSetPriority"
    | .tcbSetMCPriority      => "tcbSetMCPriority"
    | .tcbSetIPCBuffer       => "tcbSetIPCBuffer"

/-- AC4-D/IF-01: Exhaustive list of all SyscallId variants. Used by the enforcement
    boundary completeness witness to ensure every syscall is classified. The
    `all_length` theorem provides a compile-time check that this list stays in
    sync with the `count` constant. -/
def all : List SyscallId :=
  [ .send, .receive, .call, .reply
  , .cspaceMint, .cspaceCopy, .cspaceMove, .cspaceDelete
  , .lifecycleRetype, .vspaceMap, .vspaceUnmap
  , .serviceRegister, .serviceRevoke, .serviceQuery
  , .notificationSignal, .notificationWait, .replyRecv
  , .schedContextConfigure, .schedContextBind, .schedContextUnbind
  , .tcbSuspend, .tcbResume, .tcbSetPriority, .tcbSetMCPriority
  , .tcbSetIPCBuffer ]

/-- AC4-D: Compile-time check — `all` has exactly `count` elements.
    Fails at compile time if a variant is added to the inductive but not to `all`. -/
theorem all_length : all.length = count := by rfl

/-- AC4-D: Every SyscallId is a member of `all`. -/
theorem all_complete (s : SyscallId) : s ∈ all := by
  cases s <;> decide

/-- Round-trip: encoding then decoding a SyscallId recovers the original. -/
theorem ofNat_toNat (s : SyscallId) : SyscallId.ofNat? s.toNat = some s := by
  cases s <;> rfl

/-- Round-trip: decoding then encoding preserves the numeric value.

S4-I: This proof uses a uniform `match`/`simp`/`subst` pattern for each of
the 20 syscall variants plus a wildcard case. The `cases s <;> rfl` approach
used for `ofNat_toNat` is not applicable here because the hypothesis is on `n`
(a `Nat`) rather than on a finite inductive type. A `decide`-based approach
would require `BEq`/`DecidableEq` on the `Option SyscallId × Nat` pair and
scales poorly for larger enums. The current explicit case enumeration is the
most robust approach for Lean 4's pattern matching. -/
theorem toNat_ofNat {n : Nat} {s : SyscallId} (h : SyscallId.ofNat? n = some s) :
    s.toNat = n := by
  revert s
  match n with
  | 0  | 1  | 2  | 3  | 4  | 5  | 6
  | 7  | 8  | 9  | 10 | 11 | 12 | 13
  | 14 | 15 | 16 | 17 | 18 | 19
  | 20 | 21 | 22 | 23 | 24 =>
    intro s h; simp [ofNat?] at h; subst h; rfl
  | n + 25 => intro s h; simp [ofNat?] at h

/-- Injectivity: the toNat encoding is injective. -/
theorem toNat_injective {a b : SyscallId} (h : a.toNat = b.toNat) : a = b := by
  have ha := ofNat_toNat a
  have hb := ofNat_toNat b
  rw [h] at ha
  rw [ha] at hb
  exact Option.some.inj hb

end SyscallId

/-- Decoded message-info word layout, matching seL4's `seL4_MessageInfo_t`.
    Encodes the metadata carried in the message-info register (x1 on ARM64):
    - `length`: number of message registers used (0..120)
    - `extraCaps`: number of extra capabilities transferred (0..3)
    - `label`: user-specified label/tag for message discrimination

AK7-D (F-M02 / MEDIUM): The raw constructor `MessageInfo.mk` bypasses the
`maxLabel` check and the `length`/`extraCaps` bounds. Construction sites
should prefer `MessageInfo.mkChecked` (below), which returns `none` if any
field exceeds its seL4 bound. `MessageInfo.mk` is retained for test
fixtures and decode-path success branches where bounds are already
established by context. -/
structure MessageInfo where
  length    : Nat
  extraCaps : Nat
  label     : Nat
  deriving Repr, DecidableEq, Inhabited

namespace MessageInfo

/-- V2-E (M-API-3): Maximum label value — 2^20 - 1 (20 bits), matching seL4's
    `seL4_MessageInfo_t` label field width. The previous model allowed unbounded
    labels (55 bits), which diverged from seL4's 20-bit limit. -/
def maxLabel : Nat := (1 <<< 20) - 1

/-- AK7-D (F-M02 / MEDIUM): Checked constructor that validates each field
against its seL4 bound before returning a `MessageInfo`.

Enforces:
- `length ≤ maxMessageRegisters` (120 registers)
- `extraCaps ≤ maxExtraCaps` (3 extra capabilities)
- `label ≤ maxLabel` (20-bit label, 2^20 − 1)

Returns `none` on any bound violation, matching the behavior of the
validating `decode` path. Prefer this over `MessageInfo.mk` anywhere the
caller constructs a message info from unvalidated input (IPC send,
service-register ABI, test fixtures crossing bound boundaries). -/
@[inline] def mkChecked (length : Nat) (extraCaps : Nat) (label : Nat) :
    Option MessageInfo :=
  if length ≤ maxMessageRegisters ∧ extraCaps ≤ maxExtraCaps ∧ label ≤ maxLabel then
    some { length, extraCaps, label }
  else
    none

/-- AK7-D (F-M02): `mkChecked` returns `some` iff all bounds hold. -/
theorem mkChecked_isSome_iff (length extraCaps label : Nat) :
    (mkChecked length extraCaps label).isSome = true ↔
    length ≤ maxMessageRegisters ∧ extraCaps ≤ maxExtraCaps ∧ label ≤ maxLabel := by
  unfold mkChecked
  by_cases h : length ≤ maxMessageRegisters ∧ extraCaps ≤ maxExtraCaps ∧ label ≤ maxLabel
  · simp [h]
  · simp [h]

/-- AK7-D (F-M02): `mkChecked` output satisfies the bounds predicate. -/
theorem mkChecked_bounded {length extraCaps label : Nat} {mi : MessageInfo}
    (h : mkChecked length extraCaps label = some mi) :
    mi.length ≤ maxMessageRegisters ∧ mi.extraCaps ≤ maxExtraCaps ∧
    mi.label ≤ maxLabel := by
  unfold mkChecked at h
  split at h
  · rename_i hAll
    cases h
    exact hAll
  · cases h

/-- AK7-D (F-M02 / MEDIUM): Well-formedness predicate for a `MessageInfo`
value — `length ≤ maxMessageRegisters ∧ extraCaps ≤ maxExtraCaps ∧
label ≤ maxLabel`.

Rationale: `MessageInfo.mk` (the anonymous-braces constructor
`{ length := …, extraCaps := …, label := … }`) cannot be made `private`
without breaking every production and test construction site. The
`wellFormed` predicate is the Prop-level invariant that ABI dispatch and
IPC delivery paths must establish before delivering a message. Values
produced by `MessageInfo.decode` or `MessageInfo.mkChecked` satisfy
`wellFormed` by construction; callers that accept arbitrary fields must
verify the predicate explicitly. -/
def wellFormed (mi : MessageInfo) : Prop :=
  mi.length ≤ maxMessageRegisters ∧
  mi.extraCaps ≤ maxExtraCaps ∧
  mi.label ≤ maxLabel

instance (mi : MessageInfo) : Decidable mi.wellFormed :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- AK7-D (F-M02): Output of `mkChecked` is well-formed. -/
theorem mkChecked_wellFormed {length extraCaps label : Nat} {mi : MessageInfo}
    (h : mkChecked length extraCaps label = some mi) : mi.wellFormed :=
  mkChecked_bounded h

/-- Encode a MessageInfo into a single register word.
    Bit layout (seL4 convention):
    - bits  0..6  : length (7 bits, max 120)
    - bits  7..8  : extraCaps (2 bits, max 3)
    - bits  9..28 : label (20 bits, max 2^20 - 1)
    This matches seL4's `seL4_MessageInfo_t` layout. -/
@[inline] def encode (mi : MessageInfo) : Nat :=
  mi.length ||| (mi.extraCaps <<< 7) ||| (mi.label <<< 9)

/-- Decode a raw word into MessageInfo fields by extracting bit fields.
    Returns `none` if the length or extraCaps fields exceed their bounds,
    or if the label exceeds the 20-bit maximum (V2-E/M-API-3). -/
@[inline] def decode (w : Nat) : Option MessageInfo :=
  let length    := w &&& 0x7F          -- bits 0..6
  let extraCaps := (w >>> 7) &&& 0x3   -- bits 7..8
  let label     := w >>> 9             -- bits 9+
  if length ≤ maxMessageRegisters && extraCaps ≤ Model.maxExtraCaps && label ≤ maxLabel then
    some { length, extraCaps, label }
  else
    none

instance : ToString MessageInfo where
  toString mi := s!"MessageInfo(len={mi.length}, caps={mi.extraCaps}, label={mi.label})"

/-- AK7-D (F-M02): `decode` produces well-formed `MessageInfo` values —
any `MessageInfo` surfaced from a raw register word satisfies all three
seL4 bounds. -/
theorem decode_wellFormed {w : Nat} {mi : MessageInfo}
    (h : MessageInfo.decode w = some mi) : mi.wellFormed := by
  unfold MessageInfo.decode at h
  simp only at h
  split at h
  · rename_i hAll
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hAll
    cases h
    refine ⟨hAll.1.1, ?_, hAll.2⟩
    show _ ≤ maxExtraCaps
    exact hAll.1.2
  · cases h

-- ============================================================================
-- Encode/decode round-trip proof (bitwise extraction lemmas)
-- ============================================================================

/-- Bitwise extraction: AND with 0x7F (127) recovers the low 7-bit field
    when the field value fits in 7 bits. -/
private theorem and_mask_127 (a b c : Nat) (ha : a < 128) :
    (a ||| (b <<< 7) ||| (c <<< 9)) &&& 0x7F = a := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases hi : i < 7
  · have h7 : ¬(7 ≤ i) := by omega
    have h9 : ¬(9 ≤ i) := by omega
    simp only [h7, h9, decide_false, Bool.false_and, Bool.or_false]
    have hmask : (127 : Nat).testBit i = true := by
      have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [hmask, Bool.and_true]
  · have hmask : (127 : Nat).testBit i = false := by
      apply Nat.testBit_lt_two_pow
      calc (127 : Nat) < 2 ^ 7 := by decide
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
    rw [hmask, Bool.and_false]
    symm; apply Nat.testBit_lt_two_pow
    calc a < 128 := ha
      _ = 2 ^ 7 := by decide
      _ ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)

/-- Bitwise extraction: shift right 7 then AND with 0x3 recovers the 2-bit
    extraCaps field from position [7..8]. -/
private theorem shift7_and_mask_3 (a b c : Nat) (ha : a < 128) (hb : b < 4) :
    ((a ||| (b <<< 7) ||| (c <<< 9)) >>> 7) &&& 0x3 = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases hi : i < 2
  · have h7 : 7 ≤ 7 + i := by omega
    have h9 : ¬(9 ≤ 7 + i) := by omega
    simp only [h7, h9, decide_true, decide_false, Bool.true_and, Bool.false_and, Bool.or_false]
    have ha_bit : a.testBit (7 + i) = false := by
      apply Nat.testBit_lt_two_pow
      calc a < 128 := ha
        _ = 2 ^ 7 := by decide
        _ ≤ 2 ^ (7 + i) := Nat.pow_le_pow_right (by omega) (by omega)
    simp only [ha_bit, Bool.false_or]
    have : (7 + i) - 7 = i := by omega
    rw [this]
    have hmask : (3 : Nat).testBit i = true := by
      have : i = 0 ∨ i = 1 := by omega
      rcases this with rfl | rfl <;> decide
    rw [hmask, Bool.and_true]
  · have hmask : (3 : Nat).testBit i = false := by
      apply Nat.testBit_lt_two_pow
      calc (3 : Nat) < 2 ^ 2 := by decide
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
    rw [hmask, Bool.and_false]
    symm; apply Nat.testBit_lt_two_pow
    calc b < 4 := hb
      _ = 2 ^ 2 := by decide
      _ ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)

/-- Bitwise extraction: shift right 9 recovers the label field from position [9..]. -/
private theorem shift9_extracts_label (a b c : Nat) (ha : a < 128) (hb : b < 4) :
    (a ||| (b <<< 7) ||| (c <<< 9)) >>> 9 = c := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_shiftRight, Nat.testBit_or, Nat.testBit_shiftLeft]
  have h9 : 9 ≤ 9 + i := by omega
  have h7 : 7 ≤ 9 + i := by omega
  simp only [h9, h7, decide_true, Bool.true_and]
  have ha_bit : a.testBit (9 + i) = false := by
    apply Nat.testBit_lt_two_pow
    calc a < 128 := ha
      _ = 2 ^ 7 := by decide
      _ ≤ 2 ^ (9 + i) := Nat.pow_le_pow_right (by omega) (by omega)
  simp only [ha_bit, Bool.false_or]
  have hb_bit : b.testBit ((9 + i) - 7) = false := by
    have : (9 + i) - 7 = i + 2 := by omega
    rw [this]
    apply Nat.testBit_lt_two_pow
    calc b < 4 := hb
      _ = 2 ^ 2 := by decide
      _ ≤ 2 ^ (i + 2) := Nat.pow_le_pow_right (by omega) (by omega)
  simp only [hb_bit, Bool.false_or]
  have : (9 + i) - 9 = i := by omega
  rw [this]

/-- Round-trip: encoding then decoding a MessageInfo recovers the original,
    provided the fields satisfy the seL4 message-info bounds.
    This completes the round-trip proof surface for all three register decode
    components (CPtr, SyscallId, and MessageInfo). -/
theorem encode_decode_roundtrip (mi : MessageInfo)
    (hLen : mi.length ≤ maxMessageRegisters)
    (hCaps : mi.extraCaps ≤ maxExtraCaps)
    (hLabel : mi.label ≤ maxLabel := by omega) :
    MessageInfo.decode (MessageInfo.encode mi) = some mi := by
  unfold encode decode
  have hLen128 : mi.length < 128 := by unfold maxMessageRegisters at hLen; omega
  have hCaps4 : mi.extraCaps < 4 := by unfold maxExtraCaps at hCaps; omega
  rw [and_mask_127 mi.length mi.extraCaps mi.label hLen128]
  rw [shift7_and_mask_3 mi.length mi.extraCaps mi.label hLen128 hCaps4]
  rw [shift9_extracts_label mi.length mi.extraCaps mi.label hLen128 hCaps4]
  have hCond : (decide (mi.length ≤ maxMessageRegisters) && decide (mi.extraCaps ≤ maxExtraCaps)
      && decide (mi.label ≤ maxLabel)) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨hLen, hCaps⟩, hLabel⟩
  rw [if_pos hCond]

end MessageInfo

/-- Result of decoding raw register values into typed syscall arguments.
    Produced by the register decode layer; consumed by syscall dispatch.
    The `msgRegs` field carries raw values from the layout's message registers
    (x2–x5 on ARM64). Default `#[]` ensures backward compatibility with
    existing construction sites. Per-syscall argument decode (WS-K-B) extracts
    typed arguments from this array. -/
structure SyscallDecodeResult where
  capAddr      : SeLe4n.CPtr
  msgInfo      : MessageInfo
  syscallId    : SyscallId
  msgRegs      : Array SeLe4n.RegValue := #[]
  /-- V2-F (M-API-5): Cap receive slot base for IPC cap transfer.
      In seL4, this is specified by the receiver. Default `Slot.ofNat 0`
      preserves backward compatibility. Production deployments should
      extract this from the receiver's IPC buffer or syscall arguments. -/
  capRecvSlot  : SeLe4n.Slot := SeLe4n.Slot.ofNat 0
  /-- AK4-A.2 (R-ABI-C01): Number of message registers populated from inline
      GPRs (x2..x5 on ARM64 → 4). Both decoders
      (`decodeSyscallArgs`, `decodeSyscallArgsFromState`) set this to
      `layout.msgRegs.size` — the platform's inline register count (4 for
      `arm64DefaultLayout`) — on every successful decode. Combined
      invariant: `msgRegs.size = inlineCount + overflowCount`. -/
  inlineCount  : Nat := 0
  /-- AK4-A.2 (R-ABI-C01): Number of message registers read from the caller's
      IPC-buffer overflow area. Zero for all syscalls whose
      `msgInfo.length ≤ layout.msgRegs.size` and for the legacy
      `decodeSyscallArgs` path; equal to `msgInfo.length - layout.msgRegs.size`
      on the `decodeSyscallArgsFromState` overflow branch (e.g., 1 for the
      5-arg syscalls `serviceRegister` and `schedContextConfigure`). -/
  overflowCount : Nat := 0
  deriving Repr, DecidableEq
