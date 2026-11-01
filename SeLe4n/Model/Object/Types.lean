-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Machine
import SeLe4n.Model.Fault
import SeLe4n.Kernel.RobinHood
-- Only the SchedContext object type is needed here, not the subsystem hub
-- (`Kernel.SchedContext` also re-exports the budget operations and their
-- invariants, which would sit on the model layer's critical path).
import SeLe4n.Kernel.SchedContext.Types
import SeLe4n.Model.Object.UniqueSlotMap
import SeLe4n.Model.Erased
import SeLe4n.Model.Object.SlotOccupancy
import SeLe4n.Kernel.InformationFlow.Taint

namespace SeLe4n.Model


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

WS-E4/M-12: Added `replyCap` variant for one-shot reply capabilities.

WS-SM SM6.D (seL4-MCS Reply objects): `replyCap` references a first-class
`Reply` *object* by `ReplyId` (the single-use reply authority), not a raw
sender `ThreadId`.  The reply path resolves the `ReplyId` to its `reply.caller`
linkage and consumes it (`reply.caller := none`) on use.

WS-SM SM9.A.9: added `auditTrail`, the authority to read (and, with `.write`,
to drain) the declassification audit trail.

It is a **target**, not a right, and that is the whole point.
`API.syscallLookupCap` checks `cap.hasRight gate.requiredRight` and **nothing
about `cap.target`**, so an audit reader gated only on `.read` would be
reachable by any thread holding any readable capability — which in practice is
every thread, since its own TCB suffices.  That is exactly the confused deputy
closed at v0.32.97, where a thread holding only a writable capability to its own
TCB unmapped a page in a different address space; the fix there was
`vspaceCapAuthorizesAsid`, and the fix here is the same shape and cheaper,
because the trail is a singleton with no operand to bind against
(`API.extractAuditAuthority`).

The trail is not an object in the store, so `.object` would be the wrong
carrier: there is no `ObjId` to name.  Rights stay a second gate — `.read` for
the reader, `.write` for the drain — so a monitoring deployment can hand out a
read-only audit capability that cannot drain. -/
inductive CapTarget where
  | object (id : SeLe4n.ObjId)
  | cnodeSlot (cnode : SeLe4n.ObjId) (slot : SeLe4n.Slot)
  | replyCap (replyId : SeLe4n.ReplyId)
  /-- WS-SM SM9.A.9: the declassification audit trail.  Fieldless — the trail is
      a singleton `SystemState` component, not an object in the store — so this
      capability carries authority and nothing else. -/
  | auditTrail
  /-- WS-ZA ZA6.4: core `core`'s scheduling control, seL4-MCS's `SchedControl`
      capability: the one authority to configure a scheduling context's budget
      and period (`seL4_SchedControl_ConfigureFlags`).  One per core, created at
      boot and held by the root task; a scheduling-context capability binds,
      unbinds and names the context to configure, and configures nothing. -/
  | schedControl (core : Nat)
  deriving Repr, DecidableEq

/-- WS-RC R4.A: `Inhabited CapTarget` for the `Capability` Inhabited
    derivation needed by the `UniqueSlotMap` `GetElem?` `[s]` total-access
    fallback. The chosen default is `.object SeLe4n.ObjId.sentinel`, matching
    the H-06/WS-E3 sentinel convention. -/
instance : Inhabited CapTarget := ⟨.object SeLe4n.ObjId.sentinel⟩

/-- Architecture-neutral address of a capability slot inside a CNode object.

Lives here rather than in `Model/State.lean` because it is part of the *object*
model — an address into a CNode — and because `IpcMessage` below has to name one:
a transferred capability carries the slot it came from, so the derivation tree
records the real source rather than a synthesised stand-in.  `State.lean` imports
this module, and both are in `namespace SeLe4n.Model`, so `SeLe4n.Model.SlotRef`
is unchanged for every consumer. -/
structure SlotRef where
  cnode : SeLe4n.ObjId
  slot : SeLe4n.Slot
  deriving Repr

/-- Two slot addresses are equal when their CNode and slot words are.  Inlined
and field by field, so comparing two addresses builds neither (a derived
instance compares through an out-of-line function that takes the records). -/
@[inline] instance : DecidableEq SlotRef := fun a b =>
  if h1 : a.cnode = b.cnode then
    if h2 : a.slot = b.slot then isTrue (by cases a; cases b; cases h1; cases h2; rfl)
    else isFalse fun h => h2 (h ▸ rfl)
  else isFalse fun h => h1 (h ▸ rfl)

/-- A slot address rebuilt from its two words is the address.  Code that passes
an address across a call as its CNode and slot words rebuilds it where a theorem
reads it. -/
@[simp] theorem SlotRef.mk_cnode_slot (r : SlotRef) : SlotRef.mk r.cnode r.slot = r := rfl

/-- WS-G1: Hash instance for composite HashMap/HashSet keying.
    Combines cnode and slot hashes via `mixHash` for uniform distribution.
    BEq is already provided by DecidableEq via instBEqOfDecidableEq. -/
@[inline] instance : Hashable SlotRef where
  hash a := mixHash (hash a.cnode) (hash a.slot)

/-- **WS-BP BP7.1 (`v0.36.7`): where a frame capability has mapped its frame** —
the address space (by ASID) and the virtual address.

seL4's frame capability carries exactly this pair (`capFMappedASID`,
`capFMappedAddress`), and it is what makes a mapping *belong to* a capability:
deleting the capability finalises it (`finaliseCap` → `unmapPage`), so no
mapping outlives the authority that made it.  A `VSpaceRoot` records a physical
address, not the capability that installed it, so without this record a
capability deletion cannot find its own mapping — which is how a revoked frame
capability used to leave its page mapped until the untyped was reset. -/
structure FrameMapping where
  asid : SeLe4n.ASID
  vaddr : SeLe4n.VAddr
  /-- **PR #904 review (`v0.36.41`): which mapping of the frame this is.**  The
      frame's `mapEpoch` at the moment this capability mapped it; the address
      space's entry at `vaddr` carries the same number
      (`VSpaceRoot.mappingEpochs`).  A record is the capability's own mapping
      only while the two agree, so a record gone stale — the address space
      unmapped the address, or was destroyed and its ASID reused — cannot claim
      a later mapping of the same frame at the same address.  The number is
      unique for the frame's lifetime, and a frame outlives every record that
      names it (a reset refuses while any capability to it survives). -/
  epoch : Nat := 0
  deriving Repr, DecidableEq

/-- **WS-BP BP7.1 (`v0.36.7`): one page as an address space maps it** — the
ASID, the virtual address and the physical page the translation names.  The
unit a mapping teardown works in: a frame capability's `FrameMapping` together
with the frame's `base`, or a VSpace root's entry together with the root's ASID.
Carrying the physical page is what lets a teardown remove a translation only if
it still names *this* page, so a record gone stale — the address space unmapped
or reused the address — removes nothing that is not its own. -/
structure MappedPage where
  asid : SeLe4n.ASID
  vaddr : SeLe4n.VAddr
  paddr : SeLe4n.PAddr
  /-- **PR #904 review (`v0.36.41`)**: the mapping epoch a capability's record
      names (`FrameMapping.epoch`), or `none` for a page read off an address
      space itself (the pages beneath a page table being finalised,
      `pageTableMappingsBeneath`), which removes whatever maps the page. -/
  epoch : Option Nat := none
  deriving Repr, DecidableEq

/-- WS-F5/D2b: Capability with order-independent rights set.
    `rights` is an `AccessRightSet` (bitmask), replacing the prior `List AccessRight`.

    **WS-BP BP7.1 (`v0.36.7`)**: `mapping` is the frame mapping this capability
    made (`FrameMapping`).  Only `.vspaceMap` writes it, on the invoked frame
    capability's own slot; a **derived** capability — a copy, a mint, an IPC
    transfer — starts with none (`withoutMapping`, seL4's `deriveCap`), a move
    carries it, and destroying the capability unmaps what it records. -/
structure Capability where
  target : CapTarget
  rights : AccessRightSet
  /-- WS-ZA ZA5.3 part 6: the badge's word, meaningful only when `badged`.
      Held as a plain word with a flag, as a blocked sender's TCB holds its
      badge (`ipcBadge` / `ipcBadged`): an `Option` field boxed every badge a
      mint wrote, so a badged mint allocated.  Read through the `badge` view. -/
  badgeWord : SeLe4n.Badge := SeLe4n.Badge.zero
  /-- Whether the capability carries a badge (`badgeWord` holds it). -/
  badged : Bool := false
  /-- WS-ZA ZA5.4: the recorded mapping's ASID, meaningful only when `mapped`.
      The record is held as words with a flag, as seL4's frame capability holds
      its mapped ASID and address: an `Option FrameMapping` field built the
      record and its `some` on every map.  Read through the `mapping` view. -/
  mapAsid : SeLe4n.ASID := default
  /-- The recorded mapping's virtual address. -/
  mapVaddr : SeLe4n.VAddr := default
  /-- The recorded mapping's epoch (`FrameMapping.epoch`). -/
  mapEpoch : Nat := 0
  /-- Whether the capability records a mapping (`mapAsid`, `mapVaddr` and
      `mapEpoch` hold it). -/
  mapped : Bool := false
  /-- WS-ZA ZA5.4 part 13: **the free index** of the untyped this capability
      names — the byte offset in its region where the next carve through this
      capability starts — meaningful only for an untyped target, as seL4's
      `capFreeIndex`.  The carve reads it and advances it in this capability's
      own slot (`retypeFromUntyped`); a copy, mint or transfer of an untyped
      capability hands the source's index to the new capability and sets the
      source's to full (`untypedSourceSetFull`, seL4's `setUntypedCapAsFull`),
      so only the newest one carves.  A plain word, never an `Option`. -/
  freeIndex : Nat := 0
  deriving Repr, DecidableEq, Inhabited

namespace Capability

/-- WS-ZA ZA5.4: **the capability's mapping record**, the `Option` view of the
`mapped` flag and its words. -/
@[inline] def mapping (cap : Capability) : Option FrameMapping :=
  if cap.mapped then some ⟨cap.mapAsid, cap.mapVaddr, cap.mapEpoch⟩ else none

/-- The capability with its mapping record replaced: the words and flag of `m`,
zero words for `none`. -/
@[inline] def withMapping (cap : Capability) (m : Option FrameMapping) : Capability :=
  match m with
  | some m => { cap with mapAsid := m.asid, mapVaddr := m.vaddr, mapEpoch := m.epoch, mapped := true }
  | none => { cap with mapAsid := default, mapVaddr := default, mapEpoch := 0, mapped := false }

/-- The capability with mapping record `(asid, vaddr, epoch)`, written over its
own record. -/
@[inline] def setMapped (c : Capability) (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (epoch : Nat) : Capability :=
  { c with mapAsid := asid, mapVaddr := vaddr, mapEpoch := epoch, mapped := true }

theorem setMapped_eq (c : Capability) (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (epoch : Nat) : c.setMapped asid vaddr epoch = c.withMapping (some ⟨asid, vaddr, epoch⟩) := rfl

@[simp] theorem withMapping_mapping (cap : Capability) (m : Option FrameMapping) :
    (cap.withMapping m).mapping = m := by
  cases m <;> rfl

@[simp] theorem withMapping_target (cap : Capability) (m : Option FrameMapping) :
    (cap.withMapping m).target = cap.target := by cases m <;> rfl

@[simp] theorem withMapping_rights (cap : Capability) (m : Option FrameMapping) :
    (cap.withMapping m).rights = cap.rights := by cases m <;> rfl

@[simp] theorem withMapping_badgeWord (cap : Capability) (m : Option FrameMapping) :
    (cap.withMapping m).badgeWord = cap.badgeWord := by cases m <;> rfl

@[simp] theorem withMapping_badged (cap : Capability) (m : Option FrameMapping) :
    (cap.withMapping m).badged = cap.badged := by cases m <;> rfl

@[simp] theorem withMapping_freeIndex (cap : Capability) (m : Option FrameMapping) :
    (cap.withMapping m).freeIndex = cap.freeIndex := by cases m <;> rfl

/-- WS-ZA ZA5.4 part 13: **the capability with free index `idx`**, every other
field kept — seL4's `cap_untyped_cap_set_capFreeIndex`. -/
@[inline] def withFreeIndex (cap : Capability) (idx : Nat) : Capability :=
  { cap with freeIndex := idx }

@[simp] theorem withFreeIndex_freeIndex (cap : Capability) (idx : Nat) :
    (cap.withFreeIndex idx).freeIndex = idx := rfl

@[simp] theorem withFreeIndex_target (cap : Capability) (idx : Nat) :
    (cap.withFreeIndex idx).target = cap.target := rfl

@[simp] theorem withFreeIndex_rights (cap : Capability) (idx : Nat) :
    (cap.withFreeIndex idx).rights = cap.rights := rfl

@[simp] theorem withFreeIndex_badgeWord (cap : Capability) (idx : Nat) :
    (cap.withFreeIndex idx).badgeWord = cap.badgeWord := rfl

@[simp] theorem withFreeIndex_badged (cap : Capability) (idx : Nat) :
    (cap.withFreeIndex idx).badged = cap.badged := rfl

@[simp] theorem withFreeIndex_mapped (cap : Capability) (idx : Nat) :
    (cap.withFreeIndex idx).mapped = cap.mapped := rfl


/-- WS-ZA ZA5.3 part 6: **the capability's badge**, the `Option` view of the
`badged` flag and `badgeWord`. -/
@[inline] def badge (cap : Capability) : Option SeLe4n.Badge :=
  if cap.badged then some cap.badgeWord else none

/-- The capability with its badge replaced: the word and flag of `b`. -/
@[inline] def withBadge (cap : Capability) (b : Option SeLe4n.Badge) : Capability :=
  { cap with badgeWord := SeLe4n.Badge.ofOption b, badged := b.isSome }

@[simp] theorem withBadge_badge (cap : Capability) (b : Option SeLe4n.Badge) :
    (cap.withBadge b).badge = b := by
  cases b <;> rfl

@[simp] theorem withBadge_target (cap : Capability) (b : Option SeLe4n.Badge) :
    (cap.withBadge b).target = cap.target := rfl

@[simp] theorem withBadge_rights (cap : Capability) (b : Option SeLe4n.Badge) :
    (cap.withBadge b).rights = cap.rights := rfl

@[simp] theorem withBadge_mapping (cap : Capability) (b : Option SeLe4n.Badge) :
    (cap.withBadge b).mapping = cap.mapping := rfl

@[simp] theorem withBadge_freeIndex (cap : Capability) (b : Option SeLe4n.Badge) :
    (cap.withBadge b).freeIndex = cap.freeIndex := rfl

@[simp] theorem withFreeIndex_mapping (cap : Capability) (idx : Nat) :
    (cap.withFreeIndex idx).mapping = cap.mapping := rfl

@[simp] theorem withFreeIndex_badge (cap : Capability) (idx : Nat) :
    (cap.withFreeIndex idx).badge = cap.badge := rfl

/-- The capability of the given target, rights, badge words and mapping record. -/
@[inline] def ofWords (target : CapTarget) (rights : AccessRightSet) (badgeWord : SeLe4n.Badge)
    (badged : Bool) (m : Option FrameMapping) : Capability :=
  match m with
  | some m => { target, rights, badgeWord, badged, mapAsid := m.asid, mapVaddr := m.vaddr,
                mapEpoch := m.epoch, mapped := true }
  | none => { target, rights, badgeWord, badged }

@[simp] theorem ofWords_target (t : CapTarget) (r : AccessRightSet) (w : SeLe4n.Badge) (b : Bool)
    (m : Option FrameMapping) : (ofWords t r w b m).target = t := by cases m <;> rfl

@[simp] theorem ofWords_rights (t : CapTarget) (r : AccessRightSet) (w : SeLe4n.Badge) (b : Bool)
    (m : Option FrameMapping) : (ofWords t r w b m).rights = r := by cases m <;> rfl

@[simp] theorem ofWords_badgeWord (t : CapTarget) (r : AccessRightSet) (w : SeLe4n.Badge) (b : Bool)
    (m : Option FrameMapping) : (ofWords t r w b m).badgeWord = w := by cases m <;> rfl

@[simp] theorem ofWords_badged (t : CapTarget) (r : AccessRightSet) (w : SeLe4n.Badge) (b : Bool)
    (m : Option FrameMapping) : (ofWords t r w b m).badged = b := by cases m <;> rfl

@[simp] theorem ofWords_mapping (t : CapTarget) (r : AccessRightSet) (w : SeLe4n.Badge) (b : Bool)
    (m : Option FrameMapping) : (ofWords t r w b m).mapping = m := by cases m <;> rfl

@[simp] theorem ofWords_freeIndex (t : CapTarget) (r : AccessRightSet) (w : SeLe4n.Badge) (b : Bool)
    (m : Option FrameMapping) : (ofWords t r w b m).freeIndex = 0 := by cases m <;> rfl

/-- The capability of the given target, rights, badge and mapping. -/
@[inline] def ofParts (target : CapTarget) (rights : AccessRightSet)
    (badge : Option SeLe4n.Badge) (mapping : Option FrameMapping := none) : Capability :=
  ofWords target rights (SeLe4n.Badge.ofOption badge) badge.isSome mapping

@[simp] theorem ofParts_target (t : CapTarget) (r : AccessRightSet) (b : Option SeLe4n.Badge)
    (m : Option FrameMapping) : (ofParts t r b m).target = t := by simp [ofParts]

@[simp] theorem ofParts_rights (t : CapTarget) (r : AccessRightSet) (b : Option SeLe4n.Badge)
    (m : Option FrameMapping) : (ofParts t r b m).rights = r := by simp [ofParts]

@[simp] theorem ofParts_badge (t : CapTarget) (r : AccessRightSet) (b : Option SeLe4n.Badge)
    (m : Option FrameMapping) : (ofParts t r b m).badge = b := by
  cases b <;> cases m <;> rfl

@[simp] theorem ofParts_mapping (t : CapTarget) (r : AccessRightSet) (b : Option SeLe4n.Badge)
    (m : Option FrameMapping) : (ofParts t r b m).mapping = m := by simp [ofParts]

@[simp] theorem ofParts_freeIndex (t : CapTarget) (r : AccessRightSet) (b : Option SeLe4n.Badge)
    (m : Option FrameMapping) : (ofParts t r b m).freeIndex = 0 := by simp [ofParts]

/-- Two capabilities are equal exactly when their parts are. -/
theorem ofParts_inj {t t' : CapTarget} {r r' : AccessRightSet} {b b' : Option SeLe4n.Badge}
    {m m' : Option FrameMapping} :
    ofParts t r b m = ofParts t' r' b' m' ↔ t = t' ∧ r = r' ∧ b = b' ∧ m = m' := by
  constructor
  · intro h
    have h1 := congrArg target h; have h2 := congrArg rights h
    have h3 := congrArg badge h; have h4 := congrArg mapping h
    simp only [ofParts_target, ofParts_rights, ofParts_badge, ofParts_mapping] at h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩; rfl

/-- A capability of no badge has the `none` badge. -/
@[simp] theorem badge_of_unbadged (cap : Capability) (h : cap.badged = false) :
    cap.badge = none := by
  simp [badge, h]

/-- WS-F5/D2b: Check if a capability has a specific right. O(1) bit test. -/
def hasRight (cap : Capability) (right : AccessRight) : Bool :=
  cap.rights.mem right

/-- **WS-BP BP7.1 (`v0.36.7`): the capability a derivation produces** — this one
with its mapping record cleared, seL4's `deriveCap` for a frame capability.  A
copy or a transfer is a *new* authority over the frame, not the authority that
made the mapping: were the record carried, two capabilities would each claim one
mapping and destroying either would unmap the other's. -/
@[inline] def withoutMapping (cap : Capability) : Capability :=
  cap.withMapping none

/-- `withoutMapping` as compiled: a capability that records no mapping is
returned as it is, so deriving it builds no record (WS-ZA ZA5.3 part 6). -/
@[inline] def withoutMappingImpl (cap : Capability) : Capability :=
  if cap.mapAsid = default && cap.mapVaddr = default && cap.mapEpoch == 0 && !cap.mapped then cap
  else cap.withMapping none

@[csimp] theorem withoutMapping_eq_impl : @withoutMapping = @withoutMappingImpl := by
  funext cap
  unfold withoutMappingImpl withoutMapping withMapping
  by_cases h : (decide (cap.mapAsid = default) && decide (cap.mapVaddr = default) &&
      cap.mapEpoch == 0 && !cap.mapped) = true
  · rw [if_pos h]
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.not_eq_true'] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    cases cap; simp_all
  · rw [if_neg h]

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
  { target := .object ObjId.sentinel, rights := AccessRightSet.empty }

/-- AK7-I: The canonical null capability satisfies `isNull`. -/
theorem null_isNull : (Capability.null).isNull = true := by
  simp [null, isNull, AccessRightSet.empty, ObjId.isReserved, ObjId.sentinel]

/-- WS-SM SM9.A.9: **the read-only audit capability** a monitoring deployment
mints for a subject that should be able to read the declassification audit trail
but not to drain it.

Named rather than left to each mint site to assemble, because the distinction
between this and `auditTrailManage` is the whole reason the two audit syscalls
require different rights: a deployment that hands out only this one has a reader
that provably cannot remove evidence. -/
def auditTrailRead : Capability :=
  { target := .auditTrail, rights := AccessRightSet.ofList [.read] }

/-- WS-SM SM9.A.9: **the read-and-drain audit capability**, for the deployment's
audit monitor.  Draining additionally requires the configured
`LabelingContext.auditMonitorClearance`, so this right is necessary and not
sufficient. -/
def auditTrailManage : Capability :=
  { target := .auditTrail, rights := AccessRightSet.ofList [.read, .write] }

/-- WS-SM SM9.A.9 (**the separation, as a theorem**): a read-only audit
capability grants the reader's right and **not** the drain's.

The property a monitoring deployment relies on when it hands one out. -/
theorem auditTrailRead_cannot_drain :
    Capability.auditTrailRead.hasRight .read = true ∧
    Capability.auditTrailRead.hasRight .write = false := by
  constructor <;> rfl

/-- WS-SM SM9.A.9: the monitor's capability grants both. -/
theorem auditTrailManage_can_drain :
    Capability.auditTrailManage.hasRight .read = true ∧
    Capability.auditTrailManage.hasRight .write = true := by
  constructor <;> rfl

/-- WS-SM SM9.A.9: both audit capabilities are non-null, so they survive the
AK7-I null-capability gate at every entry point that runs it. -/
theorem auditTrail_capabilities_not_null :
    Capability.auditTrailRead.isNull = false ∧
    Capability.auditTrailManage.isNull = false := by
  constructor <;> rfl

/-- WS-ZA ZA6.4: **core `core`'s scheduling-control capability**, as the boot
hands it to the root task: the `.write` right a configure requires
(`syscallRequiredRight .schedContextConfigure`) and nothing else. -/
def schedControlOf (core : Nat) : Capability :=
  { target := .schedControl core, rights := AccessRightSet.ofList [.write] }

/-- WS-ZA ZA6.4: a scheduling-control capability is non-null, so it survives the
null-capability gate at every entry point that runs it. -/
theorem schedControlOf_not_null (core : Nat) : (Capability.schedControlOf core).isNull = false := by
  rfl

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
-- WS-AL AL1b (cascades AK7-I): `NonNullCap` subtype for type-level null-cap
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

/-- A capability in transit, **with the slot it was resolved from**.

The source travels with the capability because the receiving end is where the
derivation edge is recorded: the receiving copy is a child of the source slot
in the derivation tree, so revoking the source reaches the copy.

Carrying the pair in one array rather than two parallel ones is deliberate.  A
`caps` array beside a `capSrcSlots` array would have to be kept the same length
and the same order by every producer, and nothing in the type would say so —
exactly the implicit invariant this codebase requires to be structural.  A
transfer capability cannot be half-built. -/
structure TransferCap where
  /-- The capability being transferred. -/
  cap : Capability
  /-- The **slot it was resolved from** — the derivation-tree parent the
      receiving copy is recorded against (seL4's `transferCaps` passes the
      source `cte_t` the same way).

      A slot address is exact here because the resolution and the install run
      in one step: since WS-ZA ZA4.7 a blocked sender keeps capability
      addresses, not resolved capabilities (`IpcMessage` has no capability
      field), so no
      thread can delete the source slot and install something else there
      between the two.  Since WS-ZA ZA5.3 part 2 the slot is the tree's node,
      as seL4's `cte_t` is its own mapping-database node. -/
  srcSlot : SlotRef
  deriving Repr, DecidableEq

/-- A transfer capability with its source slot spelled out.

For fixtures, which build messages by hand rather than through
`resolveExtraCaps`.  There is deliberately **no** default: a stand-in derivation
parent is exactly the defect this structure exists to prevent, so a caller with
no real slot to name has to say so explicitly. -/
def TransferCap.fromSlot (cap : Capability) (src : SlotRef) : TransferCap :=
  { cap := cap, srcSlot := src }

/-- WS-E4/M-02: Structured IPC message payload for endpoint transfers.

Models seL4 message registers plus the sender badge and grant right.
WS-H12d/A-09: Registers are a bounded `Array` matching seL4's
`seL4_MsgMaxLength` (120); the bound is enforced at IPC send boundaries.

**A message holds no capabilities.**  As in seL4, the extra capabilities a
sender names are looked up in its CSpace at the rendezvous (`lookupExtraCaps`,
here `resolveExtraCaps`) and installed in the same step from a transient array
(`ipcUnwrapCaps`), so no resolved capability can be parked in a thread's
`pendingMessage`: the type has nowhere to put one. -/
structure IpcMessage where
  /-- S4-D: Changed from `Array Nat` to `Array RegValue` for type consistency
      with the machine register model. All register values in IPC messages
      are now typed, matching the `RegValue` wrapper used throughout the
      register decode and context-switch infrastructure. -/
  registers : Array SeLe4n.RegValue
  badge : Option SeLe4n.Badge := none
  /-- **The `seL4_MessageInfo_t` label this message is delivered under.**

      It exists because a fault message is a `seL4_Fault_tag` plus words: a VM
      fault and a user exception differ only in their label, so a handler
      reading a label-`0` frame could tell neither apart — nor either from a
      successful receive, `0` being the WS-RA success label too.  The model
      discards a message's label at decode time and `returnMessageInfo`
      synthesized `0` at delivery, so before RR4 there was no channel from a
      transition that *knows* the label to the receiver that needs it.  This
      field is that channel: `Architecture.encodeFault` sets it to
      `Architecture.faultLabel`, and `returnMessageInfo` carries it into the
      handler's return frame.

      **Set by kernel-originated messages only, and that is a security
      property, not an omission.**  The user syscall arms leave it at the
      default, so a thread holding a send capability to a fault-handler
      endpoint cannot mint a message bearing a `seL4_Fault_tag` — a forgery
      channel seL4 closes only by convention ("do not hand out send caps to a
      fault endpoint").  Restoring seL4's sender-side label pass-through
      therefore needs its own authority story (a badge or endpoint distinction
      that separates kernel-originated fault deliveries from user sends) and is
      registered as WS-RR debt rather than folded in here — wiring it silently
      would open the channel this default keeps shut.

      Bounded by `MessageInfo.maxLabel` on every path that sets it: the fault
      encoder emits `seL4_Fault_tag` constants
      (`Architecture.encodeFault_messageInfo_wellFormed`).
      `returnMessageInfo` additionally clamps, so even an out-of-range label
      cannot produce a malformed return word. -/
  label : Nat := 0
  deriving Repr, DecidableEq

namespace IpcMessage

def empty : IpcMessage := { registers := (#[] : Array SeLe4n.RegValue) }

/-- WS-H12d/A-09: Predicate asserting that a message's payload respects
seL4 message-register bound. -/
def bounded (msg : IpcMessage) : Prop :=
  msg.registers.size ≤ maxMessageRegisters

/-- WS-H12d/A-09: Decidable bounds check for runtime enforcement at IPC
send boundaries. Returns `true` iff the message satisfies payload bounds. -/
def checkBounds (msg : IpcMessage) : Bool :=
  msg.registers.size ≤ maxMessageRegisters

theorem empty_bounded : IpcMessage.empty.bounded := by
  unfold bounded empty maxMessageRegisters
  simp [Array.size]

theorem checkBounds_iff_bounded (msg : IpcMessage) :
    msg.checkBounds = true ↔ msg.bounded := by
  unfold checkBounds bounded maxMessageRegisters
  simp

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
  /-- The source slot was destroyed between resolution and unwrap — deleted,
  retyped away, or swept by a revoke — so installing would attach the copy
  beneath a derivation node no slot points at, where no revoke could reach it.
  The transfer is cancelled instead; the receiver simply gets one fewer
  capability, exactly as with `.grantDenied`. -/
  | sourceRevoked
  deriving Repr, DecidableEq

/-- M-D01: Aggregated results of unwrapping all extra capabilities in an
IPC message. One entry per cap in the array resolved at the rendezvous. -/
structure CapTransferSummary where
  results : Array CapTransferResult := #[]
  deriving Repr, DecidableEq

namespace CapTransferSummary

/-- The number of capabilities **actually installed** in the receiver's
CSpace — the `.installed` entries only.  `.noSlot` and `.grantDenied`
entries record caps the transfer did *not* deliver, so they must not be
counted toward anything the receiver is told arrived (PR #866 round-2
review: the return frame's `extraCaps` reads this, never the requested
count). -/
def installedCount (s : CapTransferSummary) : Nat :=
  s.results.foldl
    (fun n r => match r with
      | .installed _ _ => n + 1
      | _ => n) 0

@[simp] theorem installedCount_empty :
    installedCount { results := #[] } = 0 := rfl

end CapTransferSummary

/-- WS-Z Z6-H: Result of a timeout-aware IPC operation.
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

namespace ThreadIpcState

/-! WS-ZA ZA4.7: a thread's IPC state as two scalar codes, the form the TCB
stores it in (`TCB.ipcObjectCode`, `TCB.ipcStateCode`): a constructor with a
payload is a heap cell, so a store of `.blockedOnReceive ep` or
`.blockedOnReply ep (some r)` allocated on every IPC that blocks.  The pair
`(objectCode, stateCode)` is a bijection with `ThreadIpcState` (`ofCodes_codes`,
`objectCode_ofCodes`, `stateCode_ofCodes`): state `0` is `ready` at object `0`
and `blockedOnSend o` at object `o + 1`; states `1`–`3` are receive,
notification and call on the object; state `c + 4` is `blockedOnReply` on the
object with the reply target whose `ThreadId.optCode` is `c`. -/

/-- The object word of the state's code. -/
@[inline] def objectCode : ThreadIpcState → Nat
  | .ready => 0
  | .blockedOnSend e => e.val + 1
  | .blockedOnReceive e => e.val
  | .blockedOnNotification n => n.val
  | .blockedOnReply e _ => e.val
  | .blockedOnCall e => e.val

/-- The state word of the state's code. -/
@[inline] def stateCode : ThreadIpcState → Nat
  | .ready => 0
  | .blockedOnSend _ => 0
  | .blockedOnReceive _ => 1
  | .blockedOnNotification _ => 2
  | .blockedOnReply _ t => SeLe4n.ThreadId.optCode t + 4
  | .blockedOnCall _ => 3

/-- The state a pair of codes stands for. -/
@[inline] def ofCodes (obj state : Nat) : ThreadIpcState :=
  match state with
  | 0 => match obj with
    | 0 => .ready
    | o + 1 => .blockedOnSend ⟨o⟩
  | 1 => .blockedOnReceive ⟨obj⟩
  | 2 => .blockedOnNotification ⟨obj⟩
  | 3 => .blockedOnCall ⟨obj⟩
  | c + 4 => .blockedOnReply ⟨obj⟩ (SeLe4n.ThreadId.ofOptCode c)

@[simp] theorem ofCodes_codes (s : ThreadIpcState) :
    ofCodes s.objectCode s.stateCode = s := by
  cases s <;> simp [ofCodes, objectCode, stateCode]

@[simp] theorem ofCodes_zero_zero : ofCodes 0 0 = .ready := rfl

@[simp] theorem objectCode_ofCodes (obj state : Nat) :
    (ofCodes obj state).objectCode = obj := by
  unfold ofCodes
  split
  · split <;> rfl
  all_goals rfl

@[simp] theorem stateCode_ofCodes (obj state : Nat) :
    (ofCodes obj state).stateCode = state := by
  unfold ofCodes
  split
  · split <;> rfl
  all_goals simp [stateCode]

/-- A pair of codes stands for `s` exactly when it is `s`'s pair. -/
theorem ofCodes_eq_iff (obj state : Nat) (s : ThreadIpcState) :
    ofCodes obj state = s ↔ obj = s.objectCode ∧ state = s.stateCode := by
  constructor
  · rintro rfl; exact ⟨(objectCode_ofCodes _ _).symm, (stateCode_ofCodes _ _).symm⟩
  · rintro ⟨rfl, rfl⟩; exact ofCodes_codes s

/-- Deciding which state a pair of codes stands for compares the two words, so
a test of a thread's state (`decide (tcb.ipcState = .ready)`) builds no
constructor cell.  Inlined, so the state it is compared with is never built
either: its codes are read off the constructor where the test is written. -/
@[inline] instance (priority := high) decEqOfCodes (obj state : Nat) (s : ThreadIpcState) :
    Decidable (ofCodes obj state = s) :=
  decidable_of_iff (obj = s.objectCode ∧ state = s.stateCode) (ofCodes_eq_iff obj state s).symm

end ThreadIpcState

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

namespace QueuePPrev

/-- An optional back-pointer as one scalar: `0` for `none`, `1` for the queue
head, `t + 2` for `tcbNext t`.  A bijection with `Option QueuePPrev`, for the
reason `SeLe4n.ThreadId.optCode` gives: the `Option` and the `tcbNext` payload
are each a heap cell, the code is a scalar. -/
@[inline] def optCode : Option QueuePPrev → Nat
  | none => 0
  | some .endpointHead => 1
  | some (.tcbNext t) => t.val + 2

/-- The optional back-pointer a code stands for; inverse of `optCode`. -/
@[inline] def ofOptCode : Nat → Option QueuePPrev
  | 0 => none
  | 1 => some .endpointHead
  | k + 2 => some (.tcbNext ⟨k⟩)

@[simp] theorem ofOptCode_optCode (o : Option QueuePPrev) : ofOptCode (optCode o) = o := by
  rcases o with _ | _ | _ <;> rfl

@[simp] theorem optCode_ofOptCode (n : Nat) : optCode (ofOptCode n) = n := by
  rcases n with _ | _ | _ <;> rfl

@[simp] theorem ofOptCode_zero : ofOptCode 0 = none := rfl

@[simp] theorem optCode_none : optCode none = 0 := rfl

@[simp] theorem ofOptCode_eq_none_iff (n : Nat) : ofOptCode n = none ↔ n = 0 := by
  rcases n with _ | _ | _ <;> simp [ofOptCode]

end QueuePPrev

/-- WS-ZA ZA5.3 part 4: the words of derivation links one slot holds (parent,
first child, next sibling, previous sibling; a CNode word and a slot word each). -/
def slotLinkWords : Nat := 8

/-- WS-ZA ZA5.3 part 6: the capability with the given fields, written over the
record `r` (a slot's spare): out of line, so `r` is the only record the
compiler can write it into, and its rights read back through `r` so that `r`
stays live, since an update of every field would drop `r` and build a fresh
record.  Equal to the capability of those fields (`overwrite_eq`). -/
@[noinline] def Capability.overwrite (r : Capability) (target : CapTarget) (rights : AccessRightSet)
    (badgeWord : SeLe4n.Badge) (badged : Bool) (mapAsid : SeLe4n.ASID) (mapVaddr : SeLe4n.VAddr)
    (mapEpoch : Nat) (mapped : Bool) (freeIndex : Nat) : Capability :=
  { target, rights := if r.rights = rights then r.rights else rights, badgeWord, badged,
    mapAsid, mapVaddr, mapEpoch, mapped, freeIndex }

/-- WS-ZA ZA5.4: the target naming object `id`, built fresh, out of line. -/
@[noinline] def CapTarget.ofObject (id : SeLe4n.ObjId) : CapTarget := .object id

/-- WS-ZA ZA5.4: the target naming object `id`, written over `t` when `t` already
names an object or a reply (a constructor of one field, the same cell size, so
the compiler reuses `t`'s cell for the new one: a slot whose last capability was
a reply capability is carved into in place).  Out of line, with a distinct
fallback arm, so the first two keep their reuse of `t`'s cell. -/
@[noinline] def CapTarget.objectOver (t : CapTarget) (id : SeLe4n.ObjId) : CapTarget :=
  match t with
  | .object _ => .object id
  | .replyCap _ => .object id
  | _ => CapTarget.ofObject id

/-- WS-ZA ZA5.4: `rights`, kept as the record's own `rr` when equal.  Out of line,
so the capability built from it has no join point before it. -/
@[noinline] def AccessRightSet.keepOr (rr rights : AccessRightSet) : AccessRightSet :=
  if rr = rights then rr else rights

/-- WS-ZA ZA5.4: the capability naming object `id` with `rights` and nothing
else, written over the record `r` (a slot's spare), its target cell written over
too when it already names an object (`CapTarget.objectOver`): the record is
matched apart and rebuilt with no join point between, so it is written in place,
and its target, then owned alone, is too.  Equal to that capability
(`overwriteObject_eq`). -/
@[noinline] def Capability.overwriteObject (r : Capability) (id : SeLe4n.ObjId)
    (rights : AccessRightSet) : Capability :=
  match r with
  | ⟨t, rr, _, _, _, _, _, _, _⟩ =>
    ⟨t.objectOver id, rr.keepOr rights, SeLe4n.Badge.zero, false, default, default, 0, false, 0⟩

/-- WS-ZA ZA5.4: the capability naming object `id` with `rights` alone, built
fresh out of line, so its target is built only on the path that builds it. -/
@[noinline] def Capability.ofObject (id : SeLe4n.ObjId) (rights : AccessRightSet) : Capability :=
  ⟨.object id, rights, SeLe4n.Badge.zero, false, default, default, 0, false, 0⟩

theorem CapTarget.objectOver_eq (t : CapTarget) (id : SeLe4n.ObjId) :
    t.objectOver id = .object id := by
  cases t <;> rfl

theorem AccessRightSet.keepOr_eq (rr rights : AccessRightSet) : rr.keepOr rights = rights := by
  unfold keepOr; split <;> simp_all

theorem Capability.overwriteObject_eq (r : Capability) (id : SeLe4n.ObjId)
    (rights : AccessRightSet) :
    r.overwriteObject id rights =
      ⟨.object id, rights, SeLe4n.Badge.zero, false, default, default, 0, false, 0⟩ := by
  obtain ⟨t, rr, _, _, _, _, _, _, _⟩ := r
  unfold overwriteObject
  dsimp only
  rw [CapTarget.objectOver_eq, AccessRightSet.keepOr_eq]

/-- WS-ZA ZA5.3 part 6: the capability with the given fields, built fresh (a
slot with no record of its own).  Out of line, so a caller's literal of the same
fields is not shared with it and stays unbuilt. -/
@[noinline] def Capability.ofFields (target : CapTarget) (rights : AccessRightSet)
    (badgeWord : SeLe4n.Badge) (badged : Bool) (mapAsid : SeLe4n.ASID) (mapVaddr : SeLe4n.VAddr)
    (mapEpoch : Nat) (mapped : Bool) (freeIndex : Nat) : Capability :=
  ⟨target, rights, badgeWord, badged, mapAsid, mapVaddr, mapEpoch, mapped, freeIndex⟩

theorem Capability.overwrite_eq (r : Capability) (target : CapTarget) (rights : AccessRightSet)
    (badgeWord : SeLe4n.Badge) (badged : Bool) (mapAsid : SeLe4n.ASID) (mapVaddr : SeLe4n.VAddr)
    (mapEpoch : Nat) (mapped : Bool) (freeIndex : Nat) :
    r.overwrite target rights badgeWord badged mapAsid mapVaddr mapEpoch mapped freeIndex =
      ⟨target, rights, badgeWord, badged, mapAsid, mapVaddr, mapEpoch, mapped, freeIndex⟩ := by
  unfold overwrite; split <;> simp_all

/-- WS-ZA ZA5.3 part 6: **the records a CNode's slots keep while empty** (seL4's
`cte_t`, which a slot owns for the CNode's life).  Entry `i` is the capability
cell slot `i` last held, kept when the slot is cleared so the next capability
written there overwrites it in place instead of allocating one.  Logically a
single value (`Squash`), so no theorem reads it and a CNode with any spares is
the CNode with any other: only the compiled kernel sees the records. -/
abbrev SpareCells := Squash (Array (Option Capability))

instance : Repr SpareCells := ⟨fun _ _ => "spare cells"⟩

namespace SpareCells

/-- `sp` with slot `i` keeping the cell `o` (a cleared slot's record); a `none`
leaves the slot's spare as it was. -/
@[inline] def keep (sp : SpareCells) (i : Nat) (o : Option Capability) : SpareCells :=
  Quot.lift (fun a => Squash.mk (match o with
      | some _ => a.setIfInBounds i o
      | none => a))
    (fun _ _ _ => Quot.sound trivial) sp

/-- `sp` with each slot `i` whose cell in `cells` holds a capability `f i`
rejects keeping that capability as its record (a bulk clear's `keep`). -/
def keepFiltered (sp : SpareCells) (cells : Array (Option Capability))
    (f : Nat → Capability → Bool) : SpareCells :=
  Quot.lift (fun a => Squash.mk (a.mapIdx fun i o =>
      match cells[i]? with
      | some (some c) => if f i c then o else some c
      | _ => o))
    (fun _ _ _ => Quot.sound trivial) sp

end SpareCells

structure TCB where
  tid : SeLe4n.ThreadId
  priority : SeLe4n.Priority
  domain : SeLe4n.DomainId
  /-- The thread's two capability slots, seL4's `tcbCTable` and `tcbVTable`:
      slot 0 holds the capability to its CSpace root, slot 1 the capability to
      its VSpace root (`TCB.cspaceRootSlot`, `TCB.vspaceRootSlot`), read through
      `TCB.cspaceRoot` and `TCB.vspaceRoot`.  The same cell type as a CNode's
      slot array (`CNode.cells`); an empty slot reads as the sentinel root.  A
      fixed-size vector, so a write replaces one entry in place. -/
  spaceCells : Vector (Option Capability) 2 := #v[none, none]
  /-- The derivation links of the two slots, `slotLinkWords` words per slot in
      the layout of a CNode's `links` (parent, first child, next and previous
      sibling, each an object word and a slot word, a word of 0 meaning no
      link). -/
  spaceLinks : Vector Nat (slotLinkWords * 2) := Vector.replicate _ 0
  ipcBuffer : SeLe4n.VAddr
  /-- WS-ZA ZA4.7: the object word of the thread's IPC state, read with
      `ipcStateCode` through `TCB.ipcState` and written with it through
      `TCB.setIpcState` (`ThreadIpcState.objectCode`).  Two words rather than
      a `ThreadIpcState` field, so a block or a rendezvous writes scalars
      instead of a fresh constructor cell. -/
  ipcObjectCode : Nat := 0
  /-- V8-G1: Explicit lifecycle state. Default `.Inactive` for freshly created
      threads; set to `.Ready` when enqueued, `.Running` when dispatched. -/
  threadState : ThreadState := .Inactive
  /-- M-04/WS-E6: Remaining time-slice ticks before preemption. Reset to the
      scheduler's own `configDefaultTimeSlice` on expiry, by the live and the
      frozen tick alike. Default value matches seL4's CONFIG_TIMER_TICK_MS-based
      quantum. -/
  timeSlice : Nat := 5
  /-- M-03/WS-E6: Scheduling deadline for EDF tie-breaking within same
      priority level. 0 = no deadline (lowest urgency). Lower nonzero
      values are more urgent. -/
  deadline : SeLe4n.Deadline := ⟨0⟩
  /-- WS-E4/M-01 intrusive queue linkage, stored as a scalar code
      (`SeLe4n.ThreadId.optCode`) and read through `TCB.queuePrev`.  A code of
      `0` (`none`) means detached from every intrusive wait queue. -/
  queuePrevCode : Nat := 0
  /-- Pointer-to-previous-link metadata (`v0.12.1`, O(1) arbitrary removal),
      stored as a scalar code (`QueuePPrev.optCode`) and read through
      `TCB.queuePPrev`.  `endpointHead` means this node is referenced by its
      queue's head; `tcbNext prevTid` means it is referenced by
      `prevTid.queueNext`.  Cleared when detached. -/
  queuePPrevCode : Nat := 0
  /-- The successor link, stored as a scalar code and read through
      `TCB.queueNext`. -/
  queueNextCode : Nat := 0
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
      `none` = no fault handler configured (faults are silently dropped).
      WS-ZA ZA5.2: stored as a flag and the address's word, read through the
      view `TCB.faultHandler`, so setting a handler writes no `some` cell and
      boxes no word. -/
  faultHandlerSet : Bool := false
  /-- WS-ZA ZA5.2: the fault handler's capability address, meaningful when
      `faultHandlerSet` holds (see `TCB.faultHandler`). -/
  faultHandlerWord : SeLe4n.CPtr := SeLe4n.CPtr.ofNat 0
  /-- R7-D/L-06: Object ID of the bound notification object.
      In seL4, a thread may bind one notification object. Signals on the bound
      notification can wake the thread when it is waiting on an endpoint.
      `none` = no bound notification.  WS-ZA ZA5.2: stored as its scalar code
      (`SeLe4n.ObjId.optCode`) and read through the view `TCB.boundNotification`,
      so a bind writes no `some` cell. -/
  boundNotificationCode : Nat := 0
  /-- WS-Z Z1-J: Scheduling context binding. Determines whether this thread
      uses legacy TCB scheduling fields or a first-class SchedContext object.
      Default `.unbound` preserves backward compatibility.  WS-ZA ZA5.2: stored
      as its two scalar codes (`SchedContextBinding.scCode`, `.ownerCode`) and
      read through the view `TCB.schedContextBinding`, so a bind or a donation
      writes no constructor cell. -/
  scBindingScCode : Nat := 0
  /-- The owner word of the binding's code (`SchedContextBinding.ownerCode`). -/
  scBindingOwnerCode : Nat := 0
  /-- WS-Z Z6-A: Timeout budget reference for IPC blocking operations.
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
      Default `none` = no PIP boost (existing effective priority behavior).
      WS-ZA ZA4.7: stored as a code (`SeLe4n.Priority.optCode`) and read
      through the `TCB.pipBoost` view, so a boost write builds no cell. -/
  pipBoostCode : Nat := 0
  /-- AG8-A (H3-IPC-01/I-01): Explicit timeout flag replacing the fragile
      sentinel pattern (`gpr x0 = 0xFFFFFFFF ∧ ipcState = .ready`).
      Set to `true` by `timeoutThread` when a thread's IPC operation times
      out due to SchedContext budget expiry. Cleared to `false` by
      `timeoutAwareReceive` after the timeout is detected and reported.
      This eliminates the risk of sentinel collision with legitimate IPC data
      in register x0. -/
  timedOut : Bool := false
  /-- WS-SM SM5.B.4 (WS-SM SM5
      §3.2 / §5 SM5.B.4): CPU affinity — the core this thread is bound to.
      `none` means *unbound*: the thread is homed on the boot core
      (`determineTargetCore`), where the placement invariant keeps it; `some c`
      pins the thread to core `c`.

      Default `none` is the pre-SMP-compatible value: every thread constructed
      without an explicit affinity is unbound, so the per-core
      `switchToThreadOnCore` reject-remote gate (SM5.B.4) never fires for it
      and the single-core boot trace stays byte-identical.

      `switchToThreadOnCore` (`Scheduler/Operations/Selection.lean`) rejects a
      switch onto any core other than this affinity with
      `KernelError.threadOnDifferentCore` (Theorem 3.2.3): migration is a
      separate, explicit operation, never implicit in a context switch.  The
      field is introduced at SM5.B (rather than the plan's nominal SM5.C.7
      slot) because SM5.B.4's reject-remote semantics structurally requires a
      per-thread core binding — it cannot be expressed as a non-vacuous
      theorem without it.  SM5.C will add the `setThreadCpuAffinity` capability
      operation (SM5.C.8) and the boot-time default-affinity wiring
      (SM5.C.9). -/
  cpuAffinity : Option SeLe4n.Kernel.Concurrency.CoreId := none
  /-- WS-SM Reply objects (seL4-MCS): link to the first-class `Reply` object
      that records this thread's outstanding `Call`.  Mirrors seL4's
      `tcb->tcbReply`.  Set when the thread issues a `Call` (carried unchanged
      through the `blockedOnCall → blockedOnReply` transition); cleared when the
      reply is delivered/consumed.

      Stored on the TCB rather than inside the `blockedOnReply` `ipcState`
      payload so the `ThreadIpcState` arity is unchanged — the dozens of
      exhaustive `match`/`cases` over `ThreadIpcState` stay byte-for-byte intact,
      and `{ tcb with … }` record updates that touch `ipcState` do not have to
      thread a reply id.  This is also the seL4-faithful layout (the kernel links
      a thread to its reply via `tcb->tcbReply`, not via the blocking-state word).

      `none` = no outstanding reply object.  The default keeps every existing TCB
      construction and the boot trace byte-identical.

      WS-ZA ZA4.7: stored as a scalar code (`SeLe4n.ReplyId.optCode`) and read
      through the derived view `TCB.replyObject`, so linking a reply builds no
      cell. -/
  replyObjectCode : Nat := 0
  /-- WS-SM SM6.D (faithful seL4-MCS, server-first receive): the Reply object a
      *server* supplied on its `Recv` while no caller was yet queued.  Stashed here
      when the server blocks on receive (`.blockedOnReceive`) so that a later `Call`
      that rendezvouses with this waiting server can be linked to the reply object
      (`linkCallerReply caller rid`), then cleared.  Distinct from `replyObject`
      (this thread's *own* outstanding-Call reply): `pendingReceiveReply` is the
      reply object this thread, acting as a server, will hand to the *next* caller.
      `none` = the server provided no reply object (a plain receive that cannot
      answer a Call).  Default keeps every existing construction + boot trace
      byte-identical.

      WS-ZA ZA4.7: stored as a scalar code and read through the derived view
      `TCB.pendingReceiveReply`. -/
  pendingReceiveReplyCode : Nat := 0
  /-- WS-RR RR4: **the fault this thread is blocked on** — seL4's `tcbFault`.

      Set by the fault-delivery transition (`Kernel.faultDeliverOnCore`) at the
      moment the faulting thread blocks on its handler's endpoint, and cleared
      by the fault reply that answers it, exactly as seL4 sets `tcbFault` in
      `sendFaultIPC` and clears it in `doReplyTransfer`.

      It has to be on the TCB, not a parameter, because the reply arrives as a
      *separate syscall made by the handler*: nothing on that path knows which
      fault it is answering unless the faulted thread carries it.  And the
      answer decides the semantics — seL4's `handleFaultReply` switches on
      `receiver->tcbFault` to choose between a bare resume (VM and cap faults),
      a register-installing restart (unknown syscall, user exception) and
      leaving the thread `.Inactive`.

      `none` = the thread has no outstanding fault, seL4's
      `seL4_Fault_NullFault`.  The default keeps every existing TCB
      construction and the boot trace byte-identical. -/
  pendingFault : Option ThreadFault := none
  /-- **WS-BP BP7.9: the thread's saved FP/SIMD context** — `v0`–`v31`, `FPCR`,
      `FPSR`.  Authoritative whenever no core's registers hold the thread's live
      values (`MachineState.fpOwner`); while one does, this copy may be stale and
      is brought up to date when that core releases the thread
      (`Architecture.fpReleaseOnCore`).  Erased by `projectKernelObject`, like
      `registerContext`: it is the thread's own state, and the lazy switch is
      what keeps any other thread from reading it.  Zero for a fresh thread. -/
  fpContext : SeLe4n.FpContext := default
  /-- The predecessor in the notification wait queue this thread is on, as a
      scalar code (`SeLe4n.ThreadId.optCode`), read through `TCB.ntfnPrev`.
      A notification queue links through this pair rather than the endpoint
      links: a thread waits on at most one object (its `ipcState` names it),
      and keeping the pairs apart leaves every endpoint-queue invariant blind
      to notifications.  `0` when the thread waits on no notification or is
      its queue's head. -/
  ntfnPrevCode : Nat := 0
  /-- The successor in the notification wait queue, read through
      `TCB.ntfnNext`; `0` at the tail and off every notification queue. -/
  ntfnNextCode : Nat := 0
  /-- WS-ZA ZA4.5: the run queue this thread is on, as a code: `0` on none,
      `c + 1` on core `c`'s.  A thread is on at most one run queue, as in seL4,
      where `tcbQueued` is one flag and the links below are one set; the core
      code is what keeps one core's queue from reading another core's links.
      Read through `TCB.runCore?`. -/
  runCoreCode : Nat := 0
  /-- The priority bucket the thread is queued in.  Meaningful only while
      `runCoreCode ≠ 0`; a thread leaving the queue keeps its last value. -/
  runPrio : SeLe4n.Priority := ⟨0⟩
  /-- The predecessor in its core's queue of runnable threads, as a code
      (`LinkedQueue.code`: `0` at the head), as seL4's `tcbSchedPrev`. -/
  runPrevCode : Nat := 0
  /-- The successor in its core's queue, `0` at the tail (`tcbSchedNext`). -/
  runNextCode : Nat := 0
  /-- The predecessor in its priority bucket, `0` at the bucket's head. -/
  runBucketPrevCode : Nat := 0
  /-- The successor in its priority bucket, `0` at the bucket's tail. -/
  runBucketNextCode : Nat := 0
  /-- WS-ZA ZA4.6: the predecessor among the threads reply-blocked on the same
      server (`blockingServer?`), as a code, read through `TCB.replyWaiterPrev`.
      The server's waiters are a queue linked through this pair, so priority
      inheritance reaches them from the server (`replyWaitersHead`) without a
      scan of the object store.  A pair of its own, as the notification links
      are: a thread is reply-blocked or notification-blocked, never both, and
      the separate pair leaves each queue's invariants blind to the other.
      `0` at the head and off every reply-waiter queue. -/
  replyWaiterPrevCode : Nat := 0
  /-- The successor among the server's reply waiters, read through
      `TCB.replyWaiterNext`; `0` at the tail and off every queue. -/
  replyWaiterNextCode : Nat := 0
  /-- The first of the threads reply-blocked on this thread, read through
      `TCB.replyWaitersHead`; `0` when none is.  A caller joins at the head:
      priority inheritance reads the waiters' maximum, which no order changes,
      so the queue keeps no tail. -/
  replyWaitersHeadCode : Nat := 0
  /-- How many threads are reply-blocked on this thread: the length of the
      queue from `replyWaitersHead`, and so the bound of every walk over it. -/
  replyWaitersCount : Nat := 0
  /-- WS-ZA ZA4.7: the state word of the thread's IPC state
      (`ThreadIpcState.stateCode`); see `ipcObjectCode`. -/
  ipcStateCode : Nat := 0
  /-- WS-ZA ZA4.7: the badge of the capability a blocked sender sent through,
      as a machine word (seL4's `blockingIPCBadge`); meaningful while
      `ipcBadged`.  A blocked sender keeps its message words in its saved
      registers and IPC buffer, read at the rendezvous
      (`blockedSenderMessage`), so what its capability contributed has to be
      kept on the thread: the capability is gone by then.  Read through
      `TCB.ipcBadgeView`. -/
  ipcBadge : UInt64 := 0
  /-- Whether the sending capability carried a badge. -/
  ipcBadged : Bool := false
  /-- WS-ZA ZA4.7: may a blocked sender's extra capabilities be transferred —
      its endpoint capability had the `Grant` right (seL4's
      `blockingIPCCanGrant`). -/
  ipcCanGrant : Bool := false
  /-- WS-ZA ZA4.7: a blocked sender's message is its fault (`pendingFault`)
      rather than its registers: set by fault delivery, cleared by every user
      send or call that blocks.  seL4 decides the same question at the
      rendezvous from `tcbFault`. -/
  ipcFaultSend : Bool := false
  /-- **The scheduling context this thread is the counted origin of**, as a
      scalar code (`k + 1` for the context `⟨k⟩`, `0` for none): written by the
      first push of a donation, when the donor lends the context it owns and the
      context records it as the reservation's origin
      (`SchedContext.donationOrigin`).  The origin a context records **counts**
      only while this code names that context back (the
      check `donationOriginRecipient?` makes, `donationOriginCounted`), so the two ends validate each other and
      neither is cleared for the other's sake: a context whose origin is
      cleared on its own side leaves this code naming it, which then counts for
      nothing, and a thread that makes a second first push moves the code, so
      the context it lent before keeps a superseded origin that counts for
      nothing either -- one bounded field per context, never growing state --
      and settles as seL4's `reply_pop` settles it.  A carved thread starts at
      `0`, so an id reused after a thread is destroyed is the origin of no
      context, whatever a context still records.  -/
  originScCode : Nat := 0
  /-- WS-ZA ZA5.4 part 26: **the records the two space slots keep while
      empty**, as a CNode's slots keep theirs (`CNode.spare`): entry `i` is
      the capability cell slot `i` last held, or the one the carve made with
      the thread (seL4's TCB CTEs, which exist from the retype), so the next
      capability written there overwrites it in place.  Logically one value
      (`SpareCells`), so no theorem reads it. -/
  spaceSpare : SpareCells := Squash.mk #[none, none]
  /-- WS-ZA ZA5.11: **the thread's declassification provenance**, as plain
      words: eight tag words, the count of those in use and the saturated bit,
      read through `TCB.taintWords` (`SeLe4n.Kernel.TaintWords`) and written in
      place by the taint step.  A carved thread starts with scalar zeros, the
      empty taint, so a reused id names no provenance. -/
  taintTag0 : UInt64 := 0
  taintTag1 : UInt64 := 0
  taintTag2 : UInt64 := 0
  taintTag3 : UInt64 := 0
  taintTag4 : UInt64 := 0
  taintTag5 : UInt64 := 0
  taintTag6 : UInt64 := 0
  taintTag7 : UInt64 := 0
  /-- How many of the tag words are in use. -/
  taintCount : Nat := 0
  /-- Tainted by everything. -/
  taintSaturated : Bool := false
  /-- WS-ZA ZA6.6: **the scheduling context this thread has yielded to**,
      seL4-MCS's `tcb->tcbYieldTo`, as a code
      (`SeLe4n.SchedContextId.optCode`; `0` is none), read through
      `TCB.yieldTo`.  The context names the thread back
      (`SchedContext.yieldFromCode`, `sc->scYieldFrom`); the two ends agree
      kernel-wide (`SystemState.yieldLinksAgree`).  A plain number in the
      thread's own record, as the binding codes are, so a write of the link
      allocates nothing.  A carved thread starts at `0`. -/
  yieldToCode : Nat := 0
  deriving Repr

/-- WS-ZA ZA6.6: the scheduling context a thread has yielded to (seL4-MCS's
`tcbYieldTo`), read from its code.  Reducible, so a record update that leaves
the code alone reads the old value by `rfl`. -/
@[reducible, inline] def TCB.yieldTo (t : TCB) : Option SeLe4n.SchedContextId :=
  SeLe4n.SchedContextId.ofOptCode t.yieldToCode

/-- WS-ZA ZA5.11: the thread's taint words. -/
@[inline] def TCB.taintWords (t : TCB) : SeLe4n.Kernel.TaintWords :=
  { tag0 := t.taintTag0, tag1 := t.taintTag1, tag2 := t.taintTag2, tag3 := t.taintTag3,
    tag4 := t.taintTag4, tag5 := t.taintTag5, tag6 := t.taintTag6, tag7 := t.taintTag7,
    count := t.taintCount, saturated := t.taintSaturated }

/-- WS-ZA ZA5.11: the thread with its taint words written. -/
@[inline] def TCB.withTaintWords (t : TCB) (w : SeLe4n.Kernel.TaintWords) : TCB :=
  { t with taintTag0 := w.tag0, taintTag1 := w.tag1, taintTag2 := w.tag2,
           taintTag3 := w.tag3, taintTag4 := w.tag4, taintTag5 := w.tag5,
           taintTag6 := w.tag6, taintTag7 := w.tag7, taintCount := w.count,
           taintSaturated := w.saturated }

@[simp] theorem TCB.taintWords_withTaintWords (t : TCB) (w : SeLe4n.Kernel.TaintWords) :
    (t.withTaintWords w).taintWords = w := rfl

@[simp] theorem TCB.withTaintWords_taintWords (t : TCB) : t.withTaintWords t.taintWords = t := rfl

/-- WS-ZA ZA5.11: **discharges "this write keeps the thread's taint words"** —
the obligation every thread write that is not the taint step owes, since a
thread's taint words are one of its table back-links
(`KernelObject.tableBackLinks`).  A record update leaving them alone closes by
`rfl`; a generic update closes by the hypothesis its own caller supplied. -/
macro "taint_words_kept" : tactic =>
  `(tactic| first
    | rfl
    | (intro _; rfl)
    | assumption
    | (intro _; split <;> rfl)
    | (intro _; dsimp only; split <;> rfl)
    | (simp_all [TCB.taintWords, Notification.taintWords]; done)
    | (intro _; simp_all [TCB.taintWords, Notification.taintWords]; done))

/-- Closes `(f x).yieldToCode = x.yieldToCode` (or its `∀ x` form) for a TCB
update that writes no yield link (WS-ZA ZA6.6): by definition, by assumption,
through a case split of the update, or by simplification. -/
macro "yield_code_kept" : tactic =>
  `(tactic| first
    | rfl
    | (intro _; rfl)
    | assumption
    | (intro _; split <;> rfl)
    | (intro _; dsimp only; split <;> rfl)
    | (simp_all; done)
    | (intro _; simp_all; done))

/-! ### A thread's space slots (seL4's `tcbCTable` and `tcbVTable`)

A thread holds its CSpace and VSpace roots as capabilities in two slots of its
own (`TCB.spaceCells`), slot 0 the CSpace root and slot 1 the VSpace root.  The
roots are reads of those slots: the object the capability names, or the
sentinel when the slot is empty (an unconfigured thread). -/

/-- The slot index of a thread's CSpace root capability. -/
@[inline] def TCB.cspaceRootSlot : SeLe4n.Slot := SeLe4n.Slot.ofNat 0

/-- The slot index of a thread's VSpace root capability. -/
@[inline] def TCB.vspaceRootSlot : SeLe4n.Slot := SeLe4n.Slot.ofNat 1

/-- The rights of the capability a CSpace root slot holds when written from a
root's id: read, write and grant, the rights `resolveSetSpace` asks of the
capability it installs (`.grant` and `.write`) together with reading the
CNode's slots.  Not inlined: a constant, built once, so a write of the slot
builds no rights list. -/
def TCB.cspaceRootRights : AccessRightSet := AccessRightSet.ofList [.read, .write, .grant]

/-- The rights of the capability a VSpace root slot holds when written from a
root's id: read and write, `resolveSetSpace` asking `.write` of it.  A constant,
as `cspaceRootRights` is. -/
def TCB.vspaceRootRights : AccessRightSet := AccessRightSet.ofList [.read, .write]

/-- The object a space slot's capability names; the sentinel when the slot is
empty or its capability names no object. -/
@[inline] def TCB.spaceCellObject (o : Option Capability) : SeLe4n.ObjId :=
  match o with
  | some c =>
    match c.target with
    | .object id => id
    | _ => SeLe4n.ObjId.sentinel
  | none => SeLe4n.ObjId.sentinel

/-- The space slot naming object `id` with `rights`: empty for the sentinel (a
thread with no root), else the capability to `id` with those rights alone. -/
@[inline] def TCB.spaceCellOf (id : SeLe4n.ObjId) (rights : AccessRightSet) : Option Capability :=
  if id.isReserved then none
  else some ⟨.object id, rights, SeLe4n.Badge.zero, false, default, default, 0, false, 0⟩

@[simp] theorem TCB.spaceCellObject_spaceCellOf (id : SeLe4n.ObjId) (rights : AccessRightSet) :
    TCB.spaceCellObject (TCB.spaceCellOf id rights) = id := by
  unfold TCB.spaceCellObject TCB.spaceCellOf
  by_cases h : id.isReserved
  · simp only [h, if_true]
    cases id with
    | mk v => simp only [SeLe4n.ObjId.isReserved, decide_eq_true_eq] at h; subst h; rfl
  · simp only [h, Bool.false_eq_true, if_false]

/-- The two space slots of a thread whose CSpace root is `c` and VSpace root
`v`, each the capability the root implies (`spaceCellOf`). -/
@[inline] def TCB.spaceCellsOf (c v : SeLe4n.ObjId) : Vector (Option Capability) 2 :=
  #v[TCB.spaceCellOf c TCB.cspaceRootRights, TCB.spaceCellOf v TCB.vspaceRootRights]

/-- **The thread's CSpace root**: the object its CSpace root slot names. -/
@[reducible, inline] def TCB.cspaceRoot (t : TCB) : SeLe4n.ObjId :=
  TCB.spaceCellObject t.spaceCells[0]

/-- **The thread's VSpace root**: the object its VSpace root slot names. -/
@[reducible, inline] def TCB.vspaceRoot (t : TCB) : SeLe4n.ObjId :=
  TCB.spaceCellObject t.spaceCells[1]

@[simp] theorem TCB.spaceCellsOf_get_zero (c v : SeLe4n.ObjId) :
    (TCB.spaceCellsOf c v)[0] = TCB.spaceCellOf c TCB.cspaceRootRights := rfl

@[simp] theorem TCB.spaceCellsOf_get_one (c v : SeLe4n.ObjId) :
    (TCB.spaceCellsOf c v)[1] = TCB.spaceCellOf v TCB.vspaceRootRights := rfl

/-- WS-ZA ZA4.7: the badge a blocked sender sent under. -/
@[inline] def TCB.ipcBadgeView (t : TCB) : Option SeLe4n.Badge :=
  if t.ipcBadged then some (SeLe4n.Badge.ofWord t.ipcBadge) else none

/-- The view is the badge the word and flag stand for. -/
theorem TCB.ipcBadgeView_eq_opt (t : TCB) :
    t.ipcBadgeView = SeLe4n.Badge.opt (SeLe4n.Badge.ofWord t.ipcBadge) t.ipcBadged := rfl

/-- WS-ZA ZA4.7: record what a sender's capability contributed to the message
it blocks with: its badge and its grant right. -/
@[inline] def TCB.setSendCap (t : TCB) (badge : Option SeLe4n.Badge) (grant : Bool) : TCB :=
  { t with ipcBadge := (match badge with | some b => b.word | none => 0),
           ipcBadged := badge.isSome, ipcCanGrant := grant, ipcFaultSend := false }

@[simp] theorem TCB.setSendCap_ipcBadgeView (t : TCB) (badge : Option SeLe4n.Badge)
    (grant : Bool) : (t.setSendCap badge grant).ipcBadgeView = badge := by
  cases badge <;> rfl

@[simp] theorem TCB.setSendCap_ipcCanGrant (t : TCB) (badge : Option SeLe4n.Badge)
    (grant : Bool) : (t.setSendCap badge grant).ipcCanGrant = grant := rfl

@[simp] theorem TCB.setSendCap_ipcFaultSend (t : TCB) (badge : Option SeLe4n.Badge)
    (grant : Bool) : (t.setSendCap badge grant).ipcFaultSend = false := rfl

/-- WS-ZA ZA4.5: where a thread runs — its home core and its place in a run
queue.  The affinity setter and the scheduler's run-queue writes are the only
writes to these fields; every other TCB write is a record update of fields
outside them, so one frame over this projection carries both the home core
(`determineTargetCore`) and the run queue's links (`runQueueRefined`) across
it. -/
structure TcbPlacement where
  cpuAffinity : Option SeLe4n.Kernel.Concurrency.CoreId
  runCoreCode : Nat
  runPrio : SeLe4n.Priority
  runPrevCode : Nat
  runNextCode : Nat
  runBucketPrevCode : Nat
  runBucketNextCode : Nat

/-- A thread's placement fields (`TcbPlacement`). -/
def TCB.placement (t : TCB) : TcbPlacement :=
  ⟨t.cpuAffinity, t.runCoreCode, t.runPrio, t.runPrevCode, t.runNextCode,
    t.runBucketPrevCode, t.runBucketNextCode⟩

/-- A placement frame is an affinity frame. -/
theorem TCB.map_cpuAffinity_of_placement {o o' : Option TCB}
    (h : o.map TCB.placement = o'.map TCB.placement) :
    o.map (·.cpuAffinity) = o'.map (·.cpuAffinity) := by
  cases o <;> cases o' <;> simp_all [TCB.placement]

/-- WS-ZA ZA4.7: the thread's priority-inheritance boost, read from its code.
Reducible, so a record update that leaves the code alone reads the old boost
by `rfl`.  Written as `pipBoostCode := SeLe4n.Priority.optCode p`. -/
@[reducible, inline] def TCB.pipBoost (t : TCB) : Option SeLe4n.Priority :=
  SeLe4n.Priority.ofOptCode t.pipBoostCode

/-- WS-ZA ZA4.7: the reply object of this thread's outstanding call, read from
its code.  Reducible, as `TCB.ipcState` is, so a record update that leaves the
code alone reads the old value by `rfl`.  Written as
`replyObjectCode := SeLe4n.ReplyId.optCode r`. -/
@[reducible, inline] def TCB.replyObject (t : TCB) : Option SeLe4n.ReplyId :=
  SeLe4n.ReplyId.ofOptCode t.replyObjectCode

/-- WS-ZA ZA5.2: the fault handler's capability address, `none` when none is
configured: the view of the flag and word the TCB stores. -/
@[reducible, inline] def TCB.faultHandler (t : TCB) : Option SeLe4n.CPtr :=
  if t.faultHandlerSet then some t.faultHandlerWord else none

/-- WS-ZA ZA5.2: the bound notification, read from its code.  Reducible, so a
record update that leaves the code alone reads the old value by `rfl`.  Written
as `boundNotificationCode := SeLe4n.ObjId.optCode n`. -/
@[reducible, inline] def TCB.boundNotification (t : TCB) : Option SeLe4n.ObjId :=
  SeLe4n.ObjId.ofOptCode t.boundNotificationCode

/-- WS-ZA ZA5.2: the thread's scheduling-context binding, read from its two
codes.  Reducible, so a record update that leaves both codes alone reads the old
binding by `rfl`.  Written as `scBindingScCode := SchedContextBinding.scCode b,
scBindingOwnerCode := SchedContextBinding.ownerCode b`. -/
@[reducible, inline] def TCB.schedContextBinding (t : TCB) :
    SeLe4n.Kernel.SchedContextBinding :=
  SeLe4n.Kernel.SchedContextBinding.ofCodes t.scBindingScCode t.scBindingOwnerCode

/-- WS-ZA ZA4.7: the reply object a server stashed on its receive, read from its
code.  Written as `pendingReceiveReplyCode := SeLe4n.ReplyId.optCode r`. -/
@[reducible, inline] def TCB.pendingReceiveReply (t : TCB) : Option SeLe4n.ReplyId :=
  SeLe4n.ReplyId.ofOptCode t.pendingReceiveReplyCode

/-- WS-ZA ZA4.7: the thread's IPC state, read from its two codes.  Reducible,
so a record update that leaves both codes alone reads the old state by `rfl`
at every transparency, as it did when the state was a field. -/
@[reducible, inline] def TCB.ipcState (t : TCB) : ThreadIpcState :=
  ThreadIpcState.ofCodes t.ipcObjectCode t.ipcStateCode

/-- The record with its IPC state set to `s`: the one write of the two codes.
Reducible, so `simp` and `rfl` read every other field of the result as the
record's, as they did through a record update; `simp` leaves it folded, so a
hypothesis naming a stored record stays in normal form as written. -/
@[reducible, inline] def TCB.setIpcState (t : TCB) (s : ThreadIpcState) : TCB :=
  { t with ipcObjectCode := s.objectCode, ipcStateCode := s.stateCode }

/-! The fields of a record with its state set: the two codes are the state's,
every other field is the record's. -/

@[simp] theorem TCB.setIpcState_ipcObjectCode (t : TCB) (s : ThreadIpcState) :
    (t.setIpcState s).ipcObjectCode = s.objectCode := rfl

@[simp] theorem TCB.setIpcState_ipcStateCode (t : TCB) (s : ThreadIpcState) :
    (t.setIpcState s).ipcStateCode = s.stateCode := rfl

@[simp] theorem TCB.ipcState_setIpcState (t : TCB) (s : ThreadIpcState) :
    (t.setIpcState s).ipcState = s :=
  ThreadIpcState.ofCodes_codes s

@[simp] theorem TCB.setIpcState_tid (t : TCB) (s : ThreadIpcState) :
    (t.setIpcState s).tid = t.tid := rfl

@[simp] theorem TCB.setIpcState_priority (t : TCB) (s : ThreadIpcState) :
    (t.setIpcState s).priority = t.priority := rfl

@[simp] theorem TCB.setIpcState_domain (t : TCB) (s : ThreadIpcState) :
    (t.setIpcState s).domain = t.domain := rfl

@[simp] theorem TCB.setIpcState_cspaceRoot (t : TCB) (s : ThreadIpcState) :
    (t.setIpcState s).cspaceRoot = t.cspaceRoot := rfl

@[simp] theorem TCB.setIpcState_vspaceRoot (t : TCB) (s : ThreadIpcState) :
    (t.setIpcState s).vspaceRoot = t.vspaceRoot := rfl

@[simp] theorem TCB.setIpcState_spaceCells (t : TCB) (s : ThreadIpcState) :
    (t.setIpcState s).spaceCells = t.spaceCells := rfl

@[simp] theorem TCB.setIpcState_spaceLinks (t : TCB) (s : ThreadIpcState) :
    (t.setIpcState s).spaceLinks = t.spaceLinks := rfl

@[simp] theorem TCB.setIpcState_ipcBuffer (t : TCB) (s : ThreadIpcState) :
    (t.setIpcState s).ipcBuffer = t.ipcBuffer := rfl

@[simp] theorem TCB.setIpcState_threadState (t : TCB) (s : ThreadIpcState) :
    (t.setIpcState s).threadState = t.threadState := rfl

@[simp] theorem TCB.setIpcState_timeSlice (t : TCB) (s : ThreadIpcState) :
    (t.setIpcState s).timeSlice = t.timeSlice := rfl

@[simp] theorem TCB.setIpcState_deadline (t : TCB) (s : ThreadIpcState) :
    (t.setIpcState s).deadline = t.deadline := rfl

@[simp] theorem TCB.setIpcState_queuePrevCode (t : TCB) (s : ThreadIpcState) :
    (t.setIpcState s).queuePrevCode = t.queuePrevCode := rfl

@[simp] theorem TCB.setIpcState_queuePPrevCode (t : TCB) (s : ThreadIpcState) :
    (t.setIpcState s).queuePPrevCode = t.queuePPrevCode := rfl

@[simp] theorem TCB.setIpcState_queueNextCode (t : TCB) (s : ThreadIpcState) :
    (t.setIpcState s).queueNextCode = t.queueNextCode := rfl

@[simp] theorem TCB.setIpcState_pendingMessage (t : TCB) (s : ThreadIpcState) :
    (t.setIpcState s).pendingMessage = t.pendingMessage := rfl

@[simp] theorem TCB.setIpcState_registerContext (t : TCB) (s : ThreadIpcState) :
    (t.setIpcState s).registerContext = t.registerContext := rfl

@[simp] theorem TCB.setIpcState_faultHandler (t : TCB) (s : ThreadIpcState) :
    (t.setIpcState s).faultHandler = t.faultHandler := rfl

@[simp] theorem TCB.setIpcState_boundNotification (t : TCB) (s : ThreadIpcState) :
    (t.setIpcState s).boundNotification = t.boundNotification := rfl

@[simp] theorem TCB.setIpcState_schedContextBinding (t : TCB) (s : ThreadIpcState) :
    (t.setIpcState s).schedContextBinding = t.schedContextBinding := rfl

@[simp] theorem TCB.setIpcState_timeoutBudget (t : TCB) (s : ThreadIpcState) :
    (t.setIpcState s).timeoutBudget = t.timeoutBudget := rfl

@[simp] theorem TCB.setIpcState_maxControlledPriority (t : TCB) (s : ThreadIpcState) :
    (t.setIpcState s).maxControlledPriority = t.maxControlledPriority := rfl

@[simp] theorem TCB.setIpcState_pipBoost (t : TCB) (s : ThreadIpcState) :
    (t.setIpcState s).pipBoost = t.pipBoost := rfl

@[simp] theorem TCB.setIpcState_timedOut (t : TCB) (s : ThreadIpcState) :
    (t.setIpcState s).timedOut = t.timedOut := rfl

@[simp] theorem TCB.setIpcState_cpuAffinity (t : TCB) (s : ThreadIpcState) :
    (t.setIpcState s).cpuAffinity = t.cpuAffinity := rfl

@[simp] theorem TCB.setIpcState_replyObject (t : TCB) (s : ThreadIpcState) :
    (t.setIpcState s).replyObject = t.replyObject := rfl

@[simp] theorem TCB.setIpcState_pendingReceiveReply (t : TCB) (s : ThreadIpcState) :
    (t.setIpcState s).pendingReceiveReply = t.pendingReceiveReply := rfl

@[simp] theorem TCB.setIpcState_pendingFault (t : TCB) (s : ThreadIpcState) :
    (t.setIpcState s).pendingFault = t.pendingFault := rfl

@[simp] theorem TCB.setIpcState_fpContext (t : TCB) (s : ThreadIpcState) :
    (t.setIpcState s).fpContext = t.fpContext := rfl

@[simp] theorem TCB.setIpcState_ntfnPrevCode (t : TCB) (s : ThreadIpcState) :
    (t.setIpcState s).ntfnPrevCode = t.ntfnPrevCode := rfl

@[simp] theorem TCB.setIpcState_ntfnNextCode (t : TCB) (s : ThreadIpcState) :
    (t.setIpcState s).ntfnNextCode = t.ntfnNextCode := rfl

@[simp] theorem TCB.setIpcState_runCoreCode (t : TCB) (s : ThreadIpcState) :
    (t.setIpcState s).runCoreCode = t.runCoreCode := rfl

@[simp] theorem TCB.setIpcState_runPrio (t : TCB) (s : ThreadIpcState) :
    (t.setIpcState s).runPrio = t.runPrio := rfl

@[simp] theorem TCB.setIpcState_runPrevCode (t : TCB) (s : ThreadIpcState) :
    (t.setIpcState s).runPrevCode = t.runPrevCode := rfl

@[simp] theorem TCB.setIpcState_runNextCode (t : TCB) (s : ThreadIpcState) :
    (t.setIpcState s).runNextCode = t.runNextCode := rfl

@[simp] theorem TCB.setIpcState_runBucketPrevCode (t : TCB) (s : ThreadIpcState) :
    (t.setIpcState s).runBucketPrevCode = t.runBucketPrevCode := rfl

@[simp] theorem TCB.setIpcState_runBucketNextCode (t : TCB) (s : ThreadIpcState) :
    (t.setIpcState s).runBucketNextCode = t.runBucketNextCode := rfl

@[simp] theorem TCB.setIpcState_replyWaiterPrevCode (t : TCB) (s : ThreadIpcState) :
    (t.setIpcState s).replyWaiterPrevCode = t.replyWaiterPrevCode := rfl

@[simp] theorem TCB.setIpcState_replyWaiterNextCode (t : TCB) (s : ThreadIpcState) :
    (t.setIpcState s).replyWaiterNextCode = t.replyWaiterNextCode := rfl

@[simp] theorem TCB.setIpcState_replyWaitersHeadCode (t : TCB) (s : ThreadIpcState) :
    (t.setIpcState s).replyWaitersHeadCode = t.replyWaitersHeadCode := rfl

@[simp] theorem TCB.setIpcState_replyWaitersCount (t : TCB) (s : ThreadIpcState) :
    (t.setIpcState s).replyWaitersCount = t.replyWaitersCount := rfl


/-- WS-ZA ZA5.2: the binding of a constructed TCB is the one its two code fields
stand for, so a record update writing a binding's codes reads back that binding
(`SchedContextBinding.ofCodes_codes`). -/
@[simp] theorem TCB.schedContextBinding_mk (f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51 f52 f53 f54 f55 f56 f57 f58 f59) :
    (TCB.mk f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51 f52 f53 f54 f55 f56 f57 f58 f59).schedContextBinding =
      SeLe4n.Kernel.SchedContextBinding.ofCodes f19 f20 := rfl

/-- The roots of a constructed TCB are the objects its two space slots name, so a
record update leaving the slots alone reads the old roots. -/
@[simp] theorem TCB.cspaceRoot_mk (f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51 f52 f53 f54 f55 f56 f57 f58 f59) :
    (TCB.mk f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51 f52 f53 f54 f55 f56 f57 f58 f59).cspaceRoot = TCB.spaceCellObject f4[0] := rfl

@[simp] theorem TCB.vspaceRoot_mk (f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51 f52 f53 f54 f55 f56 f57 f58 f59) :
    (TCB.mk f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51 f52 f53 f54 f55 f56 f57 f58 f59).vspaceRoot = TCB.spaceCellObject f4[1] := rfl

@[simp] theorem TCB.ipcState_mk (f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51 f52 f53 f54 f55 f56 f57 f58 f59) :
    (TCB.mk f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51 f52 f53 f54 f55 f56 f57 f58 f59).ipcState = ThreadIpcState.ofCodes f7 f42 := rfl

@[simp] theorem TCB.replyObject_mk (f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51 f52 f53 f54 f55 f56 f57 f58 f59) :
    (TCB.mk f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51 f52 f53 f54 f55 f56 f57 f58 f59).replyObject = SeLe4n.ReplyId.ofOptCode f26 := rfl

@[simp] theorem TCB.pendingReceiveReply_mk (f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51 f52 f53 f54 f55 f56 f57 f58 f59) :
    (TCB.mk f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51 f52 f53 f54 f55 f56 f57 f58 f59).pendingReceiveReply = SeLe4n.ReplyId.ofOptCode f27 := rfl

theorem TCB.ofCodes_ipcCodes (t : TCB) :
    ThreadIpcState.ofCodes t.ipcObjectCode t.ipcStateCode = t.ipcState := rfl

@[simp] theorem TCB.objectCode_ipcState (t : TCB) :
    t.ipcState.objectCode = t.ipcObjectCode :=
  ThreadIpcState.objectCode_ofCodes _ _

@[simp] theorem TCB.stateCode_ipcState (t : TCB) :
    t.ipcState.stateCode = t.ipcStateCode :=
  ThreadIpcState.stateCode_ofCodes _ _

/-- Setting the state a record already holds leaves it unchanged. -/
@[simp] theorem TCB.setIpcState_ipcState (t : TCB) : t.setIpcState t.ipcState = t := by
  simp [TCB.setIpcState]

/-- A record's state is `s` exactly when its two codes are `s`'s. -/
theorem TCB.ipcState_eq_iff_codes (t : TCB) (s : ThreadIpcState) :
    t.ipcState = s ↔ t.ipcObjectCode = s.objectCode ∧ t.ipcStateCode = s.stateCode :=
  ThreadIpcState.ofCodes_eq_iff _ _ s

/-- Two records agree when their states and every other field do. -/
theorem TCB.ipcState_ext {a b : TCB} (h : a.ipcState = b.ipcState) :
    a.ipcObjectCode = b.ipcObjectCode ∧ a.ipcStateCode = b.ipcStateCode := by
  rw [← TCB.objectCode_ipcState, ← TCB.stateCode_ipcState, h,
    TCB.objectCode_ipcState, TCB.stateCode_ipcState]
  exact ⟨rfl, rfl⟩

/-- The predecessor link, read from its scalar code (`TCB.queuePrevCode`). -/
@[inline] def TCB.queuePrev (t : TCB) : Option SeLe4n.ThreadId :=
  SeLe4n.ThreadId.ofOptCode t.queuePrevCode

/-- The back-pointer, read from its scalar code (`TCB.queuePPrevCode`). -/
@[inline] def TCB.queuePPrev (t : TCB) : Option QueuePPrev :=
  QueuePPrev.ofOptCode t.queuePPrevCode

/-- The successor link, read from its scalar code (`TCB.queueNextCode`). -/
@[inline] def TCB.queueNext (t : TCB) : Option SeLe4n.ThreadId :=
  SeLe4n.ThreadId.ofOptCode t.queueNextCode

/-! The views through a record built field by field, and the fold back to a
view when a code is copied from another record: together they let `simp` read
a written link as the value written and an untouched link as the old view. -/

@[simp] theorem TCB.queuePrev_mk (f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51 f52 f53 f54 f55 f56 f57 f58 f59) :
    (TCB.mk f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51 f52 f53 f54 f55 f56 f57 f58 f59).queuePrev = SeLe4n.ThreadId.ofOptCode f11 := rfl

@[simp] theorem TCB.queuePPrev_mk (f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51 f52 f53 f54 f55 f56 f57 f58 f59) :
    (TCB.mk f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51 f52 f53 f54 f55 f56 f57 f58 f59).queuePPrev = QueuePPrev.ofOptCode f12 := rfl

@[simp] theorem TCB.queueNext_mk (f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51 f52 f53 f54 f55 f56 f57 f58 f59) :
    (TCB.mk f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51 f52 f53 f54 f55 f56 f57 f58 f59).queueNext = SeLe4n.ThreadId.ofOptCode f13 := rfl

/-- The notification-queue predecessor, read from its scalar code. -/
@[inline] def TCB.ntfnPrev (t : TCB) : Option SeLe4n.ThreadId :=
  SeLe4n.ThreadId.ofOptCode t.ntfnPrevCode

/-- The notification-queue successor, read from its scalar code. -/
@[inline] def TCB.ntfnNext (t : TCB) : Option SeLe4n.ThreadId :=
  SeLe4n.ThreadId.ofOptCode t.ntfnNextCode

@[simp] theorem TCB.ntfnPrev_mk (f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51 f52 f53 f54 f55 f56 f57 f58 f59) :
    (TCB.mk f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51 f52 f53 f54 f55 f56 f57 f58 f59).ntfnPrev = SeLe4n.ThreadId.ofOptCode f30 := rfl

@[simp] theorem TCB.ntfnNext_mk (f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51 f52 f53 f54 f55 f56 f57 f58 f59) :
    (TCB.mk f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51 f52 f53 f54 f55 f56 f57 f58 f59).ntfnNext = SeLe4n.ThreadId.ofOptCode f31 := rfl

@[simp] theorem TCB.ofOptCode_ntfnPrevCode (t : TCB) :
    SeLe4n.ThreadId.ofOptCode t.ntfnPrevCode = t.ntfnPrev := rfl

@[simp] theorem TCB.ofOptCode_ntfnNextCode (t : TCB) :
    SeLe4n.ThreadId.ofOptCode t.ntfnNextCode = t.ntfnNext := rfl

@[simp] theorem TCB.optCode_ntfnPrev (t : TCB) :
    SeLe4n.ThreadId.optCode t.ntfnPrev = t.ntfnPrevCode :=
  SeLe4n.ThreadId.optCode_ofOptCode _

@[simp] theorem TCB.optCode_ntfnNext (t : TCB) :
    SeLe4n.ThreadId.optCode t.ntfnNext = t.ntfnNextCode :=
  SeLe4n.ThreadId.optCode_ofOptCode _

/-- WS-ZA ZA4.6: the reply-waiter-queue predecessor, read from its code. -/
@[inline] def TCB.replyWaiterPrev (t : TCB) : Option SeLe4n.ThreadId :=
  SeLe4n.ThreadId.ofOptCode t.replyWaiterPrevCode

/-- The reply-waiter-queue successor, read from its code. -/
@[inline] def TCB.replyWaiterNext (t : TCB) : Option SeLe4n.ThreadId :=
  SeLe4n.ThreadId.ofOptCode t.replyWaiterNextCode

/-- The first thread reply-blocked on this one, read from its code. -/
@[inline] def TCB.replyWaitersHead (t : TCB) : Option SeLe4n.ThreadId :=
  SeLe4n.ThreadId.ofOptCode t.replyWaitersHeadCode

@[simp] theorem TCB.ofOptCode_replyWaiterPrevCode (t : TCB) :
    SeLe4n.ThreadId.ofOptCode t.replyWaiterPrevCode = t.replyWaiterPrev := rfl

@[simp] theorem TCB.ofOptCode_replyWaiterNextCode (t : TCB) :
    SeLe4n.ThreadId.ofOptCode t.replyWaiterNextCode = t.replyWaiterNext := rfl

@[simp] theorem TCB.ofOptCode_replyWaitersHeadCode (t : TCB) :
    SeLe4n.ThreadId.ofOptCode t.replyWaitersHeadCode = t.replyWaitersHead := rfl

@[simp] theorem TCB.optCode_replyWaiterPrev (t : TCB) :
    SeLe4n.ThreadId.optCode t.replyWaiterPrev = t.replyWaiterPrevCode :=
  SeLe4n.ThreadId.optCode_ofOptCode _

@[simp] theorem TCB.optCode_replyWaiterNext (t : TCB) :
    SeLe4n.ThreadId.optCode t.replyWaiterNext = t.replyWaiterNextCode :=
  SeLe4n.ThreadId.optCode_ofOptCode _

@[simp] theorem TCB.optCode_replyWaitersHead (t : TCB) :
    SeLe4n.ThreadId.optCode t.replyWaitersHead = t.replyWaitersHeadCode :=
  SeLe4n.ThreadId.optCode_ofOptCode _

@[simp] theorem TCB.ofOptCode_queuePrevCode (t : TCB) :
    SeLe4n.ThreadId.ofOptCode t.queuePrevCode = t.queuePrev := rfl

@[simp] theorem TCB.ofOptCode_queuePPrevCode (t : TCB) :
    QueuePPrev.ofOptCode t.queuePPrevCode = t.queuePPrev := rfl

@[simp] theorem TCB.ofOptCode_queueNextCode (t : TCB) :
    SeLe4n.ThreadId.ofOptCode t.queueNextCode = t.queueNext := rfl

@[simp] theorem TCB.optCode_queuePrev (t : TCB) :
    SeLe4n.ThreadId.optCode t.queuePrev = t.queuePrevCode :=
  SeLe4n.ThreadId.optCode_ofOptCode _

@[simp] theorem TCB.optCode_queuePPrev (t : TCB) :
    QueuePPrev.optCode t.queuePPrev = t.queuePPrevCode :=
  QueuePPrev.optCode_ofOptCode _

@[simp] theorem TCB.optCode_queueNext (t : TCB) :
    SeLe4n.ThreadId.optCode t.queueNext = t.queueNextCode :=
  SeLe4n.ThreadId.optCode_ofOptCode _

theorem TCB.queuePrevCode_eq (t : TCB) :
    t.queuePrevCode = SeLe4n.ThreadId.optCode t.queuePrev :=
  (SeLe4n.ThreadId.optCode_ofOptCode _).symm

theorem TCB.queuePPrevCode_eq (t : TCB) :
    t.queuePPrevCode = QueuePPrev.optCode t.queuePPrev :=
  (QueuePPrev.optCode_ofOptCode _).symm

theorem TCB.queueNextCode_eq (t : TCB) :
    t.queueNextCode = SeLe4n.ThreadId.optCode t.queueNext :=
  (SeLe4n.ThreadId.optCode_ofOptCode _).symm

/-- **WS-OD OD3.9**: the link update a removal writes to the **predecessor** of
the node it unlinks — the predecessor's `queueNext` skips over `removed`.

Lives beside the fields it maintains, and is one definition because "what does
unlinking `removed` write to its neighbours" is one question.  It had three
answers: `endpointQueueRemove`, `endpointQueueRemoveDual` and
`spliceOutMidQueueNode` each spelled the pair inline, and the third of them
disagreed with the other two — see `queueUnlinkSuccessor`. -/
def queueUnlinkPredecessor (removed : TCB) : TCB → TCB :=
  fun p => { p with queueNextCode := removed.queueNextCode }

/-- **WS-OD OD3.9**: the link update a removal writes to the **successor** of the
node it unlinks — the successor inherits `removed`'s `queuePrev` *and* its
`queuePPrev`.

Both fields, and the second is the one that was missing.  `queuePPrev` is the
back-pointer `endpointQueueRemoveDual` validates (`pprevConsistent`, else
`.illegalState`), and it is right in both cases by construction: a removed head
carries `.endpointHead`, which the successor inherits as the new head, and a
removed interior node carries `.tcbNext prev`, which is exactly the back-pointer
the successor's new `queuePrev` names.

WS-OD OD1.1 established this for `endpointQueueRemove` and recorded that leaving
`queuePPrev` naming the removed thread strands the successor — every later dual
removal on it fails, so it can never leave the endpoint queue.  It fixed the copy
it was looking at.  `spliceOutMidQueueNode` — the removal `.tcbSuspend` and
thread destruction run — was the third copy and kept writing `queuePrev` alone,
so the identical defect stayed live on those two paths, and OD3.5 then wrote the
divergence down as a design decision ("the two patches take different `upd`
functions and not one") rather than as the defect it was.  One definition is what
makes a fourth removal impossible to get wrong. -/
def queueUnlinkSuccessor (removed : TCB) : TCB → TCB :=
  fun n => { n with queuePrevCode := removed.queuePrevCode, queuePPrevCode := removed.queuePPrevCode }

/-- **WS-RR RR8.3**: `queuePPrev` agrees with `queuePrev` — the relation the
dual-queue removal's `pprevConsistent` guard checks, stated pointwise at the
record whose two fields it relates.

`queuePPrev` carries one bit beyond `queuePrev`: whether the thread is linked
into an endpoint queue at all.  Everything else about it is redundant, and the
three values say so — `none` is off every queue, `.endpointHead` is on a queue
with no predecessor, and `.tcbNext p` is on a queue behind `p`.  So the two
fields agree exactly when

* `.endpointHead` occurs with `queuePrev = none`, and
* `.tcbNext p` occurs with `queuePrev = some p`,

and a `queuePPrev` of `none` says the thread is on no queue, which is exactly
what makes `queuePrev = none` its obligation.

**That arm was `True` until `v0.35.99`, and the reason given for it was false.**
It read *"`tcbQueueLinkIntegrity` is what forbids a dangling `queuePrev`"* — and
that conjunct forbids a `queuePrev` whose target does not point back, not a
`queuePrev` present with no `queuePPrev`.  So a two-node queue whose tail
carried `queuePrev = some head` and `queuePPrev = none` satisfied every conjunct
of `dualQueueSystemInvariant`, while `endpointQueueRemoveDual` — whose guard
takes a `QueuePPrev`, not an `Option` — refuses that tail outright and can never
dequeue it.  That is the OD1.1/OD3.9 stranding class a third time: the pairing
closed *present but wrong* and left *absent on a linked node* open, which is
weaker than the "one bit" this field is documented to carry.  Reported on
PR #897 and confirmed by reading the two conjuncts rather than the prose.

**The `none` arm is only NECESSARY, and the HEAD case is why the "one bit" needs
two conjuncts** (PR #897 review, `v0.35.106`).  `queuePrev = none` is what a
*detached* thread carries **and** what a queue's **head** carries, so this arm
cannot distinguish them -- a pointwise predicate over one TCB structurally cannot
say "on no queue", whatever it is strengthened to.  So the bit is carried at two
levels, split by what each level can see: this predicate says the *pair* agrees at
one TCB, and `intrusiveQueueWellFormed`'s **P2** says a *queue's head* carries
`some .endpointHead`.  The second is a fact about a queue and belongs to the queue.

Until `v0.35.106` P2 constrained only `queuePrev`, so a queue whose head carried
`(none, none, none)` satisfied this arm and every other conjunct of
`dualQueueSystemInvariant` while the dual removal refused it -- the sole member of a
one-thread queue could never be dequeued.  Folding the clause into P2 cost
`dualQueueSystemInvariant` a fifth conjunct (`endpointQueueHeadDisjoint`, a
consequence of `ipcInvariantCore`'s `queueHeadBlockedConsistent`), and P2's own
docstring carries that measurement.  `tests/NegativeStateSuite.lean`'s case (5) is
the witness: the pairing accepts the corrupted head, and the bundle now refuses it.

With both halves in place a queue **member**'s `queuePPrev` is derivable rather
than hypothesised -- at the head from P2, at an interior node from
`tcbQueueLinkIntegrity`'s forward clause plus this pairing
(`queuePPrev_tcbNext_of_reachable`), joined by `queuePPrev_of_queueMember`.

**Why pointwise.**  Every operational writer of the pair writes both fields in
one store (`tcbWithQueueLinks`) or inherits them together
(`queueUnlinkSuccessor`), so the obligation each site discharges is about the
record it stores and never about the rest of the object table.  That is what
makes the store-level lift (`queuePPrevAgreesWithPrev`, the fourth of
`dualQueueSystemInvariant`'s five conjuncts) cheap to preserve: a transition that leaves both
fields alone discharges it by `rfl` through
`TCB.queuePPrevAgreesWithPrev_of_pairEq`.

**Why it is an invariant rather than a guard's private business.**  Nothing in
`ipcInvariantFull` read `queuePPrev` before this, which is why WS-OD OD1.1 and
OD3.9 each found a removal writing `queuePrev` alone and stranding the
successor — twice, eight cuts apart, in code whose own comments described the
pairing.  A field two operations must agree about, with no invariant relating
them, is the *maintained only by convention* shape. -/
def TCB.queuePPrevAgreesWithPrev (tcb : TCB) : Prop :=
  match tcb.queuePPrev with
  -- on no queue, so it has no predecessor either
  | none => tcb.queuePrev = none
  -- a queue's head, so it has no predecessor
  | some .endpointHead => tcb.queuePrev = none
  -- behind `p`, which is therefore its predecessor
  | some (.tcbNext p) => tcb.queuePrev = some p

/-- A TCB carrying neither back-pointer agrees — the detached shape every clear
writes.  It took `queuePrev = none` as a second hypothesis at `v0.35.99`: with
the `none` arm strengthened, carrying no `queuePPrev` is a *claim* that the
thread is on no queue, not a vacuity. -/
theorem TCB.queuePPrevAgreesWithPrev_of_pprev_none {tcb : TCB}
    (h : tcb.queuePPrev = none) (hPrev : tcb.queuePrev = none) :
    tcb.queuePPrevAgreesWithPrev := by
  unfold TCB.queuePPrevAgreesWithPrev; rw [h]; exact hPrev

/-- The workhorse: a TCB that agrees on **both** link fields with one that
satisfies the pairing satisfies it too.  Stated on the pair rather than on the
record, because that is the shape a `{ tcb with … }` store presents and the
reason the store-level conjunct costs a `rfl` at a site that writes neither
field. -/
theorem TCB.queuePPrevAgreesWithPrev_of_pairEq {tcb tcb' : TCB}
    (hPrev : tcb'.queuePrev = tcb.queuePrev)
    (hPPrev : tcb'.queuePPrev = tcb.queuePPrev)
    (h : tcb.queuePPrevAgreesWithPrev) : tcb'.queuePPrevAgreesWithPrev := by
  unfold TCB.queuePPrevAgreesWithPrev at h ⊢
  rw [hPPrev, hPrev]; exact h

/-- `queueUnlinkSuccessor` transports the pairing from the removed thread to the
successor that inherits it — which is *why* it writes both fields.  WS-OD OD1.1
and OD3.9 each found a removal writing `queuePrev` alone; this is that fix
stated as a property rather than left to the reader of three call sites. -/
theorem TCB.queuePPrevAgreesWithPrev_queueUnlinkSuccessor {removed n : TCB}
    (h : removed.queuePPrevAgreesWithPrev) :
    (queueUnlinkSuccessor removed n).queuePPrevAgreesWithPrev :=
  TCB.queuePPrevAgreesWithPrev_of_pairEq rfl rfl h

/-- `queueUnlinkPredecessor` writes only `queueNext`, so the predecessor keeps
whatever pairing it had. -/
theorem TCB.queuePPrevAgreesWithPrev_queueUnlinkPredecessor {removed p : TCB}
    (h : p.queuePPrevAgreesWithPrev) :
    (queueUnlinkPredecessor removed p).queuePPrevAgreesWithPrev :=
  TCB.queuePPrevAgreesWithPrev_of_pairEq rfl rfl h

/-- **WS-OD OD3.10**: the two TCBs a splice of `removed` relinks — the ones
`queueUnlinkPredecessor` and `queueUnlinkSuccessor` above are applied to.

The neutral spelling of a question two footprint families ask.  It was
`cancelSpliceNeighbors?`, in the cancellation module, when only the cancellation
arms declared a splice; the bound-notification delivery splices too
(`endpointQueueRemoveDual`), and a second copy of `(tcb.queuePrev, tcb.queueNext)`
beside this one is the shape that let the three removals disagree about
`queuePPrev`.  Arm selection stays with each arm — `cancelArmSpliceNeighbors?`
and `notificationSignalSpliceNeighbors?` are gated on their own operation's
guard — because *which* thread is spliced is an arm question and *who its
neighbours are* is not. -/
def queueSpliceNeighbors? (removed : TCB) :
    Option SeLe4n.ThreadId × Option SeLe4n.ThreadId :=
  (removed.queuePrev, removed.queueNext)

/-- The record with only its CSpace root slot written (`spaceCellOf c`). -/
@[reducible] def TCB.withCSpaceRoot (t : TCB) (c : SeLe4n.ObjId) : TCB :=
  { t with spaceCells := t.spaceCells.set 0 (TCB.spaceCellOf c TCB.cspaceRootRights) }

/-- The record with only its VSpace root slot written (`spaceCellOf v`). -/
@[reducible] def TCB.withVSpaceRoot (t : TCB) (v : SeLe4n.ObjId) : TCB :=
  { t with spaceCells := t.spaceCells.set 1 (TCB.spaceCellOf v TCB.vspaceRootRights) }

/-! Reading a record after one of its space slots is written: that root is the
one written, and the other root is the record's. -/

@[simp] theorem TCB.withCSpaceRoot_cspaceRoot (t : TCB) (c : SeLe4n.ObjId) :
    (t.withCSpaceRoot c).cspaceRoot = c := by
  simp only [TCB.cspaceRoot, Vector.getElem_set_self, TCB.spaceCellObject_spaceCellOf]

@[simp] theorem TCB.withCSpaceRoot_vspaceRoot (t : TCB) (c : SeLe4n.ObjId) :
    (t.withCSpaceRoot c).vspaceRoot = t.vspaceRoot := by
  simp only [TCB.vspaceRoot, Vector.getElem_set_ne _ _ (by decide : (0 : Nat) ≠ 1)]

@[simp] theorem TCB.withVSpaceRoot_vspaceRoot (t : TCB) (v : SeLe4n.ObjId) :
    (t.withVSpaceRoot v).vspaceRoot = v := by
  simp only [TCB.vspaceRoot, Vector.getElem_set_self, TCB.spaceCellObject_spaceCellOf]

@[simp] theorem TCB.withVSpaceRoot_cspaceRoot (t : TCB) (v : SeLe4n.ObjId) :
    (t.withVSpaceRoot v).cspaceRoot = t.cspaceRoot := by
  simp only [TCB.cspaceRoot, Vector.getElem_set_ne _ _ (by decide : (1 : Nat) ≠ 0)]

/-- WS-H12c: Manual `BEq` for `TCB`: field-wise comparison, the saved
`registerContext` by `RegisterFile`'s decidable equality.  Proofs that need
propositional equality of TCBs use `TCB.ext`. -/
instance : BEq TCB where
  beq a b :=
    a.tid == b.tid && a.priority == b.priority && a.domain == b.domain &&
    a.spaceCells == b.spaceCells && a.spaceLinks == b.spaceLinks &&
    a.ipcBuffer == b.ipcBuffer && a.ipcState == b.ipcState &&
    a.threadState == b.threadState &&
    a.timeSlice == b.timeSlice && a.deadline == b.deadline &&
    a.queuePrev == b.queuePrev && a.queuePPrev == b.queuePPrev &&
    a.queueNext == b.queueNext && a.pendingMessage == b.pendingMessage &&
    a.registerContext == b.registerContext &&
    a.faultHandlerSet == b.faultHandlerSet && a.faultHandlerWord == b.faultHandlerWord &&
    a.boundNotification == b.boundNotification &&
    a.schedContextBinding == b.schedContextBinding &&
    a.timeoutBudget == b.timeoutBudget &&
    a.maxControlledPriority == b.maxControlledPriority &&
    a.pipBoostCode == b.pipBoostCode &&
    a.timedOut == b.timedOut &&
    -- WS-SM SM5.B.4: per-TCB CPU affinity participates in structural equality.
    -- `Option CoreId` (`CoreId = Fin numCores`) derives `DecidableEq`, so its
    -- `==` agrees with `=`.
    a.cpuAffinity == b.cpuAffinity &&
    -- WS-SM Reply objects: per-TCB reply-object links participate in structural
    -- equality.  `Option ReplyId` derives `DecidableEq`, so its `==` agrees
    -- with `=`.
    a.replyObject == b.replyObject &&
    a.pendingReceiveReply == b.pendingReceiveReply &&
    -- WS-RR RR4: the outstanding fault participates in structural equality.
    -- `ThreadFault` derives `DecidableEq`, so its `==` agrees with `=`.
    a.pendingFault == b.pendingFault &&
    -- WS-BP BP7.9: the saved FP/SIMD context participates in structural
    -- equality.  `FpContext` derives `DecidableEq`, so its `==` agrees with `=`.
    a.fpContext == b.fpContext &&
    -- WS-ZA ZA4.4: the notification-queue links participate in structural
    -- equality, compared as their scalar codes.
    a.ntfnPrevCode == b.ntfnPrevCode && a.ntfnNextCode == b.ntfnNextCode &&
    -- WS-ZA ZA4.5: and the run-queue links, core and bucket.
    a.runCoreCode == b.runCoreCode && a.runPrio == b.runPrio &&
    a.runPrevCode == b.runPrevCode && a.runNextCode == b.runNextCode &&
    a.runBucketPrevCode == b.runBucketPrevCode && a.runBucketNextCode == b.runBucketNextCode &&
    -- WS-ZA ZA4.6: and the reply-waiter links and ends.
    a.replyWaiterPrevCode == b.replyWaiterPrevCode &&
    a.replyWaiterNextCode == b.replyWaiterNextCode &&
    a.replyWaitersHeadCode == b.replyWaitersHeadCode &&
    a.replyWaitersCount == b.replyWaitersCount &&
    -- WS-ZA ZA4.7: and what a blocked sender's capability contributed.
    a.ipcBadge == b.ipcBadge && a.ipcBadged == b.ipcBadged &&
    a.ipcCanGrant == b.ipcCanGrant && a.ipcFaultSend == b.ipcFaultSend &&
    -- WS-ZA ZA6.6: and the yield link, compared as its code.
    a.yieldToCode == b.yieldToCode

/-- AJ4-D (L-09): Detect sentinel-initialized (unconfigured) TCBs.
    Returns `true` if the TCB's identity or address-space references use
    reserved sentinel values (ID 0), indicating the TCB was freshly created
    by a builder and has not been configured
    via `threadConfigureOp`. Unconfigured TCBs must NOT be scheduled. -/
@[inline] def TCB.isUnconfigured (tcb : TCB) : Bool :=
  tcb.tid.isReserved || tcb.cspaceRoot.isReserved || tcb.vspaceRoot.isReserved

/-- **A thread a core may run**: ready in IPC and not suspended — seL4's
`isRunnable`.  The one test every placement that admits a thread no IPC step
just readied asks: the bind's parked-thread placement and the replenishment
wake. -/
@[inline] def TCB.isRunnable (tcb : TCB) : Bool :=
  decide (tcb.ipcState = .ready) && tcb.threadState != .Inactive

/-- **The priority a thread is actually scheduled at** -- its own, raised to any
priority it has inherited.

Priority inheritance records the raise in `TCB.pipBoost`, and every consumer
needs the merged value: the run-queue bucket a thread belongs in, the scheduler's
effective-parameter resolution, and -- since `v0.35.28` -- the frozen mirror of
both.  The expression `⟨Nat.max tcb.priority.val boost.val⟩` was spelled inline
at **eight** sites across the live tree and the frozen surface, which is this
project's own one-question-two-answers hazard at the level of an expression; it
is one function now, and every site that asks the question calls it.

It is `Priority.raisedBy` at the thread's **own** base, **at every binding**.
Until `v0.35.133` a `.bound` thread was scheduled at its *reservation's*
priority raised by the same boost, so `effectiveSchedParams` called
`Priority.raisedBy` directly on `sc.priority` there and this paragraph said the
boost was shared and the base was not.  With one home for a base priority there
is no second base to raise: `effectiveSchedParams_fst_eq_boostedPriority` and
`resolveEffectivePrioDeadline_fst_eq_boostedPriority`
(`Scheduler/Operations/Selection.lean`) state that both resolvers' priority
component **is** this accessor, unconditionally -- which is what lets the frozen
surface, whose store holds the live `TCB` and which resolves no scheduling
parameters at all, read the same priority by reading the same field. -/
@[inline] def TCB.boostedPriority (tcb : TCB) : SeLe4n.Priority :=
  tcb.priority.raisedBy tcb.pipBoost

/-- **The server this thread is blocked on**, if any -- one step of the blocking
graph, read off the thread's own `ipcState`.

The store-level `blockingServer` (`Scheduler/PriorityInheritance/BlockingGraph.lean`)
is this composed with a TCB lookup, and `waitersOf` is this asked of every thread
in the store; the frozen mirror asks both of the frozen store.  Putting the
discriminating match here means the three cannot disagree about what "blocked on
a server" is -- which they could while each spelled its own `match`, and which
matters because priority inheritance, its reversion and the frozen mirror of both
all walk that edge. -/
@[inline] def TCB.blockingServer? (tcb : TCB) : Option SeLe4n.ThreadId :=
  match tcb.ipcState with
  | .blockedOnReply _ (some server) => some server
  | _ => none

/-- Both helpers are transparent to `simp`, so a proof that knows a thread's
`ipcState` or `pipBoost` reduces them exactly as it reduced the inline `match`
they replaced.  Without these, single-sourcing the two questions would have made
every existing `simp [hIpc]` and `simp [hBoost]` a proof that no longer closes --
which is a cost the refactor does not need to impose, and an `rfl` lemma is the
whole of the remedy. -/
@[simp] theorem TCB.blockingServer?_eq (tcb : TCB) :
    tcb.blockingServer? =
      match tcb.ipcState with
      | .blockedOnReply _ (some server) => some server
      | _ => none := rfl

@[simp] theorem TCB.boostedPriority_eq (tcb : TCB) :
    tcb.boostedPriority = tcb.priority.raisedBy tcb.pipBoost := rfl

/-- **Each accessor's frame, stated where the accessor is.**  `blockingServer?`
reads `ipcState` and nothing else; `boostedPriority` reads `priority` and
`pipBoost` and nothing else.  Every consumer that rewrites one TCB into another
needs exactly this, and deriving it at the call site means unfolding the
accessor -- which, inside a `filterMap` or a fold, also rewrites the *bound*
occurrences in the tail and desynchronises the induction hypothesis.  Stated
here, the rewrite touches only the terms named. -/
theorem TCB.blockingServer?_congr {a b : TCB} (h : a.ipcState = b.ipcState) :
    a.blockingServer? = b.blockingServer? := by
  simp only [TCB.blockingServer?_eq, h]

theorem TCB.boostedPriority_congr {a b : TCB}
    (hp : a.priority = b.priority) (hb : a.pipBoost = b.pipBoost) :
    a.boostedPriority = b.boostedPriority := by
  simp only [TCB.boostedPriority_eq, hp, hb]

/-- WS-ZA ZA4.4: `a` is `b` with (only) its two notification-queue links
rewritten — every write the notification queue makes to a TCB beyond the
waiter's own state: the link-in of a new waiter and its old tail, and the
unlink's neighbours.  Every other field, the endpoint-queue links included, is
`b`'s. -/
def tcbNtfnLinkRewrite (a b : TCB) : Prop :=
  ∃ np nn, a = { b with ntfnPrevCode := np, ntfnNextCode := nn }

theorem tcbNtfnLinkRewrite.refl (a : TCB) : tcbNtfnLinkRewrite a a :=
  ⟨a.ntfnPrevCode, a.ntfnNextCode, rfl⟩

theorem tcbNtfnLinkRewrite.trans {a b c : TCB}
    (h1 : tcbNtfnLinkRewrite a b) (h2 : tcbNtfnLinkRewrite b c) :
    tcbNtfnLinkRewrite a c := by
  obtain ⟨p1, n1, rfl⟩ := h1
  obtain ⟨p2, n2, rfl⟩ := h2
  exact ⟨p1, n1, rfl⟩

/-- **A thread restored to the runnable shape** -- the field clear performed on a
thread whose blocking IPC ends, as a function of the record.

The live `restoreToReadyStaging` (`Lifecycle/Suspend.lean`) spelled this inline
inside `updateTcb`'s lambda, so it had no name and no second surface could call
it: `frozenResumeThread` cleared `ipcState` alone and left the three intrusive
queue links and the stashed receive Reply set, which is this project's
*one question answered in two places* with one of the places four fields short.
The stashed Reply is the sharper half -- `replyIsStashed` then keeps that Reply
permanently in use, so lifecycle cleanup of it answers `revocationRequired` with
no receive pending, which is the very defect PR #822's review added the clear
for.  Both surfaces call this now, so a field added to the restore reaches both
by construction rather than by whoever remembers the other one.

What it deliberately does **not** touch is `threadState`, `pipBoost` or
`registerContext`.  The first two are the caller's, and the callers disagree: a
resume writes `.Ready` and recomputes the boost from the blocking graph, a
cancellation writes neither.  The third is what `restoreToReadyStaging`'s frame
argument stages on top, which is why that helper takes one and this does not. -/
@[inline] def TCB.restoredToReady (tcb : TCB) : TCB :=
  TCB.setIpcState
    { tcb with
        queuePrevCode := 0
        queueNextCode := 0
        queuePPrevCode := 0
        pendingReceiveReplyCode := 0 } .ready

/-- Transparent to `simp`, for the reason `TCB.boostedPriority_eq` above is: a
proof that unfolded the inline record update reduces this exactly as it reduced
that, so single-sourcing the clear costs no existing proof. -/
@[simp] theorem TCB.restoredToReady_eq (tcb : TCB) :
    tcb.restoredToReady =
      TCB.setIpcState
        { tcb with
            queuePrevCode := 0
            queueNextCode := 0
            queuePPrevCode := 0
            pendingReceiveReplyCode := 0 } .ready := rfl

/-- AK7-G (F-M05 / MEDIUM): Sanctioned extensionality lemma for `TCB`.

Use this lemma instead of `==` in any proof that requires propositional
equality of TCBs. `TCB.ext` requires each structural field to match,
`registerContext` included.  Companion to `RegisterFile.ext` (Machine.lean). -/
theorem TCB.ext {a b : TCB}
    (hTid : a.tid = b.tid) (hPrio : a.priority = b.priority) (hDom : a.domain = b.domain)
    (hCells : a.spaceCells = b.spaceCells) (hLinks : a.spaceLinks = b.spaceLinks)
    (hBuf : a.ipcBuffer = b.ipcBuffer) (hIpc : a.ipcState = b.ipcState)
    (hTs : a.threadState = b.threadState)
    (hSlice : a.timeSlice = b.timeSlice) (hDeadline : a.deadline = b.deadline)
    (hQPrev : a.queuePrev = b.queuePrev) (hQPPrev : a.queuePPrev = b.queuePPrev)
    (hQNext : a.queueNext = b.queueNext) (hPend : a.pendingMessage = b.pendingMessage)
    (hRC : a.registerContext = b.registerContext)
    (hFhS : a.faultHandlerSet = b.faultHandlerSet) (hFhW : a.faultHandlerWord = b.faultHandlerWord)
    (hBn : a.boundNotification = b.boundNotification)
    (hScC : a.scBindingScCode = b.scBindingScCode)
    (hScO : a.scBindingOwnerCode = b.scBindingOwnerCode)
    (hTb : a.timeoutBudget = b.timeoutBudget)
    (hMcp : a.maxControlledPriority = b.maxControlledPriority)
    (hPip : a.pipBoost = b.pipBoost)
    (hTo : a.timedOut = b.timedOut)
    -- WS-SM SM5.B.4: extensionality covers the per-TCB CPU-affinity field.
    (hCpuAff : a.cpuAffinity = b.cpuAffinity)
    -- WS-SM Reply objects: extensionality covers the per-TCB reply-object links.
    (hReply : a.replyObject = b.replyObject)
    (hPendReply : a.pendingReceiveReply = b.pendingReceiveReply)
    -- WS-RR RR4: extensionality covers the outstanding-fault field.
    (hPendFault : a.pendingFault = b.pendingFault)
    -- WS-BP BP7.9: extensionality covers the saved FP/SIMD context.
    (hFp : a.fpContext = b.fpContext)
    -- WS-ZA ZA4.4: and the notification-queue links.
    (hNPrev : a.ntfnPrev = b.ntfnPrev)
    (hNNext : a.ntfnNext = b.ntfnNext)
    -- WS-ZA ZA4.5: and the run-queue links, core and bucket.
    (hRCore : a.runCoreCode = b.runCoreCode) (hRPrio : a.runPrio = b.runPrio)
    (hRPrev : a.runPrevCode = b.runPrevCode) (hRNext : a.runNextCode = b.runNextCode)
    (hRBPrev : a.runBucketPrevCode = b.runBucketPrevCode)
    (hRBNext : a.runBucketNextCode = b.runBucketNextCode)
    -- WS-ZA ZA4.6: and the reply-waiter links and ends.
    (hWPrev : a.replyWaiterPrevCode = b.replyWaiterPrevCode)
    (hWNext : a.replyWaiterNextCode = b.replyWaiterNextCode)
    (hWHead : a.replyWaitersHeadCode = b.replyWaitersHeadCode)
    (hWCount : a.replyWaitersCount = b.replyWaitersCount)
    -- WS-ZA ZA4.7: and what a blocked sender's capability contributed.
    (hIBadge : a.ipcBadge = b.ipcBadge) (hIBadged : a.ipcBadged = b.ipcBadged)
    (hIGrant : a.ipcCanGrant = b.ipcCanGrant) (hIFault : a.ipcFaultSend = b.ipcFaultSend)
    -- and the context it is the recorded donation origin of.
    (hOrigin : a.originScCode = b.originScCode)
    -- WS-ZA ZA5.11: and its taint words.
    (hTaint : a.taintWords = b.taintWords)
    -- WS-ZA ZA6.6: and the context it has yielded to.
    (hYield : a.yieldToCode = b.yieldToCode) :
    a = b := by
  have hNPrevC : a.ntfnPrevCode = b.ntfnPrevCode := by
    rw [← TCB.optCode_ntfnPrev a, ← TCB.optCode_ntfnPrev b, hNPrev]
  have hNNextC : a.ntfnNextCode = b.ntfnNextCode := by
    rw [← TCB.optCode_ntfnNext a, ← TCB.optCode_ntfnNext b, hNNext]
  clear hNPrev hNNext
  have hQPrevC : a.queuePrevCode = b.queuePrevCode := by
    rw [TCB.queuePrevCode_eq a, TCB.queuePrevCode_eq b, hQPrev]
  have hQPPrevC : a.queuePPrevCode = b.queuePPrevCode := by
    rw [TCB.queuePPrevCode_eq a, TCB.queuePPrevCode_eq b, hQPPrev]
  have hQNextC : a.queueNextCode = b.queueNextCode := by
    rw [TCB.queueNextCode_eq a, TCB.queueNextCode_eq b, hQNext]
  clear hQPrev hQPPrev hQNext
  obtain ⟨hIpcO, hIpcS⟩ := TCB.ipcState_ext hIpc
  clear hIpc
  have hReplyC : a.replyObjectCode = b.replyObjectCode := by
    rw [← SeLe4n.ReplyId.optCode_ofOptCode a.replyObjectCode,
      ← SeLe4n.ReplyId.optCode_ofOptCode b.replyObjectCode]
    exact congrArg _ hReply
  have hPendReplyC : a.pendingReceiveReplyCode = b.pendingReceiveReplyCode := by
    rw [← SeLe4n.ReplyId.optCode_ofOptCode a.pendingReceiveReplyCode,
      ← SeLe4n.ReplyId.optCode_ofOptCode b.pendingReceiveReplyCode]
    exact congrArg _ hPendReply
  have hBnC : a.boundNotificationCode = b.boundNotificationCode := by
    rw [← SeLe4n.ObjId.optCode_ofOptCode a.boundNotificationCode,
      ← SeLe4n.ObjId.optCode_ofOptCode b.boundNotificationCode]
    exact congrArg _ hBn
  have hPipC : a.pipBoostCode = b.pipBoostCode := by
    rw [← SeLe4n.Priority.optCode_ofOptCode a.pipBoostCode,
      ← SeLe4n.Priority.optCode_ofOptCode b.pipBoostCode]
    exact congrArg _ hPip
  clear hReply hPendReply hPip hBn
  simp only [TCB.taintWords, SeLe4n.Kernel.TaintWords.mk.injEq] at hTaint
  obtain ⟨hT0, hT1, hT2, hT3, hT4, hT5, hT6, hT7, hTC, hTS⟩ := hTaint
  cases a; cases b
  simp at *
  exact ⟨hTid, hPrio, hDom, hCells, hLinks, hBuf, hIpcO, hTs, hSlice, hDeadline,
         hQPrevC, hQPPrevC, hQNextC, hPend, hRC, hFhS, hFhW, hBnC, hScC, hScO, hTb, hMcp, hPipC, hTo,
         hCpuAff, hReplyC, hPendReplyC, hPendFault, hFp, hNPrevC, hNNextC,
         hRCore, hRPrio, hRPrev, hRNext, hRBPrev, hRBNext, hWPrev, hWNext, hWHead, hWCount,
         hIpcS, hIBadge, hIBadged, hIGrant, hIFault, hOrigin, Subsingleton.elim _ _,
         hT0, hT1, hT2, hT3, hT4, hT5, hT6, hT7, hTC, hTS, hYield⟩

/-- A thread's spare space cells are logically one value (`SpareCells`). -/
@[simp] theorem TCB.with_spaceSpare (t : TCB) (v : SpareCells) : { t with spaceSpare := v } = t := by
  cases t; congr; exact Subsingleton.elim _ _

/-- Intrusive FIFO queue metadata for endpoint wait queues.

Queue membership links are stored in the waiting TCBs (`queuePrev`/`queueNext`).
The endpoint stores only queue boundaries. -/
structure IntrusiveQueue where
  head : Option SeLe4n.ThreadId := none
  tail : Option SeLe4n.ThreadId := none
  deriving Repr, DecidableEq

/-- **WS-RR RR8.4**: the queue boundaries a removal writes — the third and last
piece of "what does unlinking `removed` write", beside `queueUnlinkPredecessor`
and `queueUnlinkSuccessor` above.

`head` and `tail` are read off **the queue's own fields**: a boundary moves
exactly when it named the removed thread, and to that thread's link on the
matching side.  The removal's two spellings differed here and this is the robust
one, which is why it is the survivor rather than an arbitrary pick.

The two spellings asked **different questions about the same fact**, and that is
the whole of their divergence.  Both moved the head on `q.head = some tid`; for
the tail, `endpointQueueRemove` asked `q.tail = some tid` while
`endpointQueueRemoveDual` asked `removed.queueNext = none` and, on a `some`,
derived the new tail from `queuePPrev` (`none` at the head, the predecessor
otherwise — which `queuePPrevAgreesWithPrev` makes exactly `removed.queuePrev`).
Under a connected queue the two conditions coincide; the bundle constrains a queue
only at its boundaries and joins them nowhere, so on a state it admits — a queued
thread with no successor that is not the tail — they part.  There the inferring
form clears the tail and **strands the queue's real tail**, a thread that can then
never be dequeued, which is the defect class WS-OD OD3.9 reported.

**`q.tail = some tid` is the fact and `removed.queueNext = none` is a proxy for
it**, so this definition asks the fact — which leaves the *other* direction to be
established rather than assumed, because clearing a head without clearing a tail
breaks `intrusiveQueueWellFormed`.  The dual **checks** the two answers agree
(`queueTailPairAgrees`, the first factor of `dualQueueRemovalGuard`) and
**refuses** the state outright, which is fail-closed where the inference was
fail-open.  `endpointQueueRemove` validates nothing, so it still performs that
removal — but every statement about it is conditioned on the dual being enabled
(`dualRemovalEnabled`), so the guard discharges what used to be assumed and
WS-OD OD1.3's `spliceRemovedIsTailWhenLast` is **deleted** rather than kept
beside its replacement.

The fact did not vanish, and a reader should not take the deletion for its
closure: queue connectivity is still a missing invariant, and it is now
`dualQueueRemovalGuardHolds`'s `hTailLast` — an obligation on whoever *calls* a
removal, where it is discharged from where the thread sits in the queue, rather
than one carried by every theorem *about* one. -/
def queueRemoveBoundary (q : IntrusiveQueue) (tid : SeLe4n.ThreadId) (removed : TCB) :
    IntrusiveQueue :=
  { head := if q.head = some tid then removed.queueNext else q.head,
    tail := if q.tail = some tid then removed.queuePrev else q.tail }

/-- The head moves only when it named the removed thread. -/
@[simp] theorem queueRemoveBoundary_head_of_head
    {q : IntrusiveQueue} {tid : SeLe4n.ThreadId} {removed : TCB} (h : q.head = some tid) :
    (queueRemoveBoundary q tid removed).head = removed.queueNext := by
  unfold queueRemoveBoundary; simp [h]

@[simp] theorem queueRemoveBoundary_head_of_not_head
    {q : IntrusiveQueue} {tid : SeLe4n.ThreadId} {removed : TCB} (h : q.head ≠ some tid) :
    (queueRemoveBoundary q tid removed).head = q.head := by
  unfold queueRemoveBoundary; simp [h]

/-- The tail moves only when it named the removed thread. -/
@[simp] theorem queueRemoveBoundary_tail_of_tail
    {q : IntrusiveQueue} {tid : SeLe4n.ThreadId} {removed : TCB} (h : q.tail = some tid) :
    (queueRemoveBoundary q tid removed).tail = removed.queuePrev := by
  unfold queueRemoveBoundary; simp [h]

@[simp] theorem queueRemoveBoundary_tail_of_not_tail
    {q : IntrusiveQueue} {tid : SeLe4n.ThreadId} {removed : TCB} (h : q.tail ≠ some tid) :
    (queueRemoveBoundary q tid removed).tail = q.tail := by
  unfold queueRemoveBoundary; simp [h]

-- ============================================================================
-- WS-RR RR8.5: the removal guard, in the model beside the fields it reads
-- ============================================================================

/-- **WS-RR RR8.5**: `endpointQueueRemoveDual`'s precondition lives here, not in
`Kernel/IPC/DualQueue/Core.lean`, and the move is the whole of a finding RR8.4
registered rather than closed.

The guard is a predicate over `(IntrusiveQueue, ThreadId, TCB, QueuePPrev)` —
model types, with no kernel dependency — and `SeLe4n/Kernel/FrozenOps/Core.lean`
imports only `Model.FrozenState` and `Model.FreezeProofs`, deliberately, the
frozen surface being a thin layer over the model.  So while the guard sat in the
IPC layer the frozen mirror **could not carry it**, and `frozenQueueRemove`
refused only `queuePPrev.isNone` where `endpointQueueRemoveDual` refuses a
pairing violation, a position violation and a tail disagreement: the mirror
**succeeded where the kernel refuses**, which is the direction that matters on a
differential surface — `frozenRunAgrees` then reports agreement on states the
kernel never reaches and says nothing about the three it declines.

What stays in the kernel is what genuinely needs the store: the *discharges*
(`dualQueueRemovalGuardHolds`, `…_of_dualQueueSystemInvariant`,
`queueTailPairAgrees_of_wellFormed`, `queuePPrevHeadPositionAgrees_of_member`)
read `intrusiveQueueWellFormed`, `tcbQueueLinkIntegrity`, the store-level
`queuePPrevAgreesWithPrev` and `QueueNextPath`.  The guard is model-level; its
discharges are kernel-level, and the layering now says so.

`tcbWithQueueLinks` comes with it as the third member of the link-write family
(`queueUnlinkPredecessor` / `queueUnlinkSuccessor` above), which is where WS-OD
OD3.9 said what unlinking writes belongs. -/
def tcbWithQueueLinks
    (tcb : TCB)
    (prev : Option SeLe4n.ThreadId)
    (pprev : Option QueuePPrev)
    (next : Option SeLe4n.ThreadId) : TCB :=
  { tcb with queuePrevCode := SeLe4n.ThreadId.optCode prev,
             queuePPrevCode := QueuePPrev.optCode pprev,
             queueNextCode := SeLe4n.ThreadId.optCode next }

@[simp] theorem tcbWithQueueLinks_queuePrev (tcb : TCB) (prev pprev next) :
    (tcbWithQueueLinks tcb prev pprev next).queuePrev = prev := by
  simp [tcbWithQueueLinks]

@[simp] theorem tcbWithQueueLinks_queuePPrev (tcb : TCB) (prev pprev next) :
    (tcbWithQueueLinks tcb prev pprev next).queuePPrev = pprev := by
  simp [tcbWithQueueLinks]

@[simp] theorem tcbWithQueueLinks_queueNext (tcb : TCB) (prev pprev next) :
    (tcbWithQueueLinks tcb prev pprev next).queueNext = next := by
  simp [tcbWithQueueLinks]

/-- **WS-RR RR8.3**: the pairing condition on the *values* a link store writes.

`tcbWithQueueLinks` overwrites all three link fields at once, so whether the
result satisfies `TCB.queuePPrevAgreesWithPrev` depends on the arguments alone
and not on the record displaced.  Naming that condition is what lets each
queue-writing call site state its own obligation — which is the whole content of
the invariant: `endpointQueueEnqueue` discharges it because it writes
`(none, .endpointHead)` on an empty queue and `(some t, .tcbNext t)` behind a
tail, `endpointQueuePopHead` because it promotes the successor to
`(none, .endpointHead)`, and every clear because it writes `(none, none)`.

**Strengthened at `v0.35.99` with `TCB.queuePPrevAgreesWithPrev`**, whose `none`
arm this is: a `pprev` of `none` says the node is on no queue, so writing it
beside a `prev` of `some p` is the stranding shape (see the record-level
predicate for the two-node queue that exhibited it).  Free for
`dualQueueRemovalGuard`, which applies this at a `QueuePPrev` rather than an
`Option` and so never reaches the arm. -/
def queueLinkPairAgrees
    (prev : Option SeLe4n.ThreadId) (pprev : Option QueuePPrev) : Prop :=
  match pprev with
  | none => prev = none
  | some .endpointHead => prev = none
  | some (.tcbNext p) => prev = some p

@[simp] theorem queueLinkPairAgrees_none :
    queueLinkPairAgrees none none := rfl

@[simp] theorem queueLinkPairAgrees_endpointHead :
    queueLinkPairAgrees none (some .endpointHead) := rfl

@[simp] theorem queueLinkPairAgrees_tcbNext (p : SeLe4n.ThreadId) :
    queueLinkPairAgrees (some p) (some (.tcbNext p)) := rfl

/-- The pairing is decidable: each arm is an equality of `Option ThreadId`.  The
instance is what lets `dualQueueRemovalGuard`'s `Bool` check be stated as the
conjunction of a position question and *this* proposition, rather than as a second
spelling of it. -/
instance queueLinkPairAgrees_decidable
    (prev : Option SeLe4n.ThreadId) (pprev : Option QueuePPrev) :
    Decidable (queueLinkPairAgrees prev pprev) := by
  unfold queueLinkPairAgrees
  cases pprev with
  | none => exact inferInstanceAs (Decidable (prev = none))
  | some pp => cases pp with
    | endpointHead => exact inferInstanceAs (Decidable (prev = none))
    | tcbNext p => exact inferInstanceAs (Decidable (prev = some p))

/-- **WS-RR RR8.3**: a TCB's *own* pair agrees whenever it satisfies the pairing
— the shape every `storeTcbQueueLinks st p tcb.queuePrev tcb.queuePPrev _` site
needs, which is how a removal re-writes a neighbour's `queueNext` without
disturbing the two fields it must keep together. -/
theorem queueLinkPairAgrees_of_tcb {tcb : TCB}
    (h : tcb.queuePPrevAgreesWithPrev) :
    queueLinkPairAgrees tcb.queuePrev tcb.queuePPrev := by
  unfold TCB.queuePPrevAgreesWithPrev at h
  unfold queueLinkPairAgrees
  cases hpp : tcb.queuePPrev with
  | none => rw [hpp] at h; exact h
  | some pp =>
      rw [hpp] at h; cases pp with
      | endpointHead => exact h
      | tcbNext p => exact h

/-- The written record satisfies the pairing exactly when the written values do. -/
theorem tcbWithQueueLinks_queuePPrevAgreesWithPrev
    {tcb : TCB} {prev : Option SeLe4n.ThreadId} {pprev : Option QueuePPrev}
    {next : Option SeLe4n.ThreadId} (h : queueLinkPairAgrees prev pprev) :
    (tcbWithQueueLinks tcb prev pprev next).queuePPrevAgreesWithPrev := by
  unfold TCB.queuePPrevAgreesWithPrev tcbWithQueueLinks
  simp only [TCB.queuePPrev_mk, TCB.queuePrev_mk, QueuePPrev.ofOptCode_optCode,
    SeLe4n.ThreadId.ofOptCode_optCode]
  unfold queueLinkPairAgrees at h
  cases pprev with
  | none => exact h
  | some pp => cases pp with
    | endpointHead => exact h
    | tcbNext p => exact h

/-- **WS-RR RR8.3**: the head-position half of `endpointQueueRemoveDual`'s
precondition — a node whose back-pointer names the endpoint's head field *is* the
head, and one whose back-pointer names a predecessor TCB is not.

Split out from the pairing half because the two are discharged from different
places: this one from where `tid` sits in `q`, the other from the invariant.  A
caller that can supply neither is a caller that should not be unlinking. -/
def queuePPrevHeadPositionAgrees
    (q : IntrusiveQueue) (tid : SeLe4n.ThreadId) (pprev : QueuePPrev) : Bool :=
  match pprev with
  | .endpointHead => q.head = some tid
  | .tcbNext _ => q.head ≠ some tid

/-- **WS-RR RR8.4**: the tail half — the queue's `tail` field and the removed
thread's `queueNext` field must agree about whether this thread is the tail.

The *pair* is the point, as it is for `queueLinkPairAgrees` one field over.  A
removal has two ways to ask "is this the tail?" — read `q.tail`, or observe that
the thread has no successor — and `queueRemoveBoundary` asks the first, because
`q.tail = some tid` is the fact and `queueNext = none` is a proxy for it.  Asking
the fact means the *proxy's* direction has to be established: clearing a head
without clearing the tail leaves a queue that fails
`intrusiveQueueWellFormed`, and the bundle joins a queue's boundaries nowhere, so
nothing entails it — the connectivity WS-OD OD1.3 stated as a hypothesis on every
theorem about a removal, which RR8.4 deleted in favour of this check.

So `endpointQueueRemoveDual` **checks** it.  One direction is free from the
bundle — `intrusiveQueueWellFormed`'s third clause gives a tail no successor, so
a thread with one is not the tail (`spliceTail_ne_of_hasNext`) — and the other is
the missing invariant, which is why this is a runtime guard rather than a
conjunct.  The biconditional is stated because it is what "the tail question has
one answer" means; refusing the free direction as well costs nothing, since the
bundle already excludes it. -/
def queueTailPairAgrees (q : IntrusiveQueue) (tid : SeLe4n.ThreadId) (removed : TCB) : Bool :=
  (q.tail = some tid) == removed.queueNext.isNone

/-- `queueTailPairAgrees` as a proposition about the two fields. -/
theorem queueTailPairAgrees_iff
    {q : IntrusiveQueue} {tid : SeLe4n.ThreadId} {removed : TCB} :
    queueTailPairAgrees q tid removed = true ↔
      (q.tail = some tid ↔ removed.queueNext = none) := by
  unfold queueTailPairAgrees
  cases hn : removed.queueNext <;> simp

/-- The tail is cleared exactly when the removed thread had no successor — the
form `queueRemoveBoundary`'s consumers need once the guard has passed. -/
theorem queueTailPairAgrees_tail_of_no_next
    {q : IntrusiveQueue} {tid : SeLe4n.ThreadId} {removed : TCB}
    (hAgree : queueTailPairAgrees q tid removed = true) (hNext : removed.queueNext = none) :
    q.tail = some tid :=
  (queueTailPairAgrees_iff.mp hAgree).mpr hNext

/-- A thread with a successor is not the tail — the direction
`intrusiveQueueWellFormed` already carries, read off the guard. -/
theorem queueTailPairAgrees_tail_ne_of_next
    {q : IntrusiveQueue} {tid next : SeLe4n.ThreadId} {removed : TCB}
    (hAgree : queueTailPairAgrees q tid removed = true) (hNext : removed.queueNext = some next) :
    q.tail ≠ some tid := by
  intro hTail
  rw [(queueTailPairAgrees_iff.mp hAgree).mp hTail] at hNext
  exact absurd hNext (by simp)

/-- **WS-RR RR8.4**: the four shapes a *guarded* removal writes to the queue's
boundaries, named after the four cases the removal splits on — whether the thread
is the head, and whether it has a successor.

`queueRemoveBoundary` reads `q.tail` and the guard supplies the bridge to
`removed.queueNext`, so each shape needs only the head and successor facts the
branch already has.  These are the forms `endpointQueueRemoveDual`'s invariant
proofs and `endpointQueueRemove_agrees_*` both consume: one derivation of "what
does this branch write", rather than one per proof. -/
theorem queueRemoveBoundary_headLast
    {q : IntrusiveQueue} {tid : SeLe4n.ThreadId} {removed : TCB}
    (hPair : queueTailPairAgrees q tid removed = true)
    (hHead : q.head = some tid) (hNext : removed.queueNext = none)
    (hPrev : removed.queuePrev = none) :
    queueRemoveBoundary q tid removed = {} := by
  unfold queueRemoveBoundary
  simp [hHead, hNext, hPrev, queueTailPairAgrees_tail_of_no_next hPair hNext]

theorem queueRemoveBoundary_headMore
    {q : IntrusiveQueue} {tid next : SeLe4n.ThreadId} {removed : TCB}
    (hPair : queueTailPairAgrees q tid removed = true)
    (hHead : q.head = some tid) (hNext : removed.queueNext = some next) :
    queueRemoveBoundary q tid removed = { head := some next, tail := q.tail } := by
  unfold queueRemoveBoundary
  simp [hHead, hNext, queueTailPairAgrees_tail_ne_of_next hPair hNext]

theorem queueRemoveBoundary_midLast
    {q : IntrusiveQueue} {tid : SeLe4n.ThreadId} {removed : TCB}
    (hPair : queueTailPairAgrees q tid removed = true)
    (hHeadNe : q.head ≠ some tid) (hNext : removed.queueNext = none) :
    queueRemoveBoundary q tid removed = { head := q.head, tail := removed.queuePrev } := by
  unfold queueRemoveBoundary
  simp [hHeadNe, queueTailPairAgrees_tail_of_no_next hPair hNext]

theorem queueRemoveBoundary_midMore
    {q : IntrusiveQueue} {tid next : SeLe4n.ThreadId} {removed : TCB}
    (hPair : queueTailPairAgrees q tid removed = true)
    (hHeadNe : q.head ≠ some tid) (hNext : removed.queueNext = some next) :
    queueRemoveBoundary q tid removed = { head := q.head, tail := q.tail } := by
  unfold queueRemoveBoundary
  simp [hHeadNe, queueTailPairAgrees_tail_ne_of_next hPair hNext]

/-- **WS-RR RR8.3**: `endpointQueueRemoveDual`'s `pprevConsistent` check, named.

The operation reads *this* definition, so the check and the theorem that
discharges it (`dualQueueRemovalGuardHolds`) cannot describe different
conditions.  Before RR8.3 it was an anonymous `let` inside the transition, which
is why nothing could state that a caller had established it. -/
def dualQueueRemovalGuard
    (q : IntrusiveQueue) (tid : SeLe4n.ThreadId) (tcb : TCB) (pprev : QueuePPrev) : Bool :=
  queueTailPairAgrees q tid tcb &&
    match pprev with
    | .endpointHead => q.head = some tid && tcb.queuePrev.isNone
    | .tcbNext prevTid => q.head ≠ some tid && tcb.queuePrev = some prevTid

/-- **WS-RR RR8.3**, extended by **RR8.4**: the guard factors into three
questions — where `tid` sits in `q`, whether its two back-pointer fields pair,
and whether the queue's tail field and its `queueNext` agree.

This is the statement that makes the fourth `dualQueueSystemInvariant` conjunct
worth having: the invariant discharges the *pairing* factor system-wide, and
`intrusiveQueueWellFormed` discharges one direction of the tail factor, leaving
the caller the position and the queue connectivity nothing entails.  It is stated
as an equality of `Bool`s rather than an `Iff` so it rewrites inside the
transition's own `if`. -/
theorem dualQueueRemovalGuard_eq_position_and_pair
    (q : IntrusiveQueue) (tid : SeLe4n.ThreadId) (tcb : TCB) (pprev : QueuePPrev) :
    dualQueueRemovalGuard q tid tcb pprev =
      (queueTailPairAgrees q tid tcb && queuePPrevHeadPositionAgrees q tid pprev &&
        decide (queueLinkPairAgrees tcb.queuePrev (some pprev))) := by
  unfold dualQueueRemovalGuard queuePPrevHeadPositionAgrees queueLinkPairAgrees
  cases pprev with
  | endpointHead => cases tcb.queuePrev <;> simp
  | tcbNext p =>
    cases tcb.queuePrev with
    | none => simp
    | some v => simp [Bool.and_assoc]

/-- **`v0.35.59`**: a removal needs a queue with both boundaries populated.

Named because it is the *second* thing `endpointQueueRemoveDual` refuses, and the
frozen mirror refused none of them: a mirror that carries the named guard and not
its unnamed neighbours still succeeds where the kernel refuses.  Spelled exactly
as the transition spelled it inline, with a `@[simp]` equation, so every proof
that reasoned through the old `if` sees the same term. -/
def queueBoundariesEmpty (q : IntrusiveQueue) : Bool :=
  q.head.isNone || q.tail.isNone

@[simp] theorem queueBoundariesEmpty_eq (q : IntrusiveQueue) :
    queueBoundariesEmpty q = (q.head.isNone || q.tail.isNone) := rfl

/-- **`v0.35.59`**: the *whole* store-free precondition of a dual-queue removal.

`dualQueueRemovalGuard` is one of two conditions `endpointQueueRemoveDual` checks
before it writes anything, and naming only the one it discharges from an invariant
is what let the frozen mirror carry a **subset** of the refusal set while reading
a shared definition.  Both removals read this, so a condition added here reaches
both by construction — the difference between sharing an answer and sharing the
*question*. -/
def dualQueueRemovalEnabled
    (q : IntrusiveQueue) (tid : SeLe4n.ThreadId) (tcb : TCB) (pprev : QueuePPrev) : Bool :=
  !queueBoundariesEmpty q && dualQueueRemovalGuard q tid tcb pprev

@[simp] theorem dualQueueRemovalEnabled_eq
    (q : IntrusiveQueue) (tid : SeLe4n.ThreadId) (tcb : TCB) (pprev : QueuePPrev) :
    dualQueueRemovalEnabled q tid tcb pprev =
      (!(q.head.isNone || q.tail.isNone) && dualQueueRemovalGuard q tid tcb pprev) := rfl

/-- The guard half of the enabling condition. -/
theorem dualQueueRemovalEnabled_guard
    {q : IntrusiveQueue} {tid : SeLe4n.ThreadId} {tcb : TCB} {pprev : QueuePPrev}
    (h : dualQueueRemovalEnabled q tid tcb pprev = true) :
    dualQueueRemovalGuard q tid tcb pprev = true := by
  unfold dualQueueRemovalEnabled at h
  exact (Bool.and_eq_true .. |>.mp h).2

/-- The populated-boundaries half. -/
theorem dualQueueRemovalEnabled_boundaries
    {q : IntrusiveQueue} {tid : SeLe4n.ThreadId} {tcb : TCB} {pprev : QueuePPrev}
    (h : dualQueueRemovalEnabled q tid tcb pprev = true) :
    queueBoundariesEmpty q = false := by
  unfold dualQueueRemovalEnabled at h
  have := (Bool.and_eq_true .. |>.mp h).1
  simpa using this

/-- **`v0.35.59`**: the predecessor's own forward link must name the thread being
removed.  The third refusal the frozen mirror lacked, and the one that needs a
store lookup, so each side resolves `prevTcb` itself and both read this. -/
def queuePredecessorNamesSuccessor (prevTcb : TCB) (tid : SeLe4n.ThreadId) : Bool :=
  prevTcb.queueNext = some tid

@[simp] theorem queuePredecessorNamesSuccessor_eq (prevTcb : TCB) (tid : SeLe4n.ThreadId) :
    queuePredecessorNamesSuccessor prevTcb tid = decide (prevTcb.queueNext = some tid) := rfl

/-- **WS-RR RR8.4**: the tail factor, read straight off the guard.  Consumers
reach for this rather than re-deriving it from the factorisation. -/
theorem dualQueueRemovalGuard_tail_half
    {q : IntrusiveQueue} {tid : SeLe4n.ThreadId} {tcb : TCB} {pprev : QueuePPrev}
    (hGuard : dualQueueRemovalGuard q tid tcb pprev = true) :
    queueTailPairAgrees q tid tcb = true := by
  unfold dualQueueRemovalGuard at hGuard
  exact (Bool.and_eq_true .. |>.mp hGuard).1

/-- **WS-RR RR8.3**: the pairing half of the guard, discharged from the
`TCB`-level predicate the fourth conjunct lifts. -/
theorem dualQueueRemovalGuard_pair_half {tcb : TCB} {pprev : QueuePPrev}
    (hPPrev : tcb.queuePPrev = some pprev) (hPair : tcb.queuePPrevAgreesWithPrev) :
    queueLinkPairAgrees tcb.queuePrev (some pprev) := by
  have h := queueLinkPairAgrees_of_tcb hPair
  rw [hPPrev] at h
  exact h

/-- **The service record an endpoint holds**, read as one value: whether a
service is registered on the endpoint, and the registration's words — the
interface it implements and the capability the registration keeps, less that
capability's target, which is the endpoint itself.  The endpoint stores these as
scalar fields of its own (`Endpoint.serviceRegistered` and the `service*`
fields), so a registration is a write in the endpoint's slot and builds no
record; this structure is the view proofs and specifications read
(`Endpoint.service`), never a stored field.  The default is the clear record a
carved endpoint starts with and a revocation leaves. -/
structure EndpointService where
  registered      : Bool := false
  interfaceId     : SeLe4n.InterfaceId := default
  methodCount     : Nat := 0
  maxMessageSize  : Nat := 0
  maxResponseSize : Nat := 0
  requiresGrant   : Bool := false
  capRights       : AccessRightSet := AccessRightSet.empty
  capBadgeWord    : SeLe4n.Badge := SeLe4n.Badge.zero
  capBadged       : Bool := false
  capMapAsid      : SeLe4n.ASID := default
  capMapVaddr     : SeLe4n.VAddr := default
  capMapEpoch     : Nat := 0
  capMapped       : Bool := false
  capFreeIndex    : Nat := 0
  deriving Repr, DecidableEq

instance : Inhabited EndpointService := ⟨{}⟩

/-- Endpoint object model.

WS-H12a: Endpoint structure uses only intrusive dual-queue fields.
Legacy WS-E3 fields (`state`, `queue`, `waitingReceiver`) and the
`EndpointState` type have been removed — all IPC operations use the O(1)
dual-queue path (`endpointSendDual`/`endpointReceiveDual`).

WS-LS LS3.1: the endpoint's lock is a key of the ghost lock table
(`Concurrency/Locks/LockState.lean`), not a field; IPC transitions
(`endpointSendDual`, `endpointReceiveDual`, `endpointCallDual`) declare it in
write mode and lookups in read mode. -/
structure Endpoint where
  /-- WS-ZA ZA4.7: the send queue's head, as a scalar code
      (`SeLe4n.ThreadId.optCode`); read through `Endpoint.sendQ`. -/
  sendHeadCode : Nat := 0
  /-- The send queue's tail, as a scalar code. -/
  sendTailCode : Nat := 0
  /-- The receive queue's head, as a scalar code; read through
      `Endpoint.receiveQ`. -/
  recvHeadCode : Nat := 0
  /-- The receive queue's tail, as a scalar code. -/
  recvTailCode : Nat := 0
  /-- **Whether a service registration holds a capability to this endpoint**:
      set by `registerService`, cleared by the revocation of that registration.
      A service's identity is its endpoint's (`ServiceRegistration.sid`), so the
      flag names the registration without encoding an identity of its own.  A
      registration keeps its endpoint capability outside every slot, so the
      finality the tree answers does not see it; this back-reference is what a
      final delete reads instead of walking the registry
      (`SystemState.tableReferencesRecorded`).  A carved endpoint starts clear. -/
  serviceRegistered : Bool := false
  /-- **The registration's words** (WS-ZA ZA5.8), meaningful only while
      `serviceRegistered` is set: the interface the service implements, and the
      capability the registration keeps, as plain words with flags, as a
      capability holds its badge and mapping.  The capability's target is not
      stored: it is this endpoint.  Read through `Endpoint.service`; written by
      `registerService` and cleared by the revocation. -/
  serviceInterfaceId : SeLe4n.InterfaceId := default
  /-- The interface's method count. -/
  serviceMethodCount : Nat := 0
  /-- The interface's request bound, in message registers. -/
  serviceMaxMessageSize : Nat := 0
  /-- The interface's response bound, in message registers. -/
  serviceMaxResponseSize : Nat := 0
  /-- Whether invoking the interface requires the grant right. -/
  serviceRequiresGrant : Bool := false
  /-- The kept capability's rights. -/
  serviceCapRights : AccessRightSet := AccessRightSet.empty
  /-- The kept capability's badge word, meaningful only when `serviceCapBadged`. -/
  serviceCapBadgeWord : SeLe4n.Badge := SeLe4n.Badge.zero
  /-- Whether the kept capability carries a badge. -/
  serviceCapBadged : Bool := false
  /-- The kept capability's mapping ASID, meaningful only when `serviceCapMapped`. -/
  serviceCapMapAsid : SeLe4n.ASID := default
  /-- The kept capability's mapping address. -/
  serviceCapMapVaddr : SeLe4n.VAddr := default
  /-- The kept capability's mapping epoch. -/
  serviceCapMapEpoch : Nat := 0
  /-- Whether the kept capability records a mapping. -/
  serviceCapMapped : Bool := false
  /-- The kept capability's free index. -/
  serviceCapFreeIndex : Nat := 0
  deriving Repr, DecidableEq

/-- The send queue's boundaries, read from their codes.  The endpoint keeps
the four ends as scalar fields of its own (WS-ZA ZA4.7), so a write of one
queue's ends rewrites the endpoint in place and builds no `some` cell and no
queue record. -/
@[inline] def Endpoint.sendQ (e : Endpoint) : IntrusiveQueue :=
  { head := SeLe4n.ThreadId.ofOptCode e.sendHeadCode,
    tail := SeLe4n.ThreadId.ofOptCode e.sendTailCode }

/-- The receive queue's boundaries, read from their codes. -/
@[inline] def Endpoint.receiveQ (e : Endpoint) : IntrusiveQueue :=
  { head := SeLe4n.ThreadId.ofOptCode e.recvHeadCode,
    tail := SeLe4n.ThreadId.ofOptCode e.recvTailCode }

/-- The endpoint with its send queue's ends replaced. -/
@[inline] def Endpoint.withSendQ (e : Endpoint) (q : IntrusiveQueue) : Endpoint :=
  { e with sendHeadCode := SeLe4n.ThreadId.optCode q.head,
           sendTailCode := SeLe4n.ThreadId.optCode q.tail }

/-- The endpoint with its receive queue's ends replaced. -/
@[inline] def Endpoint.withReceiveQ (e : Endpoint) (q : IntrusiveQueue) : Endpoint :=
  { e with recvHeadCode := SeLe4n.ThreadId.optCode q.head,
           recvTailCode := SeLe4n.ThreadId.optCode q.tail }

/-- The endpoint whose queues are `s` and `r`. -/
@[inline] def Endpoint.ofQueues (s r : IntrusiveQueue) : Endpoint :=
  { sendHeadCode := SeLe4n.ThreadId.optCode s.head,
    sendTailCode := SeLe4n.ThreadId.optCode s.tail,
    recvHeadCode := SeLe4n.ThreadId.optCode r.head,
    recvTailCode := SeLe4n.ThreadId.optCode r.tail }

/-- **The endpoint's service record** (WS-ZA ZA5.8), read from its fields. -/
@[inline] def Endpoint.service (e : Endpoint) : EndpointService :=
  { registered := e.serviceRegistered, interfaceId := e.serviceInterfaceId,
    methodCount := e.serviceMethodCount, maxMessageSize := e.serviceMaxMessageSize,
    maxResponseSize := e.serviceMaxResponseSize, requiresGrant := e.serviceRequiresGrant,
    capRights := e.serviceCapRights, capBadgeWord := e.serviceCapBadgeWord,
    capBadged := e.serviceCapBadged, capMapAsid := e.serviceCapMapAsid,
    capMapVaddr := e.serviceCapMapVaddr, capMapEpoch := e.serviceCapMapEpoch,
    capMapped := e.serviceCapMapped, capFreeIndex := e.serviceCapFreeIndex }

/-- The endpoint with its service record written as `sv`'s words, its queues
untouched: a registration sets it, a revocation clears it. -/
@[inline] def Endpoint.withService (e : Endpoint) (sv : EndpointService) : Endpoint :=
  { e with serviceRegistered := sv.registered, serviceInterfaceId := sv.interfaceId,
           serviceMethodCount := sv.methodCount, serviceMaxMessageSize := sv.maxMessageSize,
           serviceMaxResponseSize := sv.maxResponseSize,
           serviceRequiresGrant := sv.requiresGrant, serviceCapRights := sv.capRights,
           serviceCapBadgeWord := sv.capBadgeWord, serviceCapBadged := sv.capBadged,
           serviceCapMapAsid := sv.capMapAsid, serviceCapMapVaddr := sv.capMapVaddr,
           serviceCapMapEpoch := sv.capMapEpoch, serviceCapMapped := sv.capMapped,
           serviceCapFreeIndex := sv.capFreeIndex }

namespace Endpoint

@[simp] theorem service_registered (e : Endpoint) : e.service.registered = e.serviceRegistered :=
  rfl

@[simp] theorem service_withService (e : Endpoint) (sv : EndpointService) :
    (e.withService sv).service = sv := rfl

@[simp] theorem serviceRegistered_withService (e : Endpoint) (sv : EndpointService) :
    (e.withService sv).serviceRegistered = sv.registered := rfl

@[simp] theorem sendQ_withService (e : Endpoint) (sv : EndpointService) :
    (e.withService sv).sendQ = e.sendQ := rfl

@[simp] theorem receiveQ_withService (e : Endpoint) (sv : EndpointService) :
    (e.withService sv).receiveQ = e.receiveQ := rfl

@[simp] theorem withService_withService (e : Endpoint) (a b : EndpointService) :
    (e.withService a).withService b = e.withService b := rfl

@[simp] theorem sendQ_withSendQ (e : Endpoint) (q : IntrusiveQueue) :
    (e.withSendQ q).sendQ = q := by
  simp only [sendQ, withSendQ, SeLe4n.ThreadId.ofOptCode_optCode]

@[simp] theorem receiveQ_withSendQ (e : Endpoint) (q : IntrusiveQueue) :
    (e.withSendQ q).receiveQ = e.receiveQ := rfl

@[simp] theorem sendQ_withReceiveQ (e : Endpoint) (q : IntrusiveQueue) :
    (e.withReceiveQ q).sendQ = e.sendQ := rfl

@[simp] theorem receiveQ_withReceiveQ (e : Endpoint) (q : IntrusiveQueue) :
    (e.withReceiveQ q).receiveQ = q := by
  simp only [receiveQ, withReceiveQ, SeLe4n.ThreadId.ofOptCode_optCode]

@[simp] theorem sendQ_ofQueues (s r : IntrusiveQueue) : (ofQueues s r).sendQ = s := by
  simp only [sendQ, ofQueues, SeLe4n.ThreadId.ofOptCode_optCode]

@[simp] theorem receiveQ_ofQueues (s r : IntrusiveQueue) : (ofQueues s r).receiveQ = r := by
  simp only [receiveQ, ofQueues, SeLe4n.ThreadId.ofOptCode_optCode]

/-- The send queue's head read from its code is the view's head. -/
theorem ofOptCode_sendHeadCode (e : Endpoint) :
    SeLe4n.ThreadId.ofOptCode e.sendHeadCode = e.sendQ.head := rfl

/-- The receive queue's head read from its code is the view's head. -/
theorem ofOptCode_recvHeadCode (e : Endpoint) :
    SeLe4n.ThreadId.ofOptCode e.recvHeadCode = e.receiveQ.head := rfl

/-- The receive queue's tail read from its code is the view's tail. -/
theorem ofOptCode_recvTailCode (e : Endpoint) :
    SeLe4n.ThreadId.ofOptCode e.recvTailCode = e.receiveQ.tail := rfl

/-- A write of the receive queue's head alone is a write of its code. -/
theorem withReceiveQ_head (e : Endpoint) (h : Option SeLe4n.ThreadId) :
    e.withReceiveQ { head := h, tail := e.receiveQ.tail } =
      { e with recvHeadCode := SeLe4n.ThreadId.optCode h } := by
  simp only [withReceiveQ, receiveQ, SeLe4n.ThreadId.optCode_ofOptCode]

/-- A write of the receive queue's tail alone is a write of its code. -/
theorem withReceiveQ_tail (e : Endpoint) (t : Option SeLe4n.ThreadId) :
    e.withReceiveQ { head := e.receiveQ.head, tail := t } =
      { e with recvTailCode := SeLe4n.ThreadId.optCode t } := by
  simp only [withReceiveQ, receiveQ, SeLe4n.ThreadId.optCode_ofOptCode]

/-- A write of the send queue's head alone is a write of its code. -/
theorem withSendQ_head (e : Endpoint) (h : Option SeLe4n.ThreadId) :
    e.withSendQ { head := h, tail := e.sendQ.tail } =
      { e with sendHeadCode := SeLe4n.ThreadId.optCode h } := by
  simp only [withSendQ, sendQ, SeLe4n.ThreadId.optCode_ofOptCode]

/-- A write of the send queue's tail alone is a write of its code. -/
theorem withSendQ_tail (e : Endpoint) (t : Option SeLe4n.ThreadId) :
    e.withSendQ { head := e.sendQ.head, tail := t } =
      { e with sendTailCode := SeLe4n.ThreadId.optCode t } := by
  simp only [withSendQ, sendQ, SeLe4n.ThreadId.optCode_ofOptCode]

@[simp] theorem sendQ_default : (({} : Endpoint)).sendQ = {} := rfl

@[simp] theorem receiveQ_default : (({} : Endpoint)).receiveQ = {} := rfl

/-- An endpoint is its two queues and the service record it holds: equal
    queues and equal records, equal endpoints. -/
theorem ext_queues {a b : Endpoint} (hs : a.sendQ = b.sendQ) (hr : a.receiveQ = b.receiveQ)
    (hc : a.service = b.service) : a = b := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18⟩ := a
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18⟩ := b
  simp only [sendQ, receiveQ, service, IntrusiveQueue.mk.injEq, EndpointService.mk.injEq]
    at hs hr hc
  obtain ⟨c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18⟩ := hc
  subst c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18
  have inj : ∀ {x y : Nat}, SeLe4n.ThreadId.ofOptCode x = SeLe4n.ThreadId.ofOptCode y → x = y :=
    fun {x y} h => by
      rw [← SeLe4n.ThreadId.optCode_ofOptCode x, h, SeLe4n.ThreadId.optCode_ofOptCode]
  rw [inj hs.1, inj hs.2, inj hr.1, inj hr.2]

theorem ext_queues_iff {a b : Endpoint} :
    a = b ↔ a.sendQ = b.sendQ ∧ a.receiveQ = b.receiveQ ∧ a.service = b.service :=
  ⟨fun h => h ▸ ⟨rfl, rfl, rfl⟩, fun ⟨hs, hr, hc⟩ => ext_queues hs hr hc⟩

@[simp] theorem withSendQ_sendQ (e : Endpoint) : e.withSendQ e.sendQ = e :=
  ext_queues (by simp) rfl rfl

@[simp] theorem withReceiveQ_receiveQ (e : Endpoint) : e.withReceiveQ e.receiveQ = e :=
  ext_queues rfl (by simp) rfl

@[simp] theorem withService_service (e : Endpoint) : e.withService e.service = e := rfl

@[simp] theorem service_withSendQ (e : Endpoint) (q : IntrusiveQueue) :
    (e.withSendQ q).service = e.service := rfl

@[simp] theorem service_withReceiveQ (e : Endpoint) (q : IntrusiveQueue) :
    (e.withReceiveQ q).service = e.service := rfl

@[simp] theorem serviceRegistered_withSendQ (e : Endpoint) (q : IntrusiveQueue) :
    (e.withSendQ q).serviceRegistered = e.serviceRegistered := rfl

@[simp] theorem serviceRegistered_withReceiveQ (e : Endpoint) (q : IntrusiveQueue) :
    (e.withReceiveQ q).serviceRegistered = e.serviceRegistered := rfl

end Endpoint

inductive NotificationState where
  | idle
  | waiting
  | active
  deriving Repr, DecidableEq

/-- Minimal notification object model for WS-B6.

`active` stores a single pending badge, while `waiting` tracks blocked receivers.

**The wait queue links through the waiting TCBs** (WS-ZA ZA4.4).  The
notification holds the queue's head and tail, as scalar codes
(`SeLe4n.ThreadId.optCode`), and each waiter its predecessor and successor
(`TCB.ntfnPrev`, `TCB.ntfnNext`).  A wait appends at the tail and a signal
wakes the head, first in first out as seL4's `tcbEPAppend`/`tcbEPDequeue`;
cancellation unlinks a waiter in place.  Nothing on these paths allocates:
the list this replaced built a cell for every wait. -/
structure Notification where
  state : NotificationState
  /-- The wait queue's head, as a scalar code; read through
      `Notification.waitHead`.  `0` when no thread waits. -/
  waitHeadCode : Nat := 0
  /-- The wait queue's tail, as a scalar code; read through
      `Notification.waitTail`. -/
  waitTailCode : Nat := 0
  /-- Whether a badge is pending.  The pending badge is stored as a flag plus a
      machine word (`pendingWord`) rather than an `Option SeLe4n.Badge`: an
      `Option` around a 64-bit scalar is a heap cell, so every signal that left
      a badge pending allocated.  As fields of the notification the flag and
      the word live in its scalar area and a signal updates them in place.
      Read the pair through `Notification.pendingBadge`; write it through
      `hasPendingBadge := false, pendingWord := SeLe4n.Badge.zero` (cleared) or
      `hasPendingBadge := true, pendingWord := b` (pending).  The word is zero
      whenever the flag is clear (`pendingWord_cleared`), so the pair and
      `Option SeLe4n.Badge` are in bijection on every notification. -/
  hasPendingBadge : Bool := false
  /-- The pending badge word; meaningful only when `hasPendingBadge`. -/
  pendingWord : SeLe4n.Badge := SeLe4n.Badge.zero
  /-- A clear flag carries the zero word, so no notification holds a word that
      its pending badge does not show (a boot configuration or any other
      constructor cannot hide content in the word).  A proof, erased at run
      time; a literal construction discharges it automatically. -/
  pendingWord_cleared : if hasPendingBadge then True else pendingWord = SeLe4n.Badge.zero := by
    first
      | exact trivial
      | exact rfl
      | assumption
  /-- WS-SM SM6.B (bound notification): the TCB bound to this notification, if
      any (the seL4 `NotificationBind` relation).  `bindNotification` sets it
      (and the dual `TCB.boundNotification`); `unbindNotification` clears it.
      When a notification with `boundTCB = some t` and *no* waiters is signalled
      while `t` is `BlockedOnReceive`, the signal is delivered directly to `t`
      (the bound-delivery path of `notificationSignalBound`) rather than stored as
      a pending badge.  Default `none` — a freshly-allocated notification is
      unbound, so every existing construction site is unaffected.  WS-ZA ZA5.2:
      stored as its scalar code (`SeLe4n.ThreadId.optCode`) and read through
      the view `Notification.boundTCB`, so a bind writes no `some` cell. -/
  boundTCBCode : Nat := 0
  /-- **Whether an interrupt is handled through this notification**: the
      interrupt table (`SystemState.irqHandlers`, written at boot only) names it
      by id, where seL4 keeps a capability to it in the interrupt's slot.  Set
      by the boot for every notification the table names
      (`SystemState.tableReferencesRecorded`), so a final delete reads this flag
      instead of walking the table.  A carved notification starts `false`. -/
  irqBound : Bool := false
  /-- WS-ZA ZA5.11: **the notification's declassification provenance**, as plain
      words: eight tag words, the count of those in use and the saturated bit,
      read through `TCB.taintWords` (`SeLe4n.Kernel.TaintWords`) and written in
      place by the taint step.  A carved notification starts with scalar zeros, the
      empty taint, so a reused id names no provenance. -/
  taintTag0 : UInt64 := 0
  taintTag1 : UInt64 := 0
  taintTag2 : UInt64 := 0
  taintTag3 : UInt64 := 0
  taintTag4 : UInt64 := 0
  taintTag5 : UInt64 := 0
  taintTag6 : UInt64 := 0
  taintTag7 : UInt64 := 0
  /-- How many of the tag words are in use. -/
  taintCount : Nat := 0
  /-- Tainted by everything. -/
  taintSaturated : Bool := false
  deriving Repr, DecidableEq

/-- WS-ZA ZA5.11: the notification's taint words. -/
@[inline] def Notification.taintWords (n : Notification) : SeLe4n.Kernel.TaintWords :=
  { tag0 := n.taintTag0, tag1 := n.taintTag1, tag2 := n.taintTag2, tag3 := n.taintTag3,
    tag4 := n.taintTag4, tag5 := n.taintTag5, tag6 := n.taintTag6, tag7 := n.taintTag7,
    count := n.taintCount, saturated := n.taintSaturated }

/-- WS-ZA ZA5.11: the notification with its taint words written. -/
@[inline] def Notification.withTaintWords (n : Notification) (w : SeLe4n.Kernel.TaintWords) :
    Notification :=
  { n with taintTag0 := w.tag0, taintTag1 := w.tag1, taintTag2 := w.tag2,
           taintTag3 := w.tag3, taintTag4 := w.tag4, taintTag5 := w.tag5,
           taintTag6 := w.tag6, taintTag7 := w.tag7, taintCount := w.count,
           taintSaturated := w.saturated }

@[simp] theorem Notification.taintWords_withTaintWords (n : Notification)
    (w : SeLe4n.Kernel.TaintWords) : (n.withTaintWords w).taintWords = w := rfl

@[simp] theorem Notification.withTaintWords_taintWords (n : Notification) :
    n.withTaintWords n.taintWords = n := rfl

/-- WS-ZA ZA5.2: the bound thread, read from its code.  Reducible, so a record
update that leaves the code alone reads the old value by `rfl`.  Written as
`boundTCBCode := SeLe4n.ThreadId.optCode t`. -/
@[reducible, inline] def Notification.boundTCB (n : Notification) :
    Option SeLe4n.ThreadId :=
  SeLe4n.ThreadId.ofOptCode n.boundTCBCode

/-- The pending badge, if any: the `Option` view of the `hasPendingBadge` /
    `pendingWord` pair every specification and proof reads. -/
@[inline] def Notification.pendingBadge (n : Notification) : Option SeLe4n.Badge :=
  if n.hasPendingBadge then some n.pendingWord else none

@[simp] theorem Notification.pendingBadge_mk (s hd tl h p c b i w0 w1 w2 w3 w4 w5 w6 w7 tc ts) :
    (Notification.mk s hd tl h p c b i w0 w1 w2 w3 w4 w5 w6 w7 tc ts).pendingBadge = if h then some p else none := rfl

@[simp] theorem Notification.pendingBadge_mk_true (s hd tl p c b i w0 w1 w2 w3 w4 w5 w6 w7 tc ts) :
    (Notification.mk s hd tl true p c b i w0 w1 w2 w3 w4 w5 w6 w7 tc ts).pendingBadge = some p := rfl

@[simp] theorem Notification.pendingBadge_mk_false (s hd tl p c b i w0 w1 w2 w3 w4 w5 w6 w7 tc ts) :
    (Notification.mk s hd tl false p c b i w0 w1 w2 w3 w4 w5 w6 w7 tc ts).pendingBadge = none := rfl

/-- The first waiter, read from its scalar code. -/
@[inline] def Notification.waitHead (n : Notification) : Option SeLe4n.ThreadId :=
  SeLe4n.ThreadId.ofOptCode n.waitHeadCode

/-- The last waiter, read from its scalar code. -/
@[inline] def Notification.waitTail (n : Notification) : Option SeLe4n.ThreadId :=
  SeLe4n.ThreadId.ofOptCode n.waitTailCode

@[simp] theorem Notification.waitHead_mk (s hd tl h p c b i w0 w1 w2 w3 w4 w5 w6 w7 tc ts) :
    (Notification.mk s hd tl h p c b i w0 w1 w2 w3 w4 w5 w6 w7 tc ts).waitHead = SeLe4n.ThreadId.ofOptCode hd := rfl

@[simp] theorem Notification.waitTail_mk (s hd tl h p c b i w0 w1 w2 w3 w4 w5 w6 w7 tc ts) :
    (Notification.mk s hd tl h p c b i w0 w1 w2 w3 w4 w5 w6 w7 tc ts).waitTail = SeLe4n.ThreadId.ofOptCode tl := rfl

@[simp] theorem Notification.ofOptCode_waitHeadCode (n : Notification) :
    SeLe4n.ThreadId.ofOptCode n.waitHeadCode = n.waitHead := rfl

@[simp] theorem Notification.ofOptCode_waitTailCode (n : Notification) :
    SeLe4n.ThreadId.ofOptCode n.waitTailCode = n.waitTail := rfl

@[simp] theorem Notification.optCode_waitHead (n : Notification) :
    SeLe4n.ThreadId.optCode n.waitHead = n.waitHeadCode :=
  SeLe4n.ThreadId.optCode_ofOptCode _

@[simp] theorem Notification.optCode_waitTail (n : Notification) :
    SeLe4n.ThreadId.optCode n.waitTail = n.waitTailCode :=
  SeLe4n.ThreadId.optCode_ofOptCode _

/-- WS-ZA ZA4.4: the threads a notification names itself — the two ends of its
wait queue.  The waiters between them are reached through those threads' own
links (`TCB.ntfnNext` / `TCB.ntfnPrev`), not through the notification. -/
def Notification.queueEnds (n : Notification) : List SeLe4n.ThreadId :=
  n.waitHead.toList ++ n.waitTail.toList

@[simp] theorem Notification.mem_queueEnds (n : Notification) (tid : SeLe4n.ThreadId) :
    tid ∈ n.queueEnds ↔ n.waitHead = some tid ∨ n.waitTail = some tid := by
  unfold Notification.queueEnds
  cases n.waitHead <;> cases n.waitTail <;> simp [eq_comm]

/-- WS-ZA ZA4.4: the notification once its head waiter is woken.  `next` is the
woken head's successor (its `ntfnNext`): it heads the queue, and when there is
none the queue is empty and the notification idle.  No badge is pending — a
notification with waiters holds none — and the binding is carried. -/
@[inline] def Notification.withHeadPopped (n : Notification)
    (next : Option SeLe4n.ThreadId) : Notification :=
  { state := if next.isSome then .waiting else .idle
    waitHeadCode := SeLe4n.ThreadId.optCode next
    waitTailCode := if next.isSome then n.waitTailCode else 0
    hasPendingBadge := false, pendingWord := SeLe4n.Badge.zero
    boundTCBCode := n.boundTCBCode, irqBound := n.irqBound, taintTag0 := n.taintTag0, taintTag1 := n.taintTag1, taintTag2 := n.taintTag2, taintTag3 := n.taintTag3, taintTag4 := n.taintTag4, taintTag5 := n.taintTag5, taintTag6 := n.taintTag6, taintTag7 := n.taintTag7, taintCount := n.taintCount, taintSaturated := n.taintSaturated }

/-- WS-ZA ZA4.4: the notification once `waiter` joins the back of its queue: the
waiter is the new tail, and the head too when the queue was empty. -/
@[inline] def Notification.withWaiterAppended (n : Notification)
    (waiter : SeLe4n.ThreadId) : Notification :=
  { state := .waiting
    waitHeadCode := if n.waitHeadCode = 0 then SeLe4n.ThreadId.optCode (some waiter)
      else n.waitHeadCode
    waitTailCode := SeLe4n.ThreadId.optCode (some waiter)
    hasPendingBadge := false, pendingWord := SeLe4n.Badge.zero
    boundTCBCode := n.boundTCBCode, irqBound := n.irqBound, taintTag0 := n.taintTag0, taintTag1 := n.taintTag1, taintTag2 := n.taintTag2, taintTag3 := n.taintTag3, taintTag4 := n.taintTag4, taintTag5 := n.taintTag5, taintTag6 := n.taintTag6, taintTag7 := n.taintTag7, taintCount := n.taintCount, taintSaturated := n.taintSaturated }

@[simp] theorem Notification.withHeadPopped_waitHead (n : Notification)
    (next : Option SeLe4n.ThreadId) : (n.withHeadPopped next).waitHead = next := by
  simp [Notification.withHeadPopped, Notification.waitHead]

@[simp] theorem Notification.withHeadPopped_waitTail (n : Notification)
    (next : Option SeLe4n.ThreadId) :
    (n.withHeadPopped next).waitTail = if next.isSome then n.waitTail else none := by
  cases next <;> simp only [Notification.withHeadPopped, Notification.waitTail_mk,
    Option.isSome_none, Option.isSome_some, Bool.false_eq_true, ↓reduceIte,
    SeLe4n.ThreadId.ofOptCode_zero, Notification.ofOptCode_waitTailCode]

@[simp] theorem Notification.withHeadPopped_state (n : Notification)
    (next : Option SeLe4n.ThreadId) :
    (n.withHeadPopped next).state = if next.isSome then .waiting else .idle := rfl

@[simp] theorem Notification.withHeadPopped_pendingBadge (n : Notification)
    (next : Option SeLe4n.ThreadId) : (n.withHeadPopped next).pendingBadge = none := rfl

@[simp] theorem Notification.withHeadPopped_boundTCB (n : Notification)
    (next : Option SeLe4n.ThreadId) : (n.withHeadPopped next).boundTCB = n.boundTCB := rfl

theorem Notification.waitHeadCode_eq_zero_iff (n : Notification) :
    n.waitHeadCode = 0 ↔ n.waitHead = none := by
  rw [← Notification.optCode_waitHead]
  cases n.waitHead <;> simp [SeLe4n.ThreadId.optCode]

@[simp] theorem Notification.withWaiterAppended_waitHead (n : Notification)
    (waiter : SeLe4n.ThreadId) :
    (n.withWaiterAppended waiter).waitHead = some (n.waitHead.getD waiter) := by
  unfold Notification.withWaiterAppended Notification.waitHead
  by_cases h : n.waitHeadCode = 0
  · simp [h]
  · simp only [h, ↓reduceIte]
    have h' := mt (Notification.waitHeadCode_eq_zero_iff n).mpr h
    unfold Notification.waitHead at h'
    cases hc : SeLe4n.ThreadId.ofOptCode n.waitHeadCode with
    | none => exact absurd hc h'
    | some t => rfl

@[simp] theorem Notification.withWaiterAppended_waitTail (n : Notification)
    (waiter : SeLe4n.ThreadId) : (n.withWaiterAppended waiter).waitTail = some waiter := by
  simp [Notification.withWaiterAppended, Notification.waitTail]

@[simp] theorem Notification.withWaiterAppended_state (n : Notification)
    (waiter : SeLe4n.ThreadId) : (n.withWaiterAppended waiter).state = .waiting := rfl

@[simp] theorem Notification.withWaiterAppended_pendingBadge (n : Notification)
    (waiter : SeLe4n.ThreadId) : (n.withWaiterAppended waiter).pendingBadge = none := rfl

@[simp] theorem Notification.withWaiterAppended_boundTCB (n : Notification)
    (waiter : SeLe4n.ThreadId) :
    (n.withWaiterAppended waiter).boundTCB = n.boundTCB := rfl

/-- WS-ZA ZA5.3: the capability a CNode's slot array holds at `s`; `none` past
its end. -/
@[inline] def slotArrayGet (cells : Array (Option Capability)) (s : SeLe4n.Slot) :
    Option Capability :=
  if h : s.toNat < cells.size then cells[s.toNat] else none

/-- WS-ZA ZA5.3: the `2 ^ rw`-entry slot array holding `m`'s capability at
each slot below `2 ^ rw`. -/
def slotArrayOf (rw : Nat) (m : SeLe4n.UniqueSlotMap Capability) :
    Array (Option Capability) :=
  Array.ofFn (n := 2 ^ rw) fun i => m.get? (SeLe4n.Slot.ofNat i.val)

theorem slotArrayOf_size (rw : Nat) (m : SeLe4n.UniqueSlotMap Capability) :
    (slotArrayOf rw m).size = 2 ^ rw := by
  simp [slotArrayOf]

/-- WS-ZA ZA5.3: a map holding nothing at or past `2 ^ rw` agrees with the
slot array built from it. -/
theorem slotArrayOf_agree (rw : Nat) (m : SeLe4n.UniqueSlotMap Capability)
    (hb : ∀ s : SeLe4n.Slot, 2 ^ rw ≤ s.toNat → m.get? s = none) :
    ∀ s, m.get? s = slotArrayGet (slotArrayOf rw m) s := by
  intro s
  unfold slotArrayGet
  by_cases h : s.toNat < 2 ^ rw
  · simp [slotArrayOf, h]; rfl
  · simp [slotArrayOf, h]; exact hb s (by omega)

theorem slotArrayGet_set (cells : Array (Option Capability)) (i : Nat) (v : Option Capability)
    (h : i < cells.size) (s : SeLe4n.Slot) :
    slotArrayGet (cells.set i v h) s = if s.toNat = i then v else slotArrayGet cells s := by
  unfold slotArrayGet
  by_cases hs : s.toNat = i
  · subst hs; simp [h]
  · simp [hs, Array.getElem_set, Ne.symm hs]

theorem slotArrayGet_setIfInBounds (cells : Array (Option Capability)) (i : Nat)
    (s : SeLe4n.Slot) :
    slotArrayGet (cells.setIfInBounds i none) s =
      if s.toNat = i then none else slotArrayGet cells s := by
  unfold slotArrayGet
  by_cases hs : s.toNat = i
  · subst hs; by_cases h : s.toNat < cells.size <;> simp [h]
  · by_cases h : s.toNat < cells.size
    · simp [h, hs, Array.getElem_setIfInBounds]; intro e; exact absurd e.symm hs
    · simp [h]

theorem slotArrayGet_mapIdx (cells : Array (Option Capability))
    (g : Nat → Option Capability → Option Capability) (s : SeLe4n.Slot) :
    slotArrayGet (cells.mapIdx g) s =
      if s.toNat < cells.size then g s.toNat (slotArrayGet cells s) else none := by
  unfold slotArrayGet
  by_cases h : s.toNat < cells.size <;> simp [h]

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
construction time.  The historical state-level `cspaceSlotUnique`
predicate was deleted in the WS-RC R4.A close-out; per-CNode discharge
is now via `SeLe4n.Model.CNode.slotsUnique_holds`.  Defined in
`SeLe4n/Model/Object/UniqueSlotMap.lean`.

WS-ZA ZA5.3: the slots the kernel reads and writes are `cells`, a fixed array
of `2 ^ radixWidth` entries made with the CNode (seL4's `cte_t` array), so an
insert or a removal writes one entry in place.  The map the theorems state
their claims over is ghost state (`slotsGhost`, read as `CNode.slots`): the
compiled kernel never builds it, and `slots_agree` says it holds the array's
capability at every slot, so a slot at or past `2 ^ radixWidth` holds nothing.
A CNode is built with `CNode.ofSlots`. -/
structure CNode where
  depth      : Nat          -- maximum remaining depth in bits from this node to any leaf
  guardWidth : Nat          -- width of guard field in bits
  guardValue : Nat          -- expected guard value to match
  radixWidth : Nat          -- width of slot index in bits (2^radixWidth slots)
  slotsGhost : SeLe4n.Erased (SeLe4n.UniqueSlotMap Capability)
  cells      : Array (Option Capability)
  cells_size : cells.size = 2 ^ radixWidth
  slots_agree : ∀ s, slotsGhost.out.get? s = slotArrayGet cells s
  /-- WS-ZA ZA5.3 part 4: each slot's derivation links (seL4's mapping-database
  words in `cte_t`), `slotLinkWords` words per slot: parent, first child, next
  and previous sibling, each a CNode word and a slot word, a word of 0 meaning
  no link and any other word `n` the object or slot `n - 1`.  Words, not
  records, so a link is written in place and no entry is shared. -/
  links      : Array Nat
  links_size : links.size = slotLinkWords * 2 ^ radixWidth
  /-- WS-ZA ZA5.4 part 26: **the occupied slots, linked through the slots**:
  two words per slot, its next and its previous occupied slot (`0` for none,
  `j + 1` for slot `j`), written in place when a slot is filled or emptied, so
  a walk of the occupied slots (the zombie loop of a final delete) visits no
  empty slot and nothing is allocated (`SlotOccupancy`). -/
  occ        : Array Nat
  occ_size   : occ.size = 2 * 2 ^ radixWidth
  /-- WS-ZA ZA5.4 part 26: the first occupied slot's code (`0` for none). -/
  occHead    : Nat
  /-- WS-ZA ZA5.4 part 26: **the links list exactly the occupied slots**, each
  once, from the head (`SlotOccupancy.Encodes`); the list itself is a ghost
  (`CNode.occupiedList`). -/
  occ_agree  : ∃ L, SlotOccupancy.Encodes cells occ occHead L
  /-- WS-ZA ZA5.3 part 6: the records the slots keep while empty. -/
  spare      : SpareCells
  deriving Repr

/-- WS-ZA ZA5.3: the slot map the theorems read; ghost state, equal to the slot
array at every slot (`CNode.slots_agree`). -/
noncomputable def CNode.slots (cn : CNode) : SeLe4n.UniqueSlotMap Capability :=
  cn.slotsGhost.out

/-- WS-ZA ZA5.3 part 6: a record of its own for each of a radix-`rw` CNode's
slots, made with the CNode.  Each record targets an object named by its slot
number, so the compiler cannot share one record among the slots. -/
def spareCellsFor (rw : Nat) : Array (Option Capability) :=
  Array.ofFn (n := 2 ^ rw) fun i =>
    some { target := .object ⟨i.val⟩, rights := AccessRightSet.empty }

/-- WS-ZA ZA5.3: the CNode of the given geometry holding `m`'s capability at
each slot below `2 ^ rw`; a slot at or past it holds nothing. -/
def CNode.ofSlots (depth guardWidth guardValue radixWidth : Nat)
    (m : SeLe4n.UniqueSlotMap Capability) : CNode where
  depth := depth
  guardWidth := guardWidth
  guardValue := guardValue
  radixWidth := radixWidth
  slotsGhost := .mk (m.filter fun s _ => decide (s.toNat < 2 ^ radixWidth))
  cells := slotArrayOf radixWidth m
  cells_size := slotArrayOf_size _ _
  links := Array.replicate (slotLinkWords * 2 ^ radixWidth) 0
  links_size := Array.size_replicate
  occ := SlotOccupancy.buildWords (slotArrayOf radixWidth m) (slotArrayOf radixWidth m).size
    (Array.replicate (2 * 2 ^ radixWidth) 0) 0
  occ_size := by rw [SlotOccupancy.size_buildWords, Array.size_replicate]
  occHead := SlotOccupancy.buildHead (slotArrayOf radixWidth m) (slotArrayOf radixWidth m).size 0
  occ_agree := SlotOccupancy.build_encodes _ _
    (by rw [Array.size_replicate, slotArrayOf_size])
  spare := Squash.mk (spareCellsFor radixWidth)
  slots_agree := fun s => by
    rw [SeLe4n.Erased.out_mk, SeLe4n.UniqueSlotMap.get?_filter]
    unfold slotArrayGet
    by_cases h : s.toNat < 2 ^ radixWidth
    · simp only [slotArrayOf, Array.size_ofFn, h, dite_true, Array.getElem_ofFn,
        SeLe4n.Slot.ofNat_toNat]
      cases m.get? s <;> simp [Option.filter]
    · simp only [slotArrayOf, Array.size_ofFn, h, dite_false]
      cases m.get? s <;> simp [Option.filter]

@[simp] theorem CNode.ofSlots_depth (d gw gv rw : Nat) (m : SeLe4n.UniqueSlotMap Capability) :
    (CNode.ofSlots d gw gv rw m).depth = d := rfl
@[simp] theorem CNode.ofSlots_guardWidth (d gw gv rw : Nat) (m : SeLe4n.UniqueSlotMap Capability) :
    (CNode.ofSlots d gw gv rw m).guardWidth = gw := rfl
@[simp] theorem CNode.ofSlots_guardValue (d gw gv rw : Nat) (m : SeLe4n.UniqueSlotMap Capability) :
    (CNode.ofSlots d gw gv rw m).guardValue = gv := rfl
@[simp] theorem CNode.ofSlots_radixWidth (d gw gv rw : Nat) (m : SeLe4n.UniqueSlotMap Capability) :
    (CNode.ofSlots d gw gv rw m).radixWidth = rw := rfl
@[simp] theorem CNode.slots_ofSlots (d gw gv rw : Nat) (m : SeLe4n.UniqueSlotMap Capability) :
    (CNode.ofSlots d gw gv rw m).slots = m.filter fun s _ => decide (s.toNat < 2 ^ rw) := by
  simp [CNode.ofSlots, CNode.slots]

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
from which typed kernel objects are carved via `retypeFromUntyped`.

**WS-ZA ZA5.4 part 13: the free index is not the object's.**  As in seL4, where
the free pointer is the capability's `capFreeIndex`, the offset of the next carve
is each untyped capability's own word (`Capability.freeIndex`): a carve starts at
the invoked capability's index and advances it in that capability's slot.  The
object keeps what every capability to it shares — its region, its memory kind,
its ancestry, and the record of what was carved from it.

seL4 reference: `Untyped_D` in the abstract spec — tracks device/non-device flag
and region bounds.  Our model keeps an explicit child list for non-overlap proofs
rather than relying on CSpace derivation tree ancestry. -/
structure UntypedObject where
  /-- Base physical address of the untyped region. -/
  regionBase : SeLe4n.PAddr
  /-- Total size of the region in bytes. -/
  regionSize : Nat
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

/-- Check whether an allocation of `size` bytes at free index `idx` fits within
the region. -/
def canAllocate (ut : UntypedObject) (idx size : Nat) : Bool :=
  size > 0 && idx + size ≤ ut.regionSize

/-- Allocate `size` bytes from the region at free index `idx` (the invoking
    capability's `Capability.freeIndex`), returning the updated untyped and the
    byte offset of the new allocation, which is `idx`.

    S4-H: New children are prepended to the `children` list, creating
    reverse-chronological order (most recent allocation first). Proofs that
    traverse children must account for this ordering — in particular,
    `List.mem` witnesses are preserved across allocations since prepending
    does not remove existing elements. -/
def allocate (ut : UntypedObject) (idx : Nat) (childId : SeLe4n.ObjId) (size : Nat) :
    Option (UntypedObject × Nat) :=
  if ut.canAllocate idx size then
    some ({ ut with
      children := { objId := childId, offset := idx, size := size } :: ut.children
    }, idx)
  else
    none

/-- AK7-K (F-L14 / LOW): Allocation with an explicit positive-size
precondition. `allocateChecked idx size h` rejects zero-size child
allocations statically via the `h : size > 0` witness, in addition to
the `canAllocate` region check performed by `allocate`.

A zero-size child is not ill-formed in the abstract model (the
free index is unchanged, the child list gains an empty-extent entry),
but it indicates a caller bug — no production syscall path allocates a
zero-size object. The checked variant surfaces this at the type level,
matching the F-L14 guard recommendation without breaking existing
callers. -/
def allocateChecked (ut : UntypedObject) (idx : Nat) (childId : SeLe4n.ObjId) (size : Nat)
    (_hPos : size > 0) : Option (UntypedObject × Nat) :=
  ut.allocate idx childId size

/-- AK7-K (F-L14): `allocateChecked` agrees with `allocate` on positive
sizes — it simply adds the positive-size proof obligation at the type
level without changing the body. -/
theorem allocateChecked_eq_allocate (ut : UntypedObject) (idx : Nat) (childId : SeLe4n.ObjId)
    (size : Nat) (hPos : size > 0) :
    ut.allocateChecked idx childId size hPos = ut.allocate idx childId size := rfl

/-- WS-ZA ZA5.4 part 13: a free index is within the region's bounds. -/
def freeIndexValid (ut : UntypedObject) (idx : Nat) : Prop :=
  idx ≤ ut.regionSize

/-- WS-ZA ZA5.4 part 13: every child lies below free index `idx` — what a
capability's index promises: nothing carved lies at or after it. -/
def childrenBelow (ut : UntypedObject) (idx : Nat) : Prop :=
  ∀ c ∈ ut.children, c.offset + c.size ≤ idx

/-- No two children overlap in the allocated region. -/
def childrenNonOverlap (ut : UntypedObject) : Prop :=
  ∀ c₁ c₂, c₁ ∈ ut.children → c₂ ∈ ut.children →
    c₁ ≠ c₂ → c₁.offset + c₁.size ≤ c₂.offset ∨ c₂.offset + c₂.size ≤ c₁.offset

/-- Children have distinct object identities. -/
def childrenUniqueIds (ut : UntypedObject) : Prop :=
  ∀ c₁ c₂, c₁ ∈ ut.children → c₂ ∈ ut.children →
    c₁.objId = c₂.objId → c₁ = c₂

/-- Combined well-formedness predicate for the untyped object: its children lie
inside the region, apart, with distinct identities.  What a capability's free
index adds is the capability's own (`freeIndexValid`, `childrenBelow`). -/
def wellFormed (ut : UntypedObject) : Prop :=
  ut.childrenBelow ut.regionSize ∧ ut.childrenNonOverlap ∧ ut.childrenUniqueIds

theorem empty_childrenBelow (base : SeLe4n.PAddr) (size idx : Nat) :
    ({ regionBase := base, regionSize := size,
                       children := [], isDevice := false, parent := none } : UntypedObject).childrenBelow idx := by
  intro c hMem
  simp at hMem

theorem empty_childrenNonOverlap (base : SeLe4n.PAddr) (size : Nat) :
    ({ regionBase := base, regionSize := size,
                       children := [], isDevice := false, parent := none } : UntypedObject).childrenNonOverlap := by
  intro c₁ c₂ hMem₁
  simp at hMem₁

theorem empty_childrenUniqueIds (base : SeLe4n.PAddr) (size : Nat) :
    ({ regionBase := base, regionSize := size,
                       children := [], isDevice := false, parent := none } : UntypedObject).childrenUniqueIds := by
  intro c₁ c₂ hMem₁
  simp at hMem₁

theorem empty_wellFormed (base : SeLe4n.PAddr) (size : Nat) :
    ({ regionBase := base, regionSize := size,
                       children := [], isDevice := false, parent := none } : UntypedObject).wellFormed :=
  ⟨empty_childrenBelow base size size,
   empty_childrenNonOverlap base size, empty_childrenUniqueIds base size⟩

/-- `canAllocate` being true implies the allocation fits within region bounds. -/
theorem canAllocate_implies_fits (ut : UntypedObject) (idx size : Nat)
    (hCan : ut.canAllocate idx size = true) :
    idx + size ≤ ut.regionSize := by
  simp [canAllocate] at hCan
  exact hCan.2

/-- Decomposition lemma: a successful `allocate` produces a specific updated state. -/
theorem allocate_some_iff (ut : UntypedObject) (idx : Nat) (childId : SeLe4n.ObjId) (size : Nat)
    (result : UntypedObject × Nat) :
    ut.allocate idx childId size = some result ↔
      ut.canAllocate idx size = true ∧
      result = ({ ut with
        children := { objId := childId, offset := idx, size := size } :: ut.children
      }, idx) := by
  constructor
  · intro h
    unfold allocate at h
    by_cases hCan : ut.canAllocate idx size
    · simp [hCan] at h; exact ⟨hCan, h.symm⟩
    · simp [hCan] at h
  · intro ⟨hCan, hEq⟩
    unfold allocate
    simp [hCan, hEq]

/-- After a successful `allocate`, the returned offset is the free index it was
handed. -/
theorem allocate_offset_eq (ut ut' : UntypedObject) (idx : Nat) (childId : SeLe4n.ObjId)
    (size offset : Nat) (hAlloc : ut.allocate idx childId size = some (ut', offset)) :
    offset = idx := by
  rw [allocate_some_iff] at hAlloc
  exact (Prod.mk.inj hAlloc.2).2

/-- A successful allocation leaves the advanced free index `idx + size` valid. -/
theorem allocate_freeIndexValid (ut ut' : UntypedObject) (idx : Nat) (childId : SeLe4n.ObjId)
    (size offset : Nat) (hAlloc : ut.allocate idx childId size = some (ut', offset)) :
    ut'.freeIndexValid (idx + size) := by
  rw [allocate_some_iff] at hAlloc
  rcases hAlloc with ⟨hCan, hEq⟩
  have hFits := canAllocate_implies_fits ut idx size hCan
  have hU := (Prod.mk.inj hEq).1
  subst hU; simp [freeIndexValid]; omega

/-- `allocate` does not change the region base or size. -/
theorem allocate_preserves_region (ut ut' : UntypedObject) (idx : Nat) (childId : SeLe4n.ObjId)
    (size offset : Nat) (hAlloc : ut.allocate idx childId size = some (ut', offset)) :
    ut'.regionBase = ut.regionBase ∧ ut'.regionSize = ut.regionSize := by
  rw [allocate_some_iff] at hAlloc
  rcases hAlloc with ⟨_, hEq⟩
  have hU := (Prod.mk.inj hEq).1
  subst hU; exact ⟨rfl, rfl⟩

/-- AK8-A (WS-AK / C-M01): `allocate` extends the children list — every
existing entry in `ut.children` is still present in `ut'.children`. Used
by the cross-untyped disjointness preservation proof to transport
child-exclusion hypotheses across the allocation step. -/
theorem allocate_children_extends (ut ut' : UntypedObject) (idx : Nat)
    (childId : SeLe4n.ObjId) (size offset : Nat)
    (hAlloc : ut.allocate idx childId size = some (ut', offset)) :
    ∀ c, c ∈ ut.children → c ∈ ut'.children := by
  rw [allocate_some_iff] at hAlloc
  rcases hAlloc with ⟨_, hEq⟩
  have hU := (Prod.mk.inj hEq).1; subst hU
  intro c hc; exact List.mem_cons_of_mem _ hc

/-- AK8-A (WS-AK / C-M01): `allocate` places the new child at the head of
the children list, with exact bookkeeping for `objId`, `offset`, and
`size`. -/
theorem allocate_children_new (ut ut' : UntypedObject) (idx : Nat)
    (childId : SeLe4n.ObjId) (size offset : Nat)
    (hAlloc : ut.allocate idx childId size = some (ut', offset)) :
    { objId := childId, offset := idx, size := size : UntypedChild }
      ∈ ut'.children := by
  rw [allocate_some_iff] at hAlloc
  rcases hAlloc with ⟨_, hEq⟩
  have hU := (Prod.mk.inj hEq).1; subst hU
  exact List.mem_cons_self ..

/-- AK8-A (WS-AK / C-M01): `allocate`'s post-state `children` list equals
the new child prepended onto the pre-state list. -/
theorem allocate_children_eq (ut ut' : UntypedObject) (idx : Nat)
    (childId : SeLe4n.ObjId) (size offset : Nat)
    (hAlloc : ut.allocate idx childId size = some (ut', offset)) :
    ut'.children =
      { objId := childId, offset := idx, size := size }
        :: ut.children := by
  rw [allocate_some_iff] at hAlloc
  rcases hAlloc with ⟨_, hEq⟩
  have hU := (Prod.mk.inj hEq).1; subst hU; rfl

/-- AK8-A (WS-AK / C-M01): A successful `allocate` witnesses that the
requested size fits within the parent's region — the new child's
`[parent.regionBase + offset, parent.regionBase + offset + size)` range
lies entirely inside `[parent.regionBase, parent.regionBase + parent.regionSize)`. -/
theorem allocate_child_fits_parent (ut ut' : UntypedObject) (idx : Nat)
    (childId : SeLe4n.ObjId) (size offset : Nat)
    (hAlloc : ut.allocate idx childId size = some (ut', offset)) :
    offset + size ≤ ut.regionSize := by
  rw [allocate_some_iff] at hAlloc
  rcases hAlloc with ⟨hCan, hEq⟩
  have hOffsetEq : offset = idx := (Prod.mk.inj hEq).2
  have hFits := canAllocate_implies_fits ut idx size hCan
  omega

/-- WS-ZA ZA5.4 part 14: children below an index are below every later one —
what lets a carve at the index rounded up (`alignedCarveIndex`) reuse the
bound its capability's own index carries. -/
theorem childrenBelow_mono (ut : UntypedObject) {idx idx' : Nat}
    (h : ut.childrenBelow idx) (hLe : idx ≤ idx') : ut.childrenBelow idx' :=
  fun c hc => Nat.le_trans (h c hc) hLe

/-- WS-F2, restated over the capability's free index at WS-ZA ZA5.4 part 13:
a successful allocation at `idx` keeps every child below the advanced index.
Existing children are below `idx` (so below `idx + size`), and the new child
occupies `[idx, idx + size)`. -/
theorem allocate_preserves_childrenBelow (ut ut' : UntypedObject) (idx : Nat)
    (childId : SeLe4n.ObjId) (size offset : Nat)
    (hBounds : ut.childrenBelow idx)
    (hAlloc : ut.allocate idx childId size = some (ut', offset)) :
    ut'.childrenBelow (idx + size) := by
  rw [allocate_some_iff] at hAlloc
  rcases hAlloc with ⟨_hCan, hEq⟩
  have hU := (Prod.mk.inj hEq).1; subst hU
  intro c hMem
  simp at hMem ⊢
  rcases hMem with rfl | hOld
  · dsimp; omega
  · have := hBounds c hOld; omega

/-- WS-ZA ZA5.4 part 13: a successful allocation keeps every child below any
free index at or past the region's end — the index of a capability set full. -/
theorem allocate_preserves_childrenBelow_full (ut ut' : UntypedObject) (idx : Nat)
    (childId : SeLe4n.ObjId) (size offset bound : Nat)
    (hBounds : ut.childrenBelow bound) (hFull : ut.regionSize ≤ bound)
    (hAlloc : ut.allocate idx childId size = some (ut', offset)) :
    ut'.childrenBelow bound := by
  rw [allocate_some_iff] at hAlloc
  rcases hAlloc with ⟨hCan, hEq⟩
  have hFits := canAllocate_implies_fits ut idx size hCan
  have hU := (Prod.mk.inj hEq).1; subst hU
  intro c hMem
  simp at hMem
  rcases hMem with rfl | hOld
  · dsimp; omega
  · exact hBounds c hOld

/-- WS-F2: A successful allocation preserves childrenNonOverlap, given that
existing children lie below the free index it was handed.  Since the new child
starts at that index and every existing child ends at or before it, no overlap
is possible. -/
theorem allocate_preserves_childrenNonOverlap (ut ut' : UntypedObject) (idx : Nat)
    (childId : SeLe4n.ObjId) (size offset : Nat)
    (hNonOverlap : ut.childrenNonOverlap)
    (hBounds : ut.childrenBelow idx)
    (hAlloc : ut.allocate idx childId size = some (ut', offset)) :
    ut'.childrenNonOverlap := by
  rw [allocate_some_iff] at hAlloc
  rcases hAlloc with ⟨_hCan, hEq⟩
  have hU := (Prod.mk.inj hEq).1; subst hU
  intro c₁ c₂ hMem₁ hMem₂ hNe
  simp at hMem₁ hMem₂
  rcases hMem₁ with rfl | hOld₁ <;> rcases hMem₂ with rfl | hOld₂
  · exact absurd rfl hNe
  · -- new child vs old child: old child ends ≤ idx = new child offset
    right; have := hBounds c₂ hOld₂; dsimp; omega
  · -- old child vs new child: old child ends ≤ idx = new child offset
    left; have := hBounds c₁ hOld₁; dsimp; omega
  · -- two old children: by pre-condition
    exact hNonOverlap c₁ c₂ hOld₁ hOld₂ hNe

/-- WS-F2: A successful allocation preserves childrenUniqueIds, given that
the new child's ID does not collide with any existing child. -/
theorem allocate_preserves_childrenUniqueIds (ut ut' : UntypedObject) (idx : Nat)
    (childId : SeLe4n.ObjId) (size offset : Nat)
    (hUnique : ut.childrenUniqueIds)
    (hFresh : ∀ c ∈ ut.children, c.objId ≠ childId)
    (hAlloc : ut.allocate idx childId size = some (ut', offset)) :
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
  ⟨({ regionBase := base, regionSize := size,
      children := [], isDevice := false, parent := none } : UntypedObject),
   UntypedObject.empty_wellFormed base size⟩

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
  -- 8: retired — the in-place `lifecycleRetype` (WS-ZA ZA5.4 part 14).  Every
  -- object is carved from an untyped by `.untypedRetype`, as in seL4; the
  -- number stays reserved (`retiredNumbers`) and is never reassigned.
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
  | tcbSetAffinity         -- WS-SM SM5.H.4: set thread CPU affinity (+ migration)
  | tcbBindNotification    -- WS-SM SM6.B: bind a notification to a TCB (seL4 NotificationBind)
  | tcbUnbindNotification  -- WS-SM SM6.B: unbind a TCB's bound notification
  | mintReplyCap           -- WS-SM SM6.D / PR #822 Phase H: derive a `.replyCap` from an `.object` cap to a retyped Reply
  | vspaceUnifyInstruction -- WS-SM SM7.D: publish freshly-written code (seL4 Page_Unify_Instruction)
  | declassify             -- WS-SM SM8.C.9: authorize and audit a cross-domain downgrade
  | auditRead              -- WS-SM SM9.A.6: read one word of the declassification audit trail
  | auditDrain             -- WS-SM SM9.A.6: drain a prefix of the declassification audit trail
  | declassifySignal       -- WS-SM SM9.C.8: a notification signal whose badge crosses a
                           -- label boundary the base policy denies, audited per hop
  | tcbSetFaultHandler     -- Review round (PR #887): install a thread's fault-handler CPtr
                           -- (seL4_TCB_SetSpace's fault_ep), validated at set time
  | cspaceRevoke           -- WS-RR RR8.16 (`v0.35.190`): revoke a capability's derivations
                           -- (seL4_CNode_Revoke), dispatched through `cspaceRevokeCdtFinalising`
  | untypedRetype          -- WS-BP BP7.1 (`v0.36.5`): carve a frame — or since slice 4
                           -- (`v0.36.8`) a child untyped — out of an untyped the caller
                           -- holds (seL4_Untyped_Retype), through `untypedRetypeObject`
  | untypedReset           -- WS-BP BP7.1 (`v0.36.6`): write 0 to the invoked untyped
                           -- capability's free index once nothing carved from it
                           -- survives (seL4's resetUntypedCap), through
                           -- `untypedResetFromCap`
  | tcbSetSpace            -- WS-BP BP7.1 (`v0.36.11`): set a suspended thread's CSpace and
                           -- VSpace roots (seL4_TCB_SetSpace), through `copyThreadSpaces`
  | pageTableMap           -- WS-BP BP7.1 (`v0.36.12`): install an intermediate page table
                           -- (seL4_ARM_PageTable_Map), through `pageTableMap`
  | pageTableUnmap         -- WS-BP BP7.1 (`v0.36.12`): take one out
                           -- (seL4_ARM_PageTable_Unmap), through `pageTableUnmap`
  | yield                  -- WS-ZA ZA4.3: give up the rest of the caller's budget or
                           -- time slice (seL4_Yield under MCS), through `yieldOnCore`;
                           -- invokes no capability
  | schedContextConsumed   -- WS-ZA ZA6.9: read and reset a scheduling context's
                           -- consumed time (seL4_SchedContext_Consumed), through
                           -- `schedContextConsumedOnCore`
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
  | .tcbSetAffinity        => 25
  | .tcbBindNotification   => 26
  | .tcbUnbindNotification => 27
  | .mintReplyCap          => 28
  | .vspaceUnifyInstruction => 29
  | .declassify            => 30
  | .auditRead             => 31
  | .auditDrain            => 32
  | .declassifySignal      => 33
  | .tcbSetFaultHandler    => 34
  | .cspaceRevoke          => 35
  | .untypedRetype         => 36
  | .untypedReset          => 37
  | .tcbSetSpace           => 38
  | .pageTableMap          => 39
  | .pageTableUnmap        => 40
  | .yield                 => 41
  | .schedContextConsumed  => 42

/-- Total number of modeled syscalls (variants). -/
def count : Nat := 42

/-- One past the largest syscall number: every number below it is a variant's
    or a retired one. -/
def encodingBound : Nat := 43

/-- Retired syscall numbers, reserved and never reassigned: `8`, the in-place
    lifecycle retype (WS-ZA ZA5.4 part 14). -/
def retiredNumbers : List Nat := [8]

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
  | 25 => some .tcbSetAffinity
  | 26 => some .tcbBindNotification
  | 27 => some .tcbUnbindNotification
  | 28 => some .mintReplyCap
  | 29 => some .vspaceUnifyInstruction
  | 30 => some .declassify
  | 31 => some .auditRead
  | 32 => some .auditDrain
  | 33 => some .declassifySignal
  | 34 => some .tcbSetFaultHandler
  | 35 => some .cspaceRevoke
  | 36 => some .untypedRetype
  | 37 => some .untypedReset
  | 38 => some .tcbSetSpace
  | 39 => some .pageTableMap
  | 40 => some .pageTableUnmap
  | 41 => some .yield
  | 42 => some .schedContextConsumed
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
    | .tcbSetAffinity        => "tcbSetAffinity"
    | .tcbBindNotification   => "tcbBindNotification"
    | .tcbUnbindNotification => "tcbUnbindNotification"
    | .mintReplyCap          => "mintReplyCap"
    | .vspaceUnifyInstruction => "vspaceUnifyInstruction"
    | .declassify            => "declassify"
    | .auditRead             => "auditRead"
    | .auditDrain            => "auditDrain"
    | .declassifySignal      => "declassifySignal"
    | .tcbSetFaultHandler    => "tcbSetFaultHandler"
    | .cspaceRevoke          => "cspaceRevoke"
    | .untypedRetype         => "untypedRetype"
    | .untypedReset          => "untypedReset"
    | .tcbSetSpace           => "tcbSetSpace"
    | .pageTableMap          => "pageTableMap"
    | .pageTableUnmap        => "pageTableUnmap"
    | .yield                 => "yield"
    | .schedContextConsumed  => "schedContextConsumed"

/-- AC4-D/IF-01: Exhaustive list of all SyscallId variants. Used by the enforcement
    boundary completeness witness to ensure every syscall is classified. The
    `all_length` theorem provides a compile-time check that this list stays in
    sync with the `count` constant. -/
def all : List SyscallId :=
  [ .send, .receive, .call, .reply
  , .cspaceMint, .cspaceCopy, .cspaceMove, .cspaceDelete
  , .vspaceMap, .vspaceUnmap
  , .serviceRegister, .serviceRevoke, .serviceQuery
  , .notificationSignal, .notificationWait, .replyRecv
  , .schedContextConfigure, .schedContextBind, .schedContextUnbind
  , .tcbSuspend, .tcbResume, .tcbSetPriority, .tcbSetMCPriority
  , .tcbSetIPCBuffer, .tcbSetAffinity
  , .tcbBindNotification, .tcbUnbindNotification
  , .mintReplyCap, .vspaceUnifyInstruction, .declassify
  , .auditRead, .auditDrain, .declassifySignal, .tcbSetFaultHandler
  , .cspaceRevoke, .untypedRetype, .untypedReset, .tcbSetSpace
  , .pageTableMap, .pageTableUnmap, .yield, .schedContextConsumed ]

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
the modeled syscall variants plus a wildcard case. The `cases s <;> rfl` approach
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
  | 20 | 21 | 22 | 23 | 24 | 25
  | 26 | 27 | 28 | 29 | 30
  | 31 | 32 | 33 | 34 | 35 | 36 | 37 | 38 | 39 | 40 | 41 | 42 =>
    intro s h; simp [ofNat?] at h <;> (subst h; rfl)
  | n + 43 => intro s h; simp [ofNat?] at h

/-- Injectivity: the toNat encoding is injective. -/
theorem toNat_injective {a b : SyscallId} (h : a.toNat = b.toNat) : a = b := by
  have ha := ofNat_toNat a
  have hb := ofNat_toNat b
  rw [h] at ha
  rw [ha] at hb
  exact Option.some.inj hb

/-- Every number below `encodingBound` decodes to a syscall exactly when it is
    not retired, and none at or past it does. -/
theorem ofNat?_isSome_iff (n : Nat) :
    (ofNat? n).isSome = (decide (n < encodingBound) && !retiredNumbers.contains n) := by
  match n with
  | 0  | 1  | 2  | 3  | 4  | 5  | 6
  | 7  | 8  | 9  | 10 | 11 | 12 | 13
  | 14 | 15 | 16 | 17 | 18 | 19
  | 20 | 21 | 22 | 23 | 24 | 25
  | 26 | 27 | 28 | 29 | 30
  | 31 | 32 | 33 | 34 | 35 | 36 | 37 | 38 | 39 | 40 | 41 | 42 => rfl
  | n + 43 => simp [ofNat?, encodingBound, retiredNumbers]

/-- The retired in-place retype's number names no syscall. -/
theorem ofNat?_retired : ofNat? 8 = none := rfl

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
