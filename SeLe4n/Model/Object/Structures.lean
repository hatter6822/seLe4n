-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Model.Object.Types
import SeLe4n.Model.Object.Reply
import SeLe4n.Kernel.RobinHood.Bridge

namespace SeLe4n.Model


/-- WS-H11/H-02: Per-page permission attributes modeled after ARM64 page table descriptors.

Each mapping carries read/write/execute/user-access and cacheability flags. The
kernel enforces W^X (write XOR execute) as an invariant — no mapping may have both
`write` and `execute` set simultaneously. -/
structure PagePermissions where
  read : Bool := true
  write : Bool := false
  execute : Bool := false
  user : Bool := false
  cacheable : Bool := true
  deriving Repr, DecidableEq, Inhabited

instance : BEq PagePermissions where
  beq a b := a.read == b.read && a.write == b.write && a.execute == b.execute &&
              a.user == b.user && a.cacheable == b.cacheable

instance : LawfulBEq PagePermissions where
  eq_of_beq {a b} h := by
    simp only [BEq.beq, Bool.and_eq_true_iff, decide_eq_true_eq] at h
    cases a; cases b; simp_all
  rfl {a} := by
    simp only [BEq.beq]
    cases a; simp

instance : Hashable PagePermissions where
  hash p := mixHash (hash p.read) (mixHash (hash p.write) (mixHash (hash p.execute)
            (mixHash (hash p.user) (hash p.cacheable))))

/-- T6-A/M-NEW-6: Explicit read-only permissions — least-privilege default for VSpace map
operations. Callers must explicitly request write or execute permissions.
Fields: `read := true`, all others `false` except `cacheable := true`. -/
def PagePermissions.readOnly : PagePermissions :=
  { read := true, write := false, execute := false, user := false, cacheable := true }

/-- WS-H11/H-02: W^X policy — a page permission set must not have both write and execute. -/
def PagePermissions.wxCompliant (p : PagePermissions) : Bool :=
  !(p.write && p.execute)

/-- WS-H11: Default permissions are W^X compliant (read-only, non-executable). -/
theorem PagePermissions.default_wxCompliant : (default : PagePermissions).wxCompliant = true := by
  rfl

/-- T6-A: readOnly permissions are W^X compliant. -/
theorem PagePermissions.readOnly_wxCompliant : PagePermissions.readOnly.wxCompliant = true := by
  rfl

/-- WS-K-D: Decode a raw `Nat` permissions word to `PagePermissions` using
a bitfield layout: bit 0=read, 1=write, 2=execute, 3=user, 4=cacheable.
Every `Nat` maps to a valid `PagePermissions` — W^X enforcement happens
downstream in `vspaceMapPage`.

**AK7-J (F-M08 / MEDIUM) — masked-to-5-bits semantics:** `ofNat` is total
and silently masks any bits ≥ 5 (e.g., `ofNat (2^10)` produces
all-`false` permissions). This is intentional for proof ergonomics — the
underlying bitfield layout defines only 5 permission bits. Callers that
need to reject raw permission words with reserved bits set (bit ≥ 5)
should use the validating companion `PagePermissions.ofNat?`, which
returns `none` for `n ≥ 32` and for W^X-violating inputs. Production
syscall decoders (e.g., `decodeVSpaceMapArgs`) route through `ofNat?` at
the ABI boundary to surface `.invalidArgument` rather than producing a
surprising silent downgrade. -/
def PagePermissions.ofNat (n : Nat) : PagePermissions :=
  { read      := n &&& 1 != 0
    write     := n &&& 2 != 0
    execute   := n &&& 4 != 0
    user      := n &&& 8 != 0
    cacheable := n &&& 16 != 0 }

/-- WS-K-D: Encode `PagePermissions` as a `Nat` bitfield.
Companion to `ofNat` for round-trip proofs. -/
def PagePermissions.toNat (p : PagePermissions) : Nat :=
  (if p.read then 1 else 0) |||
  (if p.write then 2 else 0) |||
  (if p.execute then 4 else 0) |||
  (if p.user then 8 else 0) |||
  (if p.cacheable then 16 else 0)

/-- T6-C/M-ARCH-1: Validating decode — returns `none` for permission values outside the
5-bit valid range (bits 0–4: read, write, execute, user, cacheable). Values ≥ 32 contain
undefined permission bits and are rejected at the ABI decode boundary.

V4-K/L-FND-2: Also rejects W^X-violating inputs (both write and execute set).
This moves W^X enforcement to the earliest possible decode point, preventing
W^X-violating `PagePermissions` values from ever being constructed via `ofNat?`. -/
def PagePermissions.ofNat? (n : Nat) : Option PagePermissions :=
  if n < 32 then
    let p := PagePermissions.ofNat n
    if p.wxCompliant then some p else none
  else none

/-- WS-ZA ZA5.4: the permissions of every 5-bit word, in word order — built
once, when the kernel initialises, so a decode hands out a shared value rather
than building one. -/
def PagePermissions.table : Array PagePermissions :=
  ((List.range 32).map PagePermissions.ofNat).toArray

theorem PagePermissions.table_size : PagePermissions.table.size = 32 := by
  simp [PagePermissions.table]

theorem PagePermissions.table_get (n : Nat) (h : n < PagePermissions.table.size) :
    PagePermissions.table[n] = PagePermissions.ofNat n := by
  simp [PagePermissions.table]

/-- WS-ZA ZA5.4: `ofNat?` as compiled — the range and W^X checks read off the
word's bits, inlined, so a decoder's `match` meets the `some`, and the
permissions are the shared entry of `table`, so none is built. -/
@[inline] def PagePermissions.ofNatChecked (n : Nat) : Option PagePermissions :=
  if h : n < 32 && !(n &&& 2 != 0 && n &&& 4 != 0) then
    some (PagePermissions.table[n]'(by
      rw [PagePermissions.table_size]
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact h.1))
  else none

@[csimp] theorem PagePermissions.ofNat?_eq_checked :
    @PagePermissions.ofNat? = @PagePermissions.ofNatChecked := by
  funext n
  unfold PagePermissions.ofNat? PagePermissions.ofNatChecked PagePermissions.wxCompliant
  by_cases h : n < 32
  · simp only [h, PagePermissions.table_get]
    unfold PagePermissions.ofNat
    simp
  · simp [h]

/-- T6-C/V4-K: `ofNat?` returns `some` for valid, W^X-compliant permission values. -/
theorem PagePermissions.ofNat?_valid (n : Nat) (h : n < 32)
    (hWx : (PagePermissions.ofNat n).wxCompliant = true) :
    PagePermissions.ofNat? n = some (PagePermissions.ofNat n) := by
  simp [PagePermissions.ofNat?, h, hWx]

/-- T6-C: `ofNat?` returns `none` for values outside the valid range. -/
theorem PagePermissions.ofNat?_invalid (n : Nat) (h : ¬(n < 32)) :
    PagePermissions.ofNat? n = none := by
  simp [PagePermissions.ofNat?, h]

/-- V4-K: `ofNat?` returns `none` for W^X-violating values (both write and execute). -/
theorem PagePermissions.ofNat?_wxViolation (n : Nat) (h : n < 32)
    (hWx : (PagePermissions.ofNat n).wxCompliant = false) :
    PagePermissions.ofNat? n = none := by
  simp [PagePermissions.ofNat?, h, hWx]

/-- V4-K: Any `PagePermissions` returned by `ofNat?` is guaranteed W^X compliant. -/
theorem PagePermissions.ofNat?_wxSafe (n : Nat) (p : PagePermissions)
    (h : PagePermissions.ofNat? n = some p) :
    p.wxCompliant = true := by
  simp [PagePermissions.ofNat?] at h
  obtain ⟨_, hWx, hEq⟩ := h
  rw [← hEq]; exact hWx

/-- WS-K-D: Round-trip: encoding then decoding recovers the original. -/
theorem PagePermissions.ofNat_toNat_roundtrip (p : PagePermissions) :
    PagePermissions.ofNat (PagePermissions.toNat p) = p := by
  simp only [PagePermissions.ofNat, PagePermissions.toNat]
  cases p with
  | mk r w e u c =>
    cases r <;> cases w <;> cases e <;> cases u <;> cases c <;> decide

/-- AK7-K (F-L5 / LOW): Reverse round-trip — decoding then re-encoding
preserves the numeric value when the input lies in the 5-bit valid
range. This completes the permission-encoding round-trip surface: the
forward direction (`ofNat_toNat_roundtrip`) is already machine-checked,
and this reverse lemma covers the opposite direction under the
validity precondition. Values `n ≥ 32` lose their upper bits through
`ofNat`'s masking (see `PagePermissions.ofNat?` for the strict reject
variant). -/
theorem PagePermissions.toNat_ofNat_roundtrip (n : Nat) (h : n < 32) :
    PagePermissions.toNat (PagePermissions.ofNat n) = n := by
  -- 5-bit exhaustive case analysis: enumerate n ∈ {0, 1, ..., 31}
  have : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨
         n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨ n = 15 ∨
         n = 16 ∨ n = 17 ∨ n = 18 ∨ n = 19 ∨ n = 20 ∨ n = 21 ∨ n = 22 ∨ n = 23 ∨
         n = 24 ∨ n = 25 ∨ n = 26 ∨ n = 27 ∨ n = 28 ∨ n = 29 ∨ n = 30 ∨ n = 31 := by
    omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
                   rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
                   rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
                   rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- **WS-BP BP7.1 (`v0.36.12`): one intermediate translation table an address
space holds** — seL4's `seL4_ARM_PageTable` mapped into a VSpace.

The ARMv8 walk this kernel targets is four levels with a 4 KiB granule and a
48-bit virtual address: the VSpace root is level 0, and the tables below it are
levels 1, 2 and 3.  A table at `level` ℓ ∈ {1, 2, 3} covers every virtual
address whose bits above its own index field equal `index`
(`PageTableSlot.covers`), and `table` is the page-table object whose page holds
it.  A carved root's slots are the levels a mapping passes through, so a frame
is mapped into a carved address space only where all three levels are present
(`VSpaceRoot.walkComplete`). -/
structure PageTableSlot where
  level : Nat
  index : Nat
  table : SeLe4n.ObjId
  deriving Repr, DecidableEq

namespace PageTableSlot

/-- **The virtual-address shift that selects a level-ℓ table**: 39, 30 and 21 for
levels 1, 2 and 3 — the bits above that level's 9-bit index field in a 48-bit,
4 KiB-granule walk (`48 - 9ℓ`). -/
def shift (level : Nat) : Nat := 48 - 9 * level

/-- The index of the level-ℓ table a virtual address passes through. -/
def indexOf (level : Nat) (vaddr : SeLe4n.VAddr) : Nat := vaddr.toNat >>> shift level

/-- A slot covers the virtual addresses whose level-ℓ index is its own. -/
def covers (slot : PageTableSlot) (vaddr : SeLe4n.VAddr) : Bool :=
  indexOf slot.level vaddr == slot.index

end PageTableSlot

/-- WS-ZA ZA5.4: the cell an unmap took out of a root's mapping table (its
`some` and its entry, the entry's value pair among them), kept for the root's
next mapping to be written over, as a hardware page table's freed entry is
the next one written.  A `Squash`, so logically one value: no theorem reads it,
and a root with any spare is the root with any other
(`VSpaceRoot.with_mappingSpare`). -/
abbrev MappingSpare :=
  Squash (Option (SeLe4n.Kernel.RobinHood.RHEntry SeLe4n.VAddr (SeLe4n.PAddr × PagePermissions)))

instance : Repr MappingSpare := ⟨fun _ _ => "spare mapping cell"⟩

/-- WS-ZA ZA5.4: the cell an unmap took out of a root's epoch table (its
`some` and its entry), kept for the root's next mapping's epoch to be written
over, as `MappingSpare` is for the translation.  Logically one value
(`VSpaceRoot.with_epochSpare`). -/
abbrev EpochSpare :=
  Squash (Option (SeLe4n.Kernel.RobinHood.RHEntry SeLe4n.VAddr Nat))

instance : Repr EpochSpare := ⟨fun _ _ => "spare epoch cell"⟩

/-- WS-ZA ZA5.4: the cell a page table's slot takes in the address space that
holds it — the list cell of `VSpaceRoot.tables` and its slot record — kept by
the table while it is installed nowhere (`PageTableObject.slotCell`), so an
install writes the slot over it, as a hardware table's parent entry is memory
already there; a removal hands it back.  A `Squash`, so logically one value: no
theorem reads it (`PageTableObject.with_slotCell`, `VSpaceRoot.with_tableSlotSpare`). -/
abbrev TableSlotCell := Squash (List PageTableSlot)

instance : Repr TableSlotCell := ⟨fun _ _ => "spare table slot cell"⟩

instance : DecidableEq TableSlotCell := fun a b => isTrue (Subsingleton.elim a b)

/-- WS-G6/F-P05: Minimal VSpace root object: ASID identity plus flat virtual→physical mappings.

This intentionally models only one-level deterministic lookup semantics for WS-B1.
Hierarchical page-table levels are deferred behind this stable executable surface.

`mappings` is backed by `RHTable VAddr (PAddr × PagePermissions)` for O(1)
amortized lookup, insert, and erase. RHTable key uniqueness is structural
(noDupKeys invariant), making `noVirtualOverlap` trivially true.

WS-H11/H-02: Enriched with per-page permissions (read/write/execute/user/cacheable). -/
structure VSpaceRoot where
  asid : SeLe4n.ASID
  mappings : SeLe4n.Kernel.RobinHood.RHTable SeLe4n.VAddr (SeLe4n.PAddr × PagePermissions)
  /-- **WS-BP BP7.1 slice 4b (`v0.36.10`): the physical page holding this
      address space's top-level translation table** — what a PE is told to walk
      (`TTBR0_EL1`, which BP7.2 installs).  `some` exactly for a root carved from
      an untyped (`untypedRetypeObject` at `CarveRequest.vspaceRoot`), whose
      page it is; `none` for a root the boot configured, which owns no page of
      its own and so cannot be installed until the boot places one.  seL4's
      VSpace object *is* this page. -/
  tableBase : Option SeLe4n.PAddr := none
  /-- **WS-BP BP7.1 (`v0.36.12`): the intermediate tables this address space
      holds**, one slot per (level, index) — installed by `.pageTableMap`,
      removed by `.pageTableUnmap`.  Always empty for a root the boot
      configured, which has no page of its own to hang them from. -/
  tables : List PageTableSlot := []
  /-- **PR #904 review (`v0.36.41`): the frame mapping epoch of each address a
      frame capability mapped** (`FrameMapping.epoch`), written by `.vspaceMap`
      beside the translation.  What makes a capability's record identify *its*
      mapping rather than any translation of the same frame at the same
      address: `mappedPageLive` asks the two to agree.  An entry lives exactly
      as long as its translation: `.vspaceMap` writes both, and every unmap
      (`unmapPage`) erases both, so the table never holds more entries than
      the root has mappings. -/
  mappingEpochs : SeLe4n.Kernel.RobinHood.RHTable SeLe4n.VAddr Nat := {}
  /-- WS-ZA ZA5.4: the cell the root's last unmap took out of `mappings`
      (`MappingSpare`), which its next map writes over. -/
  mappingSpare : MappingSpare := Squash.mk none
  /-- WS-ZA ZA5.4: the cell the root's last unmap took out of `mappingEpochs`
      (`EpochSpare`), which its next map's epoch writes over. -/
  epochSpare : EpochSpare := Squash.mk none
  /-- WS-ZA ZA5.4: the slot cell a table removal has just taken out of
      `tables`, on its way back to the table (`TableSlotCell`). -/
  tableSlotSpare : TableSlotCell := Squash.mk []
  deriving Repr

namespace VSpaceRoot

/-- WS-ZA ZA5.4: the spare cell is no part of what a root is. -/
@[simp] theorem with_mappingSpare (r : VSpaceRoot) (v : MappingSpare) :
    { r with mappingSpare := v } = r := by
  cases r
  simp only [VSpaceRoot.mk.injEq, and_true, true_and]
  exact Subsingleton.elim _ _

/-- WS-ZA ZA5.4: the spare epoch cell is no part of what a root is. -/
@[simp] theorem with_epochSpare (r : VSpaceRoot) (v : EpochSpare) :
    { r with epochSpare := v } = r := by
  cases r
  simp only [VSpaceRoot.mk.injEq, and_true, true_and]
  exact Subsingleton.elim _ _

/-- WS-ZA ZA5.4: the slot cell in transit is no part of what a root is. -/
@[simp] theorem with_tableSlotSpare (r : VSpaceRoot) (v : TableSlotCell) :
    { r with tableSlotSpare := v } = r := by
  cases r
  simp only [VSpaceRoot.mk.injEq, true_and]
  exact Subsingleton.elim _ _

/-- **WS-BP BP7.1 (`v0.36.12`)**: the levels an address space's walk passes
through below its root — 1, 2 and 3 in a 48-bit, 4 KiB-granule translation. -/
def translationLevels : List Nat := [1, 2, 3]

/-- The table this address space holds at `(level, index)`, if any. -/
def slotAt? (root : VSpaceRoot) (level index : Nat) : Option PageTableSlot :=
  root.tables.find? (fun s => s.level == level && s.index == index)

/-- **Every level of the walk to `vaddr` is present** — the condition under which
a frame can be mapped at `vaddr` in a carved address space. -/
def walkComplete (root : VSpaceRoot) (vaddr : SeLe4n.VAddr) : Bool :=
  translationLevels.all fun l => (root.slotAt? l (PageTableSlot.indexOf l vaddr)).isSome

/-- **The shallowest level the walk to `vaddr` is missing** — where
`.pageTableMap` installs the next table, so a table is never installed below a
level that is absent. -/
def missingLevel? (root : VSpaceRoot) (vaddr : SeLe4n.VAddr) : Option Nat :=
  translationLevels.find? fun l => (root.slotAt? l (PageTableSlot.indexOf l vaddr)).isNone

/-- **A frame may be mapped at `vaddr`**: the root owns a top-level table page
and its walk to `vaddr` is complete.  A root with no table page has nowhere for a
walk to start, so nothing is mapped into it — fail-closed.  Since `v0.36.13`
every root a thread can run in has one: a carved root's is the page it was
carved on, and a root the boot configures takes one from the binding's
table-page pool (`MachineConfig.bootTablePool`,
`Platform.Boot.bootRootTablesPlaced`).  The one root without a page is the
kernel's own boot root, which no capability maps into. -/
def translationReady (root : VSpaceRoot) (vaddr : SeLe4n.VAddr) : Bool :=
  root.tableBase.isSome && root.walkComplete vaddr

theorem missingLevel?_none_iff_walkComplete (root : VSpaceRoot) (vaddr : SeLe4n.VAddr) :
    root.missingLevel? vaddr = none ↔ root.walkComplete vaddr = true := by
  unfold missingLevel? walkComplete translationLevels
  cases h1 : root.slotAt? 1 (PageTableSlot.indexOf 1 vaddr) <;>
    cases h2 : root.slotAt? 2 (PageTableSlot.indexOf 2 vaddr) <;>
    cases h3 : root.slotAt? 3 (PageTableSlot.indexOf 3 vaddr) <;>
    simp [List.find?, List.all, h1, h2, h3]

/-- WS-ZA ZA5.4: **does the walk hold a table at `(level, index)`**, read as a
first-order loop — `slotAt?`'s `find?` without its predicate closure or its
`some` (`slotPresentIn_eq`). -/
def slotPresentIn (level index : Nat) : List PageTableSlot → Bool
  | [] => false
  | s :: rest => (s.level == level && s.index == index) || slotPresentIn level index rest

/-- WS-ZA ZA5.4: the table of the first slot at `(level, index)`, read as a
first-order loop (`find?_bind_eq_slotTableIn`); `⟨0⟩` when there is none, which
no reader consults (each asks `slotPresentIn` first). -/
def slotTableIn (level index : Nat) : List PageTableSlot → SeLe4n.ObjId
  | [] => ⟨0⟩
  | s :: rest => if s.level == level && s.index == index then s.table else slotTableIn level index rest

theorem slotPresentIn_eq (level index : Nat) (ts : List PageTableSlot) :
    slotPresentIn level index ts = (ts.find? fun s => s.level == level && s.index == index).isSome := by
  induction ts with
  | nil => rfl
  | cons s rest ih =>
    simp only [slotPresentIn, List.find?_cons]
    cases s.level == level && s.index == index <;> simp [ih]

/-- A `find?` of a slot followed by a read of its table is the first-order pair
of loops. -/
theorem find?_bind_eq_slotTableIn {β : Type} (level index : Nat) (ts : List PageTableSlot)
    (g : SeLe4n.ObjId → Option β) :
    (ts.find? fun s => s.level == level && s.index == index).bind (fun s => g s.table) =
      if slotPresentIn level index ts then g (slotTableIn level index ts) else none := by
  induction ts with
  | nil => rfl
  | cons s rest ih =>
    simp only [slotPresentIn, slotTableIn, List.find?_cons]
    cases h : s.level == level && s.index == index <;> simp [ih]

/-- WS-ZA ZA5.4: **does the walk hold `table` at `(level, index)`**, read as a
first-order loop — `tables.contains` of that slot without building it
(`slotHeldIn_eq`). -/
def slotHeldIn (level index : Nat) (table : SeLe4n.ObjId) : List PageTableSlot → Bool
  | [] => false
  | s :: rest =>
    (s.level == level && s.index == index && s.table == table) || slotHeldIn level index table rest

theorem slotHeldIn_eq (level index : Nat) (table : SeLe4n.ObjId) (ts : List PageTableSlot) :
    slotHeldIn level index table ts = ts.contains { level := level, index := index, table := table } := by
  induction ts with
  | nil => rfl
  | cons s rest ih =>
    simp only [slotHeldIn, List.contains_cons, ih]
    congr 1
    obtain ⟨l, i, t⟩ := s
    rw [Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, beq_iff_eq, PageTableSlot.mk.injEq]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1.symm, h2.symm, h3.symm⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1.symm, h2.symm⟩, h3.symm⟩

/-- WS-ZA ZA5.4: `walkComplete` unrolled over the three levels, each a
first-order loop (`walkComplete_eq_unrolled`). -/
def walkCompleteUnrolled (root : VSpaceRoot) (vaddr : SeLe4n.VAddr) : Bool :=
  slotPresentIn 1 (PageTableSlot.indexOf 1 vaddr) root.tables &&
  slotPresentIn 2 (PageTableSlot.indexOf 2 vaddr) root.tables &&
  slotPresentIn 3 (PageTableSlot.indexOf 3 vaddr) root.tables

@[csimp] theorem walkComplete_eq_unrolled : @walkComplete = @walkCompleteUnrolled := by
  funext root vaddr
  simp [walkComplete, walkCompleteUnrolled, translationLevels, slotAt?, slotPresentIn_eq,
    Bool.and_assoc]

/-- WS-ZA ZA5.4: `translationReady` over the unrolled walk, so the map check
compiled before `walkComplete_eq_unrolled` does not keep the closure form
(`translationReady_eq_unrolled`). -/
def translationReadyUnrolled (root : VSpaceRoot) (vaddr : SeLe4n.VAddr) : Bool :=
  root.tableBase.isSome && walkCompleteUnrolled root vaddr

@[csimp] theorem translationReady_eq_unrolled : @translationReady = @translationReadyUnrolled := by
  funext root vaddr
  rw [translationReady, translationReadyUnrolled, walkComplete_eq_unrolled]

/-- WS-ZA ZA5.4: `missingLevel?` unrolled over the three levels; each `some` is a
constant (`missingLevel?_eq_unrolled`). -/
def missingLevelUnrolled (root : VSpaceRoot) (vaddr : SeLe4n.VAddr) : Option Nat :=
  if !slotPresentIn 1 (PageTableSlot.indexOf 1 vaddr) root.tables then some 1
  else if !slotPresentIn 2 (PageTableSlot.indexOf 2 vaddr) root.tables then some 2
  else if !slotPresentIn 3 (PageTableSlot.indexOf 3 vaddr) root.tables then some 3
  else none

@[csimp] theorem missingLevel?_eq_unrolled : @missingLevel? = @missingLevelUnrolled := by
  funext root vaddr
  simp only [missingLevel?, missingLevelUnrolled, translationLevels, slotAt?, slotPresentIn_eq]
  cases h1 : (root.tables.find? fun s => s.level == 1 && s.index == PageTableSlot.indexOf 1 vaddr) <;>
    cases h2 : (root.tables.find? fun s => s.level == 2 && s.index == PageTableSlot.indexOf 2 vaddr) <;>
    cases h3 : (root.tables.find? fun s => s.level == 3 && s.index == PageTableSlot.indexOf 3 vaddr) <;>
    simp [List.find?, h1, h2, h3]

/-- WS-G6/F-P05: O(1) amortized page lookup via `HashMap[vaddr]?`.
WS-H11: Returns `(PAddr × PagePermissions)` pair. -/
def lookup (root : VSpaceRoot) (vaddr : SeLe4n.VAddr) : Option (SeLe4n.PAddr × PagePermissions) :=
  root.mappings[vaddr]?

/-- WS-ZA ZA5.2: `lookup` as compiled: through the table's own entry
(`RHTable.getEntry?`), so the inlined read's `some` meets its caller's `match`
and is never built (`SystemState.objectEntry?`'s pattern). -/
@[inline] def lookupByEntry (root : VSpaceRoot) (vaddr : SeLe4n.VAddr) :
    Option (SeLe4n.PAddr × PagePermissions) :=
  match root.mappings.getEntry? vaddr with
  | some e => some e.value
  | none => none

@[csimp] theorem lookup_eq_byEntry : @lookup = @lookupByEntry := by
  funext root vaddr
  unfold lookup lookupByEntry
  show root.mappings.get? vaddr = _
  rw [SeLe4n.Kernel.RobinHood.RHTable.get?_eq_getEntry?_map]
  cases root.mappings.getEntry? vaddr <;> rfl

/-- WS-H11: O(1) amortized physical-address-only lookup for backward compatibility. -/
def lookupAddr (root : VSpaceRoot) (vaddr : SeLe4n.VAddr) : Option SeLe4n.PAddr :=
  (root.lookup vaddr).map Prod.fst

/-- WS-G6/F-P05: O(1) amortized page mapping via `HashMap.insert`.
Returns `none` if a mapping for `vaddr` already exists (conflict).
WS-H11: Accepts permissions alongside the physical address.
AK3-B (A-H01): Additionally rejects W+X permission combinations as a
defense-in-depth layer — if upstream callers forget to check W^X before
calling `mapPage`, this layer still prevents installation of a writable +
executable page into the VSpace root. -/
def mapPage (root : VSpaceRoot) (vaddr : SeLe4n.VAddr) (paddr : SeLe4n.PAddr)
    (perms : PagePermissions := PagePermissions.readOnly) : Option VSpaceRoot :=
  if !perms.wxCompliant then none
  -- WS-BP BP7.2: both addresses are page-aligned.  The mapping table is keyed by
  -- the page base (`VAddr.pageBase`), and a hardware walk indexes by the page
  -- the address falls in — so two unaligned keys inside one page would be two
  -- mappings here and one translation on the machine.
  else if paddr.toNat % SeLe4n.pageBytes != 0 || vaddr.toNat % SeLe4n.pageBytes != 0 then none
  else match root.mappings[vaddr]? with
  | some _ => none
  | none => some { root with mappings := root.mappings.insert vaddr (paddr, perms) }

/-- **PR #845 review (P2)**: every physical address installed by `mapPage` is
page-aligned.  The structural counterpart to `mapPage_wxCompliant` — stated
about the *stored* mapping, so it is the property downstream consumers (the
SM7.D cache-maintenance operands, which the HAL rounds down to the containing
page) actually need. -/
theorem mapPage_pageAligned {root root' : VSpaceRoot} {vaddr : SeLe4n.VAddr}
    {paddr : SeLe4n.PAddr} {perms : PagePermissions}
    (hMap : root.mapPage vaddr paddr perms = some root') :
    paddr.toNat % SeLe4n.pageBytes = 0 := by
  unfold mapPage at hMap
  split at hMap
  · exact absurd hMap (by simp)
  · split at hMap
    · exact absurd hMap (by simp)
    · rename_i hAligned
      simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, Decidable.not_not] at hAligned
      exact hAligned.1

/-- **WS-BP BP7.2**: every virtual address `mapPage` installs is page-aligned —
the key a hardware walk reaches, so the model's mappings and the machine's
translations are in one-to-one correspondence. -/
theorem mapPage_vaddrAligned {root root' : VSpaceRoot} {vaddr : SeLe4n.VAddr}
    {paddr : SeLe4n.PAddr} {perms : PagePermissions}
    (hMap : root.mapPage vaddr paddr perms = some root') :
    vaddr.toNat % SeLe4n.pageBytes = 0 := by
  unfold mapPage at hMap
  split at hMap
  · exact absurd hMap (by simp)
  · split at hMap
    · exact absurd hMap (by simp)
    · rename_i hAligned
      simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, Decidable.not_not] at hAligned
      exact hAligned.2

/-- WS-G6/F-P05: O(1) amortized page unmapping via `HashMap.erase`.
Returns `none` if no mapping exists for `vaddr`. -/
def unmapPage (root : VSpaceRoot) (vaddr : SeLe4n.VAddr) : Option VSpaceRoot :=
  match root.mappings[vaddr]? with
  | none => none
  | some _ => some { root with mappings := root.mappings.erase vaddr,
                               mappingEpochs := root.mappingEpochs.erase vaddr }

/-- WS-G6: No-virtual-overlap property. With HashMap-backed mappings, this is
trivially true by key uniqueness: each VAddr maps to at most one entry.
Uses `lookup` (which delegates to `HashMap[vaddr]?`) for type resolution. -/
def noVirtualOverlap (root : VSpaceRoot) : Prop :=
  ∀ v e₁ e₂,
    root.lookup v = some e₁ →
    root.lookup v = some e₂ →
    e₁ = e₂

/-- WS-G6: With HashMap-backed mappings, `noVirtualOverlap` is trivially true
for *every* `VSpaceRoot` — key uniqueness in the HashMap guarantees that a
single `lookup` can return at most one value, so `e₁ = e₂` follows by
injection. This subsumes `noVirtualOverlap_empty`, `mapPage_noVirtualOverlap`,
and `unmapPage_noVirtualOverlap`, which are retained for API compatibility. -/
theorem noVirtualOverlap_trivial (root : VSpaceRoot) : noVirtualOverlap root := by
  intro v e₁ e₂ h₁ h₂; rw [h₁] at h₂; exact Option.some.inj h₂

/-- AK7-J (F-M10 / MEDIUM): Physical-frame uniqueness — within a single
VSpace root, two distinct virtual addresses never map to the same
physical address.

Rationale: `noVirtualOverlap_trivial` collapses trivially on functional
maps (key uniqueness on the left), so it does not assert any structural
property on the *physical* side of the mapping. `noPhysicalFrameCollision`
closes the gap by asserting that the mappings table is injective on the
physical-address projection — two distinct VAs that both resolve with
`some (p, _)` share no PA.

In `seLe4n` this predicate is not enforced structurally by the
`RHTable` key set (the hash keys are VAddrs, not PAddrs). Kernel
operations that wish to establish the invariant must verify it at the
boundary — e.g., `vspaceMapPage` callers can check the PA is fresh
before insertion. -/
def noPhysicalFrameCollision (root : VSpaceRoot) : Prop :=
  ∀ v₁ v₂ p perms₁ perms₂,
    root.lookup v₁ = some (p, perms₁) →
    root.lookup v₂ = some (p, perms₂) →
    v₁ = v₂

/-- AK7-J (F-M10): An empty VSpace trivially satisfies
`noPhysicalFrameCollision` — no lookup ever returns `some`. -/
theorem noPhysicalFrameCollision_empty (asid : SeLe4n.ASID) :
    noPhysicalFrameCollision { asid := asid, mappings := {} } := by
  intro v₁ _ _ _ _ h₁ _
  have : ({} : SeLe4n.Kernel.RobinHood.RHTable SeLe4n.VAddr (SeLe4n.PAddr × PagePermissions))[v₁]?
      = none :=
    SeLe4n.Kernel.RobinHood.RHTable.getElem?_empty 16 (by omega) v₁
  simp [VSpaceRoot.lookup, this] at h₁

/-- WS-G6: Empty mappings trivially satisfy no-virtual-overlap.
Follows directly from `noVirtualOverlap_trivial` but retained for API compatibility. -/
theorem noVirtualOverlap_empty (asid : SeLe4n.ASID) :
    noVirtualOverlap { asid := asid, mappings := {} } :=
  noVirtualOverlap_trivial _

/-- WS-G6: After unmapping vaddr, lookup returns none. Maps to `RHTable.getElem?_erase_self`.
Requires `invExt` for RHTable erase correctness. -/
theorem lookup_unmapPage_eq_none
    (root root' : VSpaceRoot)
    (vaddr : SeLe4n.VAddr)
    (hExt : root.mappings.invExt)
    (hUnmap : root.unmapPage vaddr = some root') :
    root'.lookup vaddr = none := by
  unfold unmapPage at hUnmap
  cases hLookup : root.mappings[vaddr]? with
  | none => simp [hLookup] at hUnmap
  | some p =>
      simp [hLookup] at hUnmap
      cases hUnmap
      simp only [lookup]
      exact SeLe4n.Kernel.RobinHood.RHTable.getElem?_erase_self root.mappings vaddr hExt

/-- WS-G6/WS-H11: After mapping vaddr→paddr with perms, lookup returns the entry.
Maps to `RHTable.getElem?_insert_self`. Requires `invExt` for RHTable correctness. -/
theorem lookup_mapPage_eq
    (root root' : VSpaceRoot)
    (vaddr : SeLe4n.VAddr)
    (paddr : SeLe4n.PAddr)
    (perms : PagePermissions)
    (hExt : root.mappings.invExt)
    (hMap : root.mapPage vaddr paddr perms = some root') :
    root'.lookup vaddr = some (paddr, perms) := by
  unfold mapPage at hMap
  split at hMap
  · -- AK3-B: !perms.wxCompliant case — none, contradiction
    simp at hMap
  · split at hMap
    · -- PR #845 review (P2): unaligned paddr case — none, contradiction
      simp at hMap
    · cases hLookup : root.mappings[vaddr]? with
      | some p => simp [hLookup] at hMap
      | none =>
          simp [hLookup] at hMap
          cases hMap
          simp only [lookup]
          exact SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_self
            root.mappings vaddr (paddr, perms) hExt

/-- WS-H11: After mapping vaddr→paddr with default perms, lookupAddr returns paddr.
Requires `invExt` for RHTable correctness. -/
theorem lookupAddr_mapPage_eq
    (root root' : VSpaceRoot)
    (vaddr : SeLe4n.VAddr)
    (paddr : SeLe4n.PAddr)
    (perms : PagePermissions)
    (hExt : root.mappings.invExt)
    (hMap : root.mapPage vaddr paddr perms = some root') :
    root'.lookupAddr vaddr = some paddr := by
  simp [lookupAddr, lookup_mapPage_eq root root' vaddr paddr perms hExt hMap]

/-- F-08 helper: `mapPage` preserves the VSpace root ASID. -/
theorem mapPage_asid_eq
    (root root' : VSpaceRoot)
    (vaddr : SeLe4n.VAddr)
    (paddr : SeLe4n.PAddr)
    (perms : PagePermissions := PagePermissions.readOnly)
    (hMap : root.mapPage vaddr paddr perms = some root') :
    root'.asid = root.asid := by
  unfold mapPage at hMap
  split at hMap
  · simp at hMap
  · split at hMap
    · simp at hMap
    · cases hLookup : root.mappings[vaddr]? with
      | some _ => simp [hLookup] at hMap
      | none =>
          simp [hLookup] at hMap; cases hMap; rfl

/-- F-08 helper: `unmapPage` preserves the VSpace root ASID. -/
theorem unmapPage_asid_eq
    (root root' : VSpaceRoot)
    (vaddr : SeLe4n.VAddr)
    (hUnmap : root.unmapPage vaddr = some root') :
    root'.asid = root.asid := by
  unfold unmapPage at hUnmap
  cases hLookup : root.mappings[vaddr]? with
  | none => simp [hLookup] at hUnmap
  | some _ =>
      simp [hLookup] at hUnmap; cases hUnmap; rfl

/-- WS-G6: If `lookup` returns `none`, the vaddr has no mapping in the RHTable. -/
theorem lookup_eq_none_iff
    (root : VSpaceRoot)
    (vaddr : SeLe4n.VAddr) :
    root.lookup vaddr = none ↔ vaddr ∉ root.mappings := by
  constructor
  · -- lookup = none → vaddr ∉ mappings
    intro h hMem
    simp only [lookup] at h
    change root.mappings.get? vaddr = none at h
    have hIsSome := (SeLe4n.Kernel.RobinHood.RHTable.mem_iff_isSome_getElem?
      root.mappings vaddr).mp hMem
    rw [h] at hIsSome; exact absurd hIsSome (by simp)
  · -- vaddr ∉ mappings → lookup = none
    intro h
    simp only [lookup]
    show root.mappings.get? vaddr = none
    cases hc : root.mappings.get? vaddr with
    | none => rfl
    | some v =>
      exfalso; apply h
      exact (SeLe4n.Kernel.RobinHood.RHTable.mem_iff_isSome_getElem? root.mappings vaddr).mpr
        (by simp [hc])

/-- WS-G6: A successful `mapPage` preserves the no-virtual-overlap invariant.
With HashMap-backed mappings, `noVirtualOverlap` is trivially true by key uniqueness. -/
theorem mapPage_noVirtualOverlap
    (root root' : VSpaceRoot)
    (vaddr : SeLe4n.VAddr)
    (paddr : SeLe4n.PAddr)
    (perms : PagePermissions)
    (_hOverlap : noVirtualOverlap root)
    (hMap : root.mapPage vaddr paddr perms = some root') :
    noVirtualOverlap root' := by
  unfold mapPage at hMap
  cases hLookup : root.mappings[vaddr]? with
  | some _ => simp [hLookup] at hMap
  | none =>
      simp [hLookup] at hMap; cases hMap
      exact noVirtualOverlap_trivial _

/-- WS-G6: A successful `unmapPage` preserves the no-virtual-overlap invariant.
With HashMap-backed mappings, `noVirtualOverlap` is trivially true by key uniqueness. -/
theorem unmapPage_noVirtualOverlap
    (root root' : VSpaceRoot)
    (vaddr : SeLe4n.VAddr)
    (_hOverlap : noVirtualOverlap root)
    (hUnmap : root.unmapPage vaddr = some root') :
    noVirtualOverlap root' := by
  unfold unmapPage at hUnmap
  cases hLookup : root.mappings[vaddr]? with
  | none => simp [hLookup] at hUnmap
  | some _ =>
      simp [hLookup] at hUnmap; cases hUnmap
      exact noVirtualOverlap_trivial _

/-- TPI-001 helper: mapping vaddr does not affect lookup of a different vaddr'.
Maps to `RHTable.getElem?_insert_ne` with the inequality hypothesis.
Requires `invExt` for RHTable correctness. -/
theorem lookup_mapPage_ne
    (root root' : VSpaceRoot)
    (vaddr vaddr' : SeLe4n.VAddr)
    (paddr : SeLe4n.PAddr)
    (perms : PagePermissions)
    (hNe : vaddr ≠ vaddr')
    (hExt : root.mappings.invExt)
    (hMap : root.mapPage vaddr paddr perms = some root') :
    root'.lookup vaddr' = root.lookup vaddr' := by
  unfold mapPage at hMap
  split at hMap
  · simp at hMap
  · split at hMap
    · simp at hMap
    · cases hLookup : root.mappings[vaddr]? with
      | some _ => simp [hLookup] at hMap
      | none =>
          simp [hLookup] at hMap; cases hMap
          simp only [lookup]
          exact SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_ne root.mappings vaddr vaddr'
            (paddr, perms) (fun h => hNe (eq_of_beq h)) hExt

/-- TPI-001 helper: unmapPage at vaddr does not affect lookup of a different vaddr'.
Maps to `RHTable.getElem?_erase_ne_K` with the inequality hypothesis.
Requires `invExtK` for RHTable erase correctness. -/
theorem lookup_unmapPage_ne
    (root root' : VSpaceRoot)
    (vaddr vaddr' : SeLe4n.VAddr)
    (hNe : vaddr ≠ vaddr')
    (hK : root.mappings.invExtK)
    (hUnmap : root.unmapPage vaddr = some root') :
    root'.lookup vaddr' = root.lookup vaddr' := by
  unfold unmapPage at hUnmap
  cases hLookup : root.mappings[vaddr]? with
  | none => simp [hLookup] at hUnmap
  | some _ =>
      simp [hLookup] at hUnmap; cases hUnmap
      simp only [lookup]
      exact SeLe4n.Kernel.RobinHood.RHTable.getElem?_erase_ne_K root.mappings vaddr vaddr'
        (fun h => hNe (eq_of_beq h)) hK

end VSpaceRoot

/-- **WS-BP BP7.1**: a **frame** — one page of physical memory a thread may be
given access to.

Physical memory is authority: an address space maps a page only by presenting a
capability to the frame that owns it, and the physical address the mapping
installs is the frame's `base`, never a value the caller supplies.  Until this
object existed `.vspaceMap` took the physical address from a message register,
checked against nothing but the physical-address width, alignment and the
device-execute rule, so a holder of any writable VSpace capability could map the
kernel image, the Lean heap holding every kernel object, another domain's RAM or
the interrupt controller — latent only because no mapping reached hardware yet.

A frame is exactly one `pageBytes` page, page-aligned (`wellFormed`), and never
changes after creation: `base` and `isDevice` are fixed at the carve that makes
it.  `isDevice` records that the page is MMIO rather than RAM, which the mapping
path turns into "never executable, never cacheable".  The lock hierarchy's
`page` kind (level 9) is the ghost lock key this object makes real. -/
structure FrameObject where
  base : SeLe4n.PAddr
  isDevice : Bool := false
  /-- **PR #904 review (`v0.36.41`): how many times this frame has been mapped
      by a capability.**  `.vspaceMap` hands the current value to the mapping it
      makes (`FrameMapping.epoch`, `VSpaceRoot.mappingEpochs`) and advances it,
      so no two mappings of one frame share an epoch while the frame exists. -/
  mapEpoch : Nat := 0
  deriving Repr, DecidableEq

namespace FrameObject

/-- **WS-BP BP7.1**: a frame's base is page-aligned — the only shape a page
descriptor can name, and the one every carve that creates a frame produces. -/
def wellFormed (f : FrameObject) : Prop :=
  f.base.toNat % SeLe4n.pageBytes = 0

instance (f : FrameObject) : Decidable f.wellFormed :=
  inferInstanceAs (Decidable (_ = _))

end FrameObject

/-- **WS-BP BP7.1 (`v0.36.12`): where a page table is installed** — the address
space, the level and the index of the slot that names it.  The other half of
`VSpaceRoot.tables`: the two are written together, by `.pageTableMap` and
`.pageTableUnmap`, so a table is installed in at most one slot at a time. -/
structure PageTableInstall where
  root : SeLe4n.ObjId
  level : Nat
  index : Nat
  deriving Repr, DecidableEq

/-- **WS-BP BP7.1 (`v0.36.12`): an intermediate translation table** — seL4's
`seL4_ARM_PageTable`.

A page of RAM, carved from an untyped and zeroed before any capability to it
exists, that holds one level of an address space's translation.  It is a
distinct kind from a frame because what it holds is **the kernel's**: a page a
thread could map and write would let it write its own translation, so
`.vspaceMap` maps frames only, and a table reaches an address space only through
`.pageTableMap`.  `installedIn` reads the one slot that names it, `none` while
it is installed nowhere.

WS-ZA ZA5.4: the slot is held as plain fields under a flag, as seL4's page-table
capability holds `capPTIsMapped`, `capPTMappedASID` and `capPTMappedAddress`:
an install writes the fields and a removal clears the flag, leaving the fields
as they were, so neither builds a record. -/
structure PageTableObject where
  base : SeLe4n.PAddr
  /-- Whether the table is installed; the three fields below name the slot
      only while it is. -/
  installed : Bool := false
  installRoot : SeLe4n.ObjId := ⟨0⟩
  installLevel : Nat := 0
  installIndex : Nat := 0
  /-- WS-ZA ZA5.4: the cell the table's slot takes in the root that holds it,
      kept here while it is installed nowhere (`TableSlotCell`).  A new
      table's cell is part of the table's own memory: a retype carves it with
      the object (`KernelObject.unshare` gives each its own). -/
  slotCell : TableSlotCell := Squash.mk [⟨0, 0, ⟨0⟩⟩]
  deriving Repr, DecidableEq

namespace PageTableObject

/-- The slot that names the table, `none` while it is installed nowhere. -/
@[inline] def installedIn (p : PageTableObject) : Option PageTableInstall :=
  if p.installed then some ⟨p.installRoot, p.installLevel, p.installIndex⟩ else none

/-- The table's record once it is installed nowhere: the flag cleared and the
slot words zeroed with it, so a removed table carries no trace of the slot that
named it and every uninstalled table projects the same way. -/
@[inline] def uninstalled (p : PageTableObject) : PageTableObject :=
  { p with installed := false, installRoot := ⟨0⟩, installLevel := 0, installIndex := 0 }

@[simp] theorem installedIn_uninstalled (p : PageTableObject) :
    p.uninstalled.installedIn = none := rfl

/-- WS-ZA ZA5.4: the spare slot cell is no part of what a table is. -/
@[simp] theorem with_slotCell (p : PageTableObject) (v : TableSlotCell) :
    { p with slotCell := v } = p := by
  cases p
  simp only [PageTableObject.mk.injEq, true_and]
  exact Subsingleton.elim _ _

@[simp] theorem base_uninstalled (p : PageTableObject) : p.uninstalled.base = p.base := rfl

/-- A table's page is page-aligned — the only shape a table descriptor can name,
and the one every carve produces. -/
def wellFormed (p : PageTableObject) : Prop :=
  p.base.toNat % SeLe4n.pageBytes = 0

instance (p : PageTableObject) : Decidable p.wellFormed :=
  inferInstanceAs (Decidable (_ = _))

end PageTableObject

/-- WS-G6/WS-H7: `BEq` instance for `VSpaceRoot` using entry-wise comparison on the
HashMap-backed mappings. Two VSpaceRoots are equal iff their ASID and all
mapping entries agree (same size + every key maps to the same value).
WS-H11: Updated for enriched `(PAddr × PagePermissions)` value type. -/
instance : BEq VSpaceRoot where
  beq a b :=
    a.asid == b.asid &&
    a.mappings.size == b.mappings.size &&
    a.mappings.fold (init := true) (fun acc k v => acc && b.mappings[k]? == some v) &&
    -- WS-BP BP7.1: the table page and the intermediate tables are part of what
    -- an address space is.
    a.tableBase == b.tableBase &&
    a.tables == b.tables

/-- WS-H7: VSpaceRoot BEq correctness — the fold-based comparison is sound.
When BEq returns true, the two VSpaceRoots have equal ASIDs and identical
mapping entries. The proof relies on HashMap key uniqueness: size equality +
forward containment guarantees bidirectional equality.

Note: The full `beq_correct` biconditional (`(a == b) = true ↔ a = b`) requires
extensional equality axioms beyond the RHTable surface. We prove
the forward (soundness) direction; the reverse follows from `BEq.refl` when the
structures are definitionally equal. -/
theorem VSpaceRoot.beq_sound (a b : VSpaceRoot) (h : (a == b) = true) :
    a.asid = b.asid ∧ a.mappings.size = b.mappings.size := by
  -- WS-SM SM3.A.7 audit-pass note: written with `obtain` so that adding a
  -- conjunct to the BEq definition does not silently shift positional indices.
  simp only [BEq.beq, Bool.and_eq_true_iff, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hAsid, hSize⟩, _hFold⟩, _hBase⟩, _hTables⟩ := h
  exact ⟨hAsid, hSize⟩

/-- Y2-D: BEq reflexivity for VSpaceRoot under the Robin Hood invariant.

    Proves the converse direction of `beq_sound`: if `a = b` and the mappings
    satisfy `invExt`, then `(a == b) = true`. Substituting `b := a`, this gives
    BEq reflexivity `(a == a) = true` — the strongest achievable result.

    **Proof strategy**: The fold checks `a.mappings.get? k == some v` for each
    entry `(k, v)` in the slots array. `RHTable.slot_entry_implies_get` (proven
    via `getLoop_finds_present` under `invExt`) guarantees `get? k = some v` for
    each stored entry. Combined with `LawfulBEq` reflexivity on the value type
    `(PAddr × PagePermissions)`, each fold step preserves `acc = true`.

    **Why `invExt` is required**: Without the Robin Hood invariants (`distCorrect`,
    `probeChainDominant`, `noDupKeys`), the `get?` probe sequence may not find
    entries that are stored in the slots array. The `invExt` hypothesis is always
    available in practice because all kernel VSpaceRoots are constructed through
    `vspaceMapPage`/`vspaceUnmapPage` which preserve `invExt`.

    **Why full `LawfulBEq VSpaceRoot` is not achievable**: `LawfulBEq` requires
    `eq_of_beq : (a == b) = true → a = b` where `=` is structural equality.
    The VSpaceRoot BEq compares *logical content* (same key-value pairs via
    `get?`), but two `RHTable`s with identical logical content can have different
    backing arrays from different insertion orders. Robin Hood hashing does NOT
    produce a canonical layout — the `probeChainDominant` invariant constrains
    relative ordering but not absolute slot assignment. Therefore, BEq-true does
    not imply structural equality, making `eq_of_beq` provably false in general.

    L-FND-3: `LawfulBEq VSpaceRoot` limitation closed with rigorous analysis.
    Reflexivity under `invExt` is the strongest achievable result.

    **Impact on kernel correctness**: None. VSpaceRoot equality is never used
    as a proof obligation in any kernel invariant or preservation theorem. -/
theorem VSpaceRoot.beq_refl (a : VSpaceRoot) (hExt : a.mappings.invExt) :
    (a == a) = true := by
  unfold BEq.beq instBEqVSpaceRoot
  simp only [beq_self_eq_true, Bool.true_and, Bool.and_true]
  -- Remaining goal: the fold over a.mappings produces true
  unfold SeLe4n.Kernel.RobinHood.RHTable.fold
  apply Array.foldl_induction (motive := fun _ acc => acc = true)
  · rfl
  · intro i acc hAcc
    simp only []
    split
    · exact hAcc
    · rename_i e hSlot
      -- e is an entry at slot i in the array; slots.size = capacity
      have hi : i.val < a.mappings.capacity :=
        a.mappings.hSlotsLen ▸ i.isLt
      have hGet := SeLe4n.Kernel.RobinHood.RHTable.slot_entry_implies_get
        a.mappings i.val hi e hSlot hExt
      rw [hAcc, Bool.true_and]
      show (a.mappings.get? e.key == some e.value) = true
      rw [hGet]; exact beq_self_eq_true _

namespace CNode

open SeLe4n.Kernel.RobinHood

inductive ResolveError where
  | depthMismatch
  | guardMismatch
  deriving Repr, DecidableEq

def empty : CNode :=
  ofSlots 0 0 0 0 SeLe4n.UniqueSlotMap.empty

/-- Construct a CNode at a given depth with guard/radix parameters.
    WS-RC R4.A: `s` is now `UniqueSlotMap Capability` carrying `invExtK`
    structurally. Callers that previously passed `RHTable.empty 16` should
    pass `SeLe4n.UniqueSlotMap.empty`; callers that built tables from
    literals via `RHTable.ofList` should use `SeLe4n.UniqueSlotMap.ofListWF`. -/

def mk' (d gw gv rw : Nat) : CNode :=
  ofSlots d gw gv rw SeLe4n.UniqueSlotMap.empty

/-- Number of addressable slots represented by this CNode radix width. -/
def slotCount (node : CNode) : Nat :=
  2 ^ node.radixWidth

/-- Total bits consumed by one resolution step at this CNode. -/
def bitsConsumed (node : CNode) : Nat :=
  node.guardWidth + node.radixWidth

/-- T2-J (L-NEW-4): CNode guard value is bounded by guard width.
    The guard value must fit in `guardWidth` bits, i.e., `guardValue < 2^guardWidth`.
    When `guardWidth = 0`, only `guardValue = 0` is valid (no guard bits). -/
def guardBounded (cn : CNode) : Prop :=
  cn.guardValue < 2 ^ cn.guardWidth

instance (cn : CNode) : Decidable cn.guardBounded :=
  inferInstanceAs (Decidable (cn.guardValue < 2 ^ cn.guardWidth))

/-- WS-H13 + T2-J: CNode well-formedness — consumed bits fit in remaining depth,
at least one bit is consumed (ensures termination of multi-level resolution),
and the guard value fits within the guard width (L-NEW-4). -/
def wellFormed (node : CNode) : Prop :=
  node.bitsConsumed ≤ node.depth ∧ 0 < node.bitsConsumed ∧ node.guardBounded

/-- Resolve a CPtr/depth pair into the local slot index using guard/radix semantics.

WS-H13: Uses `guardWidth` and `radixWidth` fields directly for compressed-path
resolution. The `bitsRemaining` parameter indicates how many address bits
remain to be resolved at this level.

S4-C: The slot index and guard are bit fields of the address's 64-bit word
(`CPtr.slotBits`, `CPtr.guardBits`); an address is a machine word since WS-ZA
ZA4.8, so the word mask in their statement is the identity. -/
def resolveSlot (node : CNode) (cptr : SeLe4n.CPtr) (bitsRemaining : Nat) : Except ResolveError SeLe4n.Slot :=
  let consumed := node.bitsConsumed
  if bitsRemaining < consumed then
    .error .depthMismatch
  else
    -- S4-C: the slot index and guard are bit fields of the address word
    let slotIndex := cptr.slotBits (bitsRemaining - consumed) node.radixWidth
    let guardExtracted := cptr.guardBits (bitsRemaining - consumed) node.radixWidth node.guardWidth
    if guardExtracted = node.guardValue then
      .ok (SeLe4n.Slot.ofNat slotIndex)
    else
      .error .guardMismatch

/-- S4-C: The word64 mask is idempotent — masking an already-bounded value
    produces the same result. This ensures `resolveSlot` behaves identically
    for bounded and unbounded inputs when the value fits in 64 bits. -/
theorem resolveSlot_mask_idempotent (n : Nat) (h : n < SeLe4n.machineWordMax) :
    n % SeLe4n.machineWordMax = n :=
  Nat.mod_eq_of_lt h

/-- WS-G5/F-P03: O(1) amortized slot lookup via `RHTable.get?`.  WS-ZA ZA5.3:
compiled code reads the slot array instead (`lookup_eq_lookupCells`). -/
noncomputable def lookup (node : CNode) (slot : SeLe4n.Slot) : Option Capability :=
  node.slots.get? slot

/-- WS-ZA ZA5.3: the slot's capability, read from the slot array.  Inlined, so
a caller that matches the result builds no `some` (WS-ZA ZA2.5). -/
@[inline] def lookupCells (node : CNode) (slot : SeLe4n.Slot) : Option Capability :=
  slotArrayGet node.cells slot

/-- WS-ZA ZA5.3: the map and the slot array answer every lookup alike
(`slots_agree`), so compiled code reads the array. -/
@[csimp] theorem lookup_eq_lookupCells : @lookup = @lookupCells := by
  funext node slot; exact node.slots_agree slot

/-- WS-ZA ZA5.3: the slot's array entry is its lookup. -/
theorem lookup_ofNat_eq_cells (node : CNode) (i : Nat) (h : i < node.cells.size) :
    node.lookup (SeLe4n.Slot.ofNat i) = node.cells[i] := by
  rw [lookup_eq_lookupCells]
  simp [lookupCells, slotArrayGet, SeLe4n.Slot.toNat_ofNat, h]

/-- WS-ZA ZA5.3: a fold over the occupied entries of the slot array, in slot
order.  It walks the array by index, so it builds nothing of its own.  The walk
counts down a fuel of one step per cell, structurally, so the kernel reduces it
too (boot-configuration proofs evaluate it by `decide`). -/
@[specialize] def foldCellsGo {γ : Type} (node : CNode)
    (f : γ → SeLe4n.Slot → Capability → γ) (fuel i : Nat) (acc : γ) : γ :=
  match fuel with
  | 0 => acc
  | fuel + 1 =>
    if h : i < node.cells.size then
      foldCellsGo node f fuel (i + 1) (match node.cells[i] with
        | some c => f acc (SeLe4n.Slot.ofNat i) c
        | none => acc)
    else acc

@[inline, inherit_doc foldCellsGo] def foldCells {γ : Type} (node : CNode) (init : γ)
    (f : γ → SeLe4n.Slot → Capability → γ) : γ :=
  foldCellsGo node f node.cells.size 0 init

theorem foldCells_go_preserves {γ : Type} (node : CNode)
    (f : γ → SeLe4n.Slot → Capability → γ) (P : γ → Prop)
    (hStep : ∀ acc s c, node.lookup s = some c → P acc → P (f acc s c)) :
    ∀ (fuel i : Nat) (acc : γ), P acc → P (foldCellsGo node f fuel i acc) := by
  intro fuel
  induction fuel with
  | zero => intro i acc hAcc; exact hAcc
  | succ fuel ih =>
    intro i acc hAcc
    simp only [foldCellsGo]
    split
    · rename_i h
      apply ih
      split
      · rename_i c hc
        exact hStep acc _ c (by rw [lookup_ofNat_eq_cells node i h]; exact hc) hAcc
      · exact hAcc
    · exact hAcc

/-- WS-ZA ZA5.3: a property kept by every step at an occupied slot holds after
the fold. -/
theorem foldCells_preserves {γ : Type} (node : CNode) (init : γ)
    (f : γ → SeLe4n.Slot → Capability → γ) (P : γ → Prop) (hInit : P init)
    (hStep : ∀ acc s c, node.lookup s = some c → P acc → P (f acc s c)) :
    P (node.foldCells init f) :=
  foldCells_go_preserves node f P hStep _ 0 init hInit

theorem foldCells_go_visited {γ : Type} (node : CNode)
    (f : γ → SeLe4n.Slot → Capability → γ) (P : γ → Prop) (R : SeLe4n.Slot → γ → Prop)
    (hStep : ∀ acc s c, node.lookup s = some c → P acc → P (f acc s c))
    (hEst : ∀ acc s c, node.lookup s = some c → P acc → R s (f acc s c))
    (hKeep : ∀ acc s c s', node.lookup s = some c → P acc → R s' acc → R s' (f acc s c)) :
    ∀ (fuel i : Nat) (acc : γ), node.cells.size ≤ i + fuel → P acc →
      (∀ j (hj : j < node.cells.size), j < i → ∀ c, node.cells[j] = some c →
        R (SeLe4n.Slot.ofNat j) acc) →
      P (foldCellsGo node f fuel i acc) ∧
        ∀ j (hj : j < node.cells.size), ∀ c, node.cells[j] = some c →
          R (SeLe4n.Slot.ofNat j) (foldCellsGo node f fuel i acc) := by
  intro fuel
  induction fuel with
  | zero =>
    intro i acc hFuel hP hR
    exact ⟨hP, fun j hj c hc => hR j hj (by omega) c hc⟩
  | succ fuel ih =>
    intro i acc hFuel hP hR
    simp only [foldCellsGo]
    split
    · rename_i h
      have hLk : node.lookup (SeLe4n.Slot.ofNat i) = node.cells[i] := lookup_ofNat_eq_cells node i h
      cases hc : node.cells[i] with
      | none =>
        refine ih (i + 1) acc (by omega) hP (fun j hj hji c hcj => ?_)
        by_cases hji' : j < i
        · exact hR j hj hji' c hcj
        · have hEq : j = i := by omega
          subst hEq
          exact absurd (hcj.symm.trans hc) (by simp)
      | some c0 =>
        refine ih (i + 1) _ (by omega) (hStep acc _ c0 (hLk.trans hc) hP)
          (fun j hj hji c hcj => ?_)
        by_cases hji' : j < i
        · exact hKeep acc _ c0 _ (hLk.trans hc) hP (hR j hj hji' c hcj)
        · have hEq : j = i := by omega
          subst hEq
          exact hEst acc _ c0 (hLk.trans hc) hP
    · rename_i h
      exact ⟨hP, fun j hj c hc => hR j hj (by omega) c hc⟩

/-- WS-ZA ZA5.3: a property each step establishes at its own slot and every
later step keeps holds after the fold at every occupied slot, beside a
property every step keeps. -/
theorem foldCells_preserves_visited {γ : Type} (node : CNode) (init : γ)
    (f : γ → SeLe4n.Slot → Capability → γ) (P : γ → Prop) (R : SeLe4n.Slot → γ → Prop)
    (hInit : P init)
    (hStep : ∀ acc s c, node.lookup s = some c → P acc → P (f acc s c))
    (hEst : ∀ acc s c, node.lookup s = some c → P acc → R s (f acc s c))
    (hKeep : ∀ acc s c s', node.lookup s = some c → P acc → R s' acc → R s' (f acc s c)) :
    P (node.foldCells init f) ∧
      ∀ s c, node.lookup s = some c → R s (node.foldCells init f) := by
  have h := foldCells_go_visited node f P R hStep hEst hKeep node.cells.size 0 init
    (by omega) hInit (fun j _ hj => absurd hj (Nat.not_lt_zero _))
  refine ⟨h.1, fun s c hs => ?_⟩
  have hl : s.toNat < node.cells.size := by
    rw [lookup_eq_lookupCells] at hs
    unfold lookupCells slotArrayGet at hs
    by_cases hl : s.toNat < node.cells.size
    · exact hl
    · simp [hl] at hs
  have := h.2 s.toNat hl c (by
    rw [← lookup_ofNat_eq_cells node _ hl, SeLe4n.Slot.ofNat_toNat]; exact hs)
  rwa [SeLe4n.Slot.ofNat_toNat] at this

theorem foldCells_go_and (node : CNode) (p : SeLe4n.Slot → Capability → Bool) :
    ∀ (fuel i : Nat) (acc : Bool), node.cells.size ≤ i + fuel →
      (foldCellsGo node (fun acc s c => acc && p s c) fuel i acc = true ↔
        acc = true ∧ ∀ (j : Nat) (hj : j < node.cells.size), i ≤ j →
          ∀ c, node.cells[j] = some c → p (SeLe4n.Slot.ofNat j) c = true) := by
  intro fuel
  induction fuel with
  | zero =>
    intro i acc hFuel
    simp only [foldCellsGo]
    constructor
    · intro hA; exact ⟨hA, fun j hj hij => absurd hj (by omega)⟩
    · exact fun h' => h'.1
  | succ fuel ih =>
    intro i acc hFuel
    simp only [foldCellsGo]
    split
    · rename_i h
      rw [ih (i + 1) _ (by omega)]
      constructor
      · rintro ⟨hA, hRest⟩
        have hA' : acc = true ∧ ∀ c, node.cells[i] = some c → p (SeLe4n.Slot.ofNat i) c = true := by
          revert hA; cases hc : node.cells[i] with
          | none => intro hA; exact ⟨hA, fun c hc' => by cases hc'⟩
          | some c0 =>
            intro hA; simp only [Bool.and_eq_true] at hA
            exact ⟨hA.1, fun c hc' => by cases hc'; exact hA.2⟩
        refine ⟨hA'.1, fun j hj hij c hc => ?_⟩
        by_cases hji : j = i
        · subst hji; exact hA'.2 c hc
        · exact hRest j hj (by omega) c hc
      · rintro ⟨hA, hAll⟩
        refine ⟨?_, fun j hj hij c hc => hAll j hj (by omega) c hc⟩
        cases hc : node.cells[i] with
        | none => exact hA
        | some c0 => simp only [hA, Bool.true_and]; exact hAll i h (Nat.le_refl _) c0 hc
    · rename_i h
      constructor
      · intro hA; exact ⟨hA, fun j hj hij => absurd hj (by omega)⟩
      · exact fun h' => h'.1

/-- WS-ZA ZA5.3: a conjunction folded over the slot array holds exactly when
it holds of every occupied slot. -/
theorem foldCells_and_eq_true_iff (node : CNode) (p : SeLe4n.Slot → Capability → Bool) :
    node.foldCells true (fun acc s c => acc && p s c) = true ↔
      ∀ s c, node.lookup s = some c → p s c = true := by
  unfold foldCells
  rw [foldCells_go_and node p _ 0 true (by omega)]
  constructor
  · rintro ⟨-, hAll⟩ s c hs
    have hl : s.toNat < node.cells.size := by
      rw [lookup_eq_lookupCells] at hs
      unfold lookupCells slotArrayGet at hs
      by_cases hl : s.toNat < node.cells.size
      · exact hl
      · simp [hl] at hs
    have := hAll s.toNat hl (Nat.zero_le _) c (by
      rw [← lookup_ofNat_eq_cells node _ hl, SeLe4n.Slot.ofNat_toNat]; exact hs)
    rwa [SeLe4n.Slot.ofNat_toNat] at this
  · intro hAll
    exact ⟨rfl, fun j hj _ c hc => hAll _ c (by rw [lookup_ofNat_eq_cells node j hj]; exact hc)⟩

/-- WS-ZA ZA5.3: the same conjunction folded over the ghost slot map. -/
theorem slots_fold_and_eq_true_iff (node : CNode) (p : SeLe4n.Slot → Capability → Bool) :
    node.slots.fold true (fun acc s c => acc && p s c) = true ↔
      ∀ s c, node.lookup s = some c → p s c = true := by
  constructor
  · intro hFold s c hs
    exact SeLe4n.Kernel.RobinHood.RHTable.fold_and_true_of_get? node.slots.table p hFold hs
  · intro hAll
    exact SeLe4n.Kernel.RobinHood.RHTable.fold_preserves_of_lookup node.slots.table true _
      (fun acc => acc = true) node.slots.hWF.1 rfl
      (fun acc k v hk hAcc => by simp only [hAcc, Bool.true_and]; exact hAll k v hk)

/-- WS-ZA ZA5.3: does every occupied slot satisfy `p`?  The theorems read it
over the slot map; compiled code walks the slot array (`allSlots_eq_allCells`). -/
noncomputable abbrev allSlots (node : CNode) (p : SeLe4n.Slot → Capability → Bool) : Bool :=
  node.slots.fold true (fun acc s c => acc && p s c)

/-- WS-ZA ZA5.3: `allSlots` over the slot array. -/
@[inline] def allCells (node : CNode) (p : SeLe4n.Slot → Capability → Bool) : Bool :=
  node.foldCells true (fun acc s c => acc && p s c)

@[csimp] theorem allSlots_eq_allCells : @allSlots = @allCells := by
  funext node p
  exact Bool.eq_iff_iff.2 ((slots_fold_and_eq_true_iff node p).trans
    (foldCells_and_eq_true_iff node p).symm)

/-- WS-ZA ZA5.3: how many slots hold a capability, counted over the slot array. -/
def occupiedCount (node : CNode) : Nat :=
  node.foldCells 0 fun n _ _ => n + 1

/-- WS-ZA ZA5.3: the occupied slots with their capabilities, in slot order,
read from the slot array.  Builds a list, so only tests and the trace harness
call it. -/
def occupiedSlots (node : CNode) : List (SeLe4n.Slot × Capability) :=
  (node.foldCells [] fun acc s c => (s, c) :: acc).reverse

/-- WS-ZA ZA5.4: an occupied slot is listed, with its capability. -/
theorem mem_occupiedSlots_of_lookup {node : CNode} {s : SeLe4n.Slot} {c : Capability}
    (h : node.lookup s = some c) : (s, c) ∈ node.occupiedSlots := by
  unfold occupiedSlots
  rw [List.mem_reverse]
  refine (foldCells_preserves_visited node [] (fun acc s c => (s, c) :: acc) (fun _ => True)
    (fun s acc => ∀ c, node.lookup s = some c → (s, c) ∈ acc) trivial
    (fun _ _ _ _ _ => trivial)
    (fun acc s c hs _ c' hc' => by
      rw [hs] at hc'; cases hc'; exact List.mem_cons_self ..)
    (fun _ _ _ _ _ _ hR c' hc' => List.mem_cons_of_mem _ (hR c' hc'))).2 s c h c h

/-- WS-ZA ZA5.4 part 26: **the occupancy links once slot `i` is filled**: a slot
that was empty is linked in at the head (`SlotOccupancy.linkWords`); one that
held a capability keeps its place.  Reads the slot array and the words only, so
a write that rebuilds the CNode in place keeps its link array in place too. -/
@[inline] def fillOcc (cells : Array (Option Capability)) (occ : Array Nat) (head i : Nat) :
    Array Nat :=
  if SlotOccupancy.occupied cells i then occ else SlotOccupancy.linkWords occ head i

/-- WS-ZA ZA5.4 part 26: the head word once slot `i` is filled. -/
@[inline] def fillHead (cells : Array (Option Capability)) (head i : Nat) : Nat :=
  if SlotOccupancy.occupied cells i then head else i + 1

/-- WS-ZA ZA5.4 part 26: **the occupancy links once slot `i` is emptied**: a slot
that held a capability is unlinked (`SlotOccupancy.unlinkWords`); an empty one
changes nothing. -/
@[inline] def emptyOcc (cells : Array (Option Capability)) (occ : Array Nat) (i : Nat) :
    Array Nat :=
  if SlotOccupancy.occupied cells i then SlotOccupancy.unlinkWords occ i else occ

/-- WS-ZA ZA5.4 part 26: the head word once slot `i` is emptied. -/
@[inline] def emptyHead (cells : Array (Option Capability)) (occ : Array Nat) (head i : Nat) :
    Nat :=
  if SlotOccupancy.occupied cells i then SlotOccupancy.unlinkHead occ head i else head

/-- Whether slot `i` holds a capability, out of line: the compiled writers read
it before they write the slot array, so the write is in place, and the read
adds no branch to the writer, so the writer still rebuilds its CNode in place. -/
@[noinline] def occupiedAt (cells : Array (Option Capability)) (i : Nat) : Bool :=
  SlotOccupancy.occupied cells i

/-- `fillOcc` and `fillHead` on the slot's occupancy read beforehand (`w`), as
the compiled writers take them, out of line for the same reason. -/
@[noinline] def fillOccOf (w : Bool) (occ : Array Nat) (head i : Nat) : Array Nat :=
  if w then occ else SlotOccupancy.linkWords occ head i

@[noinline] def fillHeadOf (w : Bool) (head i : Nat) : Nat := if w then head else i + 1

/-- `emptyOcc` and `emptyHead` on the slot's occupancy read beforehand (`w`):
the head is read off the links before they are unlinked, so the unlink is in
place. -/
@[noinline] def emptyOccOf (w : Bool) (occ : Array Nat) (i : Nat) : Array Nat :=
  if w then SlotOccupancy.unlinkWords occ i else occ

@[noinline] def emptyHeadOf (w : Bool) (occ : Array Nat) (head i : Nat) : Nat :=
  if w then SlotOccupancy.unlinkHead occ head i else head

theorem size_fillOcc (cells : Array (Option Capability)) (occ : Array Nat) (head i : Nat) :
    (fillOcc cells occ head i).size = occ.size := by
  unfold fillOcc; split
  · rfl
  · exact SlotOccupancy.size_linkWords _ _ _

theorem size_emptyOcc (cells : Array (Option Capability)) (occ : Array Nat) (i : Nat) :
    (emptyOcc cells occ i).size = occ.size := by
  unfold emptyOcc; split
  · exact SlotOccupancy.size_unlinkWords _ _
  · rfl

theorem occupied_set (cells : Array (Option Capability)) (i : Nat) (v : Option Capability)
    (h : i < cells.size) (j : Nat) :
    SlotOccupancy.occupied (cells.set i v h) j =
      if j = i then v.isSome else SlotOccupancy.occupied cells j := by
  unfold SlotOccupancy.occupied
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_set]
  by_cases e : i = j
  · subst e; simp [h]
  · simp [e, Ne.symm e]

theorem occupied_setIfInBounds (cells : Array (Option Capability)) (i : Nat)
    (v : Option Capability) (j : Nat) :
    SlotOccupancy.occupied (cells.setIfInBounds i v) j =
      if j = i ∧ i < cells.size then v.isSome else SlotOccupancy.occupied cells j := by
  unfold SlotOccupancy.occupied
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  by_cases e : i = j
  · subst e
    by_cases h : i < cells.size
    · simp [h]
    · simp [h, Array.getElem?_eq_none (Nat.le_of_not_lt h)]
  · simp [e, Ne.symm e]

/-- WS-ZA ZA5.4 part 26: **filling slot `i` keeps the occupancy links agreeing**. -/
theorem occ_agree_fill (node : CNode) (i : Nat) (h : i < node.cells.size) (v : Option Capability)
    (hv : v.isSome = true) :
    ∃ L, SlotOccupancy.Encodes (node.cells.set i v h) (fillOcc node.cells node.occ node.occHead i)
      (fillHead node.cells node.occHead i) L := by
  obtain ⟨L, hL⟩ := node.occ_agree
  unfold fillOcc fillHead
  split
  · next ho =>
    exact ⟨L, hL.congr (fun j => by
      rw [occupied_set]; split
      · next e => subst e; rw [hv, ho]
      · rfl)⟩
  · next ho =>
    refine ⟨i :: L, hL.link (by simpa using ho) ?_ (fun j => ?_)⟩
    · rw [Array.size_set, node.occ_size, node.cells_size]
    · rw [occupied_set]; by_cases e : j = i <;> simp [e, hv]

/-- WS-ZA ZA5.4 part 26: **emptying slot `i` keeps the occupancy links agreeing**. -/
theorem occ_agree_empty (node : CNode) (i : Nat) :
    ∃ L, SlotOccupancy.Encodes (node.cells.setIfInBounds i none)
      (emptyOcc node.cells node.occ i) (emptyHead node.cells node.occ node.occHead i) L := by
  obtain ⟨L, hL⟩ := node.occ_agree
  unfold emptyOcc emptyHead
  split
  · next ho =>
    refine ⟨L.erase i, hL.unlink ho (by rw [node.occ_size, node.cells_size]) (fun j => ?_)⟩
    rw [occupied_setIfInBounds]
    by_cases e : j = i
    · subst e; simp [SlotOccupancy.occupied_lt ho]
    · simp [e]
  · next ho =>
    exact ⟨L, hL.congr (fun j => by
      rw [occupied_setIfInBounds]; split
      · next e => obtain ⟨rfl, -⟩ := e; simpa using ho
      · rfl)⟩

/-- WS-G5/F-P03: O(1) amortized slot insert via `RHTable.insert`.
RHTable key uniqueness (noDupKeys invariant) ensures the old entry for `slot` is replaced.

WS-ZA ZA5.3: the capability is written into the slot's array entry in place.
A slot at or past `2 ^ radixWidth` has no entry, so inserting there leaves the
CNode unchanged; `cspaceInsertSlot` refuses such a slot before it gets here
(`slotAddressable`). -/
def insert (node : CNode) (slot : SeLe4n.Slot) (cap : Capability) : CNode :=
  if h : slot.toNat < node.cells.size then
    { node with
      slotsGhost := node.slotsGhost.map (·.insert slot cap)
      cells := node.cells.set slot.toNat (some cap) h
      cells_size := by rw [Array.size_set]; exact node.cells_size
      slots_agree := fun s => by
        rw [SeLe4n.Erased.out_map, SeLe4n.UniqueSlotMap.get?_insert, slotArrayGet_set, node.slots_agree s]
        by_cases e : slot = s
        · subst e; simp
        · have : s.toNat ≠ slot.toNat := fun h' => e (by
            cases slot; cases s; simp_all [SeLe4n.Slot.toNat])
          simp [e, this]
      occ := fillOcc node.cells node.occ node.occHead slot.toNat
      occ_size := by rw [size_fillOcc]; exact node.occ_size
      occHead := fillHead node.cells node.occHead slot.toNat
      occ_agree := occ_agree_fill node slot.toNat h (some cap) rfl }
  else node

/-- WS-ZA ZA5.3 part 6: two CNodes that agree on every field but their spare
records are equal; the spares are logically one value. -/
theorem ext_of_fields {a b : CNode} (h1 : a.depth = b.depth) (h2 : a.guardWidth = b.guardWidth)
    (h3 : a.guardValue = b.guardValue) (h4 : a.radixWidth = b.radixWidth)
    (h5 : a.slotsGhost = b.slotsGhost) (h6 : a.cells = b.cells) (h7 : a.links = b.links)
    (h8 : a.occ = b.occ) (h9 : a.occHead = b.occHead) :
    a = b := by
  cases a; cases b; simp only at h1 h2 h3 h4 h5 h6 h7 h8 h9; subst h1 h2 h3 h4 h5 h6 h7 h8 h9
  congr; exact Subsingleton.elim _ _

/-- The slot map with `cap` at `slot` agrees with the slot array holding it
there (`insert`'s agreement). -/
theorem insert_slots_agree (node : CNode) (slot : SeLe4n.Slot) (cap : Capability)
    (h : slot.toNat < node.cells.size) :
    ∀ s, (node.slotsGhost.map (fun m : SeLe4n.UniqueSlotMap Capability => m.insert slot cap)).out.get? s =
      slotArrayGet (node.cells.set slot.toNat (some cap) h) s := fun s => by
  rw [SeLe4n.Erased.out_map, SeLe4n.UniqueSlotMap.get?_insert, slotArrayGet_set, node.slots_agree s]
  by_cases e : slot = s
  · subst e; simp
  · have : s.toNat ≠ slot.toNat := fun h' => e (by
      cases slot; cases s; simp_all [SeLe4n.Slot.toNat])
    simp [e, this]

/-- `insert` of `cap` given the spare records `a`, its capability written over
slot `slot`'s record by `fill`, which leaves the spares.  The record is taken
out of the spares before it is matched, so nothing else holds it and `fill`
(out of line) writes `cap`'s fields into it.  Each arm builds the CNode itself,
so the CNode is written in place too.  With no record, `cap` itself is stored:
a caller passes it as a literal, so it is built only there. -/
@[inline] def insertCellWith (node : CNode) (slot : SeLe4n.Slot) (cap : Capability)
    (fill : Capability → Capability) (hfill : ∀ r, fill r = cap)
    (build : Unit → Capability) (hbuild : build () = cap)
    (h : slot.toNat < node.cells.size) (a : Array (Option Capability)) : CNode :=
  let i := slot.toNat
  let w := occupiedAt node.cells i
  if ha : i < a.size then
    let o := a[i]
    let a' := a.set i none ha
    match o with
    | some r =>
      let cell := fill r
      have hc : cell = cap := hfill r
      { node with
        slotsGhost := node.slotsGhost.map (·.insert slot cap)
        cells := node.cells.set i (some cell) h
        cells_size := by rw [Array.size_set]; exact node.cells_size
        slots_agree := by rw [hc]; exact insert_slots_agree node slot cap h
        occ := fillOccOf w node.occ node.occHead i
        occ_size := (size_fillOcc node.cells node.occ node.occHead i).trans node.occ_size
        occHead := fillHeadOf w node.occHead i
        occ_agree := occ_agree_fill node i h _ rfl
        spare := Squash.mk a' }
    | none =>
      { node with
        slotsGhost := node.slotsGhost.map (·.insert slot cap)
        cells := node.cells.set i (some (build ())) h
        cells_size := by rw [Array.size_set]; exact node.cells_size
        slots_agree := by rw [hbuild]; exact insert_slots_agree node slot cap h
        occ := fillOccOf w node.occ node.occHead i
        occ_size := (size_fillOcc node.cells node.occ node.occHead i).trans node.occ_size
        occHead := fillHeadOf w node.occHead i
        occ_agree := occ_agree_fill node i h _ rfl
        spare := Squash.mk a' }
  else
    { node with
      slotsGhost := node.slotsGhost.map (·.insert slot cap)
      cells := node.cells.set i (some (build ())) h
      cells_size := by rw [Array.size_set]; exact node.cells_size
      slots_agree := by rw [hbuild]; exact insert_slots_agree node slot cap h
      occ := fillOccOf w node.occ node.occHead i
      occ_size := (size_fillOcc node.cells node.occ node.occHead i).trans node.occ_size
      occHead := fillHeadOf w node.occHead i
      occ_agree := occ_agree_fill node i h _ rfl
      spare := Squash.mk a }

theorem insertCellWith_eq (node : CNode) (slot : SeLe4n.Slot) (cap : Capability)
    (fill : Capability → Capability) (hfill : ∀ r, fill r = cap)
    (build : Unit → Capability) (hbuild : build () = cap)
    (h : slot.toNat < node.cells.size) (a : Array (Option Capability)) :
    node.insertCellWith slot cap fill hfill build hbuild h a = node.insert slot cap := by
  unfold insertCellWith insert
  simp only [h, dite_true]
  split
  · split
    · next r _ => exact ext_of_fields rfl rfl rfl rfl rfl (by simp only [hfill r]) rfl rfl rfl
    · exact ext_of_fields rfl rfl rfl rfl rfl (by simp only [hbuild]) rfl rfl rfl
  · exact ext_of_fields rfl rfl rfl rfl rfl (by simp only [hbuild]) rfl rfl rfl

/-- `insertCellWith` writing `cap`'s fields over the record
(`Capability.overwrite`); the stored capability is `cap`'s fields, so a caller
passing `cap` as a literal never builds it. -/
@[inline] def insertCellFrom (node : CNode) (slot : SeLe4n.Slot) (cap : Capability)
    (h : slot.toNat < node.cells.size) (a : Array (Option Capability)) : CNode :=
  node.insertCellWith slot
    ⟨cap.target, cap.rights, cap.badgeWord, cap.badged, cap.mapAsid, cap.mapVaddr, cap.mapEpoch,
      cap.mapped, cap.freeIndex⟩
    (fun r => Capability.overwrite r cap.target cap.rights cap.badgeWord cap.badged cap.mapAsid
      cap.mapVaddr cap.mapEpoch cap.mapped cap.freeIndex)
    (fun r => Capability.overwrite_eq _ _ _ _ _ _ _ _ _ _)
    (fun _ => Capability.ofFields cap.target cap.rights cap.badgeWord cap.badged cap.mapAsid
      cap.mapVaddr cap.mapEpoch cap.mapped cap.freeIndex) rfl h a

theorem insertCellFrom_eq (node : CNode) (slot : SeLe4n.Slot) (cap : Capability)
    (h : slot.toNat < node.cells.size) (a : Array (Option Capability)) :
    node.insertCellFrom slot cap h a = node.insert slot cap := by
  unfold insertCellFrom; rw [insertCellWith_eq]

/-- WS-ZA ZA5.3 part 6: **`insert` as compiled** — `cap` written over the
slot's own record (its spare, `insertCellFrom`), so the write reuses the record
and its cell rather than allocating them.  A caller that passes `cap` as a
literal (mint) has its fields written straight into the record. -/
@[inline] def insertCell (node : CNode) (slot : SeLe4n.Slot) (cap : Capability) : CNode :=
  if h : slot.toNat < node.cells.size then
    Quot.lift (node.insertCellFrom slot cap h)
      (fun a b _ => by rw [insertCellFrom_eq, insertCellFrom_eq]) node.spare
  else node

theorem insertCell_eq_insert (node : CNode) (slot : SeLe4n.Slot) (cap : Capability) :
    node.insertCell slot cap = node.insert slot cap := by
  unfold insertCell
  split
  · next h =>
    induction node.spare using Squash.ind with
    | h a => exact insertCellFrom_eq node slot cap h a
  · next h => unfold insert; simp only [h, dite_false]

/-- WS-ZA ZA5.4: the CNode as it is, out of line: a write's no-op branch that
returns its CNode through this is not folded back into the stored object, which
would keep that object alive across the write and copy the CNode. -/
@[noinline] def unchanged (node : CNode) : CNode := node

/-- WS-ZA ZA5.4: `insert` of the capability naming object `id` with `rights`
alone (the capability a carve hands back), written over the slot's own record
and its target (`Capability.overwriteObject`), so neither is allocated when the
slot kept one. -/
@[inline] def insertObjectCap (node : CNode) (slot : SeLe4n.Slot) (id : SeLe4n.ObjId)
    (rights : AccessRightSet) : CNode :=
  if h : slot.toNat < node.cells.size then
    Quot.lift (fun a => node.insertCellWith slot
        ⟨.object id, rights, SeLe4n.Badge.zero, false, default, default, 0, false, 0⟩
        (fun r => r.overwriteObject id rights) (fun r => Capability.overwriteObject_eq r id rights)
        (fun _ => Capability.ofObject id rights) rfl h a)
      (fun a b _ => by dsimp only; rw [insertCellWith_eq, insertCellWith_eq]) node.spare
  else node.unchanged

theorem insertObjectCap_eq_insert (node : CNode) (slot : SeLe4n.Slot) (id : SeLe4n.ObjId)
    (rights : AccessRightSet) :
    node.insertObjectCap slot id rights =
      node.insert slot ⟨.object id, rights, SeLe4n.Badge.zero, false, default, default, 0, false, 0⟩ := by
  unfold insertObjectCap
  split
  · next h =>
    induction node.spare using Squash.ind with
    | h a => exact insertCellWith_eq _ _ _ _ _ _ _ h a
  · next h => unfold insert unchanged; simp only [h, dite_false]

/-- `insert` as compiled (`insertCell`, out of line). -/
def insertImpl (node : CNode) (slot : SeLe4n.Slot) (cap : Capability) : CNode :=
  node.insertCell slot cap

@[csimp] theorem insert_eq_impl : @insert = @insertImpl := by
  funext node slot cap; exact (insertCell_eq_insert node slot cap).symm

/-- WS-ZA ZA5.3 part 6: `insert` of the capability with these fields and no
mapping record, out of line: the caller hands over its CNode, so the CNode is
written in place, and the fields go straight into the slot's own record (mint,
copy).  The fields are a literal here, not a match on a record argument, so the
capability is never built. -/
def insertFields (node : CNode) (slot : SeLe4n.Slot) (target : CapTarget) (rights : AccessRightSet)
    (badgeWord : SeLe4n.Badge) (badged : Bool) (freeIndex : Nat) : CNode :=
  node.insertCell slot ⟨target, rights, badgeWord, badged, default, default, 0, false, freeIndex⟩

theorem insertFields_eq_insert (node : CNode) (slot : SeLe4n.Slot) (target : CapTarget)
    (rights : AccessRightSet) (badgeWord : SeLe4n.Badge) (badged : Bool) (freeIndex : Nat) :
    node.insertFields slot target rights badgeWord badged freeIndex =
      node.insert slot ((Capability.ofWords target rights badgeWord badged none).withFreeIndex freeIndex) :=
  insertCell_eq_insert _ _ _

/-- A slot array with entry `i` rewritten by `f` (which keeps an empty entry
empty) answers slot `s` as `f` of its old answer at `i`, and as before elsewhere. -/
theorem slotArrayGet_modify (cells : Array (Option Capability)) (i : Nat)
    (f : Option Capability → Option Capability) (hf : f none = none) (s : SeLe4n.Slot) :
    slotArrayGet (cells.modify i f) s =
      if s.toNat = i then f (slotArrayGet cells s) else slotArrayGet cells s := by
  unfold slotArrayGet
  by_cases hs : s.toNat = i
  · subst hs; by_cases h : s.toNat < cells.size <;> simp [h, Array.getElem_modify, hf]
  · by_cases h : s.toNat < cells.size <;> simp [h, hs, Array.getElem_modify, Ne.symm hs]

/-- WS-ZA ZA5.4 part 26: a rewrite of one entry that keeps it occupied or empty
keeps every slot's occupancy. -/
theorem occupied_modify (cells : Array (Option Capability)) (i : Nat)
    (f : Option Capability → Option Capability) (hf : ∀ o, (f o).isSome = o.isSome) (j : Nat) :
    SlotOccupancy.occupied (cells.modify i f) j = SlotOccupancy.occupied cells j := by
  unfold SlotOccupancy.occupied
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_modify]
  by_cases e : i = j
  · subst e; cases cells[i]? <;> simp [hf]
  · simp [e]

/-- WS-BP BP7.1: **the CNode with slot `slot`'s capability recording mapping
`m`** (`cspaceRecordFrameMapping`'s write); a slot holding nothing is left as
it is. -/
def recordMapping (node : CNode) (slot : SeLe4n.Slot) (m : FrameMapping) : CNode :=
  match node.lookup slot with
  | some cap => node.insert slot (cap.withMapping (some m))
  | none => node

/-- The slot entry with its capability recording `(asid, vaddr, epoch)`. -/
@[inline] def cellWithMapping (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) (epoch : Nat) :
    Option Capability → Option Capability
  | some c => some (c.setMapped asid vaddr epoch)
  | none => none

/-- The slot map with slot `slot`'s capability recording `(asid, vaddr, epoch)`. -/
noncomputable def slotsWithMapping (slot : SeLe4n.Slot) (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (epoch : Nat) (m : SeLe4n.UniqueSlotMap Capability) : SeLe4n.UniqueSlotMap Capability :=
  match m.get? slot with
  | some c => m.insert slot (c.setMapped asid vaddr epoch)
  | none => m

/-- WS-ZA ZA5.4: **`recordMapping` as compiled** — the slot's entry rewritten
where it stands (`Array.modify`), so a capability the CNode alone holds takes
the record's words in its own cell and nothing is built. -/
def recordMappingCells (node : CNode) (slot : SeLe4n.Slot) (asid : SeLe4n.ASID)
    (vaddr : SeLe4n.VAddr) (epoch : Nat) : CNode :=
  { node with
    slotsGhost := node.slotsGhost.map (slotsWithMapping slot asid vaddr epoch)
    cells := node.cells.modify slot.toNat (cellWithMapping asid vaddr epoch)
    cells_size := by rw [Array.size_modify]; exact node.cells_size
    slots_agree := fun s => by
      rw [SeLe4n.Erased.out_map, slotArrayGet_modify _ _ _ rfl, ← node.slots_agree s]
      unfold slotsWithMapping
      have hst : (s.toNat = slot.toNat) ↔ s = slot := ⟨fun h' => by
          cases slot; cases s; simp_all [SeLe4n.Slot.toNat], fun h' => by rw [h']⟩
      cases hg : node.slotsGhost.out.get? slot with
      | none =>
        by_cases hs : s = slot
        · subst hs; simp [hg, cellWithMapping]
        · simp [hs, hst]
      | some c =>
        rw [SeLe4n.UniqueSlotMap.get?_insert]
        by_cases hs : s = slot
        · subst hs; simp [hg, cellWithMapping]
        · simp [hs, hst, Ne.symm hs]
    occ_agree := by
      obtain ⟨L, hL⟩ := node.occ_agree
      exact ⟨L, hL.congr (occupied_modify _ _ _ (fun o => by cases o <;> rfl))⟩ }

theorem recordMappingCells_eq (node : CNode) (slot : SeLe4n.Slot) (asid : SeLe4n.ASID)
    (vaddr : SeLe4n.VAddr) (epoch : Nat) :
    node.recordMappingCells slot asid vaddr epoch = node.recordMapping slot ⟨asid, vaddr, epoch⟩ := by
  unfold recordMapping
  have hA := node.slots_agree slot
  unfold slotArrayGet at hA
  have hL' : node.lookup slot = node.slotsGhost.out.get? slot := rfl
  cases hL : node.lookup slot with
  | none =>
    dsimp only
    rw [hL', hA] at hL
    refine ext_of_fields rfl rfl rfl rfl ?_ ?_ rfl rfl rfl
    · apply SeLe4n.Erased.ext
      show (node.slotsGhost.map _).out = _
      rw [SeLe4n.Erased.out_map]; unfold slotsWithMapping
      rw [hA, hL]
    · show node.cells.modify slot.toNat (cellWithMapping asid vaddr epoch) = node.cells
      apply Array.ext (by simp)
      intro i h1 h2
      simp only [Array.getElem_modify]
      split
      · next e =>
        subst e
        split at hL
        · next h => simp [hL, cellWithMapping]
        · omega
      · rfl
  | some cap =>
    unfold insert
    rw [hL', hA] at hL
    have hB : slot.toNat < node.cells.size := by
      split at hL
      · assumption
      · exact absurd hL (by simp)
    simp only [hB, dite_true] at hL ⊢
    refine ext_of_fields rfl rfl rfl rfl ?_ ?_ rfl
      (by show node.occ = fillOcc _ _ _ _; unfold fillOcc; rw [if_pos (by simp [SlotOccupancy.occupied, Array.getD_eq_getD_getElem?, hB, hL])])
      (by show node.occHead = fillHead _ _ _; unfold fillHead; rw [if_pos (by simp [SlotOccupancy.occupied, Array.getD_eq_getD_getElem?, hB, hL])])
    · apply SeLe4n.Erased.ext
      show (node.slotsGhost.map _).out = (node.slotsGhost.map _).out
      rw [SeLe4n.Erased.out_map, SeLe4n.Erased.out_map]; unfold slotsWithMapping
      rw [hA]; simp only [hB, dite_true, hL]; rfl
    · show node.cells.modify slot.toNat (cellWithMapping asid vaddr epoch) = _
      apply Array.ext (by simp)
      intro i h1 h2
      simp only [Array.getElem_modify, Array.getElem_set]
      split
      · next e => subst e; simp [hL, cellWithMapping, Capability.setMapped_eq]
      · next e => simp [Ne.symm e]

/-- WS-ZA ZA5.4 part 13: **the CNode with slot `slot`'s capability holding free
index `idx`** — the write a carve makes to the capability it was invoked
through, and the write that sets a derivation's untyped source full; a slot
holding nothing is left as it is. -/
def setFreeIndex (node : CNode) (slot : SeLe4n.Slot) (idx : Nat) : CNode :=
  match node.lookup slot with
  | some cap => node.insert slot (cap.withFreeIndex idx)
  | none => node

/-- The slot entry with its capability holding free index `idx`. -/
@[inline] def cellWithFreeIndex (idx : Nat) : Option Capability → Option Capability
  | some c => some (c.withFreeIndex idx)
  | none => none

/-- The slot map with slot `slot`'s capability holding free index `idx`. -/
noncomputable def slotsWithFreeIndex (slot : SeLe4n.Slot) (idx : Nat)
    (m : SeLe4n.UniqueSlotMap Capability) : SeLe4n.UniqueSlotMap Capability :=
  match m.get? slot with
  | some c => m.insert slot (c.withFreeIndex idx)
  | none => m

/-- WS-ZA ZA5.4 part 13: **`setFreeIndex` as compiled** — the slot's entry
rewritten where it stands (`Array.modify`), so a capability the CNode alone
holds takes the word in its own cell and nothing is built. -/
def setFreeIndexCells (node : CNode) (slot : SeLe4n.Slot) (idx : Nat) : CNode :=
  { node with
    slotsGhost := node.slotsGhost.map (slotsWithFreeIndex slot idx)
    cells := node.cells.modify slot.toNat (cellWithFreeIndex idx)
    cells_size := by rw [Array.size_modify]; exact node.cells_size
    slots_agree := fun s => by
      rw [SeLe4n.Erased.out_map, slotArrayGet_modify _ _ _ rfl, ← node.slots_agree s]
      unfold slotsWithFreeIndex
      have hst : (s.toNat = slot.toNat) ↔ s = slot := ⟨fun h' => by
          cases slot; cases s; simp_all [SeLe4n.Slot.toNat], fun h' => by rw [h']⟩
      cases hg : node.slotsGhost.out.get? slot with
      | none =>
        by_cases hs : s = slot
        · subst hs; simp [hg, cellWithFreeIndex]
        · simp [hs, hst]
      | some c =>
        rw [SeLe4n.UniqueSlotMap.get?_insert]
        by_cases hs : s = slot
        · subst hs; simp [hg, cellWithFreeIndex]
        · simp [hs, hst, Ne.symm hs]
    occ_agree := by
      obtain ⟨L, hL⟩ := node.occ_agree
      exact ⟨L, hL.congr (occupied_modify _ _ _ (fun o => by cases o <;> rfl))⟩ }

theorem setFreeIndexCells_eq (node : CNode) (slot : SeLe4n.Slot) (idx : Nat) :
    node.setFreeIndexCells slot idx = node.setFreeIndex slot idx := by
  unfold setFreeIndex
  have hA := node.slots_agree slot
  unfold slotArrayGet at hA
  have hL' : node.lookup slot = node.slotsGhost.out.get? slot := rfl
  cases hL : node.lookup slot with
  | none =>
    dsimp only
    rw [hL', hA] at hL
    refine ext_of_fields rfl rfl rfl rfl ?_ ?_ rfl rfl rfl
    · apply SeLe4n.Erased.ext
      show (node.slotsGhost.map _).out = _
      rw [SeLe4n.Erased.out_map]; unfold slotsWithFreeIndex
      rw [hA, hL]
    · show node.cells.modify slot.toNat (cellWithFreeIndex idx) = node.cells
      apply Array.ext (by simp)
      intro i h1 h2
      simp only [Array.getElem_modify]
      split
      · next e =>
        subst e
        split at hL
        · next h => simp [hL, cellWithFreeIndex]
        · omega
      · rfl
  | some cap =>
    unfold insert
    rw [hL', hA] at hL
    have hB : slot.toNat < node.cells.size := by
      split at hL
      · assumption
      · exact absurd hL (by simp)
    simp only [hB, dite_true] at hL ⊢
    refine ext_of_fields rfl rfl rfl rfl ?_ ?_ rfl
      (by show node.occ = fillOcc _ _ _ _; unfold fillOcc; rw [if_pos (by simp [SlotOccupancy.occupied, Array.getD_eq_getD_getElem?, hB, hL])])
      (by show node.occHead = fillHead _ _ _; unfold fillHead; rw [if_pos (by simp [SlotOccupancy.occupied, Array.getD_eq_getD_getElem?, hB, hL])])
    · apply SeLe4n.Erased.ext
      show (node.slotsGhost.map _).out = (node.slotsGhost.map _).out
      rw [SeLe4n.Erased.out_map, SeLe4n.Erased.out_map]; unfold slotsWithFreeIndex
      rw [hA]; simp only [hB, dite_true, hL]
    · show node.cells.modify slot.toNat (cellWithFreeIndex idx) = _
      apply Array.ext (by simp)
      intro i h1 h2
      simp only [Array.getElem_modify, Array.getElem_set]
      split
      · next e => subst e; simp [hL, cellWithFreeIndex]
      · next e => simp [Ne.symm e]

/-- WS-ZA ZA5.3: a CNode of the given geometry holding `xs`, inserted in order
(the last capability at a repeated slot wins); a slot at or past
`2 ^ rw` holds nothing, as `insert` leaves it. -/
def ofList (d gw gv rw : Nat) (xs : List (SeLe4n.Slot × Capability)) : CNode :=
  xs.foldl (fun cn kv => cn.insert kv.1 kv.2) (mk' d gw gv rw)

/-- WS-G5/F-P03: O(1) amortized slot removal via `RHTable.erase`.  WS-ZA ZA5.3:
the slot's array entry is cleared in place. -/
def remove (node : CNode) (slot : SeLe4n.Slot) : CNode :=
  { node with
    slotsGhost := node.slotsGhost.map (·.erase slot)
    cells := node.cells.setIfInBounds slot.toNat none
    cells_size := by rw [Array.size_setIfInBounds]; exact node.cells_size
    slots_agree := fun s => by
      rw [SeLe4n.Erased.out_map, SeLe4n.UniqueSlotMap.get?_erase, slotArrayGet_setIfInBounds, node.slots_agree s]
      by_cases e : slot = s
      · subst e; simp
      · have : s.toNat ≠ slot.toNat := fun h' => e (by
          cases slot; cases s; simp_all [SeLe4n.Slot.toNat])
        simp [e, this]
    occ := emptyOcc node.cells node.occ slot.toNat
    occ_size := by rw [size_emptyOcc]; exact node.occ_size
    occHead := emptyHead node.cells node.occ node.occHead slot.toNat
    occ_agree := occ_agree_empty node slot.toNat }

/-- WS-ZA ZA5.3 part 6: **`remove` as compiled** — the slot's cell is kept as
its spare record (`SpareCells.keep`), so the next capability written there
reuses it. -/
def removeImpl (node : CNode) (slot : SeLe4n.Slot) : CNode :=
  if h : slot.toNat < node.cells.size then
    let o := node.cells[slot.toNat]
    have hs : node.cells.set slot.toNat none h = node.cells.setIfInBounds slot.toNat none := by
      simp [Array.setIfInBounds, h]
    let w := occupiedAt node.cells slot.toNat
    let head := emptyHeadOf w node.occ node.occHead slot.toNat
    { node with
      slotsGhost := node.slotsGhost.map (·.erase slot)
      cells := node.cells.set slot.toNat none h
      cells_size := by rw [hs]; exact (node.remove slot).cells_size
      slots_agree := by rw [hs]; exact (node.remove slot).slots_agree
      occ := emptyOccOf w node.occ slot.toNat
      occ_size := (size_emptyOcc node.cells node.occ slot.toNat).trans node.occ_size
      occHead := head
      occ_agree := by rw [hs]; exact occ_agree_empty node slot.toNat
      spare := node.spare.keep slot.toNat o }
  else node.remove slot

@[csimp] theorem remove_eq_impl : @remove = @removeImpl := by
  funext node slot
  unfold removeImpl
  split
  · next h =>
    exact ext_of_fields rfl rfl rfl rfl rfl (by simp [remove, Array.setIfInBounds, h]) rfl rfl rfl
  · rfl

/-- WS-ZA ZA5.3: a removal erases the slot from the ghost map. -/
@[simp] theorem slots_remove (node : CNode) (slot : SeLe4n.Slot) :
    (node.remove slot).slots = node.slots.erase slot := by
  simp [remove, slots, SeLe4n.Erased.out_map]

/-- M-D01: Find the first empty slot in a CNode starting from `base`,
scanning up to `limit` consecutive slot indices. Returns `none` if all
scanned slots are occupied.

The iteration is bounded by `limit` (typically `maxExtraCaps = 3`) rather
than `2^radixWidth`, because we only need slots for the (at most 3) extra
caps in the message. Termination is structural on `limit`.

**AK8-F (WS-AK / C-M07) — Radix bound:** the previous signature allowed
`limit + base.toNat ≥ 2^radixWidth`, returning slot indices outside the
CNode's addressable range. Callers that need the radix-bound guarantee
should invoke `findFirstEmptySlotChecked` (below) which additionally caps
the scan to `2^radixWidth - base.toNat`, so the returned slot index is
guaranteed to satisfy `s.toNat < 2^radixWidth` (witnessed by the
`findFirstEmptySlotChecked_within_radix` theorem). -/
def findFirstEmptySlot (cn : CNode) (base : SeLe4n.Slot)
    (limit : Nat) : Option SeLe4n.Slot :=
  match limit with
  | 0 => none
  | n + 1 =>
      match cn.lookup base with
      | none => some base
      | some _ => cn.findFirstEmptySlot (SeLe4n.Slot.ofNat (base.toNat + 1)) n

/-- AK8-F (WS-AK / C-M07): Radix-bounded variant of `findFirstEmptySlot`.

Caps the scan at `min limit (2^radixWidth - base.toNat)` so every returned
slot index fits in the CNode's `radixWidth`-addressable range. Returns
`none` if either the user-supplied `limit` or the radix window is
exhausted before an empty slot is found, OR if `base.toNat ≥ 2^radixWidth`
(in which case the scan window is zero-width).

The `base ≥ 2^radixWidth` case can occur when callers pass `.slot { val := 0 }`
(the zero slot) to a CNode with `radixWidth = 0` (a zero-sized CNode),
or when they miscompute `base` from an external index; the zero-width
window ensures no out-of-range slot is ever produced. -/
def findFirstEmptySlotChecked (cn : CNode) (base : SeLe4n.Slot)
    (limit : Nat) : Option SeLe4n.Slot :=
  if base.toNat ≥ 2 ^ cn.radixWidth then none
  else
    cn.findFirstEmptySlot base (Nat.min limit (2 ^ cn.radixWidth - base.toNat))

/-- AK8-F (C-M07): Helper — `findFirstEmptySlot` with `k` steps from `base`
produces a slot index strictly less than `base + k`. -/
private theorem findFirstEmptySlot_bounded
    (cn : CNode) (base : SeLe4n.Slot) (k : Nat) (s : SeLe4n.Slot)
    (hFind : cn.findFirstEmptySlot base k = some s) :
    s.toNat < base.toNat + k := by
  induction k generalizing base with
  | zero => simp [findFirstEmptySlot] at hFind
  | succ n ih =>
    simp only [findFirstEmptySlot] at hFind
    split at hFind
    · cases hFind; omega
    · have := ih _ hFind
      simp only [SeLe4n.Slot.toNat_ofNat] at this
      omega

/-- AK8-F (C-M07): Soundness — if `findFirstEmptySlotChecked` returns
`some s`, then `s.toNat < 2^radixWidth`. This is the radix containment
guarantee: every slot index produced by the checked variant is
addressable by the CNode's radix width. -/
theorem findFirstEmptySlotChecked_within_radix
    (cn : CNode) (base : SeLe4n.Slot) (limit : Nat) (s : SeLe4n.Slot)
    (hFind : cn.findFirstEmptySlotChecked base limit = some s) :
    s.toNat < 2 ^ cn.radixWidth := by
  unfold findFirstEmptySlotChecked at hFind
  split at hFind
  · cases hFind
  · rename_i hBaseLt
    have hBaseLt' : base.toNat < 2 ^ cn.radixWidth := Nat.lt_of_not_le hBaseLt
    have hScanBound : Nat.min limit (2 ^ cn.radixWidth - base.toNat)
        ≤ 2 ^ cn.radixWidth - base.toNat := Nat.min_le_right _ _
    have hReturnedInRange := findFirstEmptySlot_bounded cn base _ s hFind
    omega

/-- If findFirstEmptySlot returns `some s`, then `cn.lookup s = none`. -/
theorem findFirstEmptySlot_spec
    (cn : CNode) (base : SeLe4n.Slot) (limit : Nat) (s : SeLe4n.Slot)
    (hFind : cn.findFirstEmptySlot base limit = some s) :
    cn.lookup s = none := by
  induction limit generalizing base with
  | zero => simp [findFirstEmptySlot] at hFind
  | succ n ih =>
    simp only [findFirstEmptySlot] at hFind
    split at hFind
    · -- cn.lookup base = none
      cases hFind; assumption
    · -- cn.lookup base = some _
      exact ih _ hFind

/-- findFirstEmptySlot with limit 0 always returns none. -/
theorem findFirstEmptySlot_zero (cn : CNode) (base : SeLe4n.Slot) :
    cn.findFirstEmptySlot base 0 = none := by
  simp [findFirstEmptySlot]

/-- If findFirstEmptySlot returns `none`, all scanned slots are occupied. -/
theorem findFirstEmptySlot_none_iff
    (cn : CNode) (base : SeLe4n.Slot) (limit : Nat) :
    cn.findFirstEmptySlot base limit = none →
    ∀ i, i < limit →
      (cn.lookup (SeLe4n.Slot.ofNat (base.toNat + i))).isSome := by
  induction limit generalizing base with
  | zero => intro _ i hi; exact absurd hi (Nat.not_lt_zero _)
  | succ n ih =>
    simp only [findFirstEmptySlot]
    split
    · intro h; exact absurd h (by simp)
    · rename_i cap hLookup
      intro hRec i hi
      cases i with
      | zero =>
        simp only [Nat.add_zero, SeLe4n.Slot.ofNat_toNat]
        rw [hLookup]; rfl
      | succ j =>
        have hj : j < n := Nat.lt_of_succ_lt_succ hi
        have := ih (SeLe4n.Slot.ofNat (base.toNat + 1)) hRec j hj
        simp only [SeLe4n.Slot.toNat_ofNat] at this
        have hEq : base.toNat + 1 + j = base.toNat + (j + 1) := by omega
        rw [hEq] at this; exact this

/-- **WS-BP BP7.1 (`v0.36.7`): does any slot hold a capability that records a
frame mapping?**  Destroying such a capability owes the unmapping of what it
mapped (`cspaceDeleteSlotFinalising`), which a CNode's destruction by retype does
not perform, so the retype refuses a CNode for which this holds — delete those
capabilities first. -/
def holdsFrameMappingRecord (node : CNode) : Bool :=
  node.cells.any fun e => e.any (·.mapping.isSome)

/-- Which slots the local revoke keeps: the source, and every slot naming another
target.  One predicate for the CNode rewrite (`revokeTargetLocal`) and for the
detach of the slots it drops (`detachRevokedSlots`). -/
abbrev revokeTargetLocalKeeps (sourceSlot : SeLe4n.Slot) (target : CapTarget)
    (s : SeLe4n.Slot) (c : Capability) : Bool :=
  s == sourceSlot || !(c.target == target)

/-- WS-ZA ZA5.3: keep the slots whose capability satisfies `f`, in the map and
in the slot array alike.  Each slot cleared keeps the capability it held as its
record (`SpareCells.keepFiltered`), as a single removal does (`removeImpl`). -/
def filterSlots (node : CNode) (f : SeLe4n.Slot → Capability → Bool) : CNode :=
  { node with
    slotsGhost := node.slotsGhost.map (·.filter f)
    cells := node.cells.mapIdx fun i e => e.filter (f (SeLe4n.Slot.ofNat i))
    cells_size := by rw [Array.size_mapIdx]; exact node.cells_size
    slots_agree := fun s => by
      rw [SeLe4n.Erased.out_map, SeLe4n.UniqueSlotMap.get?_filter, slotArrayGet_mapIdx, node.slots_agree s]
      by_cases h : s.toNat < node.cells.size
      · simp only [h, if_true]; rfl
      · simp [slotArrayGet, h]
    occ := SlotOccupancy.buildWords (node.cells.mapIdx fun i e => e.filter (f (SeLe4n.Slot.ofNat i)))
      node.cells.size (Array.replicate (2 * 2 ^ node.radixWidth) 0) 0
    occ_size := by rw [SlotOccupancy.size_buildWords, Array.size_replicate]
    occHead := SlotOccupancy.buildHead (node.cells.mapIdx fun i e => e.filter (f (SeLe4n.Slot.ofNat i)))
      node.cells.size 0
    occ_agree := by
      have := SlotOccupancy.build_encodes
        (node.cells.mapIdx fun i e => e.filter (f (SeLe4n.Slot.ofNat i)))
        (Array.replicate (2 * 2 ^ node.radixWidth) 0)
        (by rw [Array.size_replicate, Array.size_mapIdx, node.cells_size])
      rwa [Array.size_mapIdx] at this
    spare := node.spare.keepFiltered node.cells (fun i => f (SeLe4n.Slot.ofNat i)) }

/-- WS-ZA ZA5.3 part 4: the CNode with every derivation link cleared.  The
information-flow projection reads a CNode through this, so the links, like the
derivation tree they encode, are never observable. -/
def withoutLinks (node : CNode) : CNode :=
  { node with
    links := Array.replicate (slotLinkWords * 2 ^ node.radixWidth) 0
    links_size := Array.size_replicate }

@[simp] theorem slots_withoutLinks (node : CNode) : node.withoutLinks.slots = node.slots := rfl

/-- WS-ZA ZA5.3 part 4: writing a capability, clearing a slot or filtering the
slots leaves every derivation link where it was. -/
@[simp] theorem insert_links (node : CNode) (slot : SeLe4n.Slot) (cap : Capability) :
    (node.insert slot cap).links = node.links := by
  unfold insert; split <;> rfl

@[simp] theorem remove_links (node : CNode) (slot : SeLe4n.Slot) :
    (node.remove slot).links = node.links := rfl

@[simp] theorem filterSlots_links (node : CNode) (f : SeLe4n.Slot → Capability → Bool) :
    (node.filterSlots f).links = node.links := rfl
@[simp] theorem cells_withoutLinks (node : CNode) : node.withoutLinks.cells = node.cells := rfl
@[simp] theorem depth_withoutLinks (node : CNode) : node.withoutLinks.depth = node.depth := rfl
@[simp] theorem guardWidth_withoutLinks (node : CNode) :
    node.withoutLinks.guardWidth = node.guardWidth := rfl
@[simp] theorem guardValue_withoutLinks (node : CNode) :
    node.withoutLinks.guardValue = node.guardValue := rfl
@[simp] theorem radixWidth_withoutLinks (node : CNode) :
    node.withoutLinks.radixWidth = node.radixWidth := rfl
@[simp] theorem lookup_withoutLinks (node : CNode) (s : SeLe4n.Slot) :
    node.withoutLinks.lookup s = node.lookup s := rfl

/-- WS-ZA ZA5.3: the filter on the ghost map. -/
@[simp] theorem slots_filterSlots (node : CNode) (f : SeLe4n.Slot → Capability → Bool) :
    (node.filterSlots f).slots = node.slots.filter f := by
  simp [filterSlots, slots, SeLe4n.Erased.out_map]

/-- The local same-TARGET sweep: keep the source slot, delete every other slot in
this CNode that names the same capability target.

**This is not revocation**, and nothing on a syscall path runs it since `v0.36.1`
(PR #900 review).  It predates the capability derivation tree: it was written when
a target match was the only available stand-in for "derived from the source", and
it keeps that meaning — so it also deletes an independently rooted capability to
the same object and the source's own parent when the two share a CNode.  The
derivation tree the old docstring deferred exists (`SystemState.cdt`), and
`cspaceRevokeCdtFinalising` destroys exactly the source's CDT descendants, which is
seL4's `cteRevoke` (read at `13.0.0`).  What still calls this is the local
`cspaceRevoke`, an internal operation.

WS-G5/F-P03: Inherently O(m) (filter-by-target), uses `RHTable.filter`. -/
def revokeTargetLocal (node : CNode) (sourceSlot : SeLe4n.Slot) (target : CapTarget) : CNode :=
  node.filterSlots (revokeTargetLocalKeeps sourceSlot target)

-- ============================================================================
-- WS-G5/WS-E2/C-01: CNode slot-index uniqueness infrastructure
-- ============================================================================

/-- CNode slot well-formedness: the RHTable-backed slots satisfy the extended
invariant (`invExt`) and are not full (`size < capacity`).

WS-N4: With RHTable-backed slots, key uniqueness is enforced by the `noDupKeys`
component of `invExt`. The `size < capacity` condition is maintained by the
resize-at-75%-load policy and is required for erase correctness.

WS-RC R4.A: now a trivial projection of `UniqueSlotMap.hWF`, which carries
`RHTable.invExtK` structurally at construction time. Every reachable
`CNode` satisfies this property by construction; the named predicate is
retained for caller compatibility (existing preservation theorems still
take it as a hypothesis). -/
def slotsUnique (cn : CNode) : Prop := cn.slots.table.invExtK

/-- WS-RC R4.A: `slotsUnique` is trivially derivable from the structural
    `UniqueSlotMap.hWF`. -/
theorem slotsUnique_holds (cn : CNode) : cn.slotsUnique := cn.slots.hWF

/-- WS-RC R4.A / DEEP-MODEL-01: plan-named alias for the structural
    CNode-level uniqueness witness.  Identical to `slotsUnique_holds`;
    retained under the canonical plan name (`cnode_slots_unique`) so the
    discharge-index reachability gate can locate it by the same identifier
    used in the close-out plan. -/
theorem cnode_slots_unique (cn : CNode) : cn.slotsUnique := slotsUnique_holds cn

/-- WS-G5: After removing a slot, lookup returns `none`.
Maps directly to `RHTable.getElem?_erase_self`. Requires slot invariant
(invExt) to guarantee erase+lookup correctness. -/

theorem lookup_remove_eq_none (node : CNode) (slot : SeLe4n.Slot)
    (hUniq : node.slotsUnique) :
    (node.remove slot).lookup slot = none := by
  simp only [lookup, slots_remove, SeLe4n.UniqueSlotMap.get?, SeLe4n.UniqueSlotMap.erase]
  exact RHTable.getElem?_erase_self node.slots.table slot hUniq.1

/-- WS-G5: If `lookup` returns `some`, the slot key is present in the RHTable.
Replaces the list-era membership theorem with RHTable semantics. -/

theorem lookup_mem_of_some (node : CNode) (slot : SeLe4n.Slot) (cap : Capability)
    (h : node.lookup slot = some cap) : slot ∈ node.slots.table := by
  simp [lookup, SeLe4n.UniqueSlotMap.get?] at h
  exact (RHTable.mem_iff_isSome_getElem? node.slots.table slot).mpr (by simp [h])

theorem resolveSlot_depthMismatch
    (node : CNode)
    (cptr : SeLe4n.CPtr)
    (bitsRemaining : Nat)
    (hDepth : bitsRemaining < node.bitsConsumed) :
    node.resolveSlot cptr bitsRemaining = .error .depthMismatch := by
  unfold resolveSlot bitsConsumed at *
  have h : bitsRemaining < node.guardWidth + node.radixWidth := hDepth
  simp [h]

/-- T2-J (L-NEW-4): If a CNode's guard value violates `guardBounded`
    (i.e., `guardValue ≥ 2^guardWidth`), then `resolveSlot` always returns
    `guardMismatch` for any CPtr and bitsRemaining (assuming sufficient depth).

    **Proof**: The extracted guard is computed as
    `(shiftedAddr / 2^radixWidth) % 2^guardWidth`, which is always
    `< 2^guardWidth`. Since `guardValue ≥ 2^guardWidth`, the equality check
    `guardExtracted = guardValue` is always false. -/
theorem resolveSlot_guardMismatch_of_not_guardBounded
    (node : CNode)
    (cptr : SeLe4n.CPtr)
    (bitsRemaining : Nat)
    (hBits : node.bitsConsumed ≤ bitsRemaining)
    (hNotBounded : ¬node.guardBounded) :
    node.resolveSlot cptr bitsRemaining = .error .guardMismatch := by
  simp only [guardBounded] at hNotBounded
  unfold resolveSlot
  have hNotLt : ¬(bitsRemaining < node.bitsConsumed) := by omega
  simp only [hNotLt, ↓reduceIte]
  -- After the depth check passes, resolveSlot computes:
  --   guardExtracted := (shiftedAddr / 2^radixWidth) % 2^guardWidth
  -- which is always < 2^guardWidth by Nat.mod_lt.
  -- Since ¬(guardValue < 2^guardWidth), guardExtracted ≠ guardValue.
  split
  · -- guardExtracted = guardValue case: derive contradiction
    rename_i hEq
    have hExtractLt := SeLe4n.CPtr.guardBits_lt cptr (bitsRemaining - node.bitsConsumed)
      node.radixWidth node.guardWidth
    omega
  · -- guardExtracted ≠ guardValue case: already .error .guardMismatch
    rfl

/-- WS-G5: Source slot is preserved by `revokeTargetLocal` because the filter
predicate always includes entries where `s = sourceSlot`.
Requires slot invariant for RHTable filter correctness. -/

theorem lookup_revokeTargetLocal_source_eq_lookup
    (node : CNode)
    (sourceSlot : SeLe4n.Slot)
    (target : CapTarget)
    (hUniq : node.slotsUnique) :
    (node.revokeTargetLocal sourceSlot target).lookup sourceSlot = node.lookup sourceSlot := by
  simp only [revokeTargetLocal, lookup, slots_filterSlots, SeLe4n.UniqueSlotMap.get?,
    SeLe4n.UniqueSlotMap.filter]
  exact RHTable.filter_preserves_key node.slots.table _ sourceSlot
    (fun k' _ hBeq => by simp [eq_of_beq hBeq]) hUniq.1

/-- WS-SM SM6.D / PR #822 Phase H (#1.a): `revokeTargetLocal` only *removes* slots (it filters
the slot map), so any capability present after a revoke was already present before — the post-revoke
lookups are a sub-relation of the pre-revoke ones.  Mirrors the private `revokeTargetLocal_slots_sub`
at `lookup` level; used by reply-cap backing preservation across `cspaceRevoke`. -/
theorem lookup_revokeTargetLocal_sub
    (node : CNode)
    (sourceSlot : SeLe4n.Slot)
    (target : CapTarget)
    (slot : SeLe4n.Slot)
    (cap : Capability)
    (hUniq : node.slotsUnique)
    (hLookup : (node.revokeTargetLocal sourceSlot target).lookup slot = some cap) :
    node.lookup slot = some cap := by
  simp only [revokeTargetLocal, lookup, slots_filterSlots, SeLe4n.UniqueSlotMap.get?,
    SeLe4n.UniqueSlotMap.filter] at hLookup ⊢
  exact RHTable.filter_get_subset node.slots.table _ slot cap hUniq.1 hLookup

/-- ...a slot the revoke does not keep is emptied... -/
theorem lookup_revokeTargetLocal_of_not_keeps
    (node : CNode) (sourceSlot : SeLe4n.Slot) (target : CapTarget)
    (slot : SeLe4n.Slot) (cap : Capability) (hUniq : node.slotsUnique)
    (hLookup : node.lookup slot = some cap)
    (hKeeps : revokeTargetLocalKeeps sourceSlot target slot cap = false) :
    (node.revokeTargetLocal sourceSlot target).lookup slot = none := by
  cases h : (node.revokeTargetLocal sourceSlot target).lookup slot with
  | none => rfl
  | some v =>
    have h1 := lookup_revokeTargetLocal_sub node sourceSlot target slot v hUniq h
    rw [hLookup] at h1; cases h1
    simp only [revokeTargetLocal, lookup, slots_filterSlots, SeLe4n.UniqueSlotMap.get?,
      SeLe4n.UniqueSlotMap.filter] at h
    have h2 := (RHTable.filter_getElem?_iff _ _ _ _ hUniq.1).mp h
    rw [hKeeps] at h2; cases h2.2

/-- ...and a slot the revoke keeps keeps its capability. -/
theorem lookup_revokeTargetLocal_of_keeps
    (node : CNode) (sourceSlot : SeLe4n.Slot) (target : CapTarget)
    (slot : SeLe4n.Slot) (cap : Capability) (hUniq : node.slotsUnique)
    (hLookup : node.lookup slot = some cap)
    (hKeeps : revokeTargetLocalKeeps sourceSlot target slot cap = true) :
    (node.revokeTargetLocal sourceSlot target).lookup slot = some cap := by
  simp only [revokeTargetLocal, lookup, slots_filterSlots, SeLe4n.UniqueSlotMap.get?,
    SeLe4n.UniqueSlotMap.filter] at hLookup ⊢
  exact RHTable.filter_getElem?_of_pred node.slots.table _ slot cap hUniq.1 hLookup hKeeps

/-- T2-J (L-NEW-4): The empty CNode trivially satisfies `guardBounded`
    (guardValue = 0 < 2^0 = 1). -/
theorem empty_guardBounded : CNode.empty.guardBounded := by
  simp [empty, guardBounded]

/-- WS-N4/WS-RC R4.A: The empty CNode's slots satisfy the slot invariant.
    Now trivial via `UniqueSlotMap.hWF`. -/
theorem empty_slotsUnique : CNode.empty.slotsUnique :=
  CNode.empty.slots.hWF

/-- WS-N4/WS-RC R4.A: Insert preserves the slot invariant.
    Now trivial via `UniqueSlotMap.insert`'s structural discharge. -/

theorem insert_slotsUnique
    (cn : CNode) (slot : SeLe4n.Slot) (cap : Capability)
    (_hUniq : cn.slotsUnique) :
    (cn.insert slot cap).slotsUnique :=
  (cn.insert slot cap).slots.hWF

/-- WS-N4/WS-RC R4.A: Erase preserves the slot invariant.
    Now trivial via `UniqueSlotMap.erase`'s structural discharge. -/

theorem remove_slotsUnique
    (cn : CNode) (slot : SeLe4n.Slot)
    (_hUniq : cn.slotsUnique) :
    (cn.remove slot).slotsUnique :=
  (cn.remove slot).slots.hWF

/-- WS-N4/WS-RC R4.A: Filter preserves the slot invariant.
    Now trivial via `UniqueSlotMap.filter`'s structural discharge. -/

theorem revokeTargetLocal_slotsUnique
    (cn : CNode) (sourceSlot : SeLe4n.Slot) (target : CapTarget)
    (_hUniq : cn.slotsUnique) :
    (cn.revokeTargetLocal sourceSlot target).slotsUnique :=
  (cn.revokeTargetLocal sourceSlot target).slots.hWF

-- ============================================================================
-- WS-H4: Meaningful CNode slot-count bound predicate
-- ============================================================================

/-- WS-H4/C-03: Every CNode has at most `2^radixBits` occupied slots.
This is the meaningful replacement for the trivially-true `slotsUnique`
predicate — it captures the actual capacity constraint that the CNode
guard/radix semantics enforce.

WS-RC R4.A: `cn.slots.size` is the `UniqueSlotMap.size` accessor
(forwarded to `cn.slots.table.size`). -/
def slotCountBounded (cn : CNode) : Prop :=
  cn.slots.size ≤ cn.slotCount

/-- WS-ZA ZA5.3: every occupied slot of a CNode is below `2 ^ radixWidth`: the
slot map agrees with the slot array, which has no cell beyond that. -/
theorem slots_get?_bounded (cn : CNode) :
    ∀ s : SeLe4n.Slot, cn.slots.table.get? s ≠ none → s.toNat < 2 ^ cn.radixWidth := by
  intro s hs
  have h := cn.slots_agree s
  have hne : slotArrayGet cn.cells s ≠ none := by
    rw [← h]; exact hs
  unfold slotArrayGet at hne
  by_cases hl : s.toNat < cn.cells.size
  · rw [cn.cells_size] at hl; exact hl
  · simp [hl] at hne

/-- WS-ZA ZA5.3: every CNode holds at most `slotCount` capabilities.  Its slots
are distinct indices below `2 ^ radixWidth` (`slots_get?_bounded`), so the
bound is the pigeonhole principle, not a property each operation re-proves. -/
theorem slotCountBounded_holds (cn : CNode) : cn.slotCountBounded := by
  have hWF := cn.slots.hWF
  have h := SeLe4n.Kernel.RobinHood.RHTable.size_le_length_of_keys_mem
    (fun s : SeLe4n.Slot => s.toNat) (fun a b hab => SeLe4n.Slot.ext hab)
    (List.range (2 ^ cn.radixWidth)) List.nodup_range cn.slots.table hWF.1 hWF.2.1
    (fun k v hk => List.mem_range.mpr (cn.slots_get?_bounded k (by rw [hk]; simp)))
  simpa [slotCountBounded, slotCount, SeLe4n.UniqueSlotMap.size] using h

/-- **WS-RR RR8.16** (`v0.35.201`): *is this slot index addressable by this
CNode's radix width?*

`resolveSlot` extracts a slot by masking with `2 ^ radixWidth`, so an index at or
above `slotCount` can be **stored** and can never be **reached** by any CPtr.  A
capability installed there is therefore invisible to its holder while still
consuming a slot-table entry in an object whose memory was accounted, at retype
time, by `2 ^ radixWidth` slots — so an install that does not ask this question
lets a CNode grow without bound.  Every capability install asks it, at
`cspaceInsertSlot`, which is the one primitive all four of them pass through. -/
def slotAddressable (node : CNode) (s : SeLe4n.Slot) : Bool :=
  s.toNat < node.slotCount

/-- WS-ZA ZA5.3: the slot array has an entry for exactly the addressable
slots. -/
theorem slotAddressable_iff_lt_cells (cn : CNode) (slot : SeLe4n.Slot) :
    cn.slotAddressable slot ↔ slot.toNat < cn.cells.size := by
  unfold slotAddressable slotCount; rw [cn.cells_size]; simp

/-- WS-ZA ZA5.3: an occupied slot is addressable, since the slot array has no
entry past `2 ^ radixWidth` (`slots_agree`). -/
theorem slotAddressable_of_lookup (cn : CNode) (slot : SeLe4n.Slot) (cap : Capability)
    (h : cn.lookup slot = some cap) : cn.slotAddressable slot := by
  rw [slotAddressable_iff_lt_cells]
  have := cn.slots_agree slot
  unfold lookup slots at h; rw [h] at this
  unfold slotArrayGet at this
  by_cases hl : slot.toNat < cn.cells.size
  · exact hl
  · simp [hl] at this

/-- WS-ZA ZA5.3: a slot occupied after an insert was addressable before it. -/
theorem slotAddressable_of_lookup_insert (cn : CNode) (slot t : SeLe4n.Slot)
    (cap x : Capability) (h : (cn.insert slot cap).lookup t = some x) :
    cn.slotAddressable t := by
  have := slotAddressable_of_lookup _ _ _ h
  unfold slotAddressable slotCount at *
  unfold insert at this; split at this <;> exact this

theorem insert_slots_of_addressable (cn : CNode) (slot : SeLe4n.Slot) (cap : Capability)
    (h : cn.slotAddressable slot) :
    (cn.insert slot cap).slots = cn.slots.insert slot cap := by
  unfold insert; rw [dif_pos ((slotAddressable_iff_lt_cells cn slot).1 h)]
  simp [slots, SeLe4n.Erased.out_map]

theorem insert_eq_self_of_not_addressable (cn : CNode) (slot : SeLe4n.Slot) (cap : Capability)
    (h : ¬ cn.slotAddressable slot) : cn.insert slot cap = cn := by
  unfold insert; rw [dif_neg (fun h' => h ((slotAddressable_iff_lt_cells cn slot).2 h'))]

@[simp] theorem insert_radixWidth (cn : CNode) (slot : SeLe4n.Slot) (cap : Capability) :
    (cn.insert slot cap).radixWidth = cn.radixWidth := by
  unfold insert; split <;> rfl

@[simp] theorem insert_depth (cn : CNode) (slot : SeLe4n.Slot) (cap : Capability) :
    (cn.insert slot cap).depth = cn.depth := by
  unfold insert; split <;> rfl

@[simp] theorem insert_guardWidth (cn : CNode) (slot : SeLe4n.Slot) (cap : Capability) :
    (cn.insert slot cap).guardWidth = cn.guardWidth := by
  unfold insert; split <;> rfl

@[simp] theorem insert_guardValue (cn : CNode) (slot : SeLe4n.Slot) (cap : Capability) :
    (cn.insert slot cap).guardValue = cn.guardValue := by
  unfold insert; split <;> rfl

/-- **WS-RR RR8.16** (`v0.35.201`): the radix-bounded scan produces only
addressable slots — `findFirstEmptySlotChecked_within_radix` restated in the
vocabulary the insert guard reads, so the transfer path's `.ok` is provably not
the guard's refusal. -/
theorem findFirstEmptySlotChecked_slotAddressable
    (cn : CNode) (base : SeLe4n.Slot) (limit : Nat) (s : SeLe4n.Slot)
    (hFind : cn.findFirstEmptySlotChecked base limit = some s) :
    cn.slotAddressable s = true := by
  unfold slotAddressable slotCount
  exact decide_eq_true (findFirstEmptySlotChecked_within_radix cn base limit s hFind)

/-- **WS-RR RR8.16** (`v0.35.201`): ...and so does CSpace resolution, which is
the other half of the claim: the guard refuses exactly the slots no CPtr can
name. -/
theorem resolveSlot_slotAddressable
    (node : CNode) (cptr : SeLe4n.CPtr) (bitsRemaining : Nat) (s : SeLe4n.Slot)
    (hRes : node.resolveSlot cptr bitsRemaining = .ok s) :
    node.slotAddressable s = true := by
  unfold resolveSlot at hRes
  by_cases hDepth : bitsRemaining < node.bitsConsumed
  · simp only [hDepth, if_pos] at hRes
    exact absurd hRes (by simp)
  · simp only [hDepth, if_neg, not_false_eq_true] at hRes
    by_cases hGuard :
        cptr.guardBits (bitsRemaining - node.bitsConsumed) node.radixWidth node.guardWidth =
          node.guardValue
    · simp only [hGuard, if_pos] at hRes
      cases hRes
      unfold slotAddressable slotCount SeLe4n.Slot.toNat SeLe4n.Slot.ofNat
      exact decide_eq_true (SeLe4n.CPtr.slotBits_lt _ _ _)
    · simp only [hGuard, if_neg, not_false_eq_true] at hRes
      exact absurd hRes (by simp)

/-- WS-G5: If a slot is present in the RHTable, lookup returns its value.
With RHTable-backed slots, key uniqueness is maintained by the `noDupKeys`
component of `invExt` (part of `slotsUnique`). -/

theorem mem_lookup_of_slotsUnique (node : CNode) (_hUniq : node.slotsUnique)
    (slot : SeLe4n.Slot) (hMem : slot ∈ node.slots.table) :
    ∃ v, node.lookup slot = some v := by
  have := (RHTable.mem_iff_isSome_getElem? node.slots.table slot).mp hMem
  simp [lookup, Option.isSome_iff_exists] at this ⊢
  exact this

/-- WS-G5: Lookup roundtrip after insert — inserting at `slot` makes lookup
return the inserted capability. Maps directly to `RHTable.getElem?_insert_self`. -/

theorem lookup_insert_eq
    (cn : CNode) (slot : SeLe4n.Slot) (cap : Capability)
    (hUniq : cn.slotsUnique) (hAddr : cn.slotAddressable slot) :
    (cn.insert slot cap).lookup slot = some cap := by
  simp only [lookup, insert_slots_of_addressable cn slot cap hAddr]
  exact RHTable.getElem?_insert_self cn.slots slot cap hUniq.1

/-- WS-G5: Insert at a different slot does not affect lookup.
Maps directly to `RHTable.getElem?_insert_ne`. -/

theorem lookup_insert_ne
    (cn : CNode) (slot slot' : SeLe4n.Slot) (cap : Capability)
    (hNe : slot ≠ slot')
    (hUniq : cn.slotsUnique) :
    (cn.insert slot cap).lookup slot' = cn.lookup slot' := by
  by_cases hAddr : cn.slotAddressable slot
  · simp only [lookup, insert_slots_of_addressable cn slot cap hAddr]
    exact RHTable.getElem?_insert_ne cn.slots slot slot' cap
      (fun h => hNe (eq_of_beq h)) hUniq.1
  · rw [insert_eq_self_of_not_addressable cn slot cap hAddr]

/-- WS-G5: Remove at a different slot does not affect lookup.
Maps directly to `RHTable.getElem?_erase_ne`. -/

theorem lookup_remove_ne
    (cn : CNode) (slot slot' : SeLe4n.Slot)
    (hNe : slot ≠ slot')
    (hUniq : cn.slotsUnique) :
    (cn.remove slot).lookup slot' = cn.lookup slot' := by
  simp only [lookup, slots_remove]
  -- WS-RC R4.A: cn.slots is `UniqueSlotMap`; project to `.table` for the
  -- underlying `RHTable` lemma.
  exact RHTable.getElem?_erase_ne_K cn.slots.table slot slot'
    (fun h => hNe (eq_of_beq h)) hUniq

/-- An insert keeps every occupied slot occupied. -/
theorem lookup_insert_ne_none (cn : CNode) (slot s : SeLe4n.Slot) (cap : Capability)
    (h : cn.lookup s ≠ none) : (cn.insert slot cap).lookup s ≠ none := by
  by_cases hEq : slot = s
  · subst hEq
    by_cases hAddr : cn.slotAddressable slot
    · rw [lookup_insert_eq cn slot cap (slotsUnique_holds cn) hAddr]; simp
    · rw [insert_eq_self_of_not_addressable cn slot cap hAddr]; exact h
  · rw [lookup_insert_ne cn slot s cap hEq (slotsUnique_holds cn)]; exact h

end CNode

/-- WS-H13/WS-N4: `BEq` instance for `CNode` using entry-wise comparison on the
RHTable-backed slots. Two CNodes are equal iff their depth, guardWidth,
guardValue, radixWidth, all slot entries and (WS-ZA ZA5.3 part 4) all derivation
link words agree: a comparison that ignored the links would pass a CNode whose
links a step wrote wrongly. -/

instance : BEq CNode where
  beq a b :=
    a.depth == b.depth && a.guardWidth == b.guardWidth &&
    a.guardValue == b.guardValue && a.radixWidth == b.radixWidth &&
    decide (a.cells = b.cells) && decide (a.links = b.links)

/-- WS-H13: CNode BEq soundness — when BEq returns true, the two CNodes have
equal depth, guardWidth, guardValue, radixWidth, the same capability at
every slot (WS-ZA ZA5.3: the two slot arrays are equal) and the same link words.

WS-SM SM3.A.3 audit-pass note: written with `obtain` so that a future per-CNode
field added to `BEq` does not silently shift positional indices. -/
theorem CNode.beq_sound (a b : CNode) (h : (a == b) = true) :
    a.depth = b.depth ∧ a.guardWidth = b.guardWidth ∧
    a.guardValue = b.guardValue ∧ a.radixWidth = b.radixWidth ∧
    (∀ s, a.lookup s = b.lookup s) ∧ a.links = b.links := by
  simp only [BEq.beq, Bool.and_eq_true_iff, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hDepth, hGuardWidth⟩, hGuardValue⟩, hRadixWidth⟩, hCells⟩, hLinks⟩ := h
  refine ⟨hDepth, hGuardWidth, hGuardValue, hRadixWidth, fun s => ?_, hLinks⟩
  rw [CNode.lookup_eq_lookupCells]; simp only [CNode.lookupCells, hCells]

-- ============================================================================
-- WS-H13: CSpace depth consistency predicates
-- ============================================================================

/-- WS-H13: CNode well-formedness — consumed bits fit in remaining depth,
and at least one bit is consumed (ensures termination of multi-level resolution).

The two constraints encode:
- `hConsumed`: the CNode does not consume more bits than available at its depth.
- `hProgress`: at least one bit is consumed per resolution step, preventing
  zero-width CNodes that would cause infinite loops. -/
def cnodeWellFormed (cn : CNode) : Prop :=
  cn.bitsConsumed ≤ cn.depth ∧ 0 < cn.bitsConsumed

/-- WS-H13: Empty CNode is trivially well-formed only when depth = 0.
For non-trivial resolution, CNodes must have positive bitsConsumed. -/
theorem CNode.empty_not_wellFormed : ¬ CNode.empty.wellFormed := by
  intro ⟨_, hProg⟩
  simp [CNode.empty, CNode.bitsConsumed] at hProg

-- ============================================================================
-- WS-E4/C-03: Capability Derivation Tree (CDT) model
-- ============================================================================

/-- A slot address in the global capability namespace: (CNode ObjId, Slot). -/
abbrev SlotAddr := SeLe4n.ObjId × SeLe4n.Slot

/-- The operation that created a derivation edge. -/
inductive DerivationOp where
  | mint
  | copy
  | ipcTransfer
  /-- **WS-BP BP7.1 (`v0.36.5`)**: a capability to an object carved out of an
  untyped, recorded as a child of the untyped capability that authorised the
  carve — seL4's `Untyped_Retype`, whose new capabilities are CDT children of
  the untyped's.  Revoking the untyped capability therefore reaches them. -/
  | retype
  deriving Repr, DecidableEq

-- The tree's nodes are slot addresses (`SlotRef`, in `Model/Object/Types.lean`):
-- since WS-ZA ZA5.3 part 2 a slot is its own derivation node, as seL4's
-- `cte_t` is its own mapping-database node.

/-- A single edge in the Capability Derivation Tree.

WS-E4/C-03: Each edge records the parent and child slots and the operation
that created the derivation. The CDT is a forest: each node has at most one
parent but may have many children. -/
structure CapDerivationEdge where
  parent : SlotRef
  child : SlotRef
  op : DerivationOp
  deriving Repr, DecidableEq

namespace CapDerivationEdge

def isChildOf (edge : CapDerivationEdge) (node : SlotRef) : Bool :=
  edge.child = node

def isParentOf (edge : CapDerivationEdge) (node : SlotRef) : Bool :=
  edge.parent = node

end CapDerivationEdge

/-- The Capability Derivation Tree stored at the system level.

WS-E4/C-03: A list of derivation edges forming a forest. Operations maintain
the acyclicity invariant: no slot can be both ancestor and descendant of itself.

**T2-B (H-2): Access-controlled construction.** Direct construction of
`CapDerivationTree` values is restricted to the `CapDerivationTree` namespace:
external code starts from `CapDerivationTree.empty` and changes the tree only
through its operations (`addEdge`, `appendRoot`, `spliceNode`, `moveNode`).

**WS-ZA ZA5.3 part 4: the edge list is the tree.**  Its parent and child reads
(`parentOf`, `childrenOf`) are read off the edges; the kernel's executable
reads walk the derivation links each slot holds (seL4's mapping database),
which an invariant ties to these. -/
structure CapDerivationTree where
  private mk ::
  /-- The edges, as ghost state (`edges`): proofs read them, and the compiled
  kernel stores none of them. -/
  edgesGhost : SeLe4n.Erased (List CapDerivationEdge)
  /-- The sibling chains of the slots with no parent, each in order (ghost): a
  slot with no parent edge is linked to its neighbours in its chain, as seL4's
  mapping database links every capability.  A parentless slot no chain lists
  is a chain of its own.  Boot lays its capabilities in one chain. -/
  rootChainsGhost : SeLe4n.Erased (List (List SlotRef))
  /-- A bound on the number of edges, kept as a word: the fuel of the link
  walks that read the tree (`SystemState.linkChildrenOf`, the revoke loop).
  Each added edge raises it by one and no other change lowers it. -/
  edgeBound : Nat
  edges_le : edgesGhost.out.length ≤ edgeBound
  deriving Repr

namespace CapDerivationTree

/-- **The tree's edges** (WS-ZA ZA5.3 part 5: a ghost).  Only proofs read them;
the kernel reads the tree through the slot links that agree with it. -/
noncomputable def edges (cdt : CapDerivationTree) : List CapDerivationEdge :=
  cdt.edgesGhost.out

theorem edges_length_le (cdt : CapDerivationTree) : cdt.edges.length ≤ cdt.edgeBound :=
  cdt.edges_le

/-- **The root chains** (WS-ZA ZA5.4 part 15: a ghost): the sibling chains of
the slots with no parent, in order.  Only proofs read them; the kernel reads
the chains through the `next` and `prev` links that agree with them. -/
noncomputable def rootChains (cdt : CapDerivationTree) : List (List SlotRef) :=
  cdt.rootChainsGhost.out

/-- Two trees with the same edges, root chains and bound are equal. -/
theorem ext {a b : CapDerivationTree} (hE : a.edges = b.edges) (hR : a.rootChains = b.rootChains)
    (hB : a.edgeBound = b.edgeBound) : a = b := by
  cases a; cases b
  simp only at hB; subst hB
  have : _ = _ := SeLe4n.Erased.ext hE
  subst this
  have : _ = _ := SeLe4n.Erased.ext hR
  subst this; rfl

/-- T2-C (H-2): The canonical empty CDT with no edges. -/
def empty : CapDerivationTree :=
  CapDerivationTree.mk (SeLe4n.Erased.mk []) (SeLe4n.Erased.mk []) 0 (by simp)

@[simp] theorem empty_edges : CapDerivationTree.empty.edges = [] := by
  simp [empty, edges]

@[simp] theorem empty_rootChains : CapDerivationTree.empty.rootChains = [] := by
  simp [empty, rootChains]

/-- Add a derivation edge from parent to child.  The new edge is first, so the
new child is the parent's first child (`childrenOf`), which is right after the
parent in the tree's preorder, where seL4's `cteInsert` puts a derived
capability in the mapping database. -/
def addEdge (cdt : CapDerivationTree) (parent child : SlotRef)
    (op : DerivationOp) : CapDerivationTree :=
  CapDerivationTree.mk (cdt.edgesGhost.map ({ parent, child, op } :: ·)) cdt.rootChainsGhost
    (cdt.edgeBound + 1)
    (by simpa [SeLe4n.Erased.out_map] using cdt.edges_le)

@[simp] theorem addEdge_edges (cdt : CapDerivationTree) (parent child : SlotRef)
    (op : DerivationOp) :
    (cdt.addEdge parent child op).edges = { parent, child, op } :: cdt.edges := by
  unfold edges addEdge; exact SeLe4n.Erased.out_map _ _

@[simp] theorem addEdge_rootChains (cdt : CapDerivationTree) (parent child : SlotRef)
    (op : DerivationOp) : (cdt.addEdge parent child op).rootChains = cdt.rootChains := rfl

@[simp] theorem addEdge_edgeBound (cdt : CapDerivationTree) (parent child : SlotRef)
    (op : DerivationOp) : (cdt.addEdge parent child op).edgeBound = cdt.edgeBound + 1 := rfl

/-- **Append a root** `r` to the end of the first root chain (a new chain when
there is none): how boot lays its capabilities in one chain, each linked after
the one before (`LinkView.appendRoot`). -/
def appendRoot (cdt : CapDerivationTree) (r : SlotRef) : CapDerivationTree :=
  CapDerivationTree.mk cdt.edgesGhost
    (cdt.rootChainsGhost.map fun cs => match cs with
      | [] => [[r]]
      | c :: rest => (c ++ [r]) :: rest)
    cdt.edgeBound cdt.edges_le

@[simp] theorem appendRoot_edges (cdt : CapDerivationTree) (r : SlotRef) :
    (cdt.appendRoot r).edges = cdt.edges := rfl

@[simp] theorem appendRoot_edgeBound (cdt : CapDerivationTree) (r : SlotRef) :
    (cdt.appendRoot r).edgeBound = cdt.edgeBound := rfl

theorem appendRoot_rootChains (cdt : CapDerivationTree) (r : SlotRef) :
    (cdt.appendRoot r).rootChains = match cdt.rootChains with
      | [] => [[r]]
      | c :: rest => (c ++ [r]) :: rest := by
  unfold rootChains appendRoot; exact SeLe4n.Erased.out_map _ _

/-- **A slot the tree names**: an endpoint of one of its edges, or a member of a
root chain.  A slot the tree does not name is outside it: no parent, no
children, no sibling. -/
def mentions (cdt : CapDerivationTree) (ref : SlotRef) : Prop :=
  (∃ e ∈ cdt.edges, e.parent = ref ∨ e.child = ref) ∨ ref ∈ cdt.rootChains.flatten

/-- An endpoint of an edge is a slot the tree names. -/
theorem mentions_of_edge {cdt : CapDerivationTree} {e : CapDerivationEdge} (he : e ∈ cdt.edges)
    {ref : SlotRef} (h : e.parent = ref ∨ e.child = ref) : cdt.mentions ref :=
  .inl ⟨e, he, h⟩

/-- A slot the tree does not name is in no edge. -/
theorem not_edge_of_not_mentions {cdt : CapDerivationTree} {ref : SlotRef}
    (h : ¬ cdt.mentions ref) : ∀ e ∈ cdt.edges, e.parent ≠ ref ∧ e.child ≠ ref :=
  fun e he => ⟨fun hp => h (.inl ⟨e, he, .inl hp⟩), fun hc => h (.inl ⟨e, he, .inr hc⟩)⟩

/-- ...and in no root chain. -/
theorem not_root_of_not_mentions {cdt : CapDerivationTree} {ref : SlotRef}
    (h : ¬ cdt.mentions ref) : ref ∉ cdt.rootChains.flatten :=
  fun hr => h (.inr hr)

/-- The direct children of `node`, newest first (the order `addEdge` puts them
in, and the order the links' sibling chain holds them in). -/
noncomputable def childrenOf (cdt : CapDerivationTree) (node : SlotRef) : List SlotRef :=
  (cdt.edges.filter (·.isParentOf node)).map (·.child)

/-- The parent of `node`: the parent of its newest parent edge.  The tree gives
each slot at most one parent edge (`childrenUnique`), so this is its parent. -/
noncomputable def parentOf (cdt : CapDerivationTree) (node : SlotRef) : Option SlotRef :=
  (cdt.edges.find? (·.isChildOf node)).map (·.parent)

/-- Collect all descendants of a slot via bounded BFS traversal.
Uses fuel = edges.length to ensure termination and completeness
for acyclic trees.
Each step reads a node's children (`childrenOf`).
Y1-E: Uses `Std.HashSet` for O(1) visited-set membership checks (was O(n²)
with `List.Mem`). The `visited` parameter mirrors `acc` for membership;
`acc` remains the result list.

AF2-F / AG8-E: Fuel sufficiency placeholder. `descendantsOf_fuel_sufficient`
proves only `edges.length ≥ 0` (a `Nat` tautology — not a substantive fuel
sufficiency proof). `maxCdtDepth = 65536` provides the hardware-binding CDT
depth constant. The substantive fuel-sufficiency proof (connecting
`edgeWellFounded` to BFS termination) is recorded as a post-1.0 hardening
candidate; registered in `docs/REGISTERED_DEBT.md` (Registered debt index, C.1).
Structural argument (informal): the CDT is acyclic (proven by `cdtAcyclicity`
/ `edgeWellFounded`), so BFS with `edges.length` fuel visits every
reachable node — each edge is traversed at most once, and fuel ≥ edge
count guarantees no premature termination. The visited-set filter ensures
each node is processed at most once. -/
noncomputable def descendantsOf (cdt : CapDerivationTree) (root : SlotRef)
    : List SlotRef :=
  go cdt.edgeBound [root] {} []
where
  go : Nat → List SlotRef → Std.HashSet SlotRef → List SlotRef → List SlotRef
    | 0, _, _, acc => acc
    | _ + 1, [], _, acc => acc
    | fuel + 1, node :: rest, visited, acc =>
        let children := cdt.childrenOf node
        let newChildren := children.filter (fun c => !visited.contains c)
        let visited' := newChildren.foldl (fun s c => s.insert c) visited
        go fuel (rest ++ newChildren) visited' (acc ++ newChildren)

/-- CDT acyclicity: no node reaches itself through derivation edges. -/
def acyclic (cdt : CapDerivationTree) : Prop :=
  ∀ e ∈ cdt.edges, e.parent ∉ cdt.descendantsOf e.child

theorem empty_acyclic : CapDerivationTree.empty.acyclic := by
  intro e hMem
  simp [CapDerivationTree.empty_edges] at hMem

/-- The empty tree names no slot. -/
theorem empty_not_mentions (ref : SlotRef) : ¬ CapDerivationTree.empty.mentions ref := by
  rintro (⟨e, hMem, _⟩ | hR)
  · simp [CapDerivationTree.empty_edges] at hMem
  · simp [CapDerivationTree.empty_rootChains] at hR

-- ============================================================================
-- WS-H4: Edge-well-founded acyclicity (simpler formulation for subset proofs)
-- ============================================================================

/-- WS-H4/M-03: Edge-well-founded acyclicity — no node can reach itself
through a non-empty path of derivation edges. This formulation enables clean
subset-preservation proofs: if edges' ⊆ edges and edges is well-founded,
then edges' is well-founded. -/
def edgeWellFounded (cdt : CapDerivationTree) : Prop :=
  ∀ (node : SlotRef),
    ¬(∃ (path : List SlotRef),
        path.length > 1 ∧
        path.head? = some node ∧
        path.getLast? = some node ∧
        (∀ i, (h : i + 1 < path.length) →
          ∃ e ∈ cdt.edges, e.parent = path[i] ∧ e.child = path[i + 1]))

/-- WS-H4: Empty CDT is trivially edge-well-founded (no edges, no cycles). -/
theorem empty_edgeWellFounded : CapDerivationTree.empty.edgeWellFounded := by
  intro node ⟨path, _, _, _, hEdges⟩
  have h0 := hEdges 0 (by omega)
  rcases h0 with ⟨e, hMem, _, _⟩
  simp [CapDerivationTree.empty_edges] at hMem

/-- WS-H4: Edge-well-foundedness is preserved under edge-subset.
If every edge of `cdt'` is also in `cdt`, and `cdt` is well-founded,
then `cdt'` is well-founded. -/
theorem edgeWellFounded_sub
    (cdt cdt' : CapDerivationTree)
    (hWF : cdt.edgeWellFounded)
    (hSub : ∀ e ∈ cdt'.edges, e ∈ cdt.edges) :
    cdt'.edgeWellFounded := by
  intro node ⟨path, hLen, hHead, hLast, hEdges⟩
  exact hWF node ⟨path, hLen, hHead, hLast, fun i hi => by
    rcases hEdges i hi with ⟨e, hMem, hp, hc⟩
    exact ⟨e, hSub e hMem, hp, hc⟩⟩

/-- WS-H4/M-G03: Adding an edge preserves edge-well-foundedness when the child
node does not appear in any existing edge (as either parent or child). The parent
node MAY already participate in edges.  Every kernel operation that adds an edge
installs into a slot it found empty, and an empty slot is outside the tree
(`cdtCompleteness`), so this is the only form the kernel needs
(`cdt_addEdge_after_insert`). -/
theorem addEdge_preserves_edgeWellFounded_fresh
    (cdt : CapDerivationTree) (parent child : SlotRef) (op : DerivationOp)
    (hNeq : parent ≠ child)
    (hAcyclic : cdt.edgeWellFounded)
    (hFreshChild : ∀ e ∈ cdt.edges, e.parent ≠ child ∧ e.child ≠ child) :
    (cdt.addEdge parent child op).edgeWellFounded := by
  intro node ⟨path, hLen, hHead, hLast, hEdges⟩
  -- Strategy: project the cycle onto old edges. If every edge in the cycle is
  -- old, hAcyclic gives contradiction. For the new edge (parent → child),
  -- child has no outgoing edge (fresh), so the cycle cannot continue past it.
  -- We show contradiction when the new edge appears, then fall through to the
  -- old-edge case to build the projected cycle for hAcyclic.
  apply hAcyclic node
  refine ⟨path, hLen, hHead, hLast, fun i hi => ?_⟩
  have ⟨e, heMem, hep, hec⟩ := hEdges i hi
  simp only [addEdge_edges] at heMem
  rcases List.mem_cons.mp heMem with heq | hOld
  · -- e is the new edge: path[i] = parent, path[i+1] = child
    exfalso
    have hCi1 : path[i + 1] = child := by rw [← hec]; exact congrArg CapDerivationEdge.child heq
    -- Find the edge following child. Either i+2 < path.length (interior)
    -- or i+1 is the last index (cycle wraps to path[0]).
    by_cases hNext : i + 1 + 1 < path.length
    · -- Interior case: edge from path[i+1] = child to path[i+2]
      have ⟨e2, he2Mem, he2p, _⟩ := hEdges (i + 1) hNext
      simp only [addEdge_edges] at he2Mem
      rcases List.mem_cons.mp he2Mem with heq2 | hOld2
      · -- New edge again: parent = path[i+1] = child, but parent ≠ child
        have : path[i + 1] = parent := by rw [← he2p]; exact congrArg CapDerivationEdge.parent heq2
        rw [hCi1] at this; exact hNeq this.symm
      · -- Old edge with parent = child: contradicts hFreshChild
        have := (hFreshChild e2 hOld2).1
        rw [he2p, hCi1] at this; exact this rfl
    · -- Wrap-around case: i+1 = path.length - 1, so child is the last element.
      -- Since getLast? = head? = some node, child = node, and path[0] = child.
      -- Edge 0 starts from child, but child has no edges → contradiction.
      have hJLast : i + 1 = path.length - 1 := by omega
      -- Extract: path[path.length - 1] = node from getLast?
      have hLastIdx : path[path.length - 1] = node := by
        rw [List.getLast?_eq_getElem?] at hLast
        exact (List.getElem?_eq_some_iff.mp hLast).2
      -- child = node: path[i+1] = child, and i+1 = path.length-1, getLast? = some node
      have hChildIsNode : child = node := by
        rw [← hCi1, List.getElem_eq_iff (by omega), show i + 1 = path.length - 1 from hJLast,
            ← List.getLast?_eq_getElem?]
        exact hLast
      -- Extract: path[0] = node from head?
      have hFirstIdx : path[0] = node := by
        cases path with
        | nil => simp at hLen
        | cons a rest => simp [List.head?] at hHead; exact hHead
      have hChildIsFirst : path[0] = child := hFirstIdx.trans hChildIsNode.symm
      -- Edge 0: from path[0] = child to path[1]
      have hFirstEdge : 0 + 1 < path.length := by omega
      have ⟨e0, he0Mem, he0p, _⟩ := hEdges 0 hFirstEdge
      simp only [addEdge_edges] at he0Mem
      rcases List.mem_cons.mp he0Mem with heq0 | hOld0
      · -- New edge: e0.parent = parent = path[0] = child → parent = child contradiction
        have h1 : e0.parent = parent := by simp [heq0]
        exact absurd (h1.symm.trans he0p |>.trans hChildIsFirst) hNeq
      · -- Old edge from child: contradicts hFreshChild
        exact absurd (he0p.trans hChildIsFirst) (hFreshChild e0 hOld0).1
  · exact ⟨e, hOld, hep, hec⟩

/-- WS-H4/M-G03: Runtime cycle-check — returns `true` if adding edge
(parent → child) would NOT create a cycle. Checks that parent ≠ child and
parent is not reachable from child via existing edges. -/
noncomputable def addEdgeWouldBeSafe (cdt : CapDerivationTree) (parent child : SlotRef) : Bool :=
  parent != child && parent ∉ cdt.descendantsOf child

/-- AE4-C (U-18/CAP-02): Propositional reachability — `src` can reach `dst`
through a non-empty path of edges. Used as the specification-level reachability
predicate for CDT acyclicity analysis. -/
def cdtReachable (cdt : CapDerivationTree) (src dst : SlotRef) : Prop :=
  ∃ (path : List SlotRef),
    path.length > 1 ∧
    path.head? = some src ∧
    path.getLast? = some dst ∧
    (∀ i, (h : i + 1 < path.length) →
      ∃ e ∈ cdt.edges, e.parent = path[i] ∧ e.child = path[i + 1])

/-- AE4-C: A fresh child (no edges) trivially has no reachability to any node.
This bridges the gap between `addEdge_preserves_edgeWellFounded_fresh`
(which requires freshness) and the reachability-based specification. -/
theorem freshChild_not_reachable
    (cdt : CapDerivationTree) (child target : SlotRef)
    (hFresh : ∀ e ∈ cdt.edges, e.parent ≠ child ∧ e.child ≠ child) :
    ¬ cdt.cdtReachable child target := by
  intro ⟨path, hLen, hHead, hLast, hEdges⟩
  -- path[0] = child (from hHead). Edge 0→1 must exist (hLen > 1).
  have hFirst : 0 + 1 < path.length := by omega
  have ⟨e, hMem, hep, _⟩ := hEdges 0 hFirst
  -- path[0] = child
  have hP0 : path[0] = child := by
    cases path with
    | nil => simp at hLen
    | cons a rest => simp [List.head?] at hHead; exact hHead
  -- e.parent = path[0] = child, but hFresh says no edge has parent = child
  exact (hFresh e hMem).1 (hep.trans hP0)

-- W2-H (L-3): 2M heartbeats — highest in the codebase. Inherent complexity from
-- CDT acyclicity reasoning: the proof projects each cycle edge onto old CDT edges,
-- constructs a rotated sub-path from child to parent, and derives a contradiction.
-- Nested well-founded recursion over the CDT parent map makes this irreducible.
set_option maxHeartbeats 2000000 in
/-- R2-D/M-08: `addEdge` preserves `edgeWellFounded` when:
1. `parent ≠ child`
2. Existing CDT is acyclic
3. No existing edge targets `child` (no incoming edges)
4. No old-edge path from `child` to `parent` exists

Generalizes `addEdge_preserves_edgeWellFounded_fresh` to non-fresh child nodes
(child may have outgoing edges/subtree). The proof projects each cycle edge onto
old CDT edges; when the new edge is encountered, constructs a rotated sub-path
from child to parent using only old edges, contradicting hypothesis 4. -/
theorem addEdge_preserves_edgeWellFounded_noParent
    (cdt : CapDerivationTree) (parent child : SlotRef) (op : DerivationOp)
    (hNeq : parent ≠ child)
    (hAcyclic : cdt.edgeWellFounded)
    (_hNoIncoming : ∀ e ∈ cdt.edges, e.child ≠ child)
    (hNoPath : ∀ (p : List SlotRef),
      p.length > 1 → p.head? = some child → p.getLast? = some parent →
      (∀ i, (h : i + 1 < p.length) → ∃ e ∈ cdt.edges, e.parent = p[i] ∧ e.child = p[i + 1]) →
      False) :
    (cdt.addEdge parent child op).edgeWellFounded := by
  intro node ⟨path, hLen, hHead, hLast, hEdges⟩
  -- Project each edge to old CDT. If old, keep. If new (parent→child), derive ⊥ via hNoPath.
  apply hAcyclic node
  refine ⟨path, hLen, hHead, hLast, fun idx hIdx => ?_⟩
  have ⟨e, heMem, hep, hec⟩ := hEdges idx hIdx
  simp only [addEdge_edges] at heMem
  rcases List.mem_cons.mp heMem with heq | hOld
  · -- The edge at idx is the new edge: path[idx] = parent, path[idx+1] = child
    exfalso
    have hCidx : path[idx + 1] = child := by rw [← hec]; exact congrArg CapDerivationEdge.child heq
    have hPidx : path[idx] = parent := by rw [← hep]; exact congrArg CapDerivationEdge.parent heq
    -- At positions where path[j] ≠ parent, the edge is provably old
    have hOldAt : ∀ j (hj : j + 1 < path.length), path[j] ≠ parent →
        ∃ e ∈ cdt.edges, e.parent = path[j] ∧ e.child = path[j + 1] := by
      intro j hj hjNe
      obtain ⟨ej, hejMem, hejp, hejc⟩ := hEdges j hj
      simp only [addEdge_edges] at hejMem
      rcases List.mem_cons.mp hejMem with heq' | hold
      · exact absurd (by rw [← hejp]; exact congrArg CapDerivationEdge.parent heq') hjNe
      · exact ⟨ej, hold, hejp, hejc⟩
    -- Cycle boundary properties
    have hFirst : path[0]'(by omega) = node := by
      cases path with | nil => simp at hLen | cons a rest => simp [List.head?] at hHead; exact hHead
    have hLastIdx : path[path.length - 1] = node := by
      rw [List.getLast?_eq_getElem?] at hLast; exact (List.getElem?_eq_some_iff.mp hLast).2
    -- Base case: cycle of length 2 forces parent = child, contradiction
    have hL3 : path.length ≥ 3 := by
      rcases Nat.lt_or_ge path.length 3 with h | h
      · exfalso
        have hp : path[idx]'(by omega) = path[0]'(by omega) := by congr 1; omega
        have hc : path[idx + 1]'(by omega) = path[1]'(by omega) := by congr 1; omega
        have hn : path[1]'(by omega) = path[path.length - 1]'(by omega) := by congr 1; omega
        exact hNeq (hPidx.symm.trans (hp ▸ hFirst) |>.trans (hn ▸ hLastIdx).symm |>.trans (hc ▸ hCidx))
      · exact h
    -- Build rotated path from child (at idx+1) back to parent (at idx)
    let L := path.length
    let nodeAt : Fin (L - 1) → SlotRef := fun k =>
      if h : idx + 1 + k.val < L then path[idx + 1 + k.val]
      else path[idx + 1 + k.val - L + 1]'(by omega)
    let rotPath := List.ofFn nodeAt
    have hRotLen : rotPath.length = L - 1 := List.length_ofFn ..
    have hRotGet : ∀ (k : Nat) (hk : k < L - 1),
        rotPath[k]'(by rw [hRotLen]; exact hk) = nodeAt ⟨k, hk⟩ :=
      fun k hk => List.getElem_ofFn ..
    -- rotPath[0] = child
    have hRotFirst : rotPath[0]'(by rw [hRotLen]; omega) = child := by
      rw [hRotGet 0 (by omega)]
      simp only [nodeAt, dif_pos (show idx + 1 + (⟨0, by omega⟩ : Fin (L - 1)).val < L from by simp; omega)]
      exact hCidx
    -- rotPath[L-2] = parent
    have hRotLastP : rotPath[L - 2]'(by rw [hRotLen]; omega) = parent := by
      rw [hRotGet (L - 2) (by omega)]; simp only [nodeAt]
      split
      · next h =>
        have : path[idx + 1 + (L - 2)]'(by omega) = path[L - 1]'(by omega) := by congr 1; omega
        rw [this, hLastIdx, ← hFirst]
        have : path[idx]'(by omega) = path[0]'(by omega) := by congr 1; omega
        rwa [← this]
      · next h =>
        have : path[idx + 1 + (L - 2) - L + 1]'(by omega) = path[idx]'(by omega) := by congr 1; omega
        rw [this]; exact hPidx
    -- Find first parent in rotation, truncate, apply hNoPath
    have hParInRot : ∃ x ∈ rotPath, (x == parent) = true :=
      ⟨rotPath[L - 2], List.getElem_mem .., by rw [hRotLastP]; exact beq_self_eq_true _⟩
    let m := rotPath.findIdx (· == parent)
    have hm : m < rotPath.length := List.findIdx_lt_length_of_exists hParInRot
    have hmP : rotPath[m]'hm = parent := eq_of_beq (List.findIdx_getElem (w := hm))
    have hBNe : ∀ (i : Nat) (hi : i < m), rotPath[i]'(by omega) ≠ parent := by
      intro i hi habs; have := List.not_of_lt_findIdx hi; simp [habs] at this
    have hm0 : m > 0 := by
      rcases Nat.eq_zero_or_pos m with h | h
      · exact absurd (hRotFirst.symm.trans (by congr 1; omega) |>.trans hmP).symm hNeq
      · exact h
    -- opath = rotPath.take (m+1): sub-path from child to parent, all edges old
    let opath := rotPath.take (m + 1)
    have hOL : opath.length = m + 1 := by simp [opath, List.length_take, hRotLen]; omega
    apply hNoPath opath
    · rw [hOL]; omega
    · rw [List.head?_take]; simp
      cases hrot : rotPath with
      | nil => rw [hrot] at hm; simp at hm
      | cons a rest =>
        simp only [List.head?]; congr 1
        have : rotPath[0]'(by simp [hrot]) = a := by simp [hrot]
        rw [← hRotFirst, this]
    · rw [List.getLast?_take]; simp [show m + 1 - 1 = m from by omega]
      rw [show rotPath[m]? = some parent from List.getElem?_eq_some_iff.mpr ⟨hm, hmP⟩]; simp
    · intro i hi; rw [hOL] at hi
      have him : i < m := by omega
      rw [show opath[i] = rotPath[i] from List.getElem_take ..,
          show opath[i + 1] = rotPath[i + 1] from List.getElem_take ..,
          hRotGet i (by omega), hRotGet (i + 1) (by omega)]
      simp only [nodeAt]
      have hSrcNePar : nodeAt ⟨i, by omega⟩ ≠ parent := by
        rw [← hRotGet i (by omega)]; exact hBNe i him
      split <;> rename_i h1 <;> split <;> rename_i h2
      · exact hOldAt (idx + 1 + i) (by omega) (by simp only [nodeAt, dif_pos h1] at hSrcNePar; exact hSrcNePar)
      · have hSrc : path[idx + 1 + i]'(by omega) = path[0]'(by omega) := by
          have : path[idx + 1 + i]'(by omega) = path[L - 1]'(by omega) := by congr 1; omega
          rw [this, hLastIdx, ← hFirst]
        have hTgt : path[idx + 1 + (i + 1) - L + 1]'(by omega) = path[1]'(by omega) := by congr 1; omega
        rw [hSrc, hTgt]
        exact hOldAt 0 (by omega) (by
          intro h; simp only [nodeAt, dif_pos h1] at hSrcNePar; exact hSrcNePar (hSrc.symm ▸ h))
      · omega
      · have hNP : path[idx + 1 + i - L + 1]'(by omega) ≠ parent := by
          simp only [nodeAt, dif_neg h1] at hSrcNePar; exact hSrcNePar
        obtain ⟨e', he', hep', hec'⟩ := hOldAt (idx + 1 + i - L + 1) (by omega) hNP
        refine ⟨e', he', hep', ?_⟩
        have : path[(idx + 1 + i - L + 1) + 1]'(by omega) = path[idx + 1 + (i + 1) - L + 1]'(by omega) := by
          congr 1; omega
        rwa [← this]
  · exact ⟨e, hOld, hep, hec⟩

-- ============================================================================
-- WS-ZA (#951): splicing a node out of the tree
-- ============================================================================

/-- A path whose every step is `r` relates its first element to its last by the
transitive closure of `r`. -/
theorem transGen_of_steps {α : Type} {r : α → α → Prop} :
    ∀ (path : List α) (a b : α), path.length > 1 → path.head? = some a →
      path.getLast? = some b → (∀ i (h : i + 1 < path.length), r path[i] path[i + 1]) →
      Relation.TransGen r a b
  | [], _, _, h, _, _, _ => by simp at h
  | [_], _, _, h, _, _, _ => by simp at h
  | x :: y :: rest, a, b, _, hHead, hLast, hSteps => by
    simp only [List.head?, Option.some.injEq] at hHead; subst hHead
    have h0 : r x y := hSteps 0 (by simp)
    cases rest with
    | nil =>
      simp at hLast; subst hLast; exact .single h0
    | cons z rest' =>
      have ih := transGen_of_steps (y :: z :: rest') y b (by simp) rfl
        (by simpa [List.getLast?_cons_cons] using hLast)
        (fun i h => hSteps (i + 1) (by simp at h ⊢; omega))
      exact Relation.TransGen.trans (.single h0) ih

/-- The converse: the transitive closure of `r` is witnessed by a path of `r` steps. -/
theorem steps_of_transGen {α : Type} {r : α → α → Prop} {a b : α}
    (h : Relation.TransGen r a b) :
    ∃ path : List α, path.length > 1 ∧ path.head? = some a ∧ path.getLast? = some b ∧
      ∀ i (h : i + 1 < path.length), r path[i] path[i + 1] := by
  induction h with
  | single h => exact ⟨[a, _], by simp, rfl, rfl, fun i hi => by
      have : i = 0 := by simp at hi; omega
      subst this; simpa using h⟩
  | @tail c d _ hcd ih =>
    obtain ⟨p, hLen, hHead, hLast, hSteps⟩ := ih
    refine ⟨p ++ [d], by simp; omega, ?_, by simp, fun i hi => ?_⟩
    · cases p with
      | nil => simp at hLen
      | cons x xs => simpa using hHead
    · simp only [List.length_append, List.length_singleton] at hi
      by_cases hlt : i + 1 < p.length
      · rw [List.getElem_append_left (by omega), List.getElem_append_left hlt]
        exact hSteps i hlt
      · have hi' : i + 1 = p.length := by omega
        have hc : p[i]'(by omega) = c := by
          rw [List.getLast?_eq_getElem?] at hLast
          have := (List.getElem?_eq_some_iff.mp hLast).2
          simp only [show p.length - 1 = i by omega] at this; exact this
        rw [List.getElem_append_left (by omega), List.getElem_append_right (by omega)]
        simp only [hi', Nat.sub_self, List.getElem_singleton]
        rw [hc]; exact hcd

/-- Transitive closure is monotone in a relation whose steps are reached in `s`. -/
theorem transGen_lift {α : Type} {r s : α → α → Prop} {a b : α}
    (h : Relation.TransGen r a b) (hrs : ∀ x y, r x y → Relation.TransGen s x y) :
    Relation.TransGen s a b := by
  induction h with
  | single h => exact hrs _ _ h
  | tail _ h ih => exact ih.trans (hrs _ _ h)

/-- One step along a derivation edge of `cdt`. -/
def edgeStep (cdt : CapDerivationTree) (a b : SlotRef) : Prop :=
  ∃ e ∈ cdt.edges, e.parent = a ∧ e.child = b

/-- Acyclicity carries over to a tree each of whose edges joins two nodes the old
tree already linked by a path: a cycle in the new tree would trace a cycle in
the old one. -/
theorem edgeWellFounded_of_edges_transGen (cdt cdt' : CapDerivationTree)
    (hWF : cdt.edgeWellFounded)
    (hReach : ∀ e ∈ cdt'.edges, Relation.TransGen (edgeStep cdt) e.parent e.child) :
    cdt'.edgeWellFounded := by
  intro node ⟨path, hLen, hHead, hLast, hEdges⟩
  have hNew : Relation.TransGen (edgeStep cdt') node node :=
    transGen_of_steps path node node hLen hHead hLast hEdges
  have hOld := transGen_lift hNew (fun x y ⟨e, he, hp, hc⟩ => hp ▸ hc ▸ hReach e he)
  exact hWF node (steps_of_transGen hOld)


/-- The edge list with `node`'s edges taken away. -/
def withoutNodeEdges (es : List CapDerivationEdge) (node : SlotRef) : List CapDerivationEdge :=
  es.filter (fun e => !e.isParentOf node && !e.isChildOf node)

/-- `l`'s edges re-made with parent `p`, in order, each by its operation. -/
def reparentEdges (p : SlotRef) (l : List CapDerivationEdge) : List CapDerivationEdge :=
  l.map fun e => { parent := p, child := e.child, op := e.op }

theorem reparentEdges_length (p : SlotRef) (l : List CapDerivationEdge) :
    (reparentEdges p l).length = l.length := List.length_map ..

private theorem filter_not_and_length_add {α : Type} (p q : α → Bool) :
    ∀ (l : List α), (l.filter (fun e => !p e && !q e)).length + (l.filter p).length ≤ l.length
  | [] => by simp
  | x :: xs => by
    have ih := filter_not_and_length_add p q xs
    cases hp : p x <;> cases hq : q x <;> simp [hp, hq] <;> omega

/-- The edges without `node`'s, plus the edges out of `node`, number at most
the edges. -/
theorem withoutNodeEdges_length_add (es : List CapDerivationEdge) (node : SlotRef) :
    (withoutNodeEdges es node).length + (es.filter (·.isParentOf node)).length ≤ es.length :=
  filter_not_and_length_add _ _ es

/-- `l` with each `n` replaced, in place, by the list `m`. -/
def replaceSlot (n : SlotRef) (m : List SlotRef) (l : List SlotRef) : List SlotRef :=
  l.flatMap fun x => if x = n then m else [x]

theorem replaceSlot_of_not_mem {n : SlotRef} {m : List SlotRef} :
    ∀ {l : List SlotRef}, n ∉ l → replaceSlot n m l = l
  | [], _ => rfl
  | a :: l, h => by
    have ha : a ≠ n := fun e => h (e ▸ List.mem_cons_self ..)
    simp only [replaceSlot, List.flatMap_cons, if_neg ha, List.singleton_append]
    exact congrArg (a :: ·) (replaceSlot_of_not_mem (fun hm => h (List.mem_cons_of_mem _ hm)))

theorem replaceSlot_append (n : SlotRef) (m l₁ l₂ : List SlotRef) :
    replaceSlot n m (l₁ ++ l₂) = replaceSlot n m l₁ ++ replaceSlot n m l₂ := by
  simp [replaceSlot, List.flatMap_append]

theorem replaceSlot_cons_self (n : SlotRef) (m l : List SlotRef) :
    replaceSlot n m (n :: l) = m ++ replaceSlot n m l := by
  simp [replaceSlot]

theorem mem_replaceSlot {n x : SlotRef} {m l : List SlotRef} :
    x ∈ replaceSlot n m l ↔ (x ∈ l ∧ x ≠ n) ∨ (n ∈ l ∧ x ∈ m) := by
  simp only [replaceSlot, List.mem_flatMap]
  constructor
  · rintro ⟨y, hy, hx⟩
    split at hx
    · next h => subst h; exact .inr ⟨hy, hx⟩
    · next h => simp at hx; subst hx; exact .inl ⟨hy, h⟩
  · rintro (⟨hx, hn⟩ | ⟨hn, hx⟩)
    · exact ⟨x, hx, by simp [hn]⟩
    · exact ⟨n, hn, by simp [hx]⟩

/-- **The splice of `node` from a run `l` of the edges**, whose child edges of
`node` are `kids`: up to `node`'s first parent edge, the edges clear of `node`;
in that edge's place, `kids` re-made from its parent, in order; after it, the
edges clear of `node`. -/
def spliceEdgesFrom (node : SlotRef) (kids : List CapDerivationEdge) :
    List CapDerivationEdge → List CapDerivationEdge
  | [] => []
  | e :: es =>
    if e.child = node then reparentEdges e.parent kids ++ withoutNodeEdges es node
    else if e.parent = node then spliceEdgesFrom node kids es
    else e :: spliceEdgesFrom node kids es

/-- **The splice's edges** (`spliceNode`): `node`'s edges go, and `node`'s
children are re-derived from `node`'s parent in `node`'s place among its
siblings, in their order, as seL4's `cteDelete` leaves the capabilities derived
from a deleted one where they were in the mapping database. -/
def spliceEdges (es : List CapDerivationEdge) (node : SlotRef) : List CapDerivationEdge :=
  spliceEdgesFrom node (es.filter (·.isParentOf node)) es

theorem spliceEdgesFrom_length_add (node : SlotRef) (kids : List CapDerivationEdge) :
    ∀ l : List CapDerivationEdge,
      (spliceEdgesFrom node kids l).length + (l.filter (·.isParentOf node)).length ≤
        l.length + kids.length
  | [] => by simp [spliceEdgesFrom]
  | e :: es => by
    have ih := spliceEdgesFrom_length_add node kids es
    have hw := withoutNodeEdges_length_add es node
    unfold spliceEdgesFrom
    by_cases hc : e.child = node
    · rw [if_pos hc, List.length_append, reparentEdges_length]
      cases hp : e.isParentOf node <;> simp [hp] <;> omega
    · rw [if_neg hc]
      by_cases hp : e.parent = node
      · have hp' : e.isParentOf node = true := by simp [CapDerivationEdge.isParentOf, hp]
        rw [if_pos hp]; simp [hp']; omega
      · have hp' : e.isParentOf node = false := by simp [CapDerivationEdge.isParentOf, hp]
        rw [if_neg hp]; simp [hp']; omega

theorem spliceEdges_length_le (es : List CapDerivationEdge) (node : SlotRef) :
    (spliceEdges es node).length ≤ es.length := by
  have := spliceEdgesFrom_length_add node (es.filter (·.isParentOf node)) es
  unfold spliceEdges; omega

/-- A run with no parent edge of `node` loses `node`'s edges and nothing else. -/
theorem spliceEdgesFrom_of_no_parent (node : SlotRef) (kids : List CapDerivationEdge) :
    ∀ l : List CapDerivationEdge, (∀ e ∈ l, e.child ≠ node) →
      spliceEdgesFrom node kids l = withoutNodeEdges l node
  | [], _ => rfl
  | e :: es, h => by
    have hc := h e (List.mem_cons_self ..)
    have ih := spliceEdgesFrom_of_no_parent node kids es (fun x hx => h x (List.mem_cons_of_mem _ hx))
    unfold spliceEdgesFrom withoutNodeEdges
    rw [if_neg hc]
    have hc' : e.isChildOf node = false := by simp [CapDerivationEdge.isChildOf, hc]
    by_cases hp : e.parent = node
    · have hp' : e.isParentOf node = true := by simp [CapDerivationEdge.isParentOf, hp]
      rw [if_pos hp, ih]; simp [withoutNodeEdges, hp']
    · have hp' : e.isParentOf node = false := by simp [CapDerivationEdge.isParentOf, hp]
      rw [if_neg hp, ih]; simp [withoutNodeEdges, hp', hc']

/-- **The splice at `node`'s first parent edge**: the edges before it clear of
`node`, `kids` re-made from its parent, the edges after it clear of `node`. -/
theorem spliceEdgesFrom_split (node : SlotRef) (kids : List CapDerivationEdge) :
    ∀ (pre : List CapDerivationEdge) (up : CapDerivationEdge) (post : List CapDerivationEdge),
      (∀ e ∈ pre, e.child ≠ node) → up.child = node →
      spliceEdgesFrom node kids (pre ++ up :: post) =
        withoutNodeEdges pre node ++ reparentEdges up.parent kids ++ withoutNodeEdges post node
  | [], up, post, _, hu => by simp [spliceEdgesFrom, hu, withoutNodeEdges]
  | e :: pre, up, post, h, hu => by
    have hc := h e (List.mem_cons_self ..)
    have ih := spliceEdgesFrom_split node kids pre up post
      (fun x hx => h x (List.mem_cons_of_mem _ hx)) hu
    rw [List.cons_append]
    unfold spliceEdgesFrom
    rw [if_neg hc]
    have hc' : e.isChildOf node = false := by simp [CapDerivationEdge.isChildOf, hc]
    by_cases hp : e.parent = node
    · have hp' : e.isParentOf node = true := by simp [CapDerivationEdge.isParentOf, hp]
      rw [if_pos hp, ih]; simp [withoutNodeEdges, hp']
    · have hp' : e.isParentOf node = false := by simp [CapDerivationEdge.isParentOf, hp]
      rw [if_neg hp, ih]; simp [withoutNodeEdges, hp', hc']

/-- Every edge a splice of a run makes is an edge of the run clear of `node`,
or one of `kids` re-made from the parent of an edge of the run into `node`. -/
theorem mem_spliceEdgesFrom (node : SlotRef) (kids : List CapDerivationEdge) :
    ∀ (l : List CapDerivationEdge) (e' : CapDerivationEdge), e' ∈ spliceEdgesFrom node kids l →
      (e' ∈ l ∧ e'.parent ≠ node ∧ e'.child ≠ node) ∨
      ∃ up ∈ l, up.child = node ∧ ∃ k ∈ kids, e' = { parent := up.parent, child := k.child, op := k.op }
  | [], _, h => by cases h
  | e :: es, e', h => by
    unfold spliceEdgesFrom at h
    by_cases hc : e.child = node
    · rw [if_pos hc] at h
      rcases List.mem_append.mp h with h | h
      · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp h
        exact .inr ⟨e, List.mem_cons_self .., hc, k, hk, rfl⟩
      · simp only [withoutNodeEdges, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true',
          CapDerivationEdge.isParentOf, CapDerivationEdge.isChildOf, decide_eq_false_iff_not] at h
        exact .inl ⟨List.mem_cons_of_mem _ h.1, h.2.1, h.2.2⟩
    · rw [if_neg hc] at h
      have lift : e' ∈ spliceEdgesFrom node kids es →
          (e' ∈ e :: es ∧ e'.parent ≠ node ∧ e'.child ≠ node) ∨
          ∃ up ∈ e :: es, up.child = node ∧ ∃ k ∈ kids,
            e' = { parent := up.parent, child := k.child, op := k.op } := fun h' => by
        rcases mem_spliceEdgesFrom node kids es e' h' with ⟨a, b, c⟩ | ⟨up, hup, r⟩
        · exact .inl ⟨List.mem_cons_of_mem _ a, b, c⟩
        · exact .inr ⟨up, List.mem_cons_of_mem _ hup, r⟩
      by_cases hp : e.parent = node
      · rw [if_pos hp] at h; exact lift h
      · rw [if_neg hp] at h
        rcases List.mem_cons.mp h with rfl | h
        · exact .inl ⟨List.mem_cons_self .., hp, hc⟩
        · exact lift h

/-- The root chains after splicing a slot `node` with no parent edge, whose
children are `kids`: `kids` take `node`'s place in its chain, in their order; a
`node` no chain lists was a chain of its own, which `kids` now are. -/
def spliceRootChains (cs : List (List SlotRef)) (node : SlotRef) (kids : List SlotRef) :
    List (List SlotRef) :=
  if node ∈ cs.flatten then cs.map (replaceSlot node kids)
  else if kids = [] then cs else cs ++ [kids]

/-- Splicing a slot out of root chains leaves their slots but it, and its
children when it was a root. -/
theorem mem_flatten_spliceRootChains {cs : List (List SlotRef)} {node : SlotRef}
    {kids : List SlotRef} {x : SlotRef} (h : x ∈ (spliceRootChains cs node kids).flatten) :
    (x ∈ cs.flatten ∧ x ≠ node) ∨ x ∈ kids := by
  unfold spliceRootChains at h
  split at h
  · simp only [List.mem_flatten, List.mem_map] at h
    obtain ⟨c', ⟨c, hc, rfl⟩, hx⟩ := h
    rcases mem_replaceSlot.mp hx with ⟨hx, hn⟩ | ⟨_, hx⟩
    · exact .inl ⟨List.mem_flatten.mpr ⟨c, hc, hx⟩, hn⟩
    · exact .inr hx
  · next hn =>
    have ne : x ∈ cs.flatten → x ≠ node := fun hx e => hn (e ▸ hx)
    split at h
    · exact .inl ⟨h, ne h⟩
    · rw [List.flatten_append] at h
      rcases List.mem_append.mp h with h | h
      · exact .inl ⟨h, ne h⟩
      · exact .inr (by simpa using h)

/-- The root chains with `node` dropped from each. -/
theorem mem_flatten_map_replaceSlot_nil {cs : List (List SlotRef)} {node x : SlotRef}
    (h : x ∈ (cs.map (replaceSlot node [])).flatten) : x ∈ cs.flatten ∧ x ≠ node := by
  simp only [List.mem_flatten, List.mem_map] at h
  obtain ⟨c', ⟨c, hc, rfl⟩, hx⟩ := h
  rcases mem_replaceSlot.mp hx with ⟨hx, hn⟩ | ⟨_, hx⟩
  · exact ⟨List.mem_flatten.mpr ⟨c, hc, hx⟩, hn⟩
  · cases hx

/-- Whether `node` has a parent edge, as the splice decides it. -/
def hasParentEdge (es : List CapDerivationEdge) (node : SlotRef) : Bool :=
  es.any (·.isChildOf node)

theorem hasParentEdge_eq_false_iff (es : List CapDerivationEdge) (node : SlotRef) :
    hasParentEdge es node = false ↔ ∀ e ∈ es, e.child ≠ node := by
  simp [hasParentEdge, CapDerivationEdge.isChildOf]

/-- **Splice `node` out of the tree**, as seL4's `cteDelete` unlinks a
capability from the mapping database: `node`'s edges go, and each child it had
is derived from `node`'s own parent instead, by the operation it was derived by,
in `node`'s place among that parent's children and in the order they had.  A
root's children take its place in its root chain.  So the tree's preorder after
the splice is the preorder before it with `node` taken out, as seL4's list is.
Deleting a slot therefore never depends on whether it has derived capabilities,
and revoking an ancestor still reaches every capability derived through the
deleted one. -/
def spliceNode (cdt : CapDerivationTree) (node : SlotRef) : CapDerivationTree :=
  CapDerivationTree.mk (cdt.edgesGhost.map (spliceEdges · node))
    (SeLe4n.Erased.mk (if hasParentEdge cdt.edges node then cdt.rootChains.map (replaceSlot node [])
      else spliceRootChains cdt.rootChains node (cdt.childrenOf node)))
    cdt.edgeBound
    (by simpa [SeLe4n.Erased.out_map] using
      Nat.le_trans (spliceEdges_length_le _ node) cdt.edges_le)

@[simp] theorem spliceNode_edges_eq (cdt : CapDerivationTree) (node : SlotRef) :
    (cdt.spliceNode node).edges = spliceEdges cdt.edges node := by
  unfold edges spliceNode; exact SeLe4n.Erased.out_map _ _

theorem spliceNode_rootChains (cdt : CapDerivationTree) (node : SlotRef) :
    (cdt.spliceNode node).rootChains =
      if hasParentEdge cdt.edges node then cdt.rootChains.map (replaceSlot node [])
      else spliceRootChains cdt.rootChains node (cdt.childrenOf node) := by
  unfold rootChains spliceNode; exact SeLe4n.Erased.out_mk _

@[simp] theorem spliceNode_edgeBound (cdt : CapDerivationTree) (node : SlotRef) :
    (cdt.spliceNode node).edgeBound = cdt.edgeBound := rfl

/-- `old` renamed `new`. -/
@[inline] def renameSlot (old new r : SlotRef) : SlotRef := if r = old then new else r

/-- An edge with `old` renamed `new` at both ends. -/
def renameEdge (old new : SlotRef) (e : CapDerivationEdge) : CapDerivationEdge :=
  { parent := renameSlot old new e.parent, child := renameSlot old new e.child, op := e.op }

/-- **The move's edges** (`moveNode`): every edge with `old` renamed `new`, in
place. -/
def moveEdges (es : List CapDerivationEdge) (old new : SlotRef) : List CapDerivationEdge :=
  es.map (renameEdge old new)

/-- **Move node `old` to slot `new`**, as seL4's `cteMove` rewrites the moved
slot's mapping-database neighbours to name its new address: `old` is renamed
`new` in every edge and root chain, so `new` keeps `old`'s place among its
siblings and the tree's preorder is the old one with `old` renamed.  A slot
outside the tree moves nothing.

`new` is the move's destination, an empty slot, and an empty slot is outside the
tree: every delete splices its slot out of it (`spliceNode`). -/
def moveNode (cdt : CapDerivationTree) (old new : SlotRef) : CapDerivationTree :=
  CapDerivationTree.mk (cdt.edgesGhost.map (moveEdges · old new))
    (cdt.rootChainsGhost.map (·.map (·.map (renameSlot old new)))) cdt.edgeBound
    (by simpa [SeLe4n.Erased.out_map, moveEdges] using cdt.edges_le)

@[simp] theorem moveNode_edges_eq (cdt : CapDerivationTree) (old new : SlotRef) :
    (cdt.moveNode old new).edges = moveEdges cdt.edges old new := by
  unfold edges moveNode; exact SeLe4n.Erased.out_map _ _

theorem moveNode_rootChains (cdt : CapDerivationTree) (old new : SlotRef) :
    (cdt.moveNode old new).rootChains = cdt.rootChains.map (·.map (renameSlot old new)) := by
  unfold rootChains moveNode; exact SeLe4n.Erased.out_map _ _

@[simp] theorem moveNode_edgeBound (cdt : CapDerivationTree) (old new : SlotRef) :
    (cdt.moveNode old new).edgeBound = cdt.edgeBound := rfl

/-- Every edge after a splice is an old edge clear of `node`, or joins `node`'s
parent to one of `node`'s children. -/
theorem spliceNode_edges (cdt : CapDerivationTree) (node : SlotRef) :
    ∀ e' ∈ (cdt.spliceNode node).edges,
      (e' ∈ cdt.edges ∧ e'.parent ≠ node ∧ e'.child ≠ node) ∨
      ∃ up ∈ cdt.edges, ∃ e ∈ cdt.edges, up.child = node ∧ e.parent = node ∧
        e'.parent = up.parent ∧ e'.child = e.child := by
  intro e' h
  rw [spliceNode_edges_eq] at h
  rcases mem_spliceEdgesFrom node _ cdt.edges e' h with h | ⟨up, hup, huc, k, hk, rfl⟩
  · exact .inl h
  · simp only [List.mem_filter, CapDerivationEdge.isParentOf, decide_eq_true_eq] at hk
    exact .inr ⟨up, hup, k, hk.1, huc, hk.2, rfl, rfl⟩

/-- A splice keeps the tree acyclic: each new edge shortcuts an old two-edge path. -/
theorem spliceNode_edgeWellFounded (cdt : CapDerivationTree) (node : SlotRef)
    (hWF : cdt.edgeWellFounded) : (cdt.spliceNode node).edgeWellFounded :=
  edgeWellFounded_of_edges_transGen cdt _ hWF fun e' he' => by
    rcases spliceNode_edges cdt node e' he' with ⟨h, -, -⟩ | ⟨up, hUp, e, he, hUc, hEp, hP, hC⟩
    · exact .single ⟨e', h, rfl, rfl⟩
    · exact .tail (.single ⟨up, hUp, hP.symm, hUc⟩) ⟨e, he, hEp, hC.symm⟩

/-- The root chains after a splice hold only slots the tree named. -/
private theorem spliceNode_rootChains_mem (cdt : CapDerivationTree) (node : SlotRef) {x : SlotRef}
    (h : x ∈ (cdt.spliceNode node).rootChains.flatten) :
    (x ∈ cdt.rootChains.flatten ∧ x ≠ node) ∨ x ∈ cdt.childrenOf node := by
  rw [spliceNode_rootChains] at h
  split at h
  · exact .inl (mem_flatten_map_replaceSlot_nil h)
  · exact mem_flatten_spliceRootChains h

/-- Nor does a splice name a slot the tree did not: each edge it makes joins two
slots the tree named, and its root chains hold old roots and `node`'s children. -/
theorem spliceNode_mentions (cdt : CapDerivationTree) (node ref : SlotRef)
    (h : (cdt.spliceNode node).mentions ref) : cdt.mentions ref := by
  rcases h with ⟨e', he', hr⟩ | hR
  · rcases spliceNode_edges cdt node e' he' with ⟨h, -, -⟩ | ⟨up, hUp, e, he, _, _, hP, hC⟩
    · exact .inl ⟨e', h, hr⟩
    · rcases hr with hr | hr
      · exact .inl ⟨up, hUp, .inl (hP ▸ hr)⟩
      · exact .inl ⟨e, he, .inr (hC ▸ hr)⟩
  · rcases spliceNode_rootChains_mem cdt node hR with ⟨h, -⟩ | h
    · exact .inr h
    · simp only [childrenOf, List.mem_map, List.mem_filter] at h
      obtain ⟨e, ⟨he, -⟩, hc⟩ := h
      exact .inl ⟨e, he, .inr hc⟩

/-- An acyclic tree has no edge from a node to itself. -/
theorem edgeWellFounded_no_self_edge {cdt : CapDerivationTree} (hWF : cdt.edgeWellFounded)
    {e : CapDerivationEdge} (he : e ∈ cdt.edges) : e.parent ≠ e.child := by
  intro hEq
  exact hWF e.parent ⟨[e.parent, e.child], by simp, rfl, by simp [hEq],
    fun i hi => by
      have : i = 0 := by simp at hi; omega
      subst this
      exact ⟨e, he, rfl, rfl⟩⟩

/-- A splice of an acyclic tree takes its node out of the tree: the edges it
makes join the node's parent to the node's children, neither of which is the
node, and its root chains drop the node. -/
theorem spliceNode_not_mentions_self (cdt : CapDerivationTree) (node : SlotRef)
    (hWF : cdt.edgeWellFounded) : ¬ (cdt.spliceNode node).mentions node := by
  rintro (⟨e', he', hr⟩ | hR)
  · rcases spliceNode_edges cdt node e' he' with ⟨-, h1, h2⟩ | ⟨up, hUp, e, he, hUc, hEp, hP, hC⟩
    · rcases hr with hr | hr
      · exact h1 hr
      · exact h2 hr
    · rcases hr with hr | hr
      · exact edgeWellFounded_no_self_edge hWF hUp (by rw [hUc, ← hr, hP])
      · exact edgeWellFounded_no_self_edge hWF he (by rw [hEp, ← hr, hC])
  · rcases spliceNode_rootChains_mem cdt node hR with ⟨-, h⟩ | h
    · exact h rfl
    · simp only [childrenOf, List.mem_map, List.mem_filter, CapDerivationEdge.isParentOf,
        decide_eq_true_eq] at h
      obtain ⟨e, ⟨he, hp⟩, hc⟩ := h
      exact edgeWellFounded_no_self_edge hWF he (hp.trans hc.symm)

/-- A tree each of whose edges maps, under `f`, onto an edge of a well-founded
tree is well-founded: a cycle would map onto a cycle. -/
theorem edgeWellFounded_of_map (cdt cdt' : CapDerivationTree) (f : SlotRef → SlotRef)
    (hWF : cdt.edgeWellFounded)
    (hMap : ∀ e' ∈ cdt'.edges, ∃ e ∈ cdt.edges, e.parent = f e'.parent ∧ e.child = f e'.child) :
    cdt'.edgeWellFounded := by
  intro node ⟨path, hLen, hHead, hLast, hEdges⟩
  refine hWF (f node) ⟨path.map f, by simpa using hLen, ?_, ?_, fun i hi => ?_⟩
  · rw [List.head?_map, hHead]; rfl
  · rw [List.getLast?_map, hLast]; rfl
  · have hi' : i + 1 < path.length := by simpa using hi
    obtain ⟨e', he', hp, hc⟩ := hEdges i hi'
    obtain ⟨e, he, hp', hc'⟩ := hMap e' he'
    exact ⟨e, he, by rw [hp', hp, List.getElem_map], by rw [hc', hc, List.getElem_map]⟩

/-- Renaming then renaming back is the identity on a slot other than `new`. -/
theorem renameSlot_back {old new r : SlotRef} (h : r ≠ new) :
    renameSlot new old (renameSlot old new r) = r := by
  unfold renameSlot
  by_cases ho : r = old
  · subst ho; simp
  · simp [ho, h]

/-- **Moving a node to a fresh slot keeps the tree acyclic**: the moved tree is
the old one with `old` renamed `new`. -/
theorem moveNode_edgeWellFounded (cdt : CapDerivationTree) (old new : SlotRef)
    (hWF : cdt.edgeWellFounded) (hFresh : ¬ cdt.mentions new) :
    (cdt.moveNode old new).edgeWellFounded :=
  edgeWellFounded_of_map cdt _ (renameSlot new old) hWF fun e' he' => by
    rw [moveNode_edges_eq] at he'
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp he'
    have ⟨hp, hc⟩ := not_edge_of_not_mentions hFresh e he
    exact ⟨e, he, (renameSlot_back hp).symm, (renameSlot_back hc).symm⟩

/-- The moved tree names `new` and, other than `old`, only slots the old tree
named. -/
theorem moveNode_mentions (cdt : CapDerivationTree) (old new : SlotRef) (ref : SlotRef)
    (h : (cdt.moveNode old new).mentions ref) : ref = new ∨ (ref ≠ old ∧ cdt.mentions ref) := by
  have key : ∀ x, renameSlot old new x = ref → (x = old → ref = new) ∧
      (x ≠ old → ref = x) := fun x hx => by
    unfold renameSlot at hx
    by_cases hxo : x = old
    · rw [if_pos hxo] at hx; exact ⟨fun _ => hx.symm, fun h => absurd hxo h⟩
    · rw [if_neg hxo] at hx; exact ⟨fun h => absurd h hxo, fun _ => hx.symm⟩
  have conclude : ∀ x, renameSlot old new x = ref → cdt.mentions x →
      ref = new ∨ (ref ≠ old ∧ cdt.mentions ref) := fun x hx hm => by
    by_cases hxo : x = old
    · exact .inl ((key x hx).1 hxo)
    · have := (key x hx).2 hxo; subst this
      by_cases hn : ref = new
      · exact .inl hn
      · exact .inr ⟨hxo, hm⟩
  rcases h with ⟨e', he', hr⟩ | hR
  · rw [moveNode_edges_eq] at he'
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp he'
    rcases hr with hr | hr
    · exact conclude e.parent hr (.inl ⟨e, he, .inl rfl⟩)
    · exact conclude e.child hr (.inl ⟨e, he, .inr rfl⟩)
  · rw [moveNode_rootChains] at hR
    obtain ⟨c', hc', hx'⟩ := List.mem_flatten.mp hR
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hc'
    obtain ⟨x, hx, hxr⟩ := List.mem_map.mp hx'
    exact conclude x hxr (.inr (List.mem_flatten.mpr ⟨c, hc, hx⟩))

-- ============================================================================
-- Y1-E: HashSet/List sync lemma for descendantsOf proofs
-- ============================================================================

/-- Y1-E: After folding `insert` over `newChildren`, the resulting HashSet
    contains exactly the elements of the original HashSet plus the new elements.
    Used to maintain the visited/acc sync invariant through BFS iterations. -/
private theorem foldl_insert_contains
    (visited : Std.HashSet SlotRef) (newChildren : List SlotRef) (x : SlotRef) :
    (newChildren.foldl (fun s c => s.insert c) visited).contains x = true ↔
    visited.contains x = true ∨ x ∈ newChildren := by
  induction newChildren generalizing visited with
  | nil => simp [List.foldl]
  | cons c cs ih =>
    simp only [List.foldl, List.mem_cons]
    rw [ih]
    constructor
    · rintro (h | h)
      · rw [HashSet_contains_insert_iff] at h
        rcases h with rfl | h
        · right; left; rfl
        · left; exact h
      · right; right; exact h
    · rintro (h | rfl | h)
      · left; rw [HashSet_contains_insert_iff]; right; exact h
      · left; exact HashSet_contains_insert_self _ _
      · right; exact h

/-- Y1-E: Sync invariant maintenance — if `visited` and `acc` are in sync,
    then extending both with `newChildren` preserves sync. -/
private theorem sync_after_extend
    (visited : Std.HashSet SlotRef) (acc newChildren : List SlotRef)
    (hSync : ∀ x, x ∈ acc ↔ visited.contains x = true) :
    ∀ x, x ∈ (acc ++ newChildren) ↔
    (newChildren.foldl (fun s c => s.insert c) visited).contains x = true := by
  intro x
  rw [List.mem_append, foldl_insert_contains]
  exact ⟨fun h => h.elim (fun ha => .inl ((hSync x).mp ha)) .inr,
         fun h => h.elim (fun hv => .inl ((hSync x).mpr hv)) .inr⟩

-- ============================================================================
-- T4-G: descendantsOf fuel sufficiency
-- ============================================================================

/-- T4-G: Reachability via childrenOf — inductive definition of nodes
reachable from a root through the CDT's child map. -/
inductive CdtChildReachable (cdt : CapDerivationTree) : SlotRef → SlotRef → Prop where
  | child : ∀ {root c}, c ∈ cdt.childrenOf root → CdtChildReachable cdt root c
  | trans : ∀ {root mid c}, CdtChildReachable cdt root mid →
      c ∈ cdt.childrenOf mid → CdtChildReachable cdt root c

/-- T4-G: Unfolding lemma for descendantsOf.go at a cons queue step. -/
private theorem descendantsOf_go_cons (cdt : CapDerivationTree) (fuel : Nat)
    (node : SlotRef) (rest : List SlotRef)
    (visited : Std.HashSet SlotRef) (acc : List SlotRef) :
    descendantsOf.go cdt (fuel + 1) (node :: rest) visited acc =
    descendantsOf.go cdt fuel
      (rest ++ (cdt.childrenOf node).filter (fun c => !visited.contains c))
      ((cdt.childrenOf node).filter (fun c => !visited.contains c) |>.foldl (fun s c => s.insert c) visited)
      (acc ++ (cdt.childrenOf node).filter (fun c => !visited.contains c)) := by
  rfl

/-- T4-G: Unfolding lemma for descendantsOf.go at an empty queue. -/
private theorem descendantsOf_go_nil (cdt : CapDerivationTree) (fuel : Nat)
    (visited : Std.HashSet SlotRef) (acc : List SlotRef) :
    descendantsOf.go cdt (fuel + 1) [] visited acc = acc := by
  rfl

/-- T4-G: BFS accumulator monotonicity — `descendantsOf.go` only adds to acc,
never removes. -/
theorem descendantsOf_go_acc_subset
    (cdt : CapDerivationTree) (fuel : Nat) (queue : List SlotRef)
    (visited : Std.HashSet SlotRef) (acc : List SlotRef) :
    ∀ x ∈ acc, x ∈ descendantsOf.go cdt fuel queue visited acc := by
  induction fuel generalizing queue visited acc with
  | zero => intro x hx; exact hx
  | succ n ih =>
    intro x hx
    cases queue with
    | nil => rw [descendantsOf_go_nil]; exact hx
    | cons node rest =>
      rw [descendantsOf_go_cons]
      exact ih (rest ++ (cdt.childrenOf node).filter (fun c => !visited.contains c))
        ((cdt.childrenOf node).filter (fun c => !visited.contains c) |>.foldl (fun s c => s.insert c) visited)
        (acc ++ (cdt.childrenOf node).filter (fun c => !visited.contains c))
        x (List.mem_append_left _ hx)

/-- T4-G: Direct children of root appear in descendantsOf result when
fuel ≥ 1 and root is in the BFS queue. -/
theorem descendantsOf_go_children_found
    (cdt : CapDerivationTree) (fuel : Nat) (rest : List SlotRef)
    (visited : Std.HashSet SlotRef) (acc : List SlotRef)
    (root : SlotRef) (c : SlotRef)
    (hChild : c ∈ cdt.childrenOf root)
    (hNotInAcc : c ∉ acc)
    (hSync : ∀ x, x ∈ acc ↔ visited.contains x = true) :
    c ∈ descendantsOf.go cdt (fuel + 1) (root :: rest) visited acc := by
  rw [descendantsOf_go_cons]
  have hNotVis : visited.contains c = false := by
    cases h : visited.contains c
    · rfl
    · exact absurd ((hSync c).mpr h) hNotInAcc
  have hInNew : c ∈ (cdt.childrenOf root).filter (fun x => !visited.contains x) := by
    simp only [List.mem_filter]
    exact ⟨hChild, by simp [hNotVis]⟩
  have hInNewAcc : c ∈ acc ++ (cdt.childrenOf root).filter (fun x => !visited.contains x) :=
    List.mem_append_right _ hInNew
  exact descendantsOf_go_acc_subset cdt fuel _ _ _ c hInNewAcc

/-- T4-G: Direct children of the root are in the descendantsOf result,
provided the CDT has at least one edge (ensuring fuel ≥ 1). -/
theorem descendantsOf_children_subset
    (cdt : CapDerivationTree) (root : SlotRef)
    (c : SlotRef) (hChild : c ∈ cdt.childrenOf root)
    (hEdges : cdt.edges.length > 0) :
    c ∈ cdt.descendantsOf root := by
  simp only [descendantsOf]
  have hB := cdt.edges_length_le
  obtain ⟨n, hn⟩ : ∃ n, cdt.edgeBound = n + 1 := ⟨cdt.edgeBound - 1, by omega⟩
  rw [hn]
  exact descendantsOf_go_children_found cdt n [] {} [] root c hChild
    (fun h => nomatch h) (fun x => Iff.intro (fun h => nomatch h) (fun h => by simp at h))

/-- T4-G: BFS monotonicity — adding more fuel does not lose results.
If a node is found with fuel `n`, it is also found with fuel `n + k`. -/
theorem descendantsOf_go_fuel_mono
    (cdt : CapDerivationTree) (n : Nat) (queue : List SlotRef)
    (visited : Std.HashSet SlotRef) (acc : List SlotRef)
    (x : SlotRef) (hIn : x ∈ descendantsOf.go cdt n queue visited acc) :
    ∀ k, x ∈ descendantsOf.go cdt (n + k) queue visited acc := by
  induction n generalizing queue visited acc with
  | zero =>
    simp only [descendantsOf.go] at hIn
    intro k
    have : 0 + k = k := Nat.zero_add k
    rw [this]; exact descendantsOf_go_acc_subset cdt k queue visited acc x hIn
  | succ m ih =>
    intro k
    have hRw : m + 1 + k = (m + k) + 1 := by omega
    cases queue with
    | nil =>
      rw [descendantsOf_go_nil] at hIn
      rw [hRw, descendantsOf_go_nil]; exact hIn
    | cons node rest =>
      rw [descendantsOf_go_cons] at hIn
      rw [hRw, descendantsOf_go_cons]
      exact ih _ _ _ hIn k

/-- T4-G: Core BFS property — if `node` is at the head of the queue,
then all children of `node` end up in the BFS result (go processes
the head and adds its unvisited children to both queue and acc).
Requires visited/acc sync invariant: `∀ x, x ∈ acc ↔ visited.contains x`. -/
theorem descendantsOf_go_head_children_found
    (cdt : CapDerivationTree) (fuel : Nat) (rest : List SlotRef)
    (visited : Std.HashSet SlotRef) (acc : List SlotRef)
    (node : SlotRef) (c : SlotRef)
    (hChild : c ∈ cdt.childrenOf node)
    (hSync : ∀ x, x ∈ acc ↔ visited.contains x = true) :
    c ∈ descendantsOf.go cdt (fuel + 1) (node :: rest) visited acc := by
  rw [descendantsOf_go_cons]
  by_cases hcAcc : c ∈ acc
  · exact descendantsOf_go_acc_subset cdt fuel _ _ _ c (List.mem_append_left _ hcAcc)
  · have hNotVis : visited.contains c = false := by
      cases h : visited.contains c
      · rfl
      · exact absurd ((hSync c).mpr h) hcAcc
    have hcNew : c ∈ (cdt.childrenOf node).filter (fun x => !visited.contains x) := by
      simp only [List.mem_filter]
      exact ⟨hChild, by simp [hNotVis]⟩
    exact descendantsOf_go_acc_subset cdt fuel _ _ _ c (List.mem_append_right _ hcNew)

/-- T4-G: Fuel bound for `descendantsOf` — with sufficient fuel, all
direct children of the root are discovered. Combined with
`descendantsOf_go_fuel_mono`, this establishes that increasing fuel
never loses previously discovered nodes, providing the foundation
for the fuel sufficiency argument. -/
theorem descendantsOf_fuel_bound
    (cdt : CapDerivationTree) (root : SlotRef)
    (c : SlotRef) (hChild : c ∈ cdt.childrenOf root)
    (fuel : Nat) (hFuel : fuel ≥ 1) :
    c ∈ descendantsOf.go cdt fuel [root] {} [] := by
  obtain ⟨k, hk⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
  rw [hk]
  exact descendantsOf_go_children_found cdt k [] {} [] root c hChild
    (fun h => nomatch h) (fun x => Iff.intro (fun h => nomatch h) (fun h => by simp at h))

/-- T4-G (M-CAP-2): `descendantsOf` with the default fuel (`edges.length`)
discovers all direct children of the root, provided the CDT has at least one
edge. Combined with `descendantsOf_go_fuel_mono` (fuel monotonicity) and
`descendantsOf_go_acc_subset` (accumulator monotonicity), this provides the
key ingredient for revocation completeness: every direct child of a revoked
capability is included in the revocation set.

**Scope note:** This theorem proves discovery of *direct* children (depth 1).
The full multi-level fuel sufficiency (all transitive descendants via
`CdtChildReachable` found with fuel = `edges.length`) requires a CDT acyclicity
witness and an edge-counting argument showing that the BFS processes all
non-leaf queue entries.  The U4-N infrastructure (`go_queue_pos_children_found`,
`go_mem_children_found`) establishes the positional queue lemma: if a node is
anywhere in the BFS queue and fuel exceeds its position, every child of that
node appears in the result.  Combined with the existing BFS monotonicity
lemmas, this reduces the transitive closure to a queue-exhaustion argument
on acyclic CDTs.  The complete transitive closure proof (connecting
`CdtChildReachable` depth to BFS fuel bounds) is deferred to the
hardware-binding phase where concrete CDT size bounds are available.

AI6-D (M-21): See TPI-DOC for full fuel sufficiency formal bridge
(recorded as a post-1.0 hardening candidate; registered in
`docs/REGISTERED_DEBT.md`, Registered debt index, C.1).
`edgeWellFounded` (Model/Object/Structures.lean:1058)
provides the inductive well-foundedness foundation: CDT edges form a
well-founded relation on `SlotRef`, ensuring termination of any
traversal. The depth-1 proof here is the base case; the inductive step
connecting `CdtChildReachable` transitivity to BFS fuel bounds requires
composing `edgeWellFounded` with the U4-N positional queue lemmas. -/
theorem descendantsOf_fuel_sufficiency
    (cdt : CapDerivationTree) (root : SlotRef)
    (c : SlotRef) (hChild : c ∈ cdt.childrenOf root)
    (hEdges : cdt.edges.length > 0) :
    c ∈ cdt.descendantsOf root :=
  descendantsOf_children_subset cdt root c hChild hEdges

-- ============================================================================
-- U4-N: descendantsOf transitive closure infrastructure
-- ============================================================================

/-- U4-N: Positional queue lemma — if `mid` sits behind `before` entries in the
    BFS queue and the fuel exceeds `before.length`, then every child of `mid`
    appears in the BFS result.  Proof by induction on `before`: the base case
    delegates to `descendantsOf_go_head_children_found`; the step unfolds one
    BFS iteration via `descendantsOf_go_cons` and reassociates the queue. -/
private theorem descendantsOf_go_queue_pos_children_found
    (cdt : CapDerivationTree) (fuel : Nat) (before after : List SlotRef)
    (visited : Std.HashSet SlotRef) (acc : List SlotRef)
    (mid c : SlotRef) (hChild : c ∈ cdt.childrenOf mid)
    (hFuel : fuel > before.length)
    (hSync : ∀ x, x ∈ acc ↔ visited.contains x = true) :
    c ∈ descendantsOf.go cdt fuel (before ++ mid :: after) visited acc := by
  induction before generalizing fuel after visited acc with
  | nil =>
    simp only [List.nil_append]
    obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
    exact descendantsOf_go_head_children_found cdt k after visited acc mid c hChild hSync
  | cons node before' ih =>
    obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
    show c ∈ descendantsOf.go cdt (k + 1) ((node :: before') ++ mid :: after) visited acc
    rw [List.cons_append, descendantsOf_go_cons]
    let newChildren := (cdt.childrenOf node).filter (fun c => !visited.contains c)
    let visited' := newChildren.foldl (fun s c => s.insert c) visited
    have hReassoc : (before' ++ mid :: after) ++ newChildren =
        before' ++ mid :: (after ++ newChildren) := by
      rw [List.append_assoc]; rfl
    rw [hReassoc]
    exact ih k (after ++ newChildren) visited' (acc ++ newChildren)
      (by simp only [List.length_cons] at hFuel; omega)
      (sync_after_extend visited acc newChildren hSync)

/-- U4-N helper: decompose list membership into a prefix/suffix split. -/
private theorem list_mem_split {a : α} {l : List α} (h : a ∈ l) :
    ∃ s t, l = s ++ a :: t := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    simp only [List.mem_cons] at h
    rcases h with rfl | h'
    · exact ⟨[], xs, rfl⟩
    · obtain ⟨s, t, rfl⟩ := ih h'
      exact ⟨x :: s, t, rfl⟩

/-- U4-N: Queue membership variant — if `mid` is anywhere in the BFS queue
    and the fuel is at least the queue length, then every child of `mid`
    appears in the BFS result. Decomposes queue membership into a positional
    split and delegates to `descendantsOf_go_queue_pos_children_found`. -/
theorem descendantsOf_go_mem_children_found
    (cdt : CapDerivationTree) (fuel : Nat) (queue : List SlotRef)
    (visited : Std.HashSet SlotRef) (acc : List SlotRef)
    (mid c : SlotRef)
    (hMid : mid ∈ queue) (hChild : c ∈ cdt.childrenOf mid)
    (hFuel : fuel ≥ queue.length)
    (hSync : ∀ x, x ∈ acc ↔ visited.contains x = true) :
    c ∈ descendantsOf.go cdt fuel queue visited acc := by
  obtain ⟨before, after, rfl⟩ := list_mem_split hMid
  apply descendantsOf_go_queue_pos_children_found cdt fuel before after visited acc mid c hChild
  · simp only [List.length_append, List.length_cons] at hFuel; omega
  · exact hSync

-- ============================================================================
-- AG8-E: childrenOf → edge bridge + CdtChildReachable → cdtReachable
-- ============================================================================

/-- AG8-E: a child `childrenOf` reads is the child of one of the tree's edges. -/
theorem childrenOf_to_edge (cdt : CapDerivationTree) (parent child : SlotRef)
    (hChild : child ∈ cdt.childrenOf parent) :
    ∃ e ∈ cdt.edges, e.parent = parent ∧ e.child = child := by
  simp only [childrenOf, List.mem_map, List.mem_filter, CapDerivationEdge.isParentOf,
    decide_eq_true_eq] at hChild
  obtain ⟨e, ⟨he, hp⟩, hc⟩ := hChild
  exact ⟨e, he, hp, hc⟩

/-- A child of one of the tree's edges is one `childrenOf` reads. -/
theorem mem_childrenOf (cdt : CapDerivationTree) (parent child : SlotRef) :
    child ∈ cdt.childrenOf parent ↔ ∃ e ∈ cdt.edges, e.parent = parent ∧ e.child = child := by
  refine ⟨childrenOf_to_edge cdt parent child, fun ⟨e, he, hp, hc⟩ => ?_⟩
  simp only [childrenOf, List.mem_map, List.mem_filter, CapDerivationEdge.isParentOf,
    decide_eq_true_eq]
  exact ⟨e, ⟨he, hp⟩, hc⟩

/-- AG8-E: `CdtChildReachable` (inductive reachability
through `childrenOf`) implies `cdtReachable` (path-based reachability through
`edges`). This bridges the BFS-level reachability definition with the
proof-anchor edge list, enabling composition with `edgeWellFounded`. -/
theorem CdtChildReachable_implies_cdtReachable (cdt : CapDerivationTree)
    {root n : SlotRef} (hReach : CdtChildReachable cdt root n) :
    cdt.cdtReachable root n := by
  induction hReach with
  | child hChild =>
    obtain ⟨e, heMem, heP, heC⟩ := childrenOf_to_edge cdt _ _ hChild
    refine ⟨[_, _], ?_, rfl, rfl, fun i hi => ?_⟩
    · show (2 : Nat) > 1; omega
    · simp only [List.length_cons, List.length_nil] at hi
      have : i = 0 := by omega
      subst this; exact ⟨e, heMem, heP, heC⟩
  | trans _hReach hChild ih =>
    rename_i mid c
    obtain ⟨path, hLen, hHead, hLast, hEdges⟩ := ih
    obtain ⟨e, heMem, heP, heC⟩ := childrenOf_to_edge cdt _ _ hChild
    refine ⟨path ++ [c], ?_, ?_, ?_, ?_⟩
    · -- length > 1
      simp [List.length_append]; omega
    · -- head? = some root
      cases path with
      | nil => simp at hLen
      | cons a rest => simp [List.head?_cons] at hHead ⊢; exact hHead
    · -- getLast? = some c
      exact List.getLast?_concat
    · -- consecutive edges
      intro i hi
      have hAppLen : (path ++ [c]).length = path.length + 1 := List.length_append
      rw [hAppLen] at hi
      by_cases hlt : i + 1 < path.length
      · -- Index within original path
        have h1 : (path ++ [c])[i] = path[i] :=
          List.getElem_append_left (h := by omega)
        have h2 : (path ++ [c])[i + 1] = path[i + 1] :=
          List.getElem_append_left (h := hlt)
        rw [h1, h2]; exact hEdges i hlt
      · -- New edge at boundary: i + 1 = path.length
        have hBound : i + 1 = path.length := by omega
        -- path[i] = mid (last element of original path)
        have hIdx : path[i]? = some mid := by
          rw [show i = path.length - 1 from by omega, ← List.getLast?_eq_getElem?]
          exact hLast
        have hPiVal := (List.getElem?_eq_some_iff.mp hIdx).2
        have hPi : (path ++ [c])[i] = path[i] :=
          List.getElem_append_left (h := by omega)
        -- (path ++ [c])[i + 1] = c
        have hPi1 : (path ++ [c])[i + 1]? = some c := by
          rw [List.getElem?_append_right (by omega)]
          simp [show i + 1 - path.length = 0 from by omega]
        have hPi1Val := (List.getElem?_eq_some_iff.mp hPi1).2
        rw [hPi, hPiVal, hPi1Val]
        exact ⟨e, heMem, heP, heC⟩

end CapDerivationTree

/-- WS-G5: `DecidableEq` removed from `KernelObject` because `CNode.slots` is
`RHTable Slot Capability` which does not have a `DecidableEq` instance.
`Repr` is retained for trace output. `BEq` is provided manually via entry-wise
comparison for runtime test assertions.

**AK7-K (F-L10 / LOW):** The missing `DecidableEq KernelObject` is by
design — deriving it would cascade into deriving `DecidableEq` on
`RHTable`, whose structural equality on `slots : Array (Option
RHEntry)` would succeed but hide hash-layout non-determinism (two
tables with the same logical contents but different probe sequences
could compare unequal). The manual `BEq KernelObject` below is a
pragmatic runtime-testing alias; proof-critical paths should use
structural equality on per-variant projections (`TCB.ext`, etc.). -/
inductive KernelObject where
  | tcb (t : TCB)
  | endpoint (e : Endpoint)
  | notification (n : Notification)
  | cnode (c : CNode)
  | vspaceRoot (v : VSpaceRoot)
  | untyped (u : UntypedObject)
  | schedContext (sc : SeLe4n.Kernel.SchedContext)
  | reply (r : SeLe4n.Kernel.Reply)
  /-- **WS-BP BP7.1**: a page of physical memory; see `FrameObject`. -/
  | frame (f : FrameObject)
  /-- **WS-BP BP7.1 (`v0.36.12`)**: an intermediate translation table; see
      `PageTableObject`. -/
  | pageTable (p : PageTableObject)
  deriving Repr

/-- WS-G5: Manual `BEq` for `KernelObject` dispatching to constituent `BEq`
instances. CNode comparison uses the entry-wise `BEq CNode` instance above. -/
instance : BEq KernelObject where
  beq
    | .tcb a, .tcb b => a == b
    | .endpoint a, .endpoint b => a == b
    | .notification a, .notification b => a == b
    | .cnode a, .cnode b => a == b
    | .vspaceRoot a, .vspaceRoot b => a == b
    | .untyped a, .untyped b => a == b
    | .schedContext a, .schedContext b => a == b
    | .reply a, .reply b => a == b
    | .frame a, .frame b => a == b
    | .pageTable a, .pageTable b => a == b
    | _, _ => false

inductive KernelObjectType where
  | tcb
  | endpoint
  | notification
  | cnode
  | vspaceRoot
  | untyped
  | schedContext
  | reply
  | frame
  | pageTable
  deriving Repr, DecidableEq

namespace KernelObjectType

/-- R7-E/L-10: Numeric encoding of kernel object types, matching the syscall ABI.
    These tag values must be stable across ABI versions. -/
def toNat : KernelObjectType → Nat
  | .tcb => 0
  | .endpoint => 1
  | .notification => 2
  | .cnode => 3
  | .vspaceRoot => 4
  | .untyped => 5
  | .schedContext => 6
  | .reply => 7
  | .frame => 8
  | .pageTable => 9

/-- R7-E/L-10: Decode a numeric type tag to `KernelObjectType`.
    Returns `none` for unrecognized tags, ensuring only valid types are accepted. -/
def ofNat? : Nat → Option KernelObjectType
  | 0 => some .tcb
  | 1 => some .endpoint
  | 2 => some .notification
  | 3 => some .cnode
  | 4 => some .vspaceRoot
  | 5 => some .untyped
  | 6 => some .schedContext
  | 7 => some .reply
  | 8 => some .frame
  | 9 => some .pageTable
  | _ + 10 => none

/-- R7-E/L-10: `ofNat?` is a left inverse of `toNat`. -/
theorem ofNat_toNat (t : KernelObjectType) : ofNat? t.toNat = some t := by
  cases t <;> rfl

/-- R7-E/L-10: `toNat` is injective. -/
theorem toNat_injective {a b : KernelObjectType} (h : a.toNat = b.toNat) : a = b := by
  cases a <;> cases b <;> simp [toNat] at h <;> rfl

/-- **WS-BP BP7.1: the kinds a DEVICE untyped may back.**

A device untyped names MMIO, and a store to it is a command to a device, not a
write to memory.  So it backs exactly what hands that MMIO on — a child untyped,
and a frame, which is how a driver is given its registers — and nothing the
kernel itself reads or writes as data.  That is seL4's rule (`Untyped_Retype`
on a device untyped yields frames and untypeds only).

A VSpace root and a page table are refused: a translation table is memory the
kernel owns and walks, and it must be RAM, since a table walk reading a device
would read a register.

Enumerated constructor by constructor, with no wildcard: a kind a wildcard
answered would be admitted to MMIO by default. -/
def deviceBackable : KernelObjectType → Bool
  | .tcb => false
  | .endpoint => false
  | .notification => false
  | .cnode => false
  | .vspaceRoot => false
  | .untyped => true
  | .schedContext => false
  | .reply => false
  | .frame => true
  -- WS-BP BP7.1 (`v0.36.12`): a table walk reading a device would read a register.
  | .pageTable => false

end KernelObjectType

namespace KernelObject

def objectType : KernelObject → KernelObjectType
  | .tcb _ => .tcb
  | .endpoint _ => .endpoint
  | .notification _ => .notification
  | .cnode _ => .cnode
  | .vspaceRoot _ => .vspaceRoot
  | .untyped _ => .untyped
  | .schedContext _ => .schedContext
  | .reply _ => .reply
  | .frame _ => .frame
  | .pageTable _ => .pageTable

end KernelObject

namespace KernelObjectType

/-- WS-SM SM6.D, WS-BP BP7.1: the seLe4n `KernelObjectType` enumeration has
**exactly 10 variants** — the first-class `reply` object (SM6.D), the
`frame` (WS-BP BP7.1), which retires SM3.A.8's "Page is N/A" decision: while
`.vspaceMap` took a raw physical address, a page needed no object; once
physical memory is authority it does, and the lock hierarchy's `page` kind
(level 9) is that object's lock — and (`v0.36.12`) the `pageTable`, an
intermediate translation table, which is a page too and takes the same lock
kind.

This witness was written to force exactly that revisit: a kind added without
updating it fails here.  The `_count` form pins the cardinality; the
`variants_total` form enumerates each variant explicitly so a renamed-variant
refactor fails the surface check. -/
theorem variants_count_exactly_ten :
    let variants : List KernelObjectType :=
      [.tcb, .endpoint, .notification, .cnode, .vspaceRoot, .untyped, .schedContext, .reply,
        .frame, .pageTable]
    variants.length = 10 ∧ variants.Nodup := by
  refine ⟨rfl, ?_⟩
  decide

/- **Tombstone (WS-BP BP7.1)**: `variants_count_exactly_eight` and
`variants_count_exactly_nine` are `variants_count_exactly_ten` above — the
`frame` kind is the ninth and (`v0.36.12`) the `pageTable` kind the tenth. -/

/-- WS-SM SM6.D, WS-BP BP7.1: every `KernelObjectType` value is one of the 10
enumerated variants. -/
theorem variants_total (k : KernelObjectType) :
    k = .tcb ∨ k = .endpoint ∨ k = .notification ∨ k = .cnode ∨
    k = .vspaceRoot ∨ k = .untyped ∨ k = .schedContext ∨ k = .reply ∨ k = .frame ∨
    k = .pageTable := by
  cases k <;> simp

end KernelObjectType

namespace KernelObject

/-- T5-C (M-NEW-5): Object well-formedness predicate parameterized by the object store.

For each object kind, this checks structural validity constraints that must hold
at construction time:
- **TCB**: `cspaceRoot` and `vspaceRoot` must reference existing objects in the store.
- **CNode**: guard value must be bounded by guard width (`guardBounded` from T2-J).
- **Endpoint**: always well-formed (no structural constraints beyond queue invariants,
  which are tracked separately by `ipcInvariant`).
- **Notification**: always well-formed (waiter validity tracked by `crossSubsystemInvariant`).
- **VSpaceRoot**: always well-formed (ASID validity is a platform-level concern,
  tracked by `asidTableInvariant`).
- **Untyped**: always well-formed (size constraints are enforced by the allocator).
- **SchedContext**: must start with **no bound thread** (`v0.35.184`, see below).
- **Reply**: must start inert (WS-SM SM6.D, see below).
- **Frame**: page-aligned (WS-BP BP7.1, `FrameObject.wellFormed`). -/
def wellFormed (obj : KernelObject)
    (objects : SeLe4n.Kernel.RobinHood.RHTable SeLe4n.ObjId KernelObject) : Prop :=
  match obj with
  | .tcb t =>
      objects[t.cspaceRoot]? ≠ none ∧
      objects[t.vspaceRoot]? ≠ none
  | .cnode c => c.guardBounded
  | .endpoint _ => True
  | .notification _ => True
  | .vspaceRoot _ => True
  | .untyped _ => True
  -- **`v0.35.184` (register row 63)**: a created SchedContext must start with
  -- **no bound thread** -- the `Reply` clause below, one field over, for the same
  -- reason.  A scheduling context that claims a thread which does not name it
  -- back is exactly what `schedContextBindingConsistent` (Z4-O) forbids.  The
  -- carve's `.schedContext` object is `SchedContext.empty`, whose `boundThread`
  -- is at its `none` default.
  | .schedContext sc => sc.boundThread = none
  -- WS-SM SM6.D (PR #822 review): a created Reply must start INERT — no caller
  -- and no reply-stack link in either direction — mirroring the boot-safe Reply
  -- requirement, so no installed Reply bypasses the `linkCallerReply` /
  -- `replyCallerLinkage` setup path and seeds a stale/in-use link.
  | .reply r => r.caller = none ∧ r.prev = none ∧ r.next = none
  | .frame f => f.wellFormed
  | .pageTable p => p.wellFormed

/-- **`v0.35.187`: an object's own embedded identity IS the key it is stored at.**

Three kernel objects carry their own id in a field — a TCB's `tid`, a
SchedContext's `scId`, a Reply's `replyId` — and the object store is keyed by
`ObjId`, so the two can disagree.  `PlatformConfig.wellFormed`'s
`embeddedIdentitiesMatchSlots` has refused that at **boot** since PR #889 review
round 8, and its own docstring states the hazard in terms: *a SchedContext at
slot 9 carrying `scId = 12` would have its budget replenished on whatever object
12 is*.

At the **runtime** the one path that installs such an object is the untyped
carve, which builds each of the three with the child id it is stored at
(`CarveRequest.object_embeddedIdentityMatches`).

The match has **no** wildcard: a kernel object that starts carrying its own id
must be classified here, rather than silently answering `true`.  The six that
carry none answer `true` because the question does not arise for them, which is
a different fact from "not checked". -/
def embeddedIdentityMatches (obj : KernelObject) (key : SeLe4n.ObjId) : Bool :=
  match obj with
  | .tcb t => t.tid.toObjId == key
  | .schedContext sc => sc.scId.toObjId == key
  | .reply r => r.replyId.toObjId == key
  | .endpoint _ => true
  | .notification _ => true
  | .cnode _ => true
  | .vspaceRoot _ => true
  | .untyped _ => true
  | .frame _ => true
  | .pageTable _ => true

/-- T5-C: `wellFormed` is decidable for all object kinds, enabling runtime validation. -/
instance (obj : KernelObject)
    (objects : SeLe4n.Kernel.RobinHood.RHTable SeLe4n.ObjId KernelObject) :
    Decidable (obj.wellFormed objects) := by
  unfold wellFormed
  match obj with
  | .tcb _ => exact instDecidableAnd
  | .cnode _ => exact inferInstance
  | .reply _ => exact inferInstance
  | .schedContext _ => exact inferInstance
  | .frame _ => exact inferInstance
  | .pageTable _ => exact inferInstance
  | .endpoint _ | .notification _ | .vspaceRoot _ | .untyped _ =>
    exact instDecidableTrue

end KernelObject

-- ============================================================================
-- Z1-N: ThreadSchedulingParams — RETIRED at `v0.35.134` (tombstone only)
-- ============================================================================

-- **`threadSchedulingParams` stood here and is DELETED at `v0.35.134`** (PR #897
-- review, against `v0.35.133`).  It was the Z1-N "migration bridge between
-- monolithic TCB scheduling and first-class SchedContext objects" -- a fourth
-- reading of *what are a thread's effective scheduling parameters*, beside
-- `resolveEffectivePrioDeadline`, `effectiveSchedParams` and
-- `effectiveBucketPriority` -- and its `.bound` / `.donated` arm returned
-- `sc.priority`, which `v0.35.133` made wrong: with one home for a base
-- priority, a reader that takes the band from the reservation schedules at a
-- stale mirror.  The review is right that it is reachable from the root-imported
-- model API.
--
-- **Deleted rather than collapsed, on measurement**: it had *zero* consumers
-- anywhere in the tree -- not a call, not a proof, not a test -- so the
-- collapse would have produced a fourth reading nobody asks, which is this
-- project's own *a retention justification that names a consumer which does not
-- exist* shape.  The migration its docstring named is over: `effectiveSchedParams`
-- (`Scheduler/Operations/Selection.lean`) is the canonical call-side API and is
-- the reading the frozen surface is now pinned against
-- (`effectiveSchedParams_fst_eq_boostedPriority`).  A budget component, which is
-- the one thing it answered that `effectiveSchedParams` does not, is read
-- directly off `SchedContext.budgetRemaining` by every live budget predicate.
-- A Tier 3 negative refuses its return.

-- ============================================================================
-- AG8-E: descendantsOf Fuel Sufficiency (F-S05)
-- ============================================================================

/-- AG8-E: Maximum CDT depth for RPi5 hardware binding.

On ARM64 with 4-level page tables, the maximum object derivation chain depth
is bounded by the maximum number of kernel objects. Each CDT edge connects
two distinct objects, so the longest acyclic path has at most `maxObjects`
edges. Since `descendantsOf` uses `cdt.edges.length` as fuel and the CDT
is acyclic (no node is visited twice), `edges.length` fuel is always
sufficient for complete BFS traversal.

Value: matches `maxObjects` (65536) from `Model/State.lean`. -/
def maxCdtDepth : Nat := 65536

/-- AG8-E: Acyclicity transfer — under `edgeWellFounded`,
no CDT node can reach itself via `CdtChildReachable`. This bridges the
inductive reachability definition (used by BFS infrastructure) with the
path-based acyclicity definition (used by `edgeWellFounded`).

**Proof strategy**: Suppose `CdtChildReachable cdt root root`. By
`CdtChildReachable_implies_cdtReachable`, there exists a path in `cdt.edges`
from `root` back to `root` (length ≥ 2). But `edgeWellFounded` prohibits
exactly such paths. Contradiction.

This is the key acyclicity property needed for BFS fuel sufficiency: in an
acyclic CDT, BFS processes each node at most once (via the visited set),
ensuring that `edges.length` fuel suffices for complete traversal. -/
theorem edgeWellFounded_no_self_reachable (cdt : CapDerivationTree)
    (hAcyclic : cdt.edgeWellFounded) :
    ∀ root, ¬ CapDerivationTree.CdtChildReachable cdt root root := by
  intro root hReach
  have hPath := cdt.CdtChildReachable_implies_cdtReachable hReach
  exact hAcyclic root hPath

/-- AG8-E: `addEdge` increases `edges.length` by exactly 1. This is the
key building block for maintaining the CDT depth bound `edges.length ≤ maxCdtDepth`
through operations: each `addEdge` call (invoked by `retypeFromUntyped`) adds
exactly one edge, so the bound is maintained as long as the pre-operation
count is strictly less than `maxCdtDepth`.

Combined with `addEdge_preserves_edgeWellFounded_fresh` (acyclicity
preservation), this provides the full maintenance argument for CDT depth bounds. -/
theorem addEdge_edges_length (cdt : CapDerivationTree)
    (parent child : SlotRef) (op : DerivationOp) :
    (cdt.addEdge parent child op).edges.length = cdt.edges.length + 1 := by
  simp [CapDerivationTree.addEdge_edges, List.length_cons]

/-- AG8-E: CDT depth bound preservation through `addEdge`. If the CDT has
strictly fewer than `maxCdtDepth` edges before adding, it has at most
`maxCdtDepth` edges after. This is the per-operation maintenance lemma
for the system-wide CDT depth invariant.

**Proof**: `addEdge` increments `edges.length` by 1 (via `addEdge_edges_length`).
If the pre-count is `< maxCdtDepth`, the post-count is `≤ maxCdtDepth`. -/
theorem addEdge_maintains_depth_bound (cdt : CapDerivationTree)
    (parent child : SlotRef) (op : DerivationOp)
    (hBound : cdt.edges.length < maxCdtDepth) :
    (cdt.addEdge parent child op).edges.length ≤ maxCdtDepth := by
  rw [addEdge_edges_length]; omega

end SeLe4n.Model
