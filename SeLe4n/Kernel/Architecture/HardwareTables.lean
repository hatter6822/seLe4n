-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Model.State
import SeLe4n.Kernel.Architecture.PageTable
import SeLe4n.Kernel.Architecture.PhysicalWrite

/-!
# WS-BP BP7.2 — an address space's translation tables, as the walker reads them

The model holds an address space as a `VSpaceRoot`: its top-level table page
(`tableBase`), the intermediate tables installed under it (`tables`, one
`PageTableSlot` per `(level, index)`), and its mappings.  The ARMv8 walker holds
none of that — it reads **descriptors** out of **table pages**.  This module is
the function between the two: for an address space and a virtual address, which
entry of which page the walker reads at each level, and what that entry must
hold.  A transition that changes a mapping or a slot records the one store that
makes memory agree (`PhysicalWrite.storeDescriptor`), computed here from the
committed state, and the syscall seam performs it.

## The kernel window

The kernel runs identity-mapped in `TTBR0_EL1`'s half of the address space, so
an address space the kernel installs there must still translate the kernel.  The
top-level entry `0` — virtual addresses `[0, 2^39)` — is therefore the
**kernel's**: the HAL writes it with the kernel's own level-1 table descriptor
(EL1-only, never executable at EL0) when it installs the address space, and no
user mapping or table may use it (`SeLe4n.VAddr.userWindowBase`).  Every other top-level
entry is the address space's.

## Descriptor encoding

A user page is a level-3 page descriptor (`PageTable.descriptorToUInt64`'s
`.page` shape) with **nG** set — the translation is tagged with the address
space's ASID, so it is never shared with another — and **PXN** set, so the
kernel never executes a thread's page.  A cacheable page is Normal
write-back (MAIR index 0); a non-cacheable one is **Device-nGnRnE** (index 1),
never executable, since the memory a thread may map uncached is device memory
and only device memory: `frameMappingAdmissible` gives every mapping its
frame's memory type (`frameMappingAdmissible_cacheable_iff_ram`).  So a page of
RAM is mapped Normal write-back wherever it is mapped, which is the type the
kernel's own identity map gives it, and no thread holds the mismatched-attribute
alias (ARM ARM B2.8) that would let an uncached read see DRAM behind the
kernel's cached writes — the carve's zeroing among them.  (Until the WS-BP
post-landing audit, `v0.36.32`, this sentence was a claim `frameMappingAdmissible`
did not enforce: a RAM frame could be mapped uncached.)
-/

namespace SeLe4n.Kernel.Architecture

open SeLe4n.Model

/-- The address of entry `index` of the table page at `base`. -/
def tableEntryAddress (base : SeLe4n.PAddr) (index : Nat) : SeLe4n.PAddr :=
  SeLe4n.PAddr.ofNat (base.toNat + (index % 512) * 8)

/-- **The table page at `(level, index)` of `root`** — level `0` is the root's
own page, a deeper level the page of the table its slot holds. -/
def tablePageAt? (st : SystemState) (root : VSpaceRoot) (level index : Nat) :
    Option SeLe4n.PAddr :=
  if level = 0 then root.tableBase
  else (root.slotAt? level index).bind fun s => (st.getPageTable? s.table).map (·.base)

/-- A table descriptor naming the table page at `base`. -/
def tableDescriptorValue (base : SeLe4n.PAddr) : UInt64 :=
  descriptorToUInt64 (.table base)

/-- The hardware attributes of a thread's page (see the module docstring). -/
def userPageAttributes (perms : PagePermissions) : PageAttributes :=
  { attrIndex  := if perms.cacheable then ⟨0, by omega⟩ else ⟨1, by omega⟩
    ap         := if perms.write then (if perms.user && perms.read then .rwAll else .rwEL1)
                  else (if perms.user && perms.read then .roAll else .roEL1)
    sh         := .innerShareable
    af         := true
    pxn        := true
    uxn        := !(perms.execute && perms.user && perms.read && perms.cacheable)
    contiguous := false
    dirty      := false }

/-- The nG bit (ARM ARM D8.3): the translation is tagged with the ASID. -/
def notGlobalBit : UInt64 := (1 : UInt64) <<< 11

/-- **The level-3 descriptor of a thread's page.** -/
def userPageDescriptorValue (paddr : SeLe4n.PAddr) (perms : PagePermissions) : UInt64 :=
  descriptorToUInt64 (.page paddr (userPageAttributes perms)) ||| notGlobalBit

/-- **The store that makes memory agree with `root`'s mapping at `vaddr`**: the
level-3 entry the walker reads for `vaddr`, holding the page's descriptor when
`root` maps `vaddr` and an invalid descriptor when it does not.  `none` when the
walk to `vaddr` has no level-3 table — there is no entry the walker could read,
so there is nothing to write. -/
def mappingStore? (st : SystemState) (root : VSpaceRoot) (vaddr : SeLe4n.VAddr) :
    Option PhysicalWrite :=
  if root.tableBase.isNone then none
  else (tablePageAt? st root 3 (PageTableSlot.indexOf 3 vaddr)).map fun l3 =>
    .storeDescriptor (tableEntryAddress l3 (vaddr.toNat >>> 12))
      (match root.lookup vaddr with
       | some (paddr, perms) => userPageDescriptorValue paddr perms
       | none => 0)

/-- **The store that makes memory agree with `root`'s slot `(level, index)`**:
the entry of the parent table page that names the level-`level` table, holding
its table descriptor when the slot is present and an invalid descriptor when it
is not.  `none` when the parent has no page. -/
def slotStore? (st : SystemState) (root : VSpaceRoot) (level index : Nat) :
    Option PhysicalWrite :=
  (tablePageAt? st root (level - 1) (index >>> 9)).map fun parent =>
    .storeDescriptor (tableEntryAddress parent index)
      (match tablePageAt? st root level index with
       | some base => tableDescriptorValue base
       | none => 0)

/-- **Record physical writes**: append `ws` to the ledger, in order. -/
def recordPhysicalWrites (st : SystemState) (ws : List PhysicalWrite) : SystemState :=
  { st with pendingPhysicalWrites := st.pendingPhysicalWrites ++ ws }

/-- **Drain the ledger** — the syscall seam's clear, in the atomic step that
commits the transition. -/
def clearPhysicalWrites (st : SystemState) : SystemState :=
  { st with pendingPhysicalWrites := [] }

/-- Recording touches only the ledger: every other field frames. -/
theorem recordPhysicalWrites_eq (st : SystemState) (ws : List PhysicalWrite) :
    recordPhysicalWrites st ws =
      { st with pendingPhysicalWrites := st.pendingPhysicalWrites ++ ws } := rfl
@[simp] theorem recordPhysicalWrites_objects (st : SystemState) (ws : List PhysicalWrite) :
    (recordPhysicalWrites st ws).objects = st.objects := rfl
@[simp] theorem recordPhysicalWrites_asidTable (st : SystemState) (ws : List PhysicalWrite) :
    (recordPhysicalWrites st ws).asidTable = st.asidTable := rfl
@[simp] theorem recordPhysicalWrites_scheduler (st : SystemState) (ws : List PhysicalWrite) :
    (recordPhysicalWrites st ws).scheduler = st.scheduler := rfl
@[simp] theorem recordPhysicalWrites_machine (st : SystemState) (ws : List PhysicalWrite) :
    (recordPhysicalWrites st ws).machine = st.machine := rfl
@[simp] theorem recordPhysicalWrites_tlb (st : SystemState) (ws : List PhysicalWrite) :
    (recordPhysicalWrites st ws).tlb = st.tlb := rfl
@[simp] theorem recordPhysicalWrites_tlbShootdown (st : SystemState) (ws : List PhysicalWrite) :
    (recordPhysicalWrites st ws).tlbShootdown = st.tlbShootdown := rfl
@[simp] theorem recordPhysicalWrites_perCoreTlb (st : SystemState) (ws : List PhysicalWrite) :
    (recordPhysicalWrites st ws).perCoreTlb = st.perCoreTlb := rfl
@[simp] theorem recordPhysicalWrites_perCoreICache (st : SystemState) (ws : List PhysicalWrite) :
    (recordPhysicalWrites st ws).perCoreICache = st.perCoreICache := rfl
@[simp] theorem recordPhysicalWrites_pendingIcacheMaintenance (st : SystemState)
    (ws : List PhysicalWrite) :
    (recordPhysicalWrites st ws).pendingIcacheMaintenance = st.pendingIcacheMaintenance := rfl
@[simp] theorem recordPhysicalWrites_pending (st : SystemState) (ws : List PhysicalWrite) :
    (recordPhysicalWrites st ws).pendingPhysicalWrites = st.pendingPhysicalWrites ++ ws := rfl
@[simp] theorem recordPhysicalWrites_nil (st : SystemState) :
    recordPhysicalWrites st [] = st := by
  simp [recordPhysicalWrites]
@[simp] theorem clearPhysicalWrites_pending (st : SystemState) :
    (clearPhysicalWrites st).pendingPhysicalWrites = [] := rfl

/-- The mapping store for the address space `asid` names, if any. -/
def asidMappingStores (st : SystemState) (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) :
    List PhysicalWrite :=
  match st.asidTable[asid]? with
  | some oid =>
    match st.getVSpaceRoot? oid with
    | some root => if root.asid = asid then (mappingStore? st root vaddr).toList else []
    | none => []
  | none => []

/-- **WS-BP BP7.2: what `TTBR0_EL1` takes for a thread** — its address space's
top-level table page and ASID, or `(0, 0)` for the kernel's own translation.

A thread runs in its own address space exactly when its `vspaceRoot` resolves
to an address space that owns a table page and carries a non-kernel ASID; every
other thread — an idle thread, one whose root is the kernel's boot root, one
whose root has no page yet — runs under the kernel's translation, which maps
nothing at EL0.  `(0, 0)` is unambiguous because the HAL refuses a table page
at address `0` (it is the kernel image's). -/
def threadTranslationOperands (st : SystemState) (tid : SeLe4n.ThreadId) : UInt64 × UInt64 :=
  match st.getTcb? tid with
  | some tcb =>
    match st.getVSpaceRoot? tcb.vspaceRoot with
    | some root =>
      match root.tableBase with
      | some base =>
        if root.asid.toNat = 0 then (0, 0)
        else (base.toNat.toUInt64, root.asid.toNat.toUInt64)
      | none => (0, 0)
    | none => (0, 0)
  | none => (0, 0)

/-- **WS-BP BP7.2**: a thread installs its own address space only through a
root that owns a table page and a non-kernel ASID — the operands are that
page and that ASID, or the kernel's `(0, 0)`. -/
theorem threadTranslationOperands_cases (st : SystemState) (tid : SeLe4n.ThreadId) :
    threadTranslationOperands st tid = (0, 0) ∨
    ∃ tcb root base, st.getTcb? tid = some tcb ∧
      st.getVSpaceRoot? tcb.vspaceRoot = some root ∧
      root.tableBase = some base ∧ root.asid.toNat ≠ 0 ∧
      threadTranslationOperands st tid = (base.toNat.toUInt64, root.asid.toNat.toUInt64) := by
  unfold threadTranslationOperands
  split
  · rename_i tcb hTcb
    split
    · rename_i root hRoot
      split
      · rename_i base hBase
        by_cases hA : root.asid.toNat = 0
        · left; simp [hA]
        · right; exact ⟨tcb, root, base, hTcb, hRoot, hBase, hA, by simp [hA]⟩
      · left; rfl
    · left; rfl
  · left; rfl

end SeLe4n.Kernel.Architecture
