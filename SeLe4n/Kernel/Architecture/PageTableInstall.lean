-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Model.State
import SeLe4n.Kernel.Architecture.HardwareTables

/-!
# Intermediate page tables — seL4's `seL4_ARM_PageTable_Map` / `_Unmap`

**WS-BP BP7.1 (`v0.36.12`).**  A carved address space (`VSpaceRoot.tableBase =
some _`) owns its top-level table page and nothing below it.  A 48-bit,
4 KiB-granule walk passes through three more levels, and each is a page of RAM
someone must provide — in seL4, a `seL4_ARM_PageTable` object the address
space's owner carves from an untyped and installs with
`seL4_ARM_PageTable_Map`.  This module is those two operations.

* `pageTableMap tableId rootId vaddr` installs the table at the **shallowest
  level the walk to `vaddr` is missing** (`VSpaceRoot.missingLevel?`), so a table
  is never installed beneath an absent one and the three levels come in order.
  It writes both sides of the install together: the root gains the slot
  (`VSpaceRoot.tables`) and the table records where it sits
  (`PageTableObject.installedIn`).  A table installs in one place at a time
  (`.invalidCapability`, seL4's "already mapped"); a root the boot configured
  owns no page for a table to hang from (`.invalidArgument`); an address outside
  the 48-bit space has no walk (`.addressOutOfBounds`); and a walk already
  complete has nowhere to put another table (`.mappingConflict`, seL4's
  `seL4_DeleteFirst`).
* `pageTableUnmap tableId` removes the slot and clears the record.  It
  **refuses** (`.revocationRequired`) while anything still translates through
  the table — a mapping whose walk passes it, or a deeper table installed
  beneath it.  seL4 instead tears the subtree out and leaves the frame
  capabilities' records stale; refusing keeps every recorded mapping one the
  root actually holds, which is what `cspaceDeleteSlotFinalising`'s teardown
  relies on.  Destroying a table's **last** capability is different — no one is
  left to unmap it — and there the finalisation takes it out with everything
  beneath it (`finaliseDestroyedCapabilities`).

**The root is the truth.**  A table is installed exactly when the root its
record names holds the slot the record names (`pageTableInstallLive`).  The
finalisation writes roots only, so the tables it takes out keep a stale record;
every reader asks the live question, so a stale record reads as installed
nowhere.

A frame is mapped into a carved address space only where the walk is complete
(`Architecture.asidTranslationReady`, read by the live `.vspaceMap` arm).
-/

namespace SeLe4n.Kernel.Architecture

open SeLe4n.Model

/-- Addresses a thread's translation tables may cover: the user window
(`VAddr.inUserWindow`, WS-BP BP7.2) — canonical, and past level-0 entry 0,
which every user root gives to the kernel's own window.  A table installed for a
lower address would take that slot. -/
def pageTableAddressable (vaddr : SeLe4n.VAddr) : Bool :=
  vaddr.inUserWindow

/-- **A slot lies beneath the install `inst`**: a deeper level whose index,
shifted up to `inst`'s level, is `inst`'s — a table the walk reaches only
through the one installed at `inst`. -/
def _root_.SeLe4n.Model.PageTableInstall.coversSlot (inst : PageTableInstall)
    (s : PageTableSlot) : Bool :=
  inst.level < s.level && s.index >>> (9 * (s.level - inst.level)) == inst.index

/-- **The table an install record names is still in use**: the root maps an
address whose walk passes through it, or holds a deeper table beneath it. -/
def pageTableInUse (root : VSpaceRoot) (inst : PageTableInstall) : Bool :=
  root.mappings.fold (init := false)
      (fun acc vaddr _ => acc || PageTableSlot.indexOf inst.level vaddr == inst.index) ||
    root.tables.any inst.coversSlot

/-- The root's slot an install record names, for the table `tableId`. -/
def _root_.SeLe4n.Model.PageTableInstall.slotFor (inst : PageTableInstall)
    (tableId : SeLe4n.ObjId) : PageTableSlot :=
  { level := inst.level, index := inst.index, table := tableId }

/-- **Is the table installed?**  The root is the truth and the table's record a
pointer to where to look: the table is installed exactly when its record names a
root and that root holds the slot the record names, for this table.  A record
whose root no longer holds that slot is **stale** — what a finalisation leaves
behind when it takes a table out of an address space without writing the table
(`finalisePageTables`) — and reads as not installed everywhere: `.pageTableMap`
installs such a table again, `.pageTableUnmap` clears its record, and the untyped
reset does not refuse to retire it. -/
def pageTableInstallLive (st : SystemState) (tableId : SeLe4n.ObjId) : Bool :=
  match st.getPageTable? tableId with
  | some table =>
    match table.installedIn with
    | some inst => (st.getVSpaceRoot? inst.root).any (·.tables.contains (inst.slotFor tableId))
    | none => false
  | none => false

/-- **Does a capability name an installed page table?** -/
def capabilityNamesInstalledPageTable (st : SystemState) (cap : Capability) : Bool :=
  match cap.target with
  | .object id => pageTableInstallLive st id
  | _ => false

/-- **Does any slot of `cn` hold a capability naming an installed page table?**
Destroying the last such capability owes taking the table out of its address
space (`finaliseDestroyedCapabilities`), which a CNode's destruction by retype
does not perform — so the retype refuses a CNode for which this holds, as it
refuses one holding a frame capability's mapping record.  Delete those
capabilities first. -/
def cnodeHoldsInstalledPageTableCap (st : SystemState) (cn : CNode) : Bool :=
  cn.slots.fold false (fun acc _ cap => acc || capabilityNamesInstalledPageTable st cap)

/-- The mappings of `root` whose walk passes through the table installed at
`inst` — the pages that stop translating when that table leaves the walk. -/
def pageTableMappingsBeneath (root : VSpaceRoot) (inst : PageTableInstall) :
    List MappedPage :=
  root.mappings.fold (init := []) (fun acc vaddr e =>
    if PageTableSlot.indexOf inst.level vaddr == inst.index then
      { asid := root.asid, vaddr := vaddr, paddr := e.1 } :: acc
    else acc)

/-- The root once the table `table` at `inst`, and every table installed beneath
it, has left the walk.  The deeper tables' own records go stale rather than
being written, which is what keeps this a write to one object. -/
def _root_.SeLe4n.Model.VSpaceRoot.withoutTablesBeneath (root : VSpaceRoot)
    (inst : PageTableInstall) (table : SeLe4n.ObjId) : VSpaceRoot :=
  let keep := fun (s : PageTableSlot) => !(s == inst.slotFor table) && !inst.coversSlot s
  { root with tables := root.tables.filter keep }

/-- **WS-BP BP7.2: the physical writes taking `table` and everything beneath it
out of `root` owes** — the parent entry cleared, every detached table's page
zeroed (a detached table may be installed again later, and its page must then
hold nothing it translated before), and the address space's ASID invalidated,
since the walk caches intermediate levels. -/
def detachWrites (st : SystemState) (root : VSpaceRoot) (inst : PageTableInstall)
    (table : SeLe4n.ObjId) : List PhysicalWrite :=
  let removed := root.tables.filter fun s => s == inst.slotFor table || inst.coversSlot s
  (slotStore? st (root.withoutTablesBeneath inst table) inst.level inst.index).toList ++
    removed.filterMap (fun s => (st.getPageTable? s.table).map fun t => .zeroPage t.base) ++
    [.invalidateAsid root.asid]

/-- The table's record once installed at `(root, level, index)`. -/
def _root_.SeLe4n.Model.PageTableObject.installedAt (table : PageTableObject) (root : SeLe4n.ObjId)
    (level index : Nat) : PageTableObject :=
  { table with installedIn := some (PageTableInstall.mk root level index) }

/-- The root once it holds `table` at `(level, index)`. -/
def _root_.SeLe4n.Model.VSpaceRoot.withTableSlot (root : VSpaceRoot) (level index : Nat)
    (table : SeLe4n.ObjId) : VSpaceRoot :=
  { root with tables := root.tables ++ [PageTableSlot.mk level index table] }

/-- The root once the slot `inst` names for `table` is removed. -/
def _root_.SeLe4n.Model.VSpaceRoot.withoutTableSlot (root : VSpaceRoot) (inst : PageTableInstall)
    (table : SeLe4n.ObjId) : VSpaceRoot :=
  let keep := fun (s : PageTableSlot) =>
    !(s.level == inst.level && s.index == inst.index && s.table == table)
  { root with tables := root.tables.filter keep }

/-- **`seL4_ARM_PageTable_Map`**: install the page table `tableId` in the address
space `rootId` at the shallowest level the walk to `vaddr` is missing. -/
def pageTableMap (tableId rootId : SeLe4n.ObjId) (vaddr : SeLe4n.VAddr) : Kernel Unit :=
  fun st =>
    match st.getPageTable? tableId, st.getVSpaceRoot? rootId with
    | none, _ => .error .invalidCapability
    | _, none => .error .invalidCapability
    | some table, some root =>
      if pageTableInstallLive st tableId then .error .invalidCapability
      else if root.tableBase.isNone then .error .invalidArgument
      else if !pageTableAddressable vaddr then .error .addressOutOfBounds
      else
        match root.missingLevel? vaddr with
        | none => .error .mappingConflict
        | some level =>
          let index := PageTableSlot.indexOf level vaddr
          match storeObject tableId (.pageTable (table.installedAt rootId level index)) st with
          | .error e => .error e
          | .ok ((), st1) =>
            -- WS-BP BP7.2: the parent entry now names the table's page.
            storeObject rootId (.vspaceRoot (root.withTableSlot level index tableId))
              (recordPhysicalWrites st1
                (slotStore? st1 (root.withTableSlot level index tableId) level index).toList)

/-- **`seL4_ARM_PageTable_Unmap`**: take the table `tableId` out of the address
space it is installed in.  A table installed nowhere is left as it is — seL4
answers that call with success too. -/
def pageTableUnmap (tableId : SeLe4n.ObjId) : Kernel Unit :=
  fun st =>
    match st.getPageTable? tableId with
    | none => .error .invalidCapability
    | some table =>
      match table.installedIn with
      | none => .ok ((), st)
      | some inst =>
        match st.getVSpaceRoot? inst.root with
        | none =>
          -- The root is gone (retired with the table's own subtree); only the
          -- record is left to clear.
          storeObject tableId (.pageTable { table with installedIn := none }) st
        | some root =>
          if root.tables.contains (inst.slotFor tableId) then
            if pageTableInUse root inst then .error .revocationRequired
            else
              match storeObject tableId (.pageTable { table with installedIn := none }) st with
              | .error e => .error e
              | .ok ((), st1) =>
                -- WS-BP BP7.2: the parent entry is cleared, and the walk
                -- caches the address space's intermediate levels, so its ASID
                -- is invalidated.
                storeObject inst.root (.vspaceRoot (root.withoutTableSlot inst tableId))
                  (recordPhysicalWrites st1
                    ((slotStore? st1 (root.withoutTableSlot inst tableId) inst.level
                      inst.index).toList ++ [.invalidateAsid root.asid]))
          else
            -- A stale record (`pageTableInstallLive`): the root no longer holds
            -- the table, so only the record is left to clear.
            storeObject tableId (.pageTable { table with installedIn := none }) st

/-- A successful install is two stores: the table, recording where it now sits,
then the root, gaining the slot. -/
theorem pageTableMap_ok (tableId rootId : SeLe4n.ObjId) (vaddr : SeLe4n.VAddr)
    (st st' : SystemState) (h : pageTableMap tableId rootId vaddr st = .ok ((), st')) :
    ∃ table root level st1,
      st.getPageTable? tableId = some table ∧ st.getVSpaceRoot? rootId = some root ∧
      pageTableInstallLive st tableId = false ∧ root.tableBase.isSome ∧ pageTableAddressable vaddr = true ∧
      root.missingLevel? vaddr = some level ∧
      storeObject tableId (.pageTable (table.installedAt rootId level
        (PageTableSlot.indexOf level vaddr))) st = .ok ((), st1) ∧
      storeObject rootId (.vspaceRoot (root.withTableSlot level
        (PageTableSlot.indexOf level vaddr) tableId))
        (recordPhysicalWrites st1 (slotStore? st1 (root.withTableSlot level
          (PageTableSlot.indexOf level vaddr) tableId) level
          (PageTableSlot.indexOf level vaddr)).toList) = .ok ((), st') := by
  unfold pageTableMap at h
  cases hT : st.getPageTable? tableId with
  | none => rw [hT] at h; cases h
  | some table =>
    cases hR : st.getVSpaceRoot? rootId with
    | none => rw [hT, hR] at h; cases h
    | some root =>
      rw [hT, hR] at h
      simp only at h
      cases hI : pageTableInstallLive st tableId with
      | true => rw [hI] at h; simp at h
      | false =>
        rw [hI] at h
        cases hB : root.tableBase with
        | none => rw [hB] at h; simp at h
        | some _ =>
          rw [hB] at h
          cases hA : pageTableAddressable vaddr with
          | false => rw [hA] at h; simp at h
          | true =>
            rw [hA] at h
            simp only [Option.isNone_some, Bool.not_true,
              Bool.false_eq_true, ↓reduceIte] at h
            cases hL : root.missingLevel? vaddr with
            | none => rw [hL] at h; cases h
            | some level =>
              rw [hL] at h
              simp only at h
              cases hS : storeObject tableId _ st with
              | error e => rw [hS] at h; cases h
              | ok p =>
                obtain ⟨⟨⟩, st1⟩ := p
                rw [hS] at h
                exact ⟨table, root, level, st1, rfl, rfl, rfl, by simp [hB], rfl, hL, hS, h⟩

/-- **The install lands where the walk was missing**: after a successful
`pageTableMap` the root holds the table at the level the walk to `vaddr` lacked,
and the table records that slot. -/
theorem pageTableMap_ok_installed (tableId rootId : SeLe4n.ObjId) (vaddr : SeLe4n.VAddr)
    (st st' : SystemState) (hObjInv : st.objects.invExt)
    (h : pageTableMap tableId rootId vaddr st = .ok ((), st')) :
    ∃ table root level,
      st.getPageTable? tableId = some table ∧ st.getVSpaceRoot? rootId = some root ∧
      root.missingLevel? vaddr = some level ∧
      st'.objects[rootId]? = some (.vspaceRoot (root.withTableSlot level
        (PageTableSlot.indexOf level vaddr) tableId)) ∧
      st'.objects[tableId]? = some (.pageTable (table.installedAt rootId level
        (PageTableSlot.indexOf level vaddr))) := by
  obtain ⟨table, root, level, st1, hT, hR, -, -, -, hL, hS1, hS2⟩ :=
    pageTableMap_ok tableId rootId vaddr st st' h
  have hInv1 := storeObject_preserves_objects_invExt _ _ _ _ hObjInv hS1
  have hNe : tableId ≠ rootId := by
    intro hEq; subst hEq
    rw [SystemState.getPageTable?_eq_some_iff] at hT; rw [SystemState.getVSpaceRoot?_eq_some_iff] at hR
    rw [hT] at hR; cases hR
  refine ⟨table, root, level, hT, hR, hL, storeObject_objects_eq (recordPhysicalWrites st1 _) _ _ _ hInv1 hS2, ?_⟩
  rw [storeObject_objects_ne (recordPhysicalWrites st1 _) _ _ _ _ hNe hInv1 hS2]
  have hTab := storeObject_objects_eq _ _ _ _ hObjInv hS1
  exact hTab

/-- **A table something still translates through is not unmapped.** -/
theorem pageTableUnmap_refuses_in_use (tableId : SeLe4n.ObjId) (st : SystemState)
    (table : PageTableObject) (inst : PageTableInstall) (root : VSpaceRoot)
    (hT : st.getPageTable? tableId = some table) (hI : table.installedIn = some inst)
    (hR : st.getVSpaceRoot? inst.root = some root)
    (hLive : root.tables.contains (inst.slotFor tableId) = true)
    (hUse : pageTableInUse root inst = true) :
    pageTableUnmap tableId st = .error .revocationRequired := by
  have hMem : inst.slotFor tableId ∈ root.tables := by simpa using hLive
  simp [pageTableUnmap, hT, hI, hR, hMem, hUse]

end SeLe4n.Kernel.Architecture
