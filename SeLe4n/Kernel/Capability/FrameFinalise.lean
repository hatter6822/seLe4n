-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Capability.Operations
import SeLe4n.Kernel.Architecture.PageTeardownClears
import SeLe4n.Kernel.Architecture.PageTableInstall

/-!
# Frame finalisation — destroying a frame capability unmaps what it mapped

**WS-BP BP7.1 (`v0.36.7`).**  A `VSpaceRoot` records a physical address, not
the capability that installed it, so until this version destroying a frame
capability — by `.cspaceDelete`, or as a descendant swept by `.cspaceRevoke` —
left its mapping in place, and the thread whose address space held it kept
reading and writing a page it no longer held any authority over, until some
holder of the untyped capability reset the untyped.  In seL4 a frame capability
records its mapping (`capFMappedASID`, `capFMappedAddress`) and destroying it
finalises it (`finaliseCap` → `unmapPage`); revoking authority over memory
therefore revokes access to it.

This module is that finalisation.  `.vspaceMap` records the mapping on the
invoked frame capability (`Capability.mapping`, written by
`cspaceRecordFrameMapping`); a derivation — a copy, a mint, an IPC transfer —
does not carry it; and the two destroying arms are composites here:

* `cspaceDeleteSlotFinalising` — the delete, then the page the destroyed
  capability's record names (`slotMappedPages`, read from the slot the delete
  destroys) removed;
* `cspaceRevokeCdtFinalising` — the revocation, which reports the pages of
  exactly the capabilities it destroyed (`cspaceRevokeCdt`'s result,
  `revokeCdtFoldBody_records`), then those pages removed.

Both remove pages through `unmapLivePages`, the untyped reset's own teardown, so
a page is removed only while its address space still maps the address to that
frame: a record gone stale removes nothing that is not its own.  Neither
refuses after its writes: on a well-formed state (`teardownWellFormed` — every
mapping table well formed, every root resolved by its own ASID) no destroyed
capability's page survives, a theorem (`cspaceDeleteSlotFinalising_ok_unmapped`,
`cspaceRevokeCdtFinalising_ok_unmapped`) rather than a check.  Until
`v0.36.110` both decided that result afterwards and refused if it failed.

The one other way a capability can be destroyed is the destruction of the CNode
holding it; the retype of a CNode refuses while any slot holds a capability that
records a mapping (`CNode.holdsFrameMappingRecord`, `.revocationRequired`):
delete those capabilities first, which unmaps.

**Page tables (`v0.36.12`).**  A page table's install is recorded on the table
and in its root rather than on a capability, so what a destroying step owes it is
decided over the store: a table a destroyed capability named (read off the
capability before the step, `slotPageTables`, as seL4's `finaliseCap` acts on the
capability it destroys) that no slot names after it (`pageTablesOrphaned`, over
`cnodeSlotsUnreferenced` since
`v0.36.38` — a copy parked in a message can be dropped by a cancellation that
finalises nothing, so it does not keep a table installed) has lost its **final**
capability, and
seL4's `finaliseCap` → `unmapPageTable` takes it out of its address space.
`finaliseDestroyedCapabilities` is the composite both destroying arms run: it
detaches each orphaned table and every table beneath it from its root
(`detachPageTables`), removes the frame capabilities' recorded pages and the
pages that translated through the detached tables; on a well-formed state no
orphan is left in its root (`finaliseDestroyedCapabilities_ok_tables`).  The detach writes roots only; the tables it takes out
keep a stale record, which `Architecture.pageTableInstallLive` reads as
installed nowhere.  The retype of a CNode holding a capability to an installed
table is refused for the same reason as a mapping record
(`Architecture.cnodeHoldsInstalledPageTableCap`).

**The perform step (WS-ZA ZA5.3 part 4).**  A delete whose capability finalises
nothing (`capabilityFinalisesNothing`: no mapping record, not a page table) is
admitted by `cspaceDeleteAdmitted` and is the plain store write and splice
`cspaceDeletePerform`, proven equal to the finalising delete
(`cspaceDeleteSlotFinalising_of_admitted`).  A revoke whose subtree holds only
such capabilities (`cspaceRevokeAdmitted`, a stackless walk over the slot links)
runs seL4's `cteRevoke` loop, deleting the source's first child until none is
left (`cspaceRevokePerform`); `cspaceRevokeCdtFinalising` is that loop when
admitted and the general path otherwise.  Both admissions read the state before
any write, so the dispatcher runs the step through `RefusalCarrying.ofChecked`
and the store is written in place.

**Every delete (WS-ZA ZA5.3 part 7, `v0.36.110`).**  The teardown no longer
decides its result afterwards, so nothing can refuse a finalising delete once
its CNode exists (`cspaceDeleteFinalisingAdmitted`): a delete of a frame or
page-table capability is its writes too (`cspaceDeleteFinalisingPerformAt`,
`cspaceDeleteSlotFinalising_of_cnode`) and runs through `ofChecked` like any
other.  A revoke over such capabilities still takes the general path.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

-- ============================================================================
-- §1  Is a capability's mapping still live?
-- ============================================================================

/-- **The capability's recorded mapping is still in place**: it records a
mapping, targets a frame, and the address space still maps the recorded address
to that frame.  What `.vspaceMap` refuses to overwrite — a capability maps its
frame once, as in seL4, and mapping it again takes a copy. -/
def capabilityMappingLive (st : SystemState) (cap : Capability) : Bool :=
  match capabilityMappedPage st cap with
  | some p => mappedPageLive st p
  | none => false

-- ============================================================================
-- §2  Page tables: destroying the last capability takes the table out
-- ============================================================================

/-- **The page table a capability names**, if it names one in `st`. -/
@[inline] def capabilityPageTable (st : SystemState) (cap : Capability) : Option SeLe4n.ObjId :=
  match cap.target with
  | .object id => if (st.getPageTable? id).isSome then some id else none
  | _ => none

/-- **The page table the capability in `addr` names**, at most one, read before
a destroying step empties the slot: the candidate for its page-table teardown,
as seL4's `finaliseCap` acts on the capability being destroyed. -/
@[inline] def slotPageTables (st : SystemState) (addr : CSpaceAddr) : List SeLe4n.ObjId :=
  ((SystemState.lookupSlotCap st addr).bind (capabilityPageTable st)).toList

/-- **The page tables a destroying step orphaned**, each with the install its
root holds: a table a destroyed capability named (`named`, read before the step
by `slotPageTables`), installed after the step (`pageTableInstallLive`), that
no capability names after it.  That is seL4's `finaliseCap` condition for a page
table — the capability destroyed was its **final** one — and reading it off the
destroyed capabilities, not off a state before the step, is what lets the step
write the store in place.  A table another capability still names stays where
it is: the holder of that capability can still unmap it.  Each table appears
once, however many destroyed capabilities named it. -/
def pageTablesOrphaned (named : List SeLe4n.ObjId) (st : SystemState) :
    List (SeLe4n.ObjId × PageTableInstall) :=
  named.foldl (init := []) fun acc id =>
    if acc.any (·.1 == id) then acc
    else
      match st.getPageTable? id with
      | some p =>
        match p.installedIn with
        | some inst =>
          if Architecture.pageTableInstallLive st id && cnodeSlotsUnreferenced st [id] then
            (id, inst) :: acc
          else acc
        | none => acc
      | none => acc

/-- **The pages that stop translating when the orphaned tables leave their
walks** — every mapping whose walk passes through one, read off its root. -/
def orphanedTableMappings (st : SystemState) (orphans : List (SeLe4n.ObjId × PageTableInstall)) :
    List MappedPage :=
  orphans.flatMap fun o =>
    match st.getVSpaceRoot? o.2.root with
    | some root => Architecture.pageTableMappingsBeneath root o.2
    | none => []

/-- **Take each orphaned table, and every table beneath it, out of its root** —
seL4's `unmapPageTable`.  One store per orphan, to the root alone: the tables'
own records go stale rather than being written (`pageTableInstallLive`), which
is what keeps the step a write to the address spaces it changes. -/
def detachPageTables : List (SeLe4n.ObjId × PageTableInstall) → Kernel Unit
  | [] => fun st => .ok ((), st)
  | o :: rest => fun st =>
    match st.getVSpaceRoot? o.2.root with
    | none => detachPageTables rest st
    | some root =>
      match storeObject o.2.root (.vspaceRoot (root.withoutTablesBeneath o.2 o.1))
          (Architecture.recordPhysicalWrites st (Architecture.detachWrites st root o.2 o.1)) with
      | .error e => .error e
      | .ok ((), st1) => detachPageTables rest st1

/-- WS-ZA ZA5.3: **the table detach, as a step that cannot fail**: a store
never refuses (`storeObject_isOk`), so the detach is its stores; the compiled
`detachPageTables` (`detachPageTables_eq_impl`). -/
def detachPageTablesState : List (SeLe4n.ObjId × PageTableInstall) → SystemState → SystemState
  | [], st => st
  | o :: rest, st =>
    match st.getVSpaceRoot? o.2.root with
    | none => detachPageTablesState rest st
    | some root =>
      detachPageTablesState rest
        (storeObjectState o.2.root (.vspaceRoot (root.withoutTablesBeneath o.2 o.1))
          (Architecture.recordPhysicalWrites st (Architecture.detachWrites st root o.2 o.1)))

theorem detachPageTables_eq_ok_state :
    ∀ (os : List (SeLe4n.ObjId × PageTableInstall)) (st : SystemState),
      detachPageTables os st = .ok ((), detachPageTablesState os st)
  | [], _ => rfl
  | o :: rest, st => by
    unfold detachPageTables detachPageTablesState
    cases st.getVSpaceRoot? o.2.root with
    | none => exact detachPageTables_eq_ok_state rest st
    | some root =>
      simp only [storeObject_eq_storeObjectState]
      exact detachPageTables_eq_ok_state rest _

/-- The table detach never refuses: compiled, it is `detachPageTablesState`. -/
@[inline] def detachPageTablesImpl (os : List (SeLe4n.ObjId × PageTableInstall)) : Kernel Unit :=
  fun st => .ok ((), detachPageTablesState os st)

@[csimp] theorem detachPageTables_eq_impl : @detachPageTables = @detachPageTablesImpl := by
  funext os st
  exact detachPageTables_eq_ok_state os st

/-- **Each orphaned table is out of its root, and nothing translates through the
slot it held** — the teardown's result on a well-formed state
(`pageTablesDetached_of_teardown`). -/
def pageTablesDetached (st : SystemState) (orphans : List (SeLe4n.ObjId × PageTableInstall)) :
    Bool :=
  orphans.all fun o =>
    match st.getVSpaceRoot? o.2.root with
    | some root =>
      !root.tables.contains (o.2.slotFor o.1) && !Architecture.pageTableInUse root o.2
    | none => true

-- ============================================================================
-- §2a  The detach and the unmap pass take the orphaned tables out
-- ============================================================================

/-- **The detach keeps the state well formed and only shrinks roots, and every
table slot an orphan's root keeps afterwards is outside what that orphan
covered** — its own slot and every deeper one beneath it. -/
theorem detachPageTablesState_wellFormed :
    ∀ (os : List (SeLe4n.ObjId × PageTableInstall)) (st : SystemState), teardownWellFormed st →
      teardownWellFormed (detachPageTablesState os st) ∧
        vspaceRootsShrink st (detachPageTablesState os st) ∧
        ∀ o ∈ os, ∀ R : VSpaceRoot,
          (detachPageTablesState os st).objects[o.2.root]? = some (.vspaceRoot R) →
          ∀ s ∈ R.tables, s ≠ o.2.slotFor o.1 ∧ o.2.coversSlot s = false
  | [], st, hW => ⟨hW, vspaceRootsShrink.refl st, fun _ h => by cases h⟩
  | o :: rest, st, hW => by
    unfold detachPageTablesState
    cases hG : st.getVSpaceRoot? o.2.root with
    | none =>
      obtain ⟨hW2, hS2, hD2⟩ := detachPageTablesState_wellFormed rest st hW
      refine ⟨hW2, hS2, fun o' ho' R hR => ?_⟩
      rcases List.mem_cons.mp ho' with rfl | ho'
      · obtain ⟨R0, h0, -⟩ := hS2 _ R hR
        rw [(SystemState.getVSpaceRoot?_eq_some_iff st _ R0).mpr h0] at hG
        cases hG
      · exact hD2 o' ho' R hR
    | some root =>
      have hObj := (SystemState.getVSpaceRoot?_eq_some_iff st _ root).mp hG
      let root' := root.withoutTablesBeneath o.2 o.1
      let sR := Architecture.recordPhysicalWrites st (Architecture.detachWrites st root o.2 o.1)
      let sS := storeObjectState o.2.root (.vspaceRoot root') sR
      have hWR : teardownWellFormed sR := teardownWellFormed_of_tables_eq rfl rfl hW
      have hObjR : sR.objects[o.2.root]? = some (.vspaceRoot root) := hObj
      have hStore : storeObject o.2.root (.vspaceRoot root') sR = .ok ((), sS) :=
        storeObject_eq_storeObjectState _ _ _
      have hK : root.mappings.invExtK := hW.2.2.2.2.2.2.2.2.2 _ root hObj
      have hTab : ∀ s ∈ root'.tables, s ∈ root.tables ∧
          s ≠ o.2.slotFor o.1 ∧ o.2.coversSlot s = false := by
        intro s hs
        simp only [root', VSpaceRoot.withoutTablesBeneath, List.mem_filter, Bool.and_eq_true,
          Bool.not_eq_true', beq_eq_false_iff_ne] at hs
        exact ⟨hs.1, hs.2.1, hs.2.2⟩
      obtain ⟨hB, hA⟩ := Architecture.storeObject_shrunkRoot_preserves_vspaceInvariantBundle
        sR sS o.2.root root root' hWR.2.2 hWR.1 hWR.2.1 hObjR rfl (fun _ _ hm => hm) hK hStore
      have hWStored : teardownWellFormed sS :=
        ⟨storeObject_preserves_objects_invExt sR sS _ _ hWR.1 hStore, hA, hB⟩
      have hS1 : vspaceRootsShrink st sS :=
        (vspaceRootsShrink_of_tables_eq (st := st) (st' := sR) rfl).trans
          (vspaceRootsShrink_of_store hWR.1 hObjR hStore rfl (fun _ _ hm => hm) rfl
            (fun s hs => (hTab s hs).1))
      have hObjS : sS.objects[o.2.root]? = some (.vspaceRoot root') :=
        storeObject_objects_eq sR sS _ _ hWR.1 hStore
      obtain ⟨hW2, hS2, hD2⟩ := detachPageTablesState_wellFormed rest sS hWStored
      refine ⟨hW2, hS1.trans hS2, fun o' ho' R hR => ?_⟩
      rcases List.mem_cons.mp ho' with rfl | ho'
      · obtain ⟨R1, h1, -, -, -, hT1⟩ := hS2 _ R hR
        rw [hObjS] at h1
        cases h1
        exact fun s hs => (hTab s (hT1 s hs)).2
      · exact hD2 o' ho' R hR

/-- **Every mapping beneath an install is listed** by `pageTableMappingsBeneath`:
the pages the teardown unmaps when it takes the table out. -/
theorem mem_pageTableMappingsBeneath (root : VSpaceRoot) (inst : PageTableInstall)
    (hExt : root.mappings.invExt) (v : SeLe4n.VAddr) (e : SeLe4n.PAddr × PagePermissions)
    (hGet : root.mappings.get? v = some e)
    (hIdx : (PageTableSlot.indexOf inst.level v == inst.index) = true) :
    ({ asid := root.asid, vaddr := v, paddr := e.1 } : MappedPage) ∈
      Architecture.pageTableMappingsBeneath root inst := by
  unfold Architecture.pageTableMappingsBeneath
  refine SeLe4n.Kernel.RobinHood.RHTable.fold_pointwise root.mappings []
    (fun acc vaddr e => if PageTableSlot.indexOf inst.level vaddr == inst.index then
      { asid := root.asid, vaddr := vaddr, paddr := e.1 } :: acc else acc)
    (fun _ _ => True)
    (fun k acc => ∀ e', root.mappings.get? k = some e' →
      (PageTableSlot.indexOf inst.level k == inst.index) = true →
      ({ asid := root.asid, vaddr := k, paddr := e'.1 } : MappedPage) ∈ acc)
    hExt (fun _ => trivial) (fun _ _ _ _ _ _ => trivial) ?_ ?_ v e hGet e hGet hIdx
  · intro acc k w hk _ e' hk' hI
    rw [hk] at hk'; cases hk'
    simp only [hI, ↓reduceIte, List.mem_cons, true_or]
  · intro acc k k' w' _ hQ e' hk' hI
    have := hQ e' hk' hI
    dsimp only
    split
    · exact List.mem_cons_of_mem _ this
    · exact this

/-- **A root uses an install's table only through a mapping beneath it or a
deeper table**: what the fold in `pageTableInUse` finds, it finds in the root. -/
theorem pageTableInUse_mapping (root : VSpaceRoot) (inst : PageTableInstall)
    (hExt : root.mappings.invExt)
    (h : root.mappings.fold (init := false)
      (fun acc vaddr _ => acc || PageTableSlot.indexOf inst.level vaddr == inst.index) = true) :
    ∃ v e, root.mappings.get? v = some e ∧
      (PageTableSlot.indexOf inst.level v == inst.index) = true := by
  revert h
  refine SeLe4n.Kernel.RobinHood.RHTable.fold_preserves_of_lookup root.mappings false _
    (fun acc => acc = true → ∃ v e, root.mappings.get? v = some e ∧
      (PageTableSlot.indexOf inst.level v == inst.index) = true) hExt (fun h => by cases h) ?_
  intro acc k w hk hP hacc
  cases hA : acc
  · rw [hA, Bool.false_or] at hacc; exact ⟨k, w, hk, hacc⟩
  · exact hP hA

/-- **The teardown takes every orphaned table out**: after the detach and the
unmap pass over the destroyed capabilities' pages and every page beneath an
orphan, no orphan's slot is in its root and nothing translates through it — the
result the finalisation decided afterwards, and refused on, before `v0.36.110`. -/
theorem pageTablesDetached_of_teardown (ec : Concurrency.CoreId) (st : SystemState)
    (hW : teardownWellFormed st) (orphans : List (SeLe4n.ObjId × PageTableInstall))
    (pages : List MappedPage) :
    pageTablesDetached
      (unmapLivePagesState ec (pages ++ orphanedTableMappings st orphans)
        (detachPageTablesState orphans st)) orphans = true := by
  obtain ⟨hW1, hS1, hD1⟩ := detachPageTablesState_wellFormed orphans st hW
  obtain ⟨hWF, hSF, hCF⟩ := unmapLivePagesState_clears ec
    (pages ++ orphanedTableMappings st orphans) _ hW1
  unfold pageTablesDetached
  rw [List.all_eq_true]
  intro o ho
  cases hG : (unmapLivePagesState ec (pages ++ orphanedTableMappings st orphans)
      (detachPageTablesState orphans st)).getVSpaceRoot? o.2.root with
  | none => rfl
  | some Rf =>
    simp only
    have hObjF := (SystemState.getVSpaceRoot?_eq_some_iff _ _ Rf).mp hG
    obtain ⟨R1, h1, -, -, -, hT1⟩ := hSF _ Rf hObjF
    have hKeep := hD1 o ho R1 h1
    have hExtF : Rf.mappings.invExt := (hWF.2.2.2.2.2.2.2.2.2 _ Rf hObjF).1
    simp only [Bool.and_eq_true, Bool.not_eq_true']
    refine ⟨?_, ?_⟩
    · cases hc : Rf.tables.contains (o.2.slotFor o.1)
      · rfl
      · have hm : o.2.slotFor o.1 ∈ Rf.tables := List.contains_iff_mem.mp hc
        exact absurd rfl (hKeep _ (hT1 _ hm)).1
    · unfold Architecture.pageTableInUse
      simp only [Bool.or_eq_false_iff]
      refine ⟨?_, ?_⟩
      · cases hf : Rf.mappings.fold (init := false)
            (fun acc vaddr _ => acc || PageTableSlot.indexOf o.2.level vaddr == o.2.index)
        · rfl
        · exfalso
          obtain ⟨v, e, hGet, hIdx⟩ := pageTableInUse_mapping Rf o.2 hExtF hf
          obtain ⟨R0, h0, hA0, hM0, -, -⟩ := (hS1.trans hSF) _ Rf hObjF
          have hGet0 : R0.mappings.get? v = some e := hM0 v e hGet
          have hK0 : R0.mappings.invExt := (hW.2.2.2.2.2.2.2.2.2 _ R0 h0).1
          have hMem : ({ asid := R0.asid, vaddr := v, paddr := e.1 } : MappedPage) ∈
              pages ++ orphanedTableMappings st orphans := by
            refine List.mem_append_right _ ?_
            unfold orphanedTableMappings
            refine List.mem_flatMap.mpr ⟨o, ho, ?_⟩
            rw [(SystemState.getVSpaceRoot?_eq_some_iff st _ R0).mpr h0]
            exact mem_pageTableMappingsBeneath R0 o.2 hK0 v e hGet0 hIdx
          have hDead := hCF _ hMem
          have hLive : mappedPageLive (unmapLivePagesState ec (pages ++ orphanedTableMappings st orphans)
              (detachPageTablesState orphans st))
              { asid := R0.asid, vaddr := v, paddr := e.1 } = true := by
            unfold mappedPageLive
            rw [← hA0, resolveAsidRoot_of_root hWF hObjF]
            have hL : Rf.lookup v = some e := hGet
            simp [hL]
          rw [hDead] at hLive; cases hLive
      · rw [List.any_eq_false]
        intro s hs
        simp [(hKeep s (hT1 s hs)).2]

/-- The table detach is a VSpace-root-only write that keeps the scheduler, the
machine and the object table's invariant. -/
theorem detachPageTables_ok_frame :
    ∀ (os : List (SeLe4n.ObjId × PageTableInstall)) (st st' : SystemState),
      st.objects.invExt → detachPageTables os st = .ok ((), st') →
      st'.objects.invExt ∧ vspaceRootOnlyWrite st st' ∧ st'.scheduler = st.scheduler ∧
        st'.machine = st.machine
  | [], st, st', hInv, h => by
      simp only [detachPageTables, Except.ok.injEq, Prod.mk.injEq, true_and] at h
      subst h
      exact ⟨hInv, vspaceRootOnlyWrite.refl _, rfl, rfl⟩
  | o :: rest, st, st', hInv, h => by
      simp only [detachPageTables] at h
      cases hR : st.getVSpaceRoot? o.2.root with
      | none => rw [hR] at h; exact detachPageTables_ok_frame rest st st' hInv h
      | some root =>
        rw [hR] at h
        simp only at h
        cases hS : storeObject o.2.root (.vspaceRoot (root.withoutTablesBeneath o.2 o.1))
            (Architecture.recordPhysicalWrites st (Architecture.detachWrites st root o.2 o.1)) with
        | error e => rw [hS] at h; cases h
        | ok pr =>
          obtain ⟨⟨⟩, st1⟩ := pr
          rw [hS] at h
          have hObj := (SystemState.getVSpaceRoot?_eq_some_iff st o.2.root root).mp hR
          have hInv1 := storeObject_preserves_objects_invExt (Architecture.recordPhysicalWrites st (Architecture.detachWrites st root o.2 o.1)) _ _ _ hInv hS
          obtain ⟨hI2, hW2, hS2, hM2⟩ := detachPageTables_ok_frame rest st1 st' hInv1 h
          refine ⟨hI2, vspaceRootOnlyWrite.trans (fun oid => ?_) hW2,
            hS2.trans (storeObject_scheduler_eq (Architecture.recordPhysicalWrites st (Architecture.detachWrites st root o.2 o.1)) _ _ _ hS),
            hM2.trans (storeObject_machine_eq (Architecture.recordPhysicalWrites st (Architecture.detachWrites st root o.2 o.1)) _ _ _ hS)⟩
          by_cases hK : oid = o.2.root
          · subst hK
            exact Or.inr ⟨⟨root, hObj⟩, ⟨_, storeObject_objects_eq (Architecture.recordPhysicalWrites st (Architecture.detachWrites st root o.2 o.1)) _ _ _ hInv hS⟩⟩
          · exact Or.inl (storeObject_objects_ne (Architecture.recordPhysicalWrites st (Architecture.detachWrites st root o.2 o.1)) _ _ _ _ hK hInv hS)

/-- The table detach writes no scheduler and no machine state — needing none of
the object table's invariant, since a store writes neither. -/
theorem detachPageTables_ok_scheduler_machine :
    ∀ (os : List (SeLe4n.ObjId × PageTableInstall)) (st st' : SystemState),
      detachPageTables os st = .ok ((), st') →
      st'.scheduler = st.scheduler ∧ st'.machine = st.machine
  | [], st, st', h => by
      simp only [detachPageTables, Except.ok.injEq, Prod.mk.injEq, true_and] at h
      subst h; exact ⟨rfl, rfl⟩
  | o :: rest, st, st', h => by
      simp only [detachPageTables] at h
      cases hR : st.getVSpaceRoot? o.2.root with
      | none => rw [hR] at h; exact detachPageTables_ok_scheduler_machine rest st st' h
      | some root =>
        rw [hR] at h
        simp only at h
        cases hS : storeObject o.2.root (.vspaceRoot (root.withoutTablesBeneath o.2 o.1))
            (Architecture.recordPhysicalWrites st (Architecture.detachWrites st root o.2 o.1)) with
        | error e => rw [hS] at h; cases h
        | ok pr =>
          obtain ⟨⟨⟩, st1⟩ := pr
          rw [hS] at h
          obtain ⟨hS2, hM2⟩ := detachPageTables_ok_scheduler_machine rest st1 st' h
          exact ⟨hS2.trans (storeObject_scheduler_eq (Architecture.recordPhysicalWrites st (Architecture.detachWrites st root o.2 o.1)) _ _ _ hS),
            hM2.trans (storeObject_machine_eq (Architecture.recordPhysicalWrites st (Architecture.detachWrites st root o.2 o.1)) _ _ _ hS)⟩

/-- **Finalise what a destroying step destroyed**: take out the page tables it
orphaned, then remove the pages its frame capabilities recorded and the pages
that translated through those tables.  `named` is what the destroyed
capabilities named, read before the step (`slotPageTables`), `pages` what its
destroyed frame capabilities recorded.  Neither pass can refuse, so neither does
the finalisation (`finaliseDestroyedCapabilities_eq_ok_state`); on a well-formed
state no recorded page survives it and no orphaned table is left in its root
(`finaliseDestroyedCapabilities_ok_unmapped`, `_ok_tables`), as seL4's
`finaliseCap` leaves nothing to check afterwards. -/
def finaliseDestroyedCapabilities (executingCore : Concurrency.CoreId)
    (named : List SeLe4n.ObjId) (pages : List MappedPage) : Kernel Unit :=
  fun st =>
    let orphans := pageTablesOrphaned named st
    match detachPageTables orphans st with
    | .error e => .error e
    | .ok ((), st1) => unmapLivePages executingCore (pages ++ orphanedTableMappings st orphans) st1

/-- **The finalisation's post-state**: the orphans and the pages beneath them are
read off the state before the detach, then the two passes run. -/
def finaliseDestroyedCapabilitiesState (executingCore : Concurrency.CoreId)
    (named : List SeLe4n.ObjId) (pages : List MappedPage) (st : SystemState) : SystemState :=
  let orphans := pageTablesOrphaned named st
  unmapLivePagesState executingCore (pages ++ orphanedTableMappings st orphans)
    (detachPageTablesState orphans st)

/-- The finalisation never refuses: it is its post-state. -/
theorem finaliseDestroyedCapabilities_eq_ok_state (ec : Concurrency.CoreId)
    (named : List SeLe4n.ObjId) (pages : List MappedPage) (st : SystemState) :
    finaliseDestroyedCapabilities ec named pages st =
      .ok ((), finaliseDestroyedCapabilitiesState ec named pages st) := by
  unfold finaliseDestroyedCapabilities finaliseDestroyedCapabilitiesState
  simp only [detachPageTables_eq_ok_state, unmapLivePages_eq_ok_state]

/-- What a successful finalisation is: the table detach, then the page teardown. -/
theorem finaliseDestroyedCapabilities_ok (ec : Concurrency.CoreId) (named : List SeLe4n.ObjId)
    (pages : List MappedPage) (st st' : SystemState)
    (h : finaliseDestroyedCapabilities ec named pages st = .ok ((), st')) :
    ∃ st1, detachPageTables (pageTablesOrphaned named st) st = .ok ((), st1) ∧
      unmapLivePages ec (pages ++ orphanedTableMappings st (pageTablesOrphaned named st)) st1 =
        .ok ((), st') := by
  refine ⟨_, detachPageTables_eq_ok_state _ st, ?_⟩
  rw [finaliseDestroyedCapabilities_eq_ok_state] at h
  rw [unmapLivePages_eq_ok_state]
  simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at h
  rw [← h]; rfl

/-- **The finalisation is a VSpace-root-only write** that keeps the scheduler and
the object table's invariant. -/
theorem finaliseDestroyedCapabilities_ok_frame (ec : Concurrency.CoreId) (named : List SeLe4n.ObjId)
    (pages : List MappedPage) (st st' : SystemState) (hObjInv : st.objects.invExt)
    (h : finaliseDestroyedCapabilities ec named pages st = .ok ((), st')) :
    st'.objects.invExt ∧ vspaceRootOnlyWrite st st' ∧ st'.scheduler = st.scheduler := by
  obtain ⟨st1, hD, hF⟩ := finaliseDestroyedCapabilities_ok ec named pages st st' h
  obtain ⟨hI1, hW1, hS1, -⟩ := detachPageTables_ok_frame _ st st1 hObjInv hD
  obtain ⟨hI2, hW2, hS2⟩ := unmapLivePages_ok_frame ec _ st1 st' hI1 hF
  exact ⟨hI2, hW1.trans hW2, hS2.trans hS1⟩

/-- **The payoff for frames**: on a well-formed state, no page a destroyed frame
capability recorded survives the finalisation. -/
theorem finaliseDestroyedCapabilities_ok_unmapped (ec : Concurrency.CoreId) (named : List SeLe4n.ObjId)
    (pages : List MappedPage) (st st' : SystemState) (hW : teardownWellFormed st)
    (h : finaliseDestroyedCapabilities ec named pages st = .ok ((), st')) :
    ∀ p ∈ pages, mappedPageLive st' p = false := by
  rw [finaliseDestroyedCapabilities_eq_ok_state] at h
  simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at h
  subst h
  intro p hp
  have hW1 := (detachPageTablesState_wellFormed (pageTablesOrphaned named st) st hW).1
  exact (unmapLivePagesState_clears ec _ _ hW1).2.2 p (List.mem_append_left _ hp)

/-- **The payoff for page tables**: on a well-formed state, every table whose
last capability the step destroyed is out of its root, and nothing translates
through the slot it held — no mapping and no deeper table. -/
theorem finaliseDestroyedCapabilities_ok_tables (ec : Concurrency.CoreId) (named : List SeLe4n.ObjId)
    (pages : List MappedPage) (st st' : SystemState) (hW : teardownWellFormed st)
    (h : finaliseDestroyedCapabilities ec named pages st = .ok ((), st')) :
    ∀ o ∈ pageTablesOrphaned named st, ∀ root, st'.getVSpaceRoot? o.2.root = some root →
      root.tables.contains (o.2.slotFor o.1) = false ∧
        Architecture.pageTableInUse root o.2 = false := by
  rw [finaliseDestroyedCapabilities_eq_ok_state] at h
  simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at h
  subst h
  have hC := pageTablesDetached_of_teardown ec st hW (pageTablesOrphaned named st) pages
  intro o ho root hR
  have := List.all_eq_true.mp hC o ho
  unfold finaliseDestroyedCapabilitiesState at hR
  rw [hR] at this
  simpa using this

/-- **The finalisation keeps the state well formed.** -/
theorem finaliseDestroyedCapabilities_ok_wellFormed (ec : Concurrency.CoreId)
    (named : List SeLe4n.ObjId) (pages : List MappedPage) (st st' : SystemState)
    (hW : teardownWellFormed st)
    (h : finaliseDestroyedCapabilities ec named pages st = .ok ((), st')) :
    teardownWellFormed st' := by
  rw [finaliseDestroyedCapabilities_eq_ok_state] at h
  simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at h
  subst h
  exact (unmapLivePagesState_clears ec _ _
    (detachPageTablesState_wellFormed (pageTablesOrphaned named st) st hW).1).1

-- ============================================================================
-- §3  The finalising delete
-- ============================================================================

/-- The delete, then the teardown of what its capability named (`named`,
`pages`), both read before the delete by `cspaceDeleteSlotFinalising`.  Kept
out of line so those reads are made before the delete writes: the state from
before the delete is then dead when the delete runs, and its stores are made in
place. -/
@[noinline] def cspaceDeleteThenFinalise (executingCore : Concurrency.CoreId)
    (named : List SeLe4n.ObjId) (pages : List MappedPage) (addr : CSpaceAddr) :
    Kernel Unit :=
  fun st =>
    match cspaceDeleteSlot addr st with
    | .error e => .error e
    | .ok ((), st1) => finaliseDestroyedCapabilities executingCore named pages st1

/-- **`.cspaceDelete`: delete the capability in `addr`, then remove the mapping it
records.**  The page and the page table the destroyed capability names are read
off its slot before the delete (`slotMappedPages`, `slotPageTables`); the
delete writes only CNodes and the CDT, so they are still what that capability
named when the teardown runs, and nothing reads the state from before the
delete once it has run. -/
def cspaceDeleteSlotFinalising (executingCore : Concurrency.CoreId) (addr : CSpaceAddr) :
    Kernel Unit :=
  fun st =>
    cspaceDeleteThenFinalise executingCore (slotPageTables st addr)
      (slotMappedPages st addr) addr st

/-- What a successful finalising delete is: the delete, then the teardown of the
page the destroyed capability recorded. -/
theorem cspaceDeleteSlotFinalising_ok (ec : Concurrency.CoreId) (addr : CSpaceAddr)
    (st st' : SystemState) (h : cspaceDeleteSlotFinalising ec addr st = .ok ((), st')) :
    ∃ st1, cspaceDeleteSlot addr st = .ok ((), st1) ∧
      finaliseDestroyedCapabilities ec (slotPageTables st addr) (slotMappedPages st addr)
        st1 = .ok ((), st') := by
  unfold cspaceDeleteSlotFinalising cspaceDeleteThenFinalise at h
  cases hD : cspaceDeleteSlot addr st with
  | error e => rw [hD] at h; cases h
  | ok pr => obtain ⟨u, st1⟩ := pr; cases u; rw [hD] at h; exact ⟨st1, rfl, h⟩

/-- Two states whose objects agree off the derivation links hold the same
address-space roots: only CNodes differ. -/
theorem vspaceRoot_iff_of_agree {st st' : SystemState}
    (h : SystemState.objectsAgreeOffDerivationLinks st' st) (oid : SeLe4n.ObjId) (r : VSpaceRoot) :
    st'.objects[oid]? = some (KernelObject.vspaceRoot r) ↔
      st.objects[oid]? = some (KernelObject.vspaceRoot r) := by
  rcases h oid with hE | ⟨cn, cn', h1, h2, -⟩
  · rw [hE]
  · rw [h1, h2]; simp

/-- **A write of derivation links alone keeps the teardown's state well
formed**: it moves no address-space root and leaves the ASID table. -/
theorem teardownWellFormed_of_linkReach {st₀ st : SystemState}
    (h : SystemState.linkReach st₀ st) (hW : teardownWellFormed st₀) : teardownWellFormed st := by
  refine teardownWellFormed_of_roots_eq (h.invExt hW.1) ?_
    (vspaceRoot_iff_of_agree (h.agree hW.1)) hW
  rw [h.fields]

/-- **The core delete keeps the teardown's state well formed**: it writes a
CNode where a CNode stands, never an address-space root or the ASID table. -/
theorem cspaceDeleteSlotCore_preserves_teardownWellFormed {addr : CSpaceAddr}
    {st st' : SystemState} (hW : teardownWellFormed st)
    (hC : cspaceDeleteSlotCore addr st = .ok ((), st')) : teardownWellFormed st' := by
  unfold cspaceDeleteSlotCore at hC
  cases hG : st.getCNode? addr.cnode with
  | none => rw [hG] at hC; cases hC
  | some cn =>
    rw [hG] at hC
    simp only at hC
    have hO : st.objects[addr.cnode]? = some (.cnode cn) :=
      (SystemState.getCNode?_eq_some_iff st addr.cnode cn).1 hG
    cases hS : storeObject addr.cnode (.cnode (cn.remove addr.slot)) st with
    | error e => rw [hS] at hC; cases hC
    | ok pr =>
      obtain ⟨⟨⟩, st1⟩ := pr
      rw [hS] at hC
      simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at hC
      subst hC
      refine teardownWellFormed_of_roots_eq
        (storeObject_preserves_objects_invExt st _ _ _ hW.1 hS) ?_ (fun oid r => ?_) hW
      · rw [storeObject_asidTable_non_vspaceRoot st _ _ _ (fun r h => by cases h) hS, hO]
      · by_cases hK : oid = addr.cnode
        · subst hK
          rw [storeObject_objects_eq st _ _ _ hW.1 hS, hO]
          simp
        · rw [storeObject_objects_ne st _ _ oid _ hK hW.1 hS]

/-- **The delete keeps the teardown's state well formed.** -/
theorem cspaceDeleteSlot_preserves_teardownWellFormed {addr : CSpaceAddr} {st st' : SystemState}
    (hW : teardownWellFormed st) (h : cspaceDeleteSlot addr st = .ok ((), st')) :
    teardownWellFormed st' := by
  obtain ⟨stC, hC, rfl⟩ := cspaceDeleteSlot_ok_decompose addr st st' h
  exact teardownWellFormed_of_linkReach (spliceDeletedCdtNode_reach stC addr)
    (teardownWellFormed_of_tables_eq (st := stC) rfl rfl
      (cspaceDeleteSlotCore_preserves_teardownWellFormed hW hC))

/-- **The general revocation keeps the teardown's state well formed**: each
descendant is a core delete, then its node removed from the tree. -/
theorem cspaceRevokeCdt_preserves_teardownWellFormed {addr : CSpaceAddr} {st st' : SystemState}
    {pages : List MappedPage} (hW : teardownWellFormed st)
    (h : cspaceRevokeCdt addr st = .ok (pages, st')) : teardownWellFormed st' := by
  obtain ⟨-, out, hT, rfl⟩ := revokeCdtScaffold_ok_decompose _ st st' addr pages h
  refine revokeCdtMaterializedTraversal_ok_induct (P := teardownWellFormed)
    (fun stA stB node hA hP => ?_) st addr _ out hW hT
  unfold processRevokeNode at hP
  cases hC : cspaceDeleteSlotCore node stA with
  | error e => rw [hC] at hP; cases hP
  | ok pr =>
    obtain ⟨⟨⟩, stD⟩ := pr
    rw [hC] at hP
    simp only [Except.ok.injEq] at hP
    subst hP
    exact teardownWellFormed_of_linkReach (SystemState.cdtRemove_reach stD node)
      (teardownWellFormed_of_tables_eq (st := stD) rfl rfl
        (cspaceDeleteSlotCore_preserves_teardownWellFormed hA hC))

/-- **The payoff: no mapping the deleted capability recorded survives it.**  On
a well-formed state, if the capability in `addr` recorded a mapping of a frame,
that frame's page is not mapped at the recorded address in the post-state. -/
theorem cspaceDeleteSlotFinalising_ok_unmapped (ec : Concurrency.CoreId) (addr : CSpaceAddr)
    (st st' : SystemState) (hW : teardownWellFormed st)
    (h : cspaceDeleteSlotFinalising ec addr st = .ok ((), st'))
    (cap : Capability) (hCap : SystemState.lookupSlotCap st addr = some cap)
    (p : MappedPage) (hP : capabilityMappedPage st cap = some p) :
    mappedPageLive st' p = false := by
  obtain ⟨_, hD, hF⟩ := cspaceDeleteSlotFinalising_ok ec addr st st' h
  refine finaliseDestroyedCapabilities_ok_unmapped ec _ _ _ st'
    (cspaceDeleteSlot_preserves_teardownWellFormed hW hD) hF p ?_
  simp [slotMappedPages, hCap, hP]

/-- **The finalising delete keeps the teardown's state well formed.** -/
theorem cspaceDeleteSlotFinalising_preserves_teardownWellFormed (ec : Concurrency.CoreId)
    {addr : CSpaceAddr} {st st' : SystemState} (hW : teardownWellFormed st)
    (h : cspaceDeleteSlotFinalising ec addr st = .ok ((), st')) : teardownWellFormed st' := by
  obtain ⟨_, hD, hF⟩ := cspaceDeleteSlotFinalising_ok ec addr st st' h
  exact finaliseDestroyedCapabilities_ok_wellFormed ec _ _ _ st'
    (cspaceDeleteSlot_preserves_teardownWellFormed hW hD) hF

/-- **A capability whose destruction finalises nothing**: it records no mapping
and names no page table, so destroying it leaves every address space as it is
(seL4's `finaliseCap` on such a capability does no work). -/
@[inline] def capabilityFinalisesNothing (st : SystemState) (cap : Capability) : Bool :=
  cap.mapping.isNone &&
    (match cap.target with
     | .object id => (st.getPageTable? id).isNone
     | _ => true)

/-- WS-ZA ZA5.3: **`.cspaceDelete`'s checks**, read before any write: the slot's
CNode exists, and its capability, if any, finalises nothing.  An admitted delete
is its two writes (`cspaceDeleteSlotFinalising_of_admitted`). -/
@[inline] def cspaceDeleteAdmitted (addr : CSpaceAddr) (st : SystemState) : Bool :=
  match st.getCNode? addr.cnode with
  | some cn =>
    match cn.lookup addr.slot with
    | some cap => capabilityFinalisesNothing st cap
    | none => true
  | none => false

/-- WS-ZA ZA5.3: **an admitted delete's writes**: the slot emptied where its
CNode stands (`SystemState.storeCNodeWith`), then spliced out of the derivation
tree (`spliceDeletedCdtNode`). -/
@[inline] def cspaceDeletePerform (addr : CSpaceAddr) (st : SystemState) : SystemState :=
  spliceDeletedCdtNode (st.storeCNodeWith addr.cnode (·.remove addr.slot)) addr

/-- A finalisation of nothing is the identity. -/
theorem finaliseDestroyedCapabilities_nil (ec : Concurrency.CoreId) (st : SystemState) :
    finaliseDestroyedCapabilities ec [] [] st = .ok ((), st) := by
  simp [finaliseDestroyedCapabilities, pageTablesOrphaned, detachPageTables,
    orphanedTableMappings, unmapLivePages]

/-- WS-ZA ZA5.3: an admitted finalising delete is its writes. -/
theorem cspaceDeleteSlotFinalising_of_admitted {ec : Concurrency.CoreId} {addr : CSpaceAddr}
    {st : SystemState} (h : cspaceDeleteAdmitted addr st = true) :
    cspaceDeleteSlotFinalising ec addr st = .ok ((), cspaceDeletePerform addr st) := by
  unfold cspaceDeleteAdmitted SystemState.getCNode? at h
  cases hO : st.objects[addr.cnode]? with
  | none => rw [hO] at h; cases h
  | some o =>
    rw [hO] at h
    cases o
    case cnode cn =>
      simp only at h
      have hLk : SystemState.lookupSlotCap st addr = cn.lookup addr.slot := by
        simp [SystemState.lookupSlotCap, SystemState.lookupCNode, hO]
      have hNamed : slotPageTables st addr = [] ∧ slotMappedPages st addr = [] := by
        cases hC : cn.lookup addr.slot with
        | none => simp [slotPageTables, slotMappedPages, hLk, hC]
        | some cap =>
          rw [hC] at h
          simp only [capabilityFinalisesNothing, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
          obtain ⟨hM, hT⟩ := h
          refine ⟨?_, ?_⟩
          · cases hTg : cap.target <;> simp_all [slotPageTables, capabilityPageTable]
          · simp [slotMappedPages, hLk, hC, capabilityMappedPage, hM]
      unfold cspaceDeleteSlotFinalising cspaceDeleteThenFinalise
      rw [hNamed.1, hNamed.2]
      have hDel : cspaceDeleteSlot addr st = .ok ((), cspaceDeletePerform addr st) := by
        unfold cspaceDeleteSlot cspaceDeleteSlotCore cspaceDeletePerform
        have hG : st.getCNode? addr.cnode = some cn := by
          simp [SystemState.getCNode?, hO]
        rw [hG]
        simp only
        rw [SystemState.storeObject_cnode_eq_storeCNodeWith hO (·.remove addr.slot)]
      simp only [hDel, finaliseDestroyedCapabilities_nil]
    all_goals simp at h

/-- WS-ZA ZA5.3 part 7: **`.cspaceDelete`'s one check**, read before any write:
the slot's CNode exists.  Nothing else can refuse a finalising delete: the
delete itself refuses only for a missing CNode, and the teardown never
refuses (`finaliseDestroyedCapabilities_eq_ok_state`). -/
@[inline] def cspaceDeleteFinalisingAdmitted (addr : CSpaceAddr) (st : SystemState) : Bool :=
  match st.getCNode? addr.cnode with
  | some _ => true
  | none => false

/-- **A delete that finalises something**: what the capability in slot `slot`
of `cnode` names and records is read first, then the slot is emptied and
spliced out, then the teardown of what it named.  Out of line, so the plain
delete builds neither the slot's address nor the lists. -/
@[noinline] def cspaceDeleteTeardownAt (executingCore : Concurrency.CoreId)
    (cnode : SeLe4n.ObjId) (slot : SeLe4n.Slot) (st : SystemState) : SystemState :=
  let addr : CSpaceAddr := ⟨cnode, slot⟩
  let named := slotPageTables st addr
  let pages := slotMappedPages st addr
  finaliseDestroyedCapabilitiesState executingCore named pages (cspaceDeletePerform addr st)

/-- `cspaceDeletePerform` on slot `slot` of `cnode`: the dispatcher hands the
step the slot's two words, so no address record is built (WS-ZA ZA5.3 part 6). -/
def cspaceDeletePerformAt (cnode : SeLe4n.ObjId) (slot : SeLe4n.Slot) (st : SystemState) :
    SystemState :=
  cspaceDeletePerform ⟨cnode, slot⟩ st

/-- WS-ZA ZA5.3 part 7: **an admitted finalising delete's writes**, on slot
`slot` of `cnode`: a capability that finalises nothing (`cspaceDeleteAdmitted`)
is the slot emptied and spliced out (`cspaceDeletePerformAt`) alone; otherwise
the out-of-line teardown (`cspaceDeleteTeardownAt`).  Inline, so the plain
delete's branch is the dispatcher's own check and a call of
`cspaceDeletePerformAt`, as before the teardown joined it. -/
@[inline] def cspaceDeleteFinalisingPerformAt (executingCore : Concurrency.CoreId)
    (cnode : SeLe4n.ObjId) (slot : SeLe4n.Slot) (st : SystemState) : SystemState :=
  if cspaceDeleteAdmitted ⟨cnode, slot⟩ st then cspaceDeletePerformAt cnode slot st
  else cspaceDeleteTeardownAt executingCore cnode slot st


/-- The delete, when its slot's CNode exists, is the slot emptied and spliced
out. -/
theorem cspaceDeleteSlot_of_cnode {addr : CSpaceAddr} {st : SystemState}
    (h : cspaceDeleteFinalisingAdmitted addr st = true) :
    cspaceDeleteSlot addr st = .ok ((), cspaceDeletePerform addr st) := by
  unfold cspaceDeleteFinalisingAdmitted at h
  cases hG : st.getCNode? addr.cnode with
  | none => rw [hG] at h; cases h
  | some cn =>
    have hO : st.objects[addr.cnode]? = some (.cnode cn) := by
      unfold SystemState.getCNode? at hG
      cases hO : st.objects[addr.cnode]? with
      | none => rw [hO] at hG; cases hG
      | some o => rw [hO] at hG; cases o <;> simp_all
    unfold cspaceDeleteSlot cspaceDeleteSlotCore cspaceDeletePerform
    rw [hG]
    simp only
    rw [SystemState.storeObject_cnode_eq_storeCNodeWith hO (·.remove addr.slot)]

/-- WS-ZA ZA5.3 part 7: **an admitted finalising delete is its writes**, whatever
its capability names. -/
theorem cspaceDeleteSlotFinalising_of_cnode {ec : Concurrency.CoreId} {cnode : SeLe4n.ObjId}
    {slot : SeLe4n.Slot} {st : SystemState}
    (h : cspaceDeleteFinalisingAdmitted ⟨cnode, slot⟩ st = true) :
    cspaceDeleteSlotFinalising ec ⟨cnode, slot⟩ st =
      .ok ((), cspaceDeleteFinalisingPerformAt ec cnode slot st) := by
  unfold cspaceDeleteFinalisingPerformAt cspaceDeletePerformAt
  split
  · next hA => exact cspaceDeleteSlotFinalising_of_admitted hA
  · unfold cspaceDeleteSlotFinalising cspaceDeleteThenFinalise cspaceDeleteTeardownAt
    rw [cspaceDeleteSlot_of_cnode h]
    exact finaliseDestroyedCapabilities_eq_ok_state ec _ _ _

-- ============================================================================
-- §4  The finalising revocation
-- ============================================================================

/-- **The page tables the capabilities a revocation destroys name**: those in
the source's descendants, read before the revocation (`slotPageTables`). -/
def revokedPageTables (st : SystemState) (addr : CSpaceAddr) : List SeLe4n.ObjId :=
  (st.linkDescendantsOf addr).flatMap (slotPageTables st)

/-- The revocation, then the teardown of what its destroyed capabilities named
(`named`, read before it by `cspaceRevokeCdtFinalising`) and recorded.  Out of
line for the reason `cspaceDeleteThenFinalise` is. -/
@[noinline] def cspaceRevokeThenFinalise (executingCore : Concurrency.CoreId)
    (named : List SeLe4n.ObjId) (addr : CSpaceAddr) : Kernel Unit :=
  fun st =>
    match cspaceRevokeCdt addr st with
    | .error e => .error e
    | .ok (pages, st1) => finaliseDestroyedCapabilities executingCore named pages st1

/-- **Is every slot in a subtree one whose delete is admitted**
(`cspaceDeleteAdmitted`), read along the slot links in preorder and without a
stack: down a first-child link, else across a next-sibling link, else back up a
parent link to the first ancestor with a next sibling, stopping on the way up at
the root (`rc`, `rw`, its link codes).  `down` says whether `(c, w)` is being
entered (it is checked and its children come next) or left (its subtree is
done).  Each step reads link words only, so the walk builds nothing; running
out of `fuel` reads as `false`. -/
def linkSubtreeDeletable (st : SystemState) (rc rw : Nat) :
    Nat → Nat → Nat → Bool → Bool
  | 0, _, _, _ => false
  | fuel + 1, c, w, true =>
    let o := SeLe4n.ObjId.ofNat (c - 1)
    let s := SeLe4n.Slot.ofNat (w - 1)
    if cspaceDeleteAdmitted { cnode := o, slot := s } st then
      let fc := st.slotLinkNodeWord o s .firstChild
      if fc != 0 then
        linkSubtreeDeletable st rc rw fuel fc (st.slotLinkSlotWord o s .firstChild) true
      else linkSubtreeDeletable st rc rw fuel c w false
    else false
  | fuel + 1, c, w, false =>
    if c == rc && w == rw then true
    else
      let o := SeLe4n.ObjId.ofNat (c - 1)
      let s := SeLe4n.Slot.ofNat (w - 1)
      let nc := st.slotLinkNodeWord o s .next
      if nc != 0 then
        linkSubtreeDeletable st rc rw fuel nc (st.slotLinkSlotWord o s .next) true
      else
        let pc := st.slotLinkNodeWord o s .parent
        if pc != 0 then
          linkSubtreeDeletable st rc rw fuel pc (st.slotLinkSlotWord o s .parent) false
        else false

/-- WS-ZA ZA5.3: **`.cspaceRevoke`'s checks**, read before any write: the
source slot holds a capability, and every slot beneath it in the derivation
tree is one whose delete is admitted (`linkSubtreeDeletable`), so no capability
the revocation destroys has anything to finalise.  The walk's fuel covers a
walk down and back up every edge. -/
@[inline] def cspaceRevokeAdmitted (addr : CSpaceAddr) (st : SystemState) : Bool :=
  (SystemState.lookupSlotCap st addr).isSome &&
    (let fc := st.slotLinkNodeWord addr.cnode addr.slot .firstChild
     fc == 0 ||
       linkSubtreeDeletable st (addr.cnode.toNat + 1) (addr.slot.toNat + 1)
         (2 * st.cdt.edgeBound + 2) fc
         (st.slotLinkSlotWord addr.cnode addr.slot .firstChild) true)

/-- **seL4's `cteRevoke`, on an admitted revocation**: delete the source's first
child until it has none.  Each delete splices its slot out of the tree, so the
deleted child's children become the source's, and the loop reaches every
descendant without building a list of them.  A child whose delete is not
admitted ends the loop; `fuel` bounds it by the tree's edges, one of which each
splice removes. -/
def revokeFirstChildLoop (cnode : SeLe4n.ObjId) (slot : SeLe4n.Slot) :
    Nat → SystemState → SystemState
  | 0, st => st
  | n + 1, st =>
    let fc := st.slotLinkNodeWord cnode slot .firstChild
    if fc = 0 then st
    else
      let c : CSpaceAddr :=
        { cnode := SeLe4n.ObjId.ofNat (fc - 1),
          slot := SeLe4n.Slot.ofNat (st.slotLinkSlotWord cnode slot .firstChild - 1) }
      if cspaceDeleteAdmitted c st then revokeFirstChildLoop cnode slot n (cspaceDeletePerform c st)
      else st

/-- WS-ZA ZA5.3: **an admitted revocation's writes**: the first-child loop, with
fuel for every edge of the tree. -/
@[inline] def cspaceRevokePerform (addr : CSpaceAddr) (st : SystemState) : SystemState :=
  revokeFirstChildLoop addr.cnode addr.slot (st.cdt.edgeBound + 1) st

/-- `cspaceRevokePerform` on slot `slot` of `cnode`, for the same reason. -/
def cspaceRevokePerformAt (cnode : SeLe4n.ObjId) (slot : SeLe4n.Slot) (st : SystemState) :
    SystemState :=
  cspaceRevokePerform ⟨cnode, slot⟩ st

/-- **What the first-child loop is made of: finalising deletes.**  Each step it
takes is an admitted delete, which is the finalising delete
(`cspaceDeleteSlotFinalising_of_admitted`), so any property every finalising
delete keeps, the loop keeps. -/
theorem revokeFirstChildLoop_closed {ec : Concurrency.CoreId} {addr : CSpaceAddr}
    (Q : SystemState → Prop)
    (hStep : ∀ (c : CSpaceAddr) (s s' : SystemState), Q s →
      cspaceDeleteSlotFinalising ec c s = .ok ((), s') → Q s') :
    ∀ (n : Nat) (st : SystemState), Q st → Q (revokeFirstChildLoop addr.cnode addr.slot n st)
  | 0, _, h => h
  | n + 1, st, h => by
    unfold revokeFirstChildLoop
    dsimp only
    split
    · exact h
    · split
      · next hA =>
        exact revokeFirstChildLoop_closed Q hStep n _
          (hStep _ st _ h (cspaceDeleteSlotFinalising_of_admitted hA))
      · exact h

/-- **`.cspaceRevoke`: revoke the capability in `addr`, then remove every mapping
a destroyed capability recorded.**  seL4 splits the invocation into its checks
and `cteRevoke`; so does this.  When every capability beneath the source has
nothing to finalise (`cspaceRevokeAdmitted`), the revocation is the first-child
loop (`cspaceRevokePerform`), written in place.  Otherwise it is the general
revocation: the descendants destroyed in turn (`cspaceRevokeCdt`, which reports
the pages of exactly the capabilities its traversal destroyed,
`revokeCdtFoldBody_records`), then the teardown of what they named. -/
def cspaceRevokeCdtFinalising (executingCore : Concurrency.CoreId) (addr : CSpaceAddr) :
    Kernel Unit :=
  fun st =>
    if cspaceRevokeAdmitted addr st then .ok ((), cspaceRevokePerform addr st)
    else cspaceRevokeThenFinalise executingCore (revokedPageTables st addr) addr st

/-- What a successful finalising revocation is: the first-child loop of an
admitted revocation, or the general revocation and the teardown of the pages its
destroyed capabilities recorded. -/
theorem cspaceRevokeCdtFinalising_ok (ec : Concurrency.CoreId) (addr : CSpaceAddr)
    (st st' : SystemState) (h : cspaceRevokeCdtFinalising ec addr st = .ok ((), st')) :
    (cspaceRevokeAdmitted addr st = true ∧ st' = cspaceRevokePerform addr st) ∨
      ∃ pages st1, cspaceRevokeCdt addr st = .ok (pages, st1) ∧
        finaliseDestroyedCapabilities ec (revokedPageTables st addr) pages st1 =
          .ok ((), st') := by
  unfold cspaceRevokeCdtFinalising at h
  split at h
  · next hA =>
    simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at h
    exact Or.inl ⟨hA, h.symm⟩
  · unfold cspaceRevokeThenFinalise at h
    cases hR : cspaceRevokeCdt addr st with
    | error e => rw [hR] at h; cases h
    | ok pr =>
      obtain ⟨pages, st1⟩ := pr
      rw [hR] at h
      exact Or.inr ⟨pages, st1, rfl, h⟩

/-- **The finalising revocation keeps whatever every finalising delete and the
general revocation's teardown keep.**  The consumers' one case analysis: the
admitted loop is a chain of finalising deletes (`revokeFirstChildLoop_closed`),
the general path the revocation then the teardown. -/
theorem cspaceRevokeCdtFinalising_closed {ec : Concurrency.CoreId} {addr : CSpaceAddr}
    {st st' : SystemState} (Q : SystemState → Prop)
    (hDel : ∀ (c : CSpaceAddr) (s s' : SystemState), Q s →
      cspaceDeleteSlotFinalising ec c s = .ok ((), s') → Q s')
    (hGen : ∀ pages st1, cspaceRevokeCdt addr st = .ok (pages, st1) →
      finaliseDestroyedCapabilities ec (revokedPageTables st addr) pages st1 = .ok ((), st') →
      Q st')
    (hQ : Q st) (h : cspaceRevokeCdtFinalising ec addr st = .ok ((), st')) : Q st' := by
  rcases cspaceRevokeCdtFinalising_ok ec addr st st' h with ⟨-, rfl⟩ | ⟨pages, st1, hR, hF⟩
  · exact revokeFirstChildLoop_closed Q hDel _ st hQ
  · exact hGen pages st1 hR hF

/-- **The payoff: no reported page survives the revocation.**  On a well-formed
state: an admitted
revocation destroys only capabilities that record no mapping; otherwise, with
`revokeCdtFoldBody_records` — each step reports the page of the capability it
destroys — no page a destroyed frame capability recorded is still mapped. -/
theorem cspaceRevokeCdtFinalising_ok_unmapped (ec : Concurrency.CoreId) (addr : CSpaceAddr)
    (st st' : SystemState) (hW : teardownWellFormed st)
    (h : cspaceRevokeCdtFinalising ec addr st = .ok ((), st')) :
    cspaceRevokeAdmitted addr st = true ∨
      ∃ pages, (∃ st1, cspaceRevokeCdt addr st = .ok (pages, st1)) ∧
        ∀ p ∈ pages, mappedPageLive st' p = false := by
  rcases cspaceRevokeCdtFinalising_ok ec addr st st' h with ⟨hA, -⟩ | ⟨pages, st1, hC, hF⟩
  · exact Or.inl hA
  · exact Or.inr ⟨pages, ⟨st1, hC⟩, finaliseDestroyedCapabilities_ok_unmapped ec _ pages st1 st'
      (cspaceRevokeCdt_preserves_teardownWellFormed hW hC) hF⟩

end SeLe4n.Kernel
