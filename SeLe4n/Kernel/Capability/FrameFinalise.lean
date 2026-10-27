-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Capability.Operations
import SeLe4n.Model.CapabilityFinality
import SeLe4n.Kernel.Architecture.PageTeardownClears
import SeLe4n.Kernel.Architecture.PageTableInstall
import SeLe4n.Kernel.Capability.FinalRetire
import SeLe4n.Kernel.IPC.Invariant.CancelAllFrame

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
  destroys) removed, then the object it was the final capability to finalised
  and retired (`retireFinalisedObject`: an endpoint's or a notification's
  waiters cancelled and a notification unbound, `finaliseFinalObject`, then
  `retireFinalObject`);
* `cspaceRevokeCdtFinalising` — seL4's `cteRevoke`: the source's first child
  deleted by `cspaceDeleteSlotFinalising` until it has none.

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
decided over the destroyed capability: a table a destroyed capability named
when that capability was **final** (read off the capability and its slot's four
derivation links before the step, `slotPageTables` over `SystemState.capIsFinal`,
seL4's `isFinalCapability`, as seL4's `finaliseCap` acts on the capability it
destroys; under the capability bundle, no other slot names the table) has lost
its last capability (`pageTablesOrphaned`), and
seL4's `finaliseCap` → `unmapPageTable` takes it out of its address space.
Until `v0.36.131` finality was a scan of every slot of every object after the
step.
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
(`cspaceDeleteSlotFinalising_of_admitted`).

**Every delete (WS-ZA ZA5.3 part 7, `v0.36.110`).**  The teardown no longer
decides its result afterwards, so nothing can refuse a finalising delete once
its CNode exists (`cspaceDeleteFinalisingAdmitted`): a delete of a frame or
page-table capability is its writes too (`cspaceDeleteFinalisingPerformAt`,
`cspaceDeleteSlotFinalising_of_slotHolder`) and runs through `ofChecked` like any
other.

**Every revoke (WS-ZA ZA5.3 part 8).**  A revocation is seL4's `cteRevoke`
whatever its subtree holds: the source's first child deleted and finalised until
none is left (`revokeFirstChildLoop`), each step a finalising delete
(`cspaceRevokeCdtFinalising_chain`).  Its payoff is the chain's: every page a
destroyed capability recorded is not live afterwards, since each delete clears
its own page and every later one only shrinks roots
(`FinalisingDeleteChain.unmapped`).  The general revocation and its batch
teardown are retired.

**Retire on final delete (`v0.36.132`).**  seL4's `finaliseCap` acts on the
final capability, and for memory it ends the object: a delete that destroys the
final capability to a frame, a page table, an address-space root or an untyped
that records no child retires it after the teardown (`retireFinalObject`,
`Capability/FinalRetire.lean`), the object and the untyped that records it read
before the slot is emptied (`slotRetireTarget`, `slotRetireRecorder`).  The
delete fast path admits only a delete that retires nothing
(`capabilityRetiresNothing`), and every revoke retires through its deletes.

**Finalise before the retire (`v0.36.134`).**  For an endpoint seL4's
`finaliseCap` runs `cancelAllIPC`, and for a notification
`unbindMaybeNotification` then `cancelAllSignals`; the delete runs the same
(`finaliseFinalObject`, `IPC/Operations/CancelAll.lean`) before the retire, so a
busy endpoint or a busy or bound notification is emptied and then retired.  The
finalisation writes threads, endpoints and notifications only, keeping their
kinds and slots (`FinaliseFrame`, `IPC/Invariant/CancelAllFrame.lean`).
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

/-- WS-ZA ZA5.4: `capabilityMappingLive` as compiled: the record's words and the
frame's base are matched where they are read (`mappedPageLiveWords`), so no
`MappedPage` or `Option` is built for a capability whose record has gone stale
(`capabilityMappingLive_eq_words`). -/
@[inline] def capabilityMappingLiveWords (st : SystemState) (cap : Capability) : Bool :=
  if cap.mapped then
    match cap.target with
    | .object frameId =>
      match st.getFrame? frameId with
      | some f => mappedPageLiveWords st cap.mapAsid cap.mapVaddr f.base cap.mapEpoch
      | none => false
    | _ => false
  else false

@[csimp] theorem capabilityMappingLive_eq_words :
    @capabilityMappingLive = @capabilityMappingLiveWords := by
  funext st cap
  unfold capabilityMappingLive capabilityMappingLiveWords capabilityMappedPage
  rw [Capability.mapping]
  by_cases hM : cap.mapped
  · simp only [hM, if_true]
    cases cap.target with
    | object frameId =>
      cases hF : st.getFrame? frameId with
      | none => simp [hF]
      | some f =>
        simp only [hF, Option.map_some]
        exact mappedPageLive_eq_words _ _ _ _ _
    | _ => rfl
  · simp only [hM]
    rfl

-- ============================================================================
-- §2  Page tables: destroying the last capability takes the table out
-- ============================================================================

/-- **The page table a capability names**, if it names one in `st`. -/
@[inline] def capabilityPageTable (st : SystemState) (cap : Capability) : Option SeLe4n.ObjId :=
  match cap.target with
  | .object id => if (st.getPageTable? id).isSome then some id else none
  | _ => none

/-- **The page table whose final capability `addr` holds**, at most one, read
before a destroying step empties the slot: the table the capability names, when
the capability is final (`SystemState.capIsFinal`, seL4's `isFinalCapability`,
read from the slot's four derivation links).  That is the candidate for its
page-table teardown, as seL4's `finaliseCap` acts on the capability being
destroyed when it is the last one naming its object; a table another slot still
names stays where it is, since that slot's holder can still unmap it.  Equal,
under the capability bundle, to the table when no other slot names it
(`slotPageTables_of_bundle`). -/
@[inline] def slotPageTables (st : SystemState) (addr : CSpaceAddr) : List SeLe4n.ObjId :=
  match (st.slotCapAt addr).bind (capabilityPageTable st) with
  | some id => if st.capIsFinal addr.cnode addr.slot then [id] else []
  | none => []

/-- **The page tables a destroying step orphaned**, each with the install its
root holds: a table whose **final** capability the step destroyed (`named`, read
before the step by `slotPageTables`, which reads finality off the slot's
derivation links), still installed after the step (`pageTableInstallLive`).
That is seL4's `finaliseCap` condition for a page table, and reading it off the
destroyed capabilities, not off a state before the step, is what lets the step
write the store in place.  Each table appears once, however many destroyed
capabilities named it. -/
def pageTablesOrphaned (named : List SeLe4n.ObjId) (st : SystemState) :
    List (SeLe4n.ObjId × PageTableInstall) :=
  named.foldl (init := []) fun acc id =>
    if acc.any (·.1 == id) then acc
    else
      match st.getPageTable? id with
      | some p =>
        match p.installedIn with
        | some inst =>
          if Architecture.pageTableInstallLive st id then
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
      have hK := hW.2.2.2.2.2.2.2.2.2 _ root hObj
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
          (vspaceRootsShrink_of_store hWR.1 hObjR hStore rfl (fun _ _ hm => hm)
            (fun _ _ he => he) (fun s hs => (hTab s hs).1))
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
    have hExtF : Rf.mappings.invExt := (hWF.2.2.2.2.2.2.2.2.2 _ Rf hObjF).1.1
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
          have hK0 : R0.mappings.invExt := (hW.2.2.2.2.2.2.2.2.2 _ R0 h0).1.1
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
        st'.machine = st.machine ∧ st'.referenceTables = st.referenceTables
  | [], st, st', hInv, h => by
      simp only [detachPageTables, Except.ok.injEq, Prod.mk.injEq, true_and] at h
      subst h
      exact ⟨hInv, vspaceRootOnlyWrite.refl _, rfl, rfl, rfl⟩
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
          obtain ⟨hI2, hW2, hS2, hM2, hT2⟩ := detachPageTables_ok_frame rest st1 st' hInv1 h
          refine ⟨hI2, vspaceRootOnlyWrite.trans (fun oid => ?_) hW2,
            hS2.trans (storeObject_scheduler_eq (Architecture.recordPhysicalWrites st (Architecture.detachWrites st root o.2 o.1)) _ _ _ hS),
            hM2.trans (storeObject_machine_eq (Architecture.recordPhysicalWrites st (Architecture.detachWrites st root o.2 o.1)) _ _ _ hS),
            hT2.trans ((storeObject_referenceTables hS).trans rfl)⟩
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
    st'.objects.invExt ∧ vspaceRootOnlyWrite st st' ∧ st'.scheduler = st.scheduler ∧
      st'.referenceTables = st.referenceTables := by
  obtain ⟨st1, hD, hF⟩ := finaliseDestroyedCapabilities_ok ec named pages st st' h
  obtain ⟨hI1, hW1, hS1, -, hT1⟩ := detachPageTables_ok_frame _ st st1 hObjInv hD
  obtain ⟨hI2, hW2, hS2, hT2⟩ := unmapLivePages_ok_frame ec _ st1 st' hI1 hF
  exact ⟨hI2, hW1.trans hW2, hS2.trans hS1, hT2.trans hT1⟩

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
`pages`), then the retire of the object it was the final capability to
(`target`, `recorder`, `retireFinalisedObject`: the object finalised, then
retired), all read before the delete by
`cspaceDeleteSlotFinalising`.  Kept out of line so those reads are made before
the delete writes: the state from before the delete is then dead when the
delete runs, and its stores are made in place. -/
@[noinline] def cspaceDeleteThenFinalise (executingCore : Concurrency.CoreId)
    (named : List SeLe4n.ObjId) (pages : List MappedPage) (target recorder : Nat)
    (addr : CSpaceAddr) : Kernel Unit :=
  fun st =>
    match cspaceDeleteSlot addr st with
    | .error e => .error e
    | .ok ((), st1) =>
      match finaliseDestroyedCapabilities executingCore named pages st1 with
      | .error e => .error e
      | .ok ((), st2) => .ok ((), retireFinalisedObject executingCore target recorder st2)

/-- **`.cspaceDelete`: delete the capability in `addr`, then remove the mapping it
records, then retire the object it was the last capability to.**  The page and
the page table the destroyed capability names are read off its slot before the
delete (`slotMappedPages`, `slotPageTables`), and so is the object a final
capability takes with it and the untyped recording that object
(`slotRetireTarget`, `slotRetireRecorder`), as seL4's `cteDelete` decides
`isFinalCapability` before it empties the slot; the delete writes only CNodes
and the CDT, so they are still what that capability named when the teardown
runs, and nothing reads the state from before the delete once it has run. -/
def cspaceDeleteSlotFinalising (executingCore : Concurrency.CoreId) (addr : CSpaceAddr) :
    Kernel Unit :=
  fun st =>
    cspaceDeleteThenFinalise executingCore (slotPageTables st addr)
      (slotMappedPages st addr) (slotRetireTarget st addr.cnode addr.slot)
      (slotRetireRecorder st addr.cnode addr.slot) addr st

/-- What a successful finalising delete is: the delete, then the teardown of the
page the destroyed capability recorded, then the retire. -/
theorem cspaceDeleteSlotFinalising_ok (ec : Concurrency.CoreId) (addr : CSpaceAddr)
    (st st' : SystemState) (h : cspaceDeleteSlotFinalising ec addr st = .ok ((), st')) :
    ∃ st1 st2, cspaceDeleteSlot addr st = .ok ((), st1) ∧
      finaliseDestroyedCapabilities ec (slotPageTables st addr) (slotMappedPages st addr)
        st1 = .ok ((), st2) ∧
      st' = retireFinalisedObject ec (slotRetireTarget st addr.cnode addr.slot)
        (slotRetireRecorder st addr.cnode addr.slot) st2 := by
  unfold cspaceDeleteSlotFinalising cspaceDeleteThenFinalise at h
  cases hD : cspaceDeleteSlot addr st with
  | error e => rw [hD] at h; cases h
  | ok pr =>
    obtain ⟨u, st1⟩ := pr; cases u; rw [hD] at h
    dsimp only at h
    rw [finaliseDestroyedCapabilities_eq_ok_state] at h
    simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at h
    exact ⟨st1, _, rfl, finaliseDestroyedCapabilities_eq_ok_state _ _ _ _, h.symm⟩

/-- Two states whose objects agree off the derivation links hold the same
address-space roots: only CNodes and threads differ, and only in their slot
link words. -/
theorem vspaceRoot_iff_of_agree {st st' : SystemState}
    (h : SystemState.objectsAgreeOffDerivationLinks st' st) (oid : SeLe4n.ObjId) (r : VSpaceRoot) :
    st'.objects[oid]? = some (KernelObject.vspaceRoot r) ↔
      st.objects[oid]? = some (KernelObject.vspaceRoot r) := by
  rcases h oid with hE | ⟨cn, cn', h1, h2, -⟩ | ⟨t, t', h1, h2, -⟩
  · rw [hE]
  · rw [h1, h2]; simp
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
  obtain ⟨o, hO, hH, hS⟩ := cspaceDeleteSlotCore_ok hC
  have hNR : ∀ r, o.removeSlotCap addr.slot ≠ .vspaceRoot r := by
    intro r h; cases o <;> simp_all [KernelObject.holdsSlots, KernelObject.removeSlotCap]
  have hNR0 : ∀ r, o ≠ .vspaceRoot r := by
    intro r h; subst h; simp [KernelObject.holdsSlots] at hH
  refine teardownWellFormed_of_roots_eq
    (storeObject_preserves_objects_invExt st _ _ _ hW.1 hS) ?_ (fun oid r => ?_) hW
  · rw [storeObject_asidTable_non_vspaceRoot st _ _ _ hNR hS, hO]
    cases o <;> simp_all [KernelObject.holdsSlots]
  · by_cases hK : oid = addr.cnode
    · subst hK
      rw [storeObject_objects_eq st _ _ _ hW.1 hS, hO]
      simp only [Option.some.injEq]
      exact ⟨fun h => absurd h (hNR r), fun h => absurd h (hNR0 r)⟩
    · rw [storeObject_objects_ne st _ _ oid _ hK hW.1 hS]

/-- **The delete keeps the teardown's state well formed.** -/
theorem cspaceDeleteSlot_preserves_teardownWellFormed {addr : CSpaceAddr} {st st' : SystemState}
    (hW : teardownWellFormed st) (h : cspaceDeleteSlot addr st = .ok ((), st')) :
    teardownWellFormed st' := by
  obtain ⟨stC, hC, rfl⟩ := cspaceDeleteSlot_ok_decompose addr st st' h
  exact teardownWellFormed_of_linkReach (spliceDeletedCdtNode_reach stC addr)
    (teardownWellFormed_of_tables_eq (st := stC) rfl rfl
      (cspaceDeleteSlotCore_preserves_teardownWellFormed hW hC))

/-- **The payoff: no mapping the deleted capability recorded survives it.**  On
a well-formed state, if the capability in `addr` recorded a mapping of a frame,
that frame's page is not mapped at the recorded address in the post-state. -/
theorem cspaceDeleteSlotFinalising_ok_unmapped (ec : Concurrency.CoreId) (addr : CSpaceAddr)
    (st st' : SystemState) (hW : teardownWellFormed st)
    (h : cspaceDeleteSlotFinalising ec addr st = .ok ((), st'))
    (cap : Capability) (hCap : st.slotCapAt addr = some cap)
    (p : MappedPage) (hP : capabilityMappedPage st cap = some p) :
    mappedPageLive st' p = false := by
  obtain ⟨_, st2, hD, hF, rfl⟩ := cspaceDeleteSlotFinalising_ok ec addr st st' h
  have hW1 := cspaceDeleteSlot_preserves_teardownWellFormed hW hD
  have hW2 := finaliseDestroyedCapabilities_ok_wellFormed ec _ _ _ st2 hW1 hF
  refine mappedPageLive_false_of_shrink hW2
    (retireFinalisedObject_preserves_teardownWellFormed ec _ _ st2 hW2).2
    (finaliseDestroyedCapabilities_ok_unmapped ec _ _ _ st2 hW1 hF p ?_)
  simp [slotMappedPages, hCap, hP]

/-- **The finalising delete keeps the teardown's state well formed.** -/
theorem cspaceDeleteSlotFinalising_preserves_teardownWellFormed (ec : Concurrency.CoreId)
    {addr : CSpaceAddr} {st st' : SystemState} (hW : teardownWellFormed st)
    (h : cspaceDeleteSlotFinalising ec addr st = .ok ((), st')) : teardownWellFormed st' := by
  obtain ⟨_, st2, hD, hF, rfl⟩ := cspaceDeleteSlotFinalising_ok ec addr st st' h
  exact (retireFinalisedObject_preserves_teardownWellFormed ec _ _ st2
    (finaliseDestroyedCapabilities_ok_wellFormed ec _ _ _ st2
      (cspaceDeleteSlot_preserves_teardownWellFormed hW hD) hF)).1

/-- **A capability whose destruction finalises nothing**: it records no mapping
and names no page table, so destroying it leaves every address space as it is
(seL4's `finaliseCap` on such a capability does no work). -/
@[inline] def capabilityFinalisesNothing (st : SystemState) (cap : Capability) : Bool :=
  cap.mapping.isNone &&
    (match cap.target with
     | .object id => (st.getPageTable? id).isNone
     | _ => true)

/-- WS-ZA ZA5.3: **a finalising delete's checks**, read before any write: the
address names an object that holds slots (a CNode, a thread), and the slot's
capability, if any, finalises nothing and retires nothing
(`capabilityRetiresNothing`: it is not the final capability to a memory
object).  An admitted delete is its two writes
(`cspaceDeleteSlotFinalising_of_admitted`). -/
@[inline] def cspaceDeleteAdmitted (addr : CSpaceAddr) (st : SystemState) : Bool :=
  match st.getObject? addr.cnode with
  | some o =>
    o.holdsSlots &&
      (match o.slotCap addr.slot with
       | some cap =>
         capabilityFinalisesNothing st cap && capabilityRetiresNothing st addr.cnode addr.slot cap
       | none => true)
  | none => false

/-- The thread arm of the compiled `cspaceDeleteAdmitted`, out of line, on the
address's two words. -/
@[noinline] def threadSlotDeleteAdmitted (tcbId : SeLe4n.ObjId) (slot : SeLe4n.Slot)
    (st : SystemState) : Bool :=
  match st.getObject? tcbId with
  | some (.tcb t) =>
    match t.spaceSlotCap slot with
    | some cap => capabilityFinalisesNothing st cap && capabilityRetiresNothing st tcbId slot cap
    | none => true
  | _ => false

/-- `cspaceDeleteAdmitted` as compiled: the CNode arm inline, as before a
thread's slots joined it. -/
@[inline] def cspaceDeleteAdmittedImpl (addr : CSpaceAddr) (st : SystemState) : Bool :=
  match st.getCNode? addr.cnode with
  | some cn =>
    match cn.lookup addr.slot with
    | some cap =>
      capabilityFinalisesNothing st cap && capabilityRetiresNothing st addr.cnode addr.slot cap
    | none => true
  | none => threadSlotDeleteAdmitted addr.cnode addr.slot st

@[csimp] theorem cspaceDeleteAdmitted_eq_impl : @cspaceDeleteAdmitted = @cspaceDeleteAdmittedImpl := by
  funext addr st
  unfold cspaceDeleteAdmitted cspaceDeleteAdmittedImpl threadSlotDeleteAdmitted
  cases hO : st.objects[addr.cnode]? with
  | none => simp [SystemState.getObject?, SystemState.getCNode?, hO]
  | some o =>
    cases o <;> simp [SystemState.getObject?, SystemState.getCNode?, hO, KernelObject.holdsSlots,
      KernelObject.slotCap]

/-- WS-ZA ZA5.3: **an admitted delete's writes**: the slot emptied where its
object stands (`slotCleared`), then spliced out of the derivation tree
(`spliceDeletedCdtNode`). -/
@[inline] def cspaceDeletePerform (addr : CSpaceAddr) (st : SystemState) : SystemState :=
  spliceDeletedCdtNode (slotCleared addr st) addr

/-- A finalisation of nothing is the identity. -/
theorem finaliseDestroyedCapabilities_nil (ec : Concurrency.CoreId) (st : SystemState) :
    finaliseDestroyedCapabilities ec [] [] st = .ok ((), st) := by
  simp [finaliseDestroyedCapabilities, pageTablesOrphaned, detachPageTables,
    orphanedTableMappings, unmapLivePages]

/-- WS-ZA ZA5.3: an admitted finalising delete is its writes. -/
theorem cspaceDeleteSlotFinalising_of_admitted {ec : Concurrency.CoreId} {addr : CSpaceAddr}
    {st : SystemState} (h : cspaceDeleteAdmitted addr st = true) :
    cspaceDeleteSlotFinalising ec addr st = .ok ((), cspaceDeletePerform addr st) := by
  unfold cspaceDeleteAdmitted SystemState.getObject? at h
  cases hO : st.objects[addr.cnode]? with
  | none => rw [hO] at h; cases h
  | some o =>
    rw [hO] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨hH, h⟩ := h
    have hLk : st.slotCapAt addr = o.slotCap addr.slot := SystemState.slotCapAt_of_object hO
    have hNamed : slotPageTables st addr = [] ∧ slotMappedPages st addr = [] ∧
        slotRetireTarget st addr.cnode addr.slot = 0 := by
      cases hC : o.slotCap addr.slot with
      | none =>
        refine ⟨by simp [slotPageTables, hLk, hC],
          by simp [slotMappedPages, hLk, hC], slotRetireTarget_of_empty ?_⟩
        rw [hLk, hC]
      | some cap =>
        rw [hC] at h
        simp only [Bool.and_eq_true] at h
        obtain ⟨h, hRet⟩ := h
        simp only [capabilityFinalisesNothing, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
        obtain ⟨hM, hT⟩ := h
        refine ⟨?_, ?_, (slotRetireTarget_eq_zero_iff (by rw [hLk, hC])).mpr hRet⟩
        · cases hTg : cap.target <;> simp_all [slotPageTables, capabilityPageTable]
        · simp [slotMappedPages, hLk, hC, capabilityMappedPage, hM]
    unfold cspaceDeleteSlotFinalising cspaceDeleteThenFinalise
    rw [hNamed.1, hNamed.2.1, hNamed.2.2]
    have hDel : cspaceDeleteSlot addr st = .ok ((), cspaceDeletePerform addr st) := by
      unfold cspaceDeleteSlot cspaceDeletePerform
      rw [cspaceDeleteSlotCore_eq_slotCleared hO hH]
    simp only [hDel, finaliseDestroyedCapabilities_nil, retireFinalisedObject_zero]

/-- WS-ZA ZA5.3 part 7: **a finalising delete's one check**, read before any
write: the address names an object that holds slots, a CNode or a thread.
Nothing else can refuse a finalising delete: the delete itself refuses only for
such a missing object, and the teardown never refuses
(`finaliseDestroyedCapabilities_eq_ok_state`).  The revocation loop asks it of
each child; a user's delete asks the CNode-only `cnodeInvoked` first. -/
@[inline] def cspaceDeleteFinalisingAdmitted (addr : CSpaceAddr) (st : SystemState) : Bool :=
  match st.getObject? addr.cnode with
  | some o => o.holdsSlots
  | none => false

/-- A CNode invocation's object holds slots, so its delete is admitted. -/
theorem cspaceDeleteFinalisingAdmitted_of_cnodeInvoked {addr : CSpaceAddr} {st : SystemState}
    (h : cnodeInvoked addr.cnode st = true) : cspaceDeleteFinalisingAdmitted addr st = true := by
  unfold cnodeInvoked SystemState.getCNode? at h
  unfold cspaceDeleteFinalisingAdmitted SystemState.getObject?
  cases hO : st.objects[addr.cnode]? with
  | none => rw [hO] at h; cases h
  | some o => rw [hO] at h; cases o <;> simp_all [KernelObject.holdsSlots]

/-- **A delete that finalises something**: what the capability in slot `slot`
of `cnode` names and records, and what it retires, is read first, then the slot
is emptied and spliced out, then the teardown of what it named, then the
retire.  Out of line, so the plain delete builds neither the slot's address nor
the lists. -/
@[noinline] def cspaceDeleteTeardownAt (executingCore : Concurrency.CoreId)
    (cnode : SeLe4n.ObjId) (slot : SeLe4n.Slot) (st : SystemState) : SystemState :=
  let addr : CSpaceAddr := ⟨cnode, slot⟩
  let named := slotPageTables st addr
  let pages := slotMappedPages st addr
  let target := slotRetireTarget st cnode slot
  let recorder := recorderFor st target cnode slot
  retireFinalisedObject executingCore target recorder
    (finaliseDestroyedCapabilitiesState executingCore named pages (cspaceDeletePerform addr st))

/-- `cspaceDeletePerform` on slot `slot` of `cnode`: the dispatcher hands the
step the slot's two words, so no address record is built (WS-ZA ZA5.3 part 6). -/
def cspaceDeletePerformAt (cnode : SeLe4n.ObjId) (slot : SeLe4n.Slot) (st : SystemState) :
    SystemState :=
  cspaceDeletePerform ⟨cnode, slot⟩ st

/-- WS-ZA ZA5.4: **`cspaceDeleteTeardownAt` for a frame's capability**, on the
record's words: the capability's mapping record, its frame's base and what the
delete retires are read before the delete, then the slot is emptied, then the
one page is unmapped if the capability recorded one and it is still live
(`mappedPageLiveWords`), then the frame is retired if the capability was its
last (`retireFinalisedObject`, whose finalisation does nothing to a frame).  A frame names no page table, so the table pass has
nothing to do and no list, page record or slot address is built.  Any other
capability takes `cspaceDeleteTeardownAt` (`cspaceDeleteTeardownAt_eq_frame`). -/
@[noinline] def cspaceDeleteTeardownAtFrame (executingCore : Concurrency.CoreId)
    (cnode : SeLe4n.ObjId) (slot : SeLe4n.Slot) (st : SystemState) : SystemState :=
  match st.slotCapAt ⟨cnode, slot⟩ with
  | some cap =>
    match cap.target with
    | .object frameId =>
      match st.getFrame? frameId with
      | some f =>
        let target := slotRetireTarget st cnode slot
        let recorder := recorderFor st target cnode slot
        let st1 := cspaceDeletePerformAt cnode slot st
        retireFinalisedObject executingCore target recorder
          (match cap.mapping with
           | some m =>
             if mappedPageLiveWords st1 m.asid m.vaddr f.base m.epoch then
               unmapPageState executingCore m.asid m.vaddr st1
             else st1
           | none => st1)
      | none =>
        if (st.getPageTable? frameId).isSome then
          cspaceDeleteTeardownAt executingCore cnode slot st
        else
          let target := slotRetireTarget st cnode slot
          let recorder := recorderFor st target cnode slot
          retireFinalisedObject executingCore target recorder (cspaceDeletePerformAt cnode slot st)
    | _ =>
      let target := slotRetireTarget st cnode slot
      let recorder := recorderFor st target cnode slot
      retireFinalisedObject executingCore target recorder (cspaceDeletePerformAt cnode slot st)
  | none =>
    let target := slotRetireTarget st cnode slot
    let recorder := recorderFor st target cnode slot
    retireFinalisedObject executingCore target recorder (cspaceDeletePerformAt cnode slot st)

/-- A teardown of nothing is the identity. -/
theorem finaliseDestroyedCapabilitiesState_nil (ec : Concurrency.CoreId) (st : SystemState) :
    finaliseDestroyedCapabilitiesState ec [] [] st = st := by
  simp [finaliseDestroyedCapabilitiesState, pageTablesOrphaned, detachPageTablesState,
    orphanedTableMappings, unmapLivePagesState]

/-- **A teardown with nothing to tear down**: when the slot's capability names
no page table and records no page, `cspaceDeleteTeardownAt` is the delete then
the retire, with no list and no slot address built. -/
theorem cspaceDeleteTeardownAt_of_nothing (ec : Concurrency.CoreId) (cnode : SeLe4n.ObjId)
    (slot : SeLe4n.Slot) (st : SystemState)
    (hNamed : slotPageTables st ⟨cnode, slot⟩ = [])
    (hPages : slotMappedPages st ⟨cnode, slot⟩ = []) :
    cspaceDeleteTeardownAt ec cnode slot st =
      retireFinalisedObject ec (slotRetireTarget st cnode slot)
        (recorderFor st (slotRetireTarget st cnode slot) cnode slot)
        (cspaceDeletePerformAt cnode slot st) := by
  unfold cspaceDeleteTeardownAt
  dsimp only
  rw [hNamed, hPages, finaliseDestroyedCapabilitiesState_nil]
  rfl

theorem cspaceDeleteTeardownAt_eq_frame :
    @cspaceDeleteTeardownAt = @cspaceDeleteTeardownAtFrame := by
  funext ec cnode slot st
  unfold cspaceDeleteTeardownAtFrame
  cases hL : st.slotCapAt ⟨cnode, slot⟩ with
  | none =>
    exact cspaceDeleteTeardownAt_of_nothing ec cnode slot st
      (by simp [slotPageTables, hL]) (by simp [slotMappedPages, hL])
  | some cap =>
    dsimp only
    cases hT : cap.target with
    | cnodeSlot _ _ =>
      refine cspaceDeleteTeardownAt_of_nothing ec cnode slot st ?_ ?_
      · simp [slotPageTables, hL, capabilityPageTable, hT]
      · cases hM : cap.mapping <;> simp [slotMappedPages, hL, capabilityMappedPage, hT, hM]
    | replyCap _ =>
      refine cspaceDeleteTeardownAt_of_nothing ec cnode slot st ?_ ?_
      · simp [slotPageTables, hL, capabilityPageTable, hT]
      · cases hM : cap.mapping <;> simp [slotMappedPages, hL, capabilityMappedPage, hT, hM]
    | auditTrail =>
      refine cspaceDeleteTeardownAt_of_nothing ec cnode slot st ?_ ?_
      · simp [slotPageTables, hL, capabilityPageTable, hT]
      · cases hM : cap.mapping <;> simp [slotMappedPages, hL, capabilityMappedPage, hT, hM]
    | object frameId =>
      dsimp only
      cases hF : st.getFrame? frameId with
      | none =>
        dsimp only
        cases hPT : (st.getPageTable? frameId).isSome with
        | true => rfl
        | false =>
          refine cspaceDeleteTeardownAt_of_nothing ec cnode slot st ?_ ?_
          · simp [slotPageTables, hL, capabilityPageTable, hT, hPT]
          · cases hM : cap.mapping <;>
              simp [slotMappedPages, hL, capabilityMappedPage, hT, hF, hM]
      | some f =>
        dsimp only
        have hPT : st.getPageTable? frameId = none := by
          unfold SystemState.getFrame? at hF
          unfold SystemState.getPageTable?
          cases hO : st.objects[frameId]? with
          | none => rfl
          | some o => rw [hO] at hF; cases o <;> simp_all
        have hNamed : slotPageTables st ⟨cnode, slot⟩ = [] := by
          simp [slotPageTables, hL, capabilityPageTable, hT, hPT]
        unfold cspaceDeleteTeardownAt
        dsimp only
        rw [hNamed]
        cases hM : cap.mapping with
        | none =>
          have hPages : slotMappedPages st ⟨cnode, slot⟩ = [] := by
            simp [slotMappedPages, hL, capabilityMappedPage, hM]
          rw [hPages, finaliseDestroyedCapabilitiesState_nil]
          rfl
        | some m =>
          have hPages : slotMappedPages st ⟨cnode, slot⟩ =
              [{ asid := m.asid, vaddr := m.vaddr, paddr := f.base, epoch := some m.epoch }] := by
            simp [slotMappedPages, hL, capabilityMappedPage, hM, hT, hF]
          rw [hPages]
          dsimp only
          simp only [finaliseDestroyedCapabilitiesState, pageTablesOrphaned, List.foldl_nil,
            orphanedTableMappings, List.flatMap_nil, List.append_nil, detachPageTablesState,
            unmapLivePagesState, cspaceDeletePerformAt, mappedPageLive_eq_words]

/-- WS-ZA ZA5.4: **`cspaceDeleteTeardownAt` for a page table's capability**, on
the slot's words: the capability names the table and records no page.  When it
is the table's final capability (`SystemState.capIsFinal`, read from the slot's
four derivation links before the delete), the slot is emptied and the table is
taken out of its root only if it is still installed there after the delete
(`pageTablesOrphaned`); a capability that is not final, or a table installed
nowhere, leaves nothing to finalise.  Then the table is retired if the
capability was its last (`retireFinalisedObject`, whose finalisation does nothing
to a page table).  No list or slot address is
built.  Any other capability takes `cspaceDeleteTeardownAtFrame`
(`cspaceDeleteTeardownAt_eq_table`). -/
@[noinline] def cspaceDeleteTeardownAtTable (executingCore : Concurrency.CoreId)
    (cnode : SeLe4n.ObjId) (slot : SeLe4n.Slot) (st : SystemState) : SystemState :=
  match st.slotCapAt ⟨cnode, slot⟩ with
  | some cap =>
    match cap.target with
    | .object tableId =>
      match st.getPageTable? tableId with
      | some _ =>
        let target := slotRetireTarget st cnode slot
        let recorder := recorderFor st target cnode slot
        retireFinalisedObject executingCore target recorder
          (if st.capIsFinal cnode slot then
            let st1 := cspaceDeletePerformAt cnode slot st
            if Architecture.pageTableInstallLive st1 tableId then
              finaliseDestroyedCapabilitiesState executingCore [tableId] [] st1
            else st1
          else cspaceDeletePerformAt cnode slot st)
      | none => cspaceDeleteTeardownAtFrame executingCore cnode slot st
    | _ => cspaceDeleteTeardownAtFrame executingCore cnode slot st
  | none => cspaceDeleteTeardownAtFrame executingCore cnode slot st

@[csimp] theorem cspaceDeleteTeardownAt_eq_table :
    @cspaceDeleteTeardownAt = @cspaceDeleteTeardownAtTable := by
  funext ec cnode slot st
  unfold cspaceDeleteTeardownAtTable
  rw [← cspaceDeleteTeardownAt_eq_frame]
  cases hL : st.slotCapAt ⟨cnode, slot⟩ with
  | none => rfl
  | some cap =>
    dsimp only
    cases hT : cap.target with
    | cnodeSlot _ _ => rfl
    | replyCap _ => rfl
    | auditTrail => rfl
    | object tableId =>
      dsimp only
      cases hPT : st.getPageTable? tableId with
      | none => rfl
      | some p =>
        dsimp only
        have hF : st.getFrame? tableId = none := by
          unfold SystemState.getPageTable? at hPT
          unfold SystemState.getFrame?
          cases hO : st.objects[tableId]? with
          | none => rfl
          | some o => rw [hO] at hPT; cases o <;> simp_all
        have hPages : slotMappedPages st ⟨cnode, slot⟩ = [] := by
          cases hM : cap.mapping <;> simp [slotMappedPages, hL, capabilityMappedPage, hM, hT, hF]
        unfold cspaceDeleteTeardownAt
        dsimp only
        rw [hPages]
        simp only [cspaceDeletePerformAt]
        congr 1
        cases hFin : st.capIsFinal cnode slot with
        | false =>
          have hNamed : slotPageTables st ⟨cnode, slot⟩ = [] := by
            simp [slotPageTables, hL, capabilityPageTable, hT, hPT, hFin]
          rw [hNamed]
          simp only [Bool.false_eq_true, ↓reduceIte, finaliseDestroyedCapabilitiesState,
            pageTablesOrphaned, List.foldl_nil, orphanedTableMappings, List.flatMap_nil,
            List.append_nil, detachPageTablesState, unmapLivePagesState]
        | true =>
        have hNamed : slotPageTables st ⟨cnode, slot⟩ = [tableId] := by
          simp [slotPageTables, hL, capabilityPageTable, hT, hPT, hFin]
        rw [hNamed]
        simp only [↓reduceIte]
        split
        · rfl
        · next hLive =>
          unfold finaliseDestroyedCapabilitiesState
          have hO : pageTablesOrphaned [tableId] (cspaceDeletePerform ⟨cnode, slot⟩ st) = [] := by
            simp only [pageTablesOrphaned, List.foldl_cons, List.foldl_nil, List.any_nil,
              Bool.false_eq_true, ↓reduceIte]
            split
            · split
              · simp [hLive]
              · rfl
            · rfl
          simp only [hO, orphanedTableMappings, List.flatMap_nil, List.append_nil,
            detachPageTablesState, unmapLivePagesState]

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


/-- The delete, when its address names an object that holds slots, is the slot
emptied and spliced out. -/
theorem cspaceDeleteSlot_of_slotHolder {addr : CSpaceAddr} {st : SystemState}
    (h : cspaceDeleteFinalisingAdmitted addr st = true) :
    cspaceDeleteSlot addr st = .ok ((), cspaceDeletePerform addr st) := by
  unfold cspaceDeleteFinalisingAdmitted SystemState.getObject? at h
  cases hO : st.objects[addr.cnode]? with
  | none => rw [hO] at h; cases h
  | some o =>
    rw [hO] at h
    unfold cspaceDeleteSlot cspaceDeletePerform
    rw [cspaceDeleteSlotCore_eq_slotCleared hO h]

/-- WS-ZA ZA5.3 part 7: **an admitted finalising delete is its writes**, whatever
its capability names. -/
theorem cspaceDeleteSlotFinalising_of_slotHolder {ec : Concurrency.CoreId} {cnode : SeLe4n.ObjId}
    {slot : SeLe4n.Slot} {st : SystemState}
    (h : cspaceDeleteFinalisingAdmitted ⟨cnode, slot⟩ st = true) :
    cspaceDeleteSlotFinalising ec ⟨cnode, slot⟩ st =
      .ok ((), cspaceDeleteFinalisingPerformAt ec cnode slot st) := by
  unfold cspaceDeleteFinalisingPerformAt cspaceDeletePerformAt
  split
  · next hA => exact cspaceDeleteSlotFinalising_of_admitted hA
  · unfold cspaceDeleteSlotFinalising cspaceDeleteThenFinalise cspaceDeleteTeardownAt
    rw [cspaceDeleteSlot_of_slotHolder h]
    dsimp only
    rw [finaliseDestroyedCapabilities_eq_ok_state]
    rfl

-- ============================================================================
-- §4  The finalising revocation
-- ============================================================================

/-- A step that keeps every address-space root it leaves shrinks the roots. -/
theorem vspaceRootsShrink_of_roots {st st' : SystemState}
    (h : ∀ (oid : SeLe4n.ObjId) (r : VSpaceRoot),
      st'.objects[oid]? = some (KernelObject.vspaceRoot r) →
        st.objects[oid]? = some (KernelObject.vspaceRoot r)) :
    vspaceRootsShrink st st' :=
  fun oid r' h' => ⟨r', h oid r' h', rfl, fun _ _ hm => hm, fun _ _ he => he, fun _ hs => hs⟩

/-- **The core delete keeps every address-space root**: it writes a CNode where
a CNode stands. -/
theorem cspaceDeleteSlotCore_shrinks {addr : CSpaceAddr} {st st' : SystemState}
    (hObjInv : st.objects.invExt) (hC : cspaceDeleteSlotCore addr st = .ok ((), st')) :
    vspaceRootsShrink st st' := by
  obtain ⟨o, hO, hH, hS⟩ := cspaceDeleteSlotCore_ok hC
  refine vspaceRootsShrink_of_roots (fun oid r hR => ?_)
  by_cases hK : oid = addr.cnode
  · subst hK
    rw [storeObject_objects_eq st _ _ _ hObjInv hS] at hR
    cases o <;> simp_all [KernelObject.holdsSlots, KernelObject.removeSlotCap]
  · rwa [storeObject_objects_ne st _ _ oid _ hK hObjInv hS] at hR

/-- **The delete keeps every address-space root**: the core delete, then a write
of derivation links. -/
theorem cspaceDeleteSlot_shrinks {addr : CSpaceAddr} {st st' : SystemState}
    (hW : teardownWellFormed st) (h : cspaceDeleteSlot addr st = .ok ((), st')) :
    vspaceRootsShrink st st' := by
  obtain ⟨stC, hC, rfl⟩ := cspaceDeleteSlot_ok_decompose addr st st' h
  have hWC := cspaceDeleteSlotCore_preserves_teardownWellFormed hW hC
  have hR := (spliceDeletedCdtNode_reach stC addr).agree hWC.1
  exact (cspaceDeleteSlotCore_shrinks hW.1 hC).trans
    (vspaceRootsShrink_of_roots (fun oid r h => (vspaceRoot_iff_of_agree hR oid r).1 h))

/-- **The finalisation only shrinks roots**: the table detach, then the unmap
pass. -/
theorem finaliseDestroyedCapabilities_shrinks (ec : Concurrency.CoreId)
    (named : List SeLe4n.ObjId) (pages : List MappedPage) (st st' : SystemState)
    (hW : teardownWellFormed st)
    (h : finaliseDestroyedCapabilities ec named pages st = .ok ((), st')) :
    vspaceRootsShrink st st' := by
  rw [finaliseDestroyedCapabilities_eq_ok_state] at h
  simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at h
  subst h
  obtain ⟨hW1, hS1, -⟩ := detachPageTablesState_wellFormed (pageTablesOrphaned named st) st hW
  exact hS1.trans (unmapLivePagesState_clears ec _ _ hW1).2.1

/-- **The finalising delete only shrinks roots.** -/
theorem cspaceDeleteSlotFinalising_shrinks (ec : Concurrency.CoreId) {addr : CSpaceAddr}
    {st st' : SystemState} (hW : teardownWellFormed st)
    (h : cspaceDeleteSlotFinalising ec addr st = .ok ((), st')) : vspaceRootsShrink st st' := by
  obtain ⟨st1, st2, hD, hF, rfl⟩ := cspaceDeleteSlotFinalising_ok ec addr st st' h
  have hW1 := cspaceDeleteSlot_preserves_teardownWellFormed hW hD
  exact ((cspaceDeleteSlot_shrinks hW hD).trans
    (finaliseDestroyedCapabilities_shrinks ec _ _ st1 st2 hW1 hF)).trans
    (retireFinalisedObject_preserves_teardownWellFormed ec _ _ st2
      (finaliseDestroyedCapabilities_ok_wellFormed ec _ _ _ st2 hW1 hF)).2

/-- **A run of finalising deletes and finalisations**, one after another: what
seL4's `cteRevoke` and `cteDelete`'s zombie loop are made of.  A finalisation
step is the finalisation of a thread the zombie loop reaches before it deletes
the thread's space slots (`zombieFinaliseAt`). -/
inductive FinalisingDeleteChain (ec : Concurrency.CoreId) : SystemState → SystemState → Prop
  | refl (st : SystemState) : FinalisingDeleteChain ec st st
  | step {s1 s2 s3 : SystemState} (c : CSpaceAddr)
      (hD : cspaceDeleteSlotFinalising ec c s1 = .ok ((), s2))
      (hRest : FinalisingDeleteChain ec s2 s3) : FinalisingDeleteChain ec s1 s3
  | finalise {s1 s3 : SystemState} (target : Nat)
      (hRest : FinalisingDeleteChain ec (finaliseFinalObject target s1) s3) :
      FinalisingDeleteChain ec s1 s3

/-- **A chain keeps whatever every finalising delete and every finalisation
keeps.** -/
theorem FinalisingDeleteChain.closed {ec : Concurrency.CoreId} (Q : SystemState → Prop)
    (hStep : ∀ (c : CSpaceAddr) (s s' : SystemState), Q s →
      cspaceDeleteSlotFinalising ec c s = .ok ((), s') → Q s')
    (hFin : ∀ (target : Nat) (s : SystemState), Q s → Q (finaliseFinalObject target s)) :
    ∀ {st st' : SystemState}, FinalisingDeleteChain ec st st' → Q st → Q st'
  | _, _, .refl _, h => h
  | _, _, .step c hD hRest, h =>
    FinalisingDeleteChain.closed Q hStep hFin hRest (hStep c _ _ h hD)
  | _, _, .finalise d hRest, h => FinalisingDeleteChain.closed Q hStep hFin hRest (hFin d _ h)

/-- **Two chains run one after the other are a chain.** -/
theorem FinalisingDeleteChain.trans {ec : Concurrency.CoreId} :
    ∀ {s1 s2 s3 : SystemState}, FinalisingDeleteChain ec s1 s2 → FinalisingDeleteChain ec s2 s3 →
      FinalisingDeleteChain ec s1 s3
  | _, _, _, .refl _, h => h
  | _, _, _, .step c hD hRest, h => .step c hD (hRest.trans h)
  | _, _, _, .finalise d hRest, h => .finalise d (hRest.trans h)

/-- **A chain keeps the teardown's state well formed and only shrinks roots.** -/
theorem FinalisingDeleteChain.wellFormed {ec : Concurrency.CoreId} :
    ∀ {st st' : SystemState}, FinalisingDeleteChain ec st st' → teardownWellFormed st →
      teardownWellFormed st' ∧ vspaceRootsShrink st st'
  | _, _, .refl st, hW => ⟨hW, vspaceRootsShrink.refl st⟩
  | _, _, .step _ hD hRest, hW =>
    have hW1 := cspaceDeleteSlotFinalising_preserves_teardownWellFormed ec hW hD
    have hR := FinalisingDeleteChain.wellFormed hRest hW1
    ⟨hR.1, (cspaceDeleteSlotFinalising_shrinks ec hW hD).trans hR.2⟩
  | _, _, .finalise d hRest, hW =>
    have hF := finaliseFinalObject_preserves_teardownWellFormed d _ hW
    have hR := FinalisingDeleteChain.wellFormed hRest hF.1
    ⟨hR.1, hF.2.trans hR.2⟩

/-- **No page a chain's delete destroyed survives the chain.**  The delete
leaves the page its capability recorded not live
(`cspaceDeleteSlotFinalising_ok_unmapped`), and every later delete only shrinks
roots, so no later step brings it back (`mappedPageLive_false_of_shrink`). -/
theorem FinalisingDeleteChain.unmapped {ec : Concurrency.CoreId} {s s2 st' : SystemState}
    {c : CSpaceAddr} (hW : teardownWellFormed s)
    (hD : cspaceDeleteSlotFinalising ec c s = .ok ((), s2))
    (hRest : FinalisingDeleteChain ec s2 st')
    (cap : Capability) (hCap : s.slotCapAt c = some cap)
    (p : MappedPage) (hP : capabilityMappedPage s cap = some p) :
    mappedPageLive st' p = false := by
  have hW2 := cspaceDeleteSlotFinalising_preserves_teardownWellFormed ec hW hD
  exact mappedPageLive_false_of_shrink hW2 (hRest.wellFormed hW2).2
    (cspaceDeleteSlotFinalising_ok_unmapped ec c s s2 hW hD cap hCap p hP)

-- ============================================================================
-- §4a  The zombie loop: the final delete of an object that holds capabilities
-- ============================================================================

/-- **The slot of `o` a final delete empties next**, as a code (`k + 1` for slot
`k`, `0` when `o` holds no capability past `skip`), passing over the slot whose
code is `skip` (`0` passes over none): a CNode's most recently filled occupied
slot, the head of its occupancy links (`CNode.occHead`), or the one linked after
it when the head is `skip`; a thread's CSpace root slot, then its VSpace root
slot.  The one place the order is chosen: seL4's zombie empties a CNode from its
highest slot down, and this loop empties the most recently filled first, the
order the occupancy links give without a scan (decided by Adam on the ZA5.4
thread, card, 2026-10-25: "list order"). -/
@[inline] def zombieNextSlot (o : KernelObject) (skip : Nat) : Nat :=
  match o with
  | .cnode cn =>
    if skip != 0 && cn.occHead == skip then SlotOccupancy.nextWord cn.occ (cn.occHead - 1)
    else cn.occHead
  | .tcb t =>
    if t.spaceCells[0].isSome && skip != 1 then 1
    else if t.spaceCells[1].isSome && skip != 2 then 2 else 0
  | _ => 0

/-- An object with a slot left to empty holds slots. -/
theorem holdsSlots_of_zombieNextSlot {o : KernelObject} {skip : Nat}
    (h : zombieNextSlot o skip ≠ 0) : o.holdsSlots = true := by
  cases o <;> first | rfl | exact absurd rfl h

/-- **Whether a thread the loop reaches is finalised**: its own record quiescent
but for its space slots (`threadLinksQuiescent`) and held by no core, so its
space slots are what is left to delete. -/
@[inline] def zombieThreadFinalised (st : SystemState) (t : TCB) : Bool :=
  threadLinksQuiescent t && !threadHeldOnSomeCore st t.tid

/-- The code of the loop's own slot, `rootSlot` of `root`, inside the object
`x`: passed over when the loop empties `x`. -/
@[inline] def zombieSkip (root : SeLe4n.ObjId) (rootSlot : SeLe4n.Slot) (x : SeLe4n.ObjId) : Nat :=
  if x == root then rootSlot.toNat + 1 else 0

/-- **What the zombie loop does at slot `slot` of `cnode`**, as a code: `0`, the
slot is a leaf, emptied by one finalising delete (its capability is not final,
or what it names holds no capability); `1`, its final capability names a thread
not yet finalised, which is finalised first; `k + 2`, its final capability names
an object holding a capability in slot `k` (`zombieNextSlot`), visited next.
The loop's own slot (`rootSlot` of `root`) is passed over. -/
@[inline] def zombieSlotClass (st : SystemState) (root : SeLe4n.ObjId) (rootSlot : SeLe4n.Slot)
    (cnode : SeLe4n.ObjId) (slot : SeLe4n.Slot) : Nat :=
  let d := slotRetireTarget st cnode slot
  if d = 0 then 0
  else
    let x := SeLe4n.ObjId.ofNat (d - 1)
    match st.getObject? x with
    | some o =>
      let k := zombieNextSlot o (zombieSkip root rootSlot x)
      if k = 0 then 0
      else
        match o with
        | .tcb t => if zombieThreadFinalised st t then k + 1 else 1
        | _ => k + 1
    | none => 0

/-- **One finalising delete of slot `slot` of `cnode`**, when an object holding
slots stands there (`cspaceDeleteFinalisingAdmitted`); nothing otherwise. -/
@[inline] def zombieDeleteSlot (executingCore : Concurrency.CoreId) (cnode : SeLe4n.ObjId)
    (slot : SeLe4n.Slot) (st : SystemState) : SystemState :=
  if cspaceDeleteFinalisingAdmitted ⟨cnode, slot⟩ st then
    cspaceDeleteFinalisingPerformAt executingCore cnode slot st
  else st

/-- **The thread the final capability in slot `slot` of `cnode` names,
finalised** (`finaliseFinalObject`, seL4's `finaliseCap` before its zombie's
slots are emptied); if that leaves it unfinalised (`zombieThreadFinalised`), the
slot is deleted, as the delete of a thread the finalisation refuses is. -/
@[inline] def zombieFinaliseAt (executingCore : Concurrency.CoreId) (cnode : SeLe4n.ObjId)
    (slot : SeLe4n.Slot) (st : SystemState) : SystemState :=
  let d := slotRetireTarget st cnode slot
  let st1 := finaliseFinalObject d st
  match st1.getObject? (SeLe4n.ObjId.ofNat (d - 1)) with
  | some (.tcb t) =>
    if zombieThreadFinalised st1 t then st1 else zombieDeleteSlot executingCore cnode slot st1
  | _ => zombieDeleteSlot executingCore cnode slot st1

/-- **How many slots of the object at `x` the loop may empty in one pass**: a
CNode's slot count, a thread's two. -/
@[inline] def zombieObjectSlots (st : SystemState) (x : SeLe4n.ObjId) : Nat :=
  match st.getObject? x with
  | some (.cnode cn) => cn.cells.size
  | some (.tcb _) => 2
  | _ => 0

/-- **Empty the object at `x`'s leaf slots**, each by one finalising delete, the
next slot chosen by `zombieNextSlot`, until it holds no capability or its next
slot is no leaf; at most `fuel` of them. -/
def zombieEmptyObject (executingCore : Concurrency.CoreId) (root : SeLe4n.ObjId)
    (rootSlot : SeLe4n.Slot) (x : SeLe4n.ObjId) : Nat → SystemState → SystemState
  | 0, st => st
  | n + 1, st =>
    match st.getObject? x with
    | some o =>
      let k := zombieNextSlot o (zombieSkip root rootSlot x)
      if k = 0 then st
      else if zombieSlotClass st root rootSlot x (SeLe4n.Slot.ofNat (k - 1)) = 0 then
        zombieEmptyObject executingCore root rootSlot x n
          (zombieDeleteSlot executingCore x (SeLe4n.Slot.ofNat (k - 1)) st)
      else st
    | none => st

/-- **One pass of the loop, from slot `slot` of `cnode`, whose class is `cls`**
(`zombieSlotClass`): a leaf is deleted; a thread not yet finalised is
finalised; otherwise the pass goes down to the object the slot's final
capability names, at the slot `zombieNextSlot` chooses, and when that slot is a
leaf it empties that object (`zombieEmptyObject`).  A tail call, so the pass
runs in constant stack whatever the nesting; `depth` bounds the way down. -/
def zombieDescend (executingCore : Concurrency.CoreId) (root : SeLe4n.ObjId)
    (rootSlot : SeLe4n.Slot) : Nat → SeLe4n.ObjId → SeLe4n.Slot → Nat → SystemState → SystemState
  | 0, cnode, slot, _, st => zombieDeleteSlot executingCore cnode slot st
  | depth + 1, cnode, slot, cls, st =>
    if cls = 0 then zombieDeleteSlot executingCore cnode slot st
    else if cls = 1 then zombieFinaliseAt executingCore cnode slot st
    else
      let x := SeLe4n.ObjId.ofNat (slotRetireTarget st cnode slot - 1)
      let s := SeLe4n.Slot.ofNat (cls - 2)
      let j := zombieSlotClass st root rootSlot x s
      if j = 0 then zombieEmptyObject executingCore root rootSlot x (zombieObjectSlots st x) st
      else zombieDescend executingCore root rootSlot depth x s j st

/-- **The way down's bound**: the objects a pass passes through are distinct, so
no more than the store holds. -/
@[inline] def zombieDepth (st : SystemState) : Nat := st.objects.size + 1

/-- **The loop's bound on its passes**: `3 · n + 2` for a store of `n` objects.
Each pass but the last ends with the object it empties holding no capability,
with that object's next slot naming an object holding capabilities (which a
later pass empties first), or with a thread finalised; an object is emptied
once and a thread finalised once, so `2 · n + n` passes and the root's own
delete suffice. -/
@[inline] def zombieFuel (st : SystemState) : Nat := 3 * st.objects.size + 2

/-- **seL4's `finaliseSlot` loop**, from the loop's own slot `rootSlot` of
`root`: while the slot's final capability names an object that still holds
capabilities, one pass (`zombieDescend`) empties the deepest object it reaches
or finalises a thread.  The capability stays in its slot all the while, as
seL4's Zombie does, and each pass starts again from the slots, not from
anything the last pass kept, so a preemption point drops in between passes as a
return and a restart of the call.  At most `fuel` passes; the slot itself is
deleted after them (`zombieDeleteAt`). -/
def zombiePasses (executingCore : Concurrency.CoreId) (root : SeLe4n.ObjId)
    (rootSlot : SeLe4n.Slot) : Nat → SystemState → SystemState
  | 0, st => st
  | n + 1, st =>
    let cls := zombieSlotClass st root rootSlot root rootSlot
    if cls = 0 then st
    else
      zombiePasses executingCore root rootSlot n
        (zombieDescend executingCore root rootSlot (zombieDepth st) root rootSlot cls st)

/-- **The zombie loop's passes on slot `slot` of `cnode`, then the slot's own
delete**, with at most `fuel` passes: when the passes end with the slot's final
capability naming nothing that holds a capability (`zombieSlotClass` zero), the
slot is deleted by the finalising delete that retires what it named; when the
fuel runs out first, the slot is **kept** — its capability stays in place and
the root delete makes no write, the passes already run persist (each a
`FinalisingDeleteChain`), and a caller sees the slot still occupied and retries,
the retry continuing from the slots as they stand, as seL4's preempted
`cteDelete` leaves its Zombie in the slot and is restarted.  On the fuel
`zombieDeleteAt` gives it the slot is never kept on a reachable state; that the
fuel always suffices is `docs/planning/UNTYPED_RESET_PLAN.md` row 35
(`docs/REGISTERED_DEBT.md`, "The zombie fuel always suffices on a reachable
state").  The fuel is a parameter so a test can drive the kept branch. -/
def zombieDeleteAtFuel (executingCore : Concurrency.CoreId) (cnode : SeLe4n.ObjId)
    (slot : SeLe4n.Slot) (fuel : Nat) (st : SystemState) : SystemState :=
  let s := zombiePasses executingCore cnode slot fuel st
  if zombieSlotClass s cnode slot cnode slot = 0 then zombieDeleteSlot executingCore cnode slot s
  else s

/-- **A final delete of slot `slot` of `cnode`, emptying what it destroys**
(seL4's `cteDelete`): a capability that finalises and retires nothing is the
slot emptied and spliced out (`cspaceDeletePerformAt`); any other has the zombie
loop's passes run on it, at most `zombieFuel`, then the slot is deleted by the
finalising delete that retires what its capability named, or kept when the
passes have not ended (`zombieDeleteAtFuel`). -/
@[inline] def zombieDeleteAt (executingCore : Concurrency.CoreId) (cnode : SeLe4n.ObjId)
    (slot : SeLe4n.Slot) (st : SystemState) : SystemState :=
  if cspaceDeleteAdmitted ⟨cnode, slot⟩ st then cspaceDeletePerformAt cnode slot st
  else zombieDeleteAtFuel executingCore cnode slot (zombieFuel st) st

/-- **`.cspaceDelete`: seL4's `cteDelete`**: when an object holding slots stands
at the address (`cspaceDeleteFinalisingAdmitted`), the zombie delete of its slot
(`zombieDeleteAt`); otherwise the finalising delete's refusal. -/
def cspaceDeleteSlotZombie (executingCore : Concurrency.CoreId) (addr : CSpaceAddr) :
    Kernel Unit :=
  fun st =>
    if cspaceDeleteFinalisingAdmitted addr st then
      .ok ((), zombieDeleteAt executingCore addr.cnode addr.slot st)
    else cspaceDeleteSlotFinalising executingCore addr st

/-- **One slot's delete is a chain**: one finalising delete, or nothing. -/
theorem zombieDeleteSlot_chain (ec : Concurrency.CoreId) (cnode : SeLe4n.ObjId)
    (slot : SeLe4n.Slot) (st : SystemState) :
    FinalisingDeleteChain ec st (zombieDeleteSlot ec cnode slot st) := by
  unfold zombieDeleteSlot
  split
  · next hA => exact .step _ (cspaceDeleteSlotFinalising_of_slotHolder hA) (.refl _)
  · exact .refl st

/-- **A thread's finalisation in the loop is a chain**: the finalisation, then
at most one delete. -/
theorem zombieFinaliseAt_chain (ec : Concurrency.CoreId) (cnode : SeLe4n.ObjId)
    (slot : SeLe4n.Slot) (st : SystemState) :
    FinalisingDeleteChain ec st (zombieFinaliseAt ec cnode slot st) := by
  unfold zombieFinaliseAt
  dsimp only
  refine .finalise (slotRetireTarget st cnode slot) ?_
  split
  · split
    · exact .refl _
    · exact zombieDeleteSlot_chain ec cnode slot _
  · exact zombieDeleteSlot_chain ec cnode slot _

/-- **Emptying an object is a chain** of finalising deletes. -/
theorem zombieEmptyObject_chain (ec : Concurrency.CoreId) (root : SeLe4n.ObjId)
    (rootSlot : SeLe4n.Slot) (x : SeLe4n.ObjId) :
    ∀ (n : Nat) (st : SystemState),
      FinalisingDeleteChain ec st (zombieEmptyObject ec root rootSlot x n st)
  | 0, st => .refl st
  | n + 1, st => by
    unfold zombieEmptyObject
    split
    · dsimp only
      split
      · exact .refl st
      · split
        · exact (zombieDeleteSlot_chain ec x _ st).trans
            (zombieEmptyObject_chain ec root rootSlot x n _)
        · exact .refl st
    · exact .refl st

/-- **A pass is a chain** of finalising deletes and finalisations. -/
theorem zombieDescend_chain (ec : Concurrency.CoreId) (root : SeLe4n.ObjId)
    (rootSlot : SeLe4n.Slot) :
    ∀ (depth : Nat) (cnode : SeLe4n.ObjId) (slot : SeLe4n.Slot) (cls : Nat) (st : SystemState),
      FinalisingDeleteChain ec st (zombieDescend ec root rootSlot depth cnode slot cls st)
  | 0, cnode, slot, _, st => zombieDeleteSlot_chain ec cnode slot st
  | depth + 1, cnode, slot, cls, st => by
    unfold zombieDescend
    split
    · exact zombieDeleteSlot_chain ec cnode slot st
    · split
      · exact zombieFinaliseAt_chain ec cnode slot st
      · dsimp only
        split
        · exact zombieEmptyObject_chain ec root rootSlot _ _ st
        · exact zombieDescend_chain ec root rootSlot depth _ _ _ st

/-- **The loop's passes, counted**: a run of `n` passes, each a chain. -/
inductive ZombieRun (ec : Concurrency.CoreId) : Nat → SystemState → SystemState → Prop
  | stop (st : SystemState) : ZombieRun ec 0 st st
  | pass {n : Nat} {s1 s2 s3 : SystemState} (hP : FinalisingDeleteChain ec s1 s2)
      (hRest : ZombieRun ec n s2 s3) : ZombieRun ec (n + 1) s1 s3

/-- **A run of passes with one more chain after it.** -/
theorem ZombieRun.append {ec : Concurrency.CoreId} :
    ∀ {n : Nat} {s1 s2 s3 : SystemState}, ZombieRun ec n s1 s2 → FinalisingDeleteChain ec s2 s3 →
      ZombieRun ec (n + 1) s1 s3
  | _, _, _, _, .stop _, h => .pass h (.stop _)
  | _, _, _, _, .pass hP hRest, h => .pass hP (hRest.append h)

/-- **A run of passes is a chain.** -/
theorem ZombieRun.chain {ec : Concurrency.CoreId} :
    ∀ {n : Nat} {st st' : SystemState}, ZombieRun ec n st st' → FinalisingDeleteChain ec st st'
  | _, _, _, .stop st => .refl st
  | _, _, _, .pass hP hRest => hP.trans hRest.chain

/-- **The passes with `fuel` are at most `fuel`**, each a chain of finalising
deletes and finalisations. -/
theorem zombiePasses_run (ec : Concurrency.CoreId) (root : SeLe4n.ObjId)
    (rootSlot : SeLe4n.Slot) :
    ∀ (fuel : Nat) (st : SystemState),
      ∃ n, n ≤ fuel ∧ ZombieRun ec n st (zombiePasses ec root rootSlot fuel st)
  | 0, st => ⟨0, Nat.le_refl 0, .stop st⟩
  | fuel + 1, st => by
    unfold zombiePasses
    dsimp only
    split
    · exact ⟨0, by omega, .stop st⟩
    · obtain ⟨n, hn, hR⟩ := zombiePasses_run ec root rootSlot fuel
        (zombieDescend ec root rootSlot (zombieDepth st) root rootSlot
          (zombieSlotClass st root rootSlot root rootSlot) st)
      exact ⟨n + 1, by omega, .pass (zombieDescend_chain ec root rootSlot _ _ _ _ st) hR⟩

/-- **The zombie delete of a slot**: the plain delete, or the passes then the
slot's own finalising delete. -/
theorem zombieDeleteAt_cases (ec : Concurrency.CoreId) (cnode : SeLe4n.ObjId)
    (slot : SeLe4n.Slot) (st : SystemState) :
    (cspaceDeleteAdmitted ⟨cnode, slot⟩ st = true ∧
      zombieDeleteAt ec cnode slot st = cspaceDeletePerformAt cnode slot st) ∨
    ∃ n, n ≤ zombieFuel st ∧
      ZombieRun ec n st (zombiePasses ec cnode slot (zombieFuel st) st) ∧
      zombieDeleteAt ec cnode slot st =
        zombieDeleteAtFuel ec cnode slot (zombieFuel st) st := by
  unfold zombieDeleteAt
  split
  · next hD => exact .inl ⟨hD, rfl⟩
  · obtain ⟨n, hn, hR⟩ := zombiePasses_run ec cnode slot (zombieFuel st) st
    exact .inr ⟨n, hn, hR, rfl⟩

/-- **The zombie delete with fuel `fuel` is a run of at most `fuel + 1`
passes**: the passes, then the slot's own delete or nothing. -/
theorem zombieDeleteAtFuel_run (ec : Concurrency.CoreId) (cnode : SeLe4n.ObjId)
    (slot : SeLe4n.Slot) (fuel : Nat) (st : SystemState) :
    ∃ n, n ≤ fuel + 1 ∧ ZombieRun ec n st (zombieDeleteAtFuel ec cnode slot fuel st) := by
  obtain ⟨n, hn, hR⟩ := zombiePasses_run ec cnode slot fuel st
  unfold zombieDeleteAtFuel
  dsimp only
  split
  · exact ⟨n + 1, by omega, hR.append (zombieDeleteSlot_chain ec cnode slot _)⟩
  · exact ⟨n, by omega, hR⟩

/-- **A kept slot is one whose passes did not end**: when the zombie delete
returns the passes' state, the slot's class there is nonzero, and otherwise the
slot's own delete ran. -/
theorem zombieDeleteAtFuel_kept_or_deleted (ec : Concurrency.CoreId) (cnode : SeLe4n.ObjId)
    (slot : SeLe4n.Slot) (fuel : Nat) (st : SystemState) :
    (zombieSlotClass (zombiePasses ec cnode slot fuel st) cnode slot cnode slot = 0 ∧
      zombieDeleteAtFuel ec cnode slot fuel st =
        zombieDeleteSlot ec cnode slot (zombiePasses ec cnode slot fuel st)) ∨
    (zombieSlotClass (zombiePasses ec cnode slot fuel st) cnode slot cnode slot ≠ 0 ∧
      zombieDeleteAtFuel ec cnode slot fuel st = zombiePasses ec cnode slot fuel st) := by
  unfold zombieDeleteAtFuel
  dsimp only
  split
  · next h => exact .inl ⟨h, rfl⟩
  · next h => exact .inr ⟨h, rfl⟩

/-- **The zombie delete of an admitted slot makes at most `zombieFuel` passes**
(`3 · n + 2` for a store of `n` objects) and the slot's own delete: a run of at
most `zombieFuel st + 1` passes. -/
theorem zombieDeleteAt_run (ec : Concurrency.CoreId) (cnode : SeLe4n.ObjId) (slot : SeLe4n.Slot)
    (st : SystemState) :
    ∃ n, n ≤ zombieFuel st + 1 ∧ ZombieRun ec n st (zombieDeleteAt ec cnode slot st) := by
  rcases zombieDeleteAt_cases ec cnode slot st with ⟨hD, e⟩ | ⟨-, -, -, e⟩
  · rw [e]
    refine ⟨1, by omega, .pass ?_ (.stop _)⟩
    exact .step _ (cspaceDeleteSlotFinalising_of_admitted hD) (.refl _)
  · rw [e]
    obtain ⟨m, hm, hR'⟩ := zombieDeleteAtFuel_run ec cnode slot (zombieFuel st) st
    exact ⟨m, hm, hR'⟩

/-- **A successful zombie delete is at most `zombieFuel st + 1` passes**, each a
chain of finalising deletes and finalisations: the zombie loop's passes, at most
`zombieFuel st = 3 · n + 2` for a store of `n` objects, then the slot's own
delete. -/
theorem cspaceDeleteSlotZombie_run (ec : Concurrency.CoreId) (addr : CSpaceAddr)
    {st st' : SystemState} (h : cspaceDeleteSlotZombie ec addr st = .ok ((), st')) :
    ∃ n, n ≤ zombieFuel st + 1 ∧ ZombieRun ec n st st' := by
  unfold cspaceDeleteSlotZombie at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at h
    subst h
    exact zombieDeleteAt_run ec addr.cnode addr.slot st
  · exact ⟨1, by omega, .pass (.step addr h (.refl _)) (.stop _)⟩

/-- **A zombie delete is a chain.** -/
theorem cspaceDeleteSlotZombie_chain (ec : Concurrency.CoreId) (addr : CSpaceAddr)
    {st st' : SystemState} (h : cspaceDeleteSlotZombie ec addr st = .ok ((), st')) :
    FinalisingDeleteChain ec st st' :=
  (cspaceDeleteSlotZombie_run ec addr h).choose_spec.2.chain

/-- **A zombie delete keeps whatever every finalising delete and every
finalisation keeps.** -/
theorem cspaceDeleteSlotZombie_closed {ec : Concurrency.CoreId} {addr : CSpaceAddr}
    {st st' : SystemState} (Q : SystemState → Prop)
    (hDel : ∀ (c : CSpaceAddr) (s s' : SystemState), Q s →
      cspaceDeleteSlotFinalising ec c s = .ok ((), s') → Q s')
    (hFin : ∀ (target : Nat) (s : SystemState), Q s → Q (finaliseFinalObject target s))
    (hQ : Q st) (h : cspaceDeleteSlotZombie ec addr st = .ok ((), st')) : Q st' :=
  (cspaceDeleteSlotZombie_chain ec addr h).closed Q hDel hFin hQ

/-- An admitted zombie delete is its writes. -/
theorem cspaceDeleteSlotZombie_of_admitted {ec : Concurrency.CoreId} {addr : CSpaceAddr}
    {st : SystemState} (h : cspaceDeleteFinalisingAdmitted addr st = true) :
    cspaceDeleteSlotZombie ec addr st = .ok ((), zombieDeleteAt ec addr.cnode addr.slot st) := by
  unfold cspaceDeleteSlotZombie; rw [if_pos h]

/-- **A zombie delete whose slot retires nothing is the finalising delete**: the
loop's passes stop at once, and the slot's own delete is all that runs. -/
theorem cspaceDeleteSlotZombie_of_target_zero {ec : Concurrency.CoreId} {addr : CSpaceAddr}
    {st : SystemState} (h0 : slotRetireTarget st addr.cnode addr.slot = 0) :
    cspaceDeleteSlotZombie ec addr st = cspaceDeleteSlotFinalising ec addr st := by
  unfold cspaceDeleteSlotZombie
  split
  · next hA =>
    unfold zombieDeleteAt
    split
    · next hD => rw [cspaceDeleteSlotFinalising_of_admitted hD]; rfl
    · have hP : zombiePasses ec addr.cnode addr.slot (zombieFuel st) st = st := by
        show zombiePasses ec addr.cnode addr.slot (3 * st.objects.size + 1 + 1) st = st
        unfold zombiePasses
        have : zombieSlotClass st addr.cnode addr.slot addr.cnode addr.slot = 0 := by
          unfold zombieSlotClass; simp only [h0, if_true]
        simp only [this, if_true]
      unfold zombieDeleteAtFuel
      dsimp only
      rw [hP, if_pos (by unfold zombieSlotClass; simp only [h0, if_true])]
      unfold zombieDeleteSlot
      rw [if_pos hA, cspaceDeleteSlotFinalising_of_slotHolder hA]
  · rfl

/-- **A space change whose old CSpace root names an object holding capabilities**
(`zombieSlotClass` nonzero: the old capability is that object's last), after its
checks have passed: seL4's `TCB_SetSpace` deletes the old root by `cteDelete`,
the zombie loop, before it inserts the new one.  The loop's passes run on the
thread's CSpace root slot (`zombiePasses`); when they end with the slot naming
nothing that holds a capability, the checks are asked again of the state they
leave (`copyThreadSpacesAdmitted`, so the set reads no state its checks did not)
and the two slots are set (`copyThreadSpacesPerform`), whose delete of the old
root retires the emptied object.  When the passes run out of fuel, or the
thread no longer passes the checks, the passes' work stands and nothing else is
written: the caller sees the thread's roots unchanged and retries, as seL4's
preempted `TCB_SetSpace` is restarted.  Not reachable while the fuel suffices
(`docs/planning/UNTYPED_RESET_PLAN.md` row 35).  Out of line: only a space
change replacing the last capability to a populated CNode takes it. -/
@[noinline] def copyThreadSpacesAfterZombie (executingCore : Concurrency.CoreId) (st : SystemState)
    (vtid : SeLe4n.ValidThreadId) (cnSrc vrSrc : CSpaceAddr) : SystemState :=
  let s := zombiePasses executingCore vtid.val.toObjId TCB.cspaceRootSlot (zombieFuel st) st
  if zombieSlotClass s vtid.val.toObjId TCB.cspaceRootSlot vtid.val.toObjId TCB.cspaceRootSlot = 0 &&
      copyThreadSpacesAdmitted s vtid cnSrc vrSrc then
    copyThreadSpacesPerform executingCore s vtid.val cnSrc.cnode cnSrc.slot vrSrc.cnode vrSrc.slot
  else s

/-- **An admitted space change's writes, the old CSpace root deleted as
`cteDelete` deletes it**: when the old root names nothing holding a capability
the two slot sets (`copyThreadSpacesPerform`) alone, as before the zombie loop;
otherwise the loop first (`copyThreadSpacesAfterZombie`).  A VSpace root holds
no slots, so the VSpace slot's old capability never needs the loop. -/
@[inline] def copyThreadSpacesZombiePerform (executingCore : Concurrency.CoreId) (st : SystemState)
    (vtid : SeLe4n.ValidThreadId) (cnCNode : SeLe4n.ObjId) (cnSlot : SeLe4n.Slot)
    (vrCNode : SeLe4n.ObjId) (vrSlot : SeLe4n.Slot) : SystemState :=
  if zombieSlotClass st vtid.val.toObjId TCB.cspaceRootSlot vtid.val.toObjId TCB.cspaceRootSlot = 0 then
    copyThreadSpacesPerform executingCore st vtid.val cnCNode cnSlot vrCNode vrSlot
  else
    copyThreadSpacesAfterZombie executingCore st vtid ⟨cnCNode, cnSlot⟩ ⟨vrCNode, vrSlot⟩

/-- **`.tcbSetSpace`: seL4's `TCB_SetSpace`**, the old roots deleted through the
zombie delete: refused, committing nothing, as `copyThreadSpaces` refuses
(its checks, read before any write); otherwise its writes with the old CSpace
root's object emptied first (`copyThreadSpacesZombiePerform`, on the source
slots' words, so the dispatcher builds no address record). -/
def copyThreadSpacesZombie (executingCore : Concurrency.CoreId) (st : SystemState)
    (vtid : SeLe4n.ValidThreadId) (cnSrc vrSrc : CSpaceAddr) : Except KernelError SystemState :=
  if copyThreadSpacesAdmitted st vtid cnSrc vrSrc then
    .ok (copyThreadSpacesZombiePerform executingCore st vtid cnSrc.cnode cnSrc.slot vrSrc.cnode
      vrSrc.slot)
  else copyThreadSpaces executingCore st vtid cnSrc vrSrc

/-- An admitted space change through the zombie delete is its writes. -/
theorem copyThreadSpacesZombie_of_admitted {ec : Concurrency.CoreId} {st : SystemState}
    {vtid : SeLe4n.ValidThreadId} {cnSrc vrSrc : CSpaceAddr}
    (h : copyThreadSpacesAdmitted st vtid cnSrc vrSrc = true) :
    copyThreadSpacesZombie ec st vtid cnSrc vrSrc =
      .ok (copyThreadSpacesZombiePerform ec st vtid cnSrc.cnode cnSrc.slot vrSrc.cnode vrSrc.slot) := by
  unfold copyThreadSpacesZombie; rw [if_pos h]

/-- **What a successful space change through the zombie delete consists of**:
the plain space change from the pre-state (`copyThreadSpaces`), or a run of the
zombie loop's passes on the old CSpace root slot (`ZombieRun`) and then either
nothing more or the plain space change from the state the passes leave. -/
theorem copyThreadSpacesZombie_cases {ec : Concurrency.CoreId} {st st' : SystemState}
    {vtid : SeLe4n.ValidThreadId} {cnSrc vrSrc : CSpaceAddr}
    (h : copyThreadSpacesZombie ec st vtid cnSrc vrSrc = .ok st') :
    copyThreadSpaces ec st vtid cnSrc vrSrc = .ok st' ∨
      ∃ n s, ZombieRun ec n st s ∧ (st' = s ∨ copyThreadSpaces ec s vtid cnSrc vrSrc = .ok st') := by
  unfold copyThreadSpacesZombie at h
  split at h
  · next hA =>
    simp only [Except.ok.injEq] at h
    subst h
    unfold copyThreadSpacesZombiePerform
    split
    · exact .inl (copyThreadSpaces_of_admitted hA)
    · right
      obtain ⟨n, -, hR⟩ := zombiePasses_run ec vtid.val.toObjId TCB.cspaceRootSlot (zombieFuel st) st
      refine ⟨n, _, hR, ?_⟩
      unfold copyThreadSpacesAfterZombie
      dsimp only
      split
      · next hB =>
        exact .inr (copyThreadSpaces_of_admitted ((Bool.and_eq_true _ _).mp hB).2)
      · exact .inl rfl
  · exact .inl h

/-- **A space change through the zombie delete keeps whatever every finalising
delete, every finalisation and every plain space change keeps.** -/
theorem copyThreadSpacesZombie_closed {ec : Concurrency.CoreId} {st st' : SystemState}
    {vtid : SeLe4n.ValidThreadId} {cnSrc vrSrc : CSpaceAddr} (Q : SystemState → Prop)
    (hDel : ∀ (c : CSpaceAddr) (s s' : SystemState), Q s →
      cspaceDeleteSlotFinalising ec c s = .ok ((), s') → Q s')
    (hFin : ∀ (target : Nat) (s : SystemState), Q s → Q (finaliseFinalObject target s))
    (hSet : ∀ s s', Q s → copyThreadSpaces ec s vtid cnSrc vrSrc = .ok s' → Q s')
    (hQ : Q st) (h : copyThreadSpacesZombie ec st vtid cnSrc vrSrc = .ok st') : Q st' := by
  rcases copyThreadSpacesZombie_cases h with h1 | ⟨n, s, hR, rfl | h2⟩
  · exact hSet _ _ hQ h1
  · exact hR.chain.closed Q hDel hFin hQ
  · exact hSet _ _ (hR.chain.closed Q hDel hFin hQ) h2

/-- **seL4's `cteRevoke`**: delete the source's first child, finalising it,
until the source has none.  Each delete splices its slot out of the tree, so
the deleted child's children become the source's, and the loop reaches every
descendant without building a list of them; `fuel` bounds it by the tree's
edges, one of which each splice removes.  Each delete is admitted when its
CNode exists (`cspaceDeleteFinalisingAdmitted`) and is then the zombie delete
(`zombieDeleteAt`, seL4's `cteDelete`), which empties a child's CNode or
thread before the child itself goes.  A child the zombie delete keeps, its
passes out of fuel (`zombieDeleteAtFuel`), ends the loop with what it has done,
as seL4's preempted `cteRevoke` returns and is restarted: the caller sees the
child's slot still occupied and retries; on a reachable state it never happens
(the fuel's sufficiency, `docs/planning/UNTYPED_RESET_PLAN.md` row 35).  A child
outside every CNode ends the loop,
which on a state the capability invariants hold in never happens: there the
loop ends with the source childless (`cspaceRevokeCdtFinalising_ok_childless`).
Retiring the stop is a `docs/REGISTERED_DEBT.md` table C row (ZA5.4). -/
def revokeFirstChildLoop (executingCore : Concurrency.CoreId) (cnode : SeLe4n.ObjId)
    (slot : SeLe4n.Slot) : Nat → SystemState → SystemState
  | 0, st => st
  | n + 1, st =>
    let fc := st.slotLinkNodeWord cnode slot .firstChild
    if fc = 0 then st
    else
      let cc := SeLe4n.ObjId.ofNat (fc - 1)
      let cs := SeLe4n.Slot.ofNat (st.slotLinkSlotWord cnode slot .firstChild - 1)
      if cspaceDeleteFinalisingAdmitted { cnode := cc, slot := cs } st then
        let s := zombieDeleteAt executingCore cc cs st
        if zombieSlotClass s cc cs cc cs = 0 then revokeFirstChildLoop executingCore cnode slot n s
        else s
      else st

/-- **The loop is a run of finalising deletes.** -/
theorem revokeFirstChildLoop_chain (ec : Concurrency.CoreId) (cnode : SeLe4n.ObjId)
    (slot : SeLe4n.Slot) :
    ∀ (n : Nat) (st : SystemState),
      FinalisingDeleteChain ec st (revokeFirstChildLoop ec cnode slot n st)
  | 0, st => .refl st
  | n + 1, st => by
    unfold revokeFirstChildLoop
    dsimp only
    split
    · exact .refl st
    · split
      · next hA =>
        split
        · exact (zombieDeleteAt_run ec _ _ _).choose_spec.2.chain.trans
            (revokeFirstChildLoop_chain ec cnode slot n _)
        · exact (zombieDeleteAt_run ec _ _ _).choose_spec.2.chain
      · exact .refl st

/-- WS-ZA ZA5.3 part 8: **`.cspaceRevoke`'s check**, read before any write: the
source slot holds a capability. -/
@[inline] def cspaceRevokeAdmitted (addr : CSpaceAddr) (st : SystemState) : Bool :=
  (SystemState.lookupSlotCap st addr).isSome

/-- **An admitted revocation's writes**: the first-child loop, with fuel for
every edge of the tree. -/
def cspaceRevokePerformAt (executingCore : Concurrency.CoreId) (cnode : SeLe4n.ObjId)
    (slot : SeLe4n.Slot) (st : SystemState) : SystemState :=
  revokeFirstChildLoop executingCore cnode slot (st.cdt.edgeBound + 1) st

/-- **`.cspaceRevoke`: revoke the capability in `addr`**, seL4's `cteRevoke`:
the source slot is looked up, then its first child deleted and finalised until
it has none (`revokeFirstChildLoop`), so every mapping a destroyed frame
capability recorded and every page table that lost its last capability is
torn down with the capability (`FinalisingDeleteChain.unmapped`).  The check
reads the state before any write, so the dispatcher runs the step through
`RefusalCarrying.ofChecked` and the store is written in place. -/
def cspaceRevokeCdtFinalising (executingCore : Concurrency.CoreId) (addr : CSpaceAddr) :
    Kernel Unit :=
  fun st =>
    match SystemState.lookupSlotCap st addr with
    | some _ => .ok ((), cspaceRevokePerformAt executingCore addr.cnode addr.slot st)
    | none =>
      match st.getCNode? addr.cnode with
      | some _ => .error .invalidCapability
      | none => .error .objectNotFound

/-- An admitted revocation is its writes. -/
theorem cspaceRevokeCdtFinalising_of_admitted {ec : Concurrency.CoreId} {addr : CSpaceAddr}
    {st : SystemState} (h : cspaceRevokeAdmitted addr st = true) :
    cspaceRevokeCdtFinalising ec addr st =
      .ok ((), cspaceRevokePerformAt ec addr.cnode addr.slot st) := by
  unfold cspaceRevokeAdmitted at h
  unfold cspaceRevokeCdtFinalising
  cases hL : SystemState.lookupSlotCap st addr with
  | none => rw [hL] at h; cases h
  | some _ => rfl

/-- **A successful revocation witnesses an occupied source slot**: the tie that
keeps `cdtNodeIsRevocable` revocation's own precondition rather than a second
opinion about it. -/
theorem cspaceRevokeCdtFinalising_ok_implies_slot_occupied {ec : Concurrency.CoreId}
    {addr : CSpaceAddr} {st st' : SystemState}
    (h : cspaceRevokeCdtFinalising ec addr st = .ok ((), st')) :
    (SystemState.lookupSlotCap st addr).isSome := by
  unfold cspaceRevokeCdtFinalising at h
  split at h
  · next hL => rw [hL]; rfl
  · split at h <;> cases h

/-- **A node `cdtNodeIsRevocable` refuses is a node no revocation can enter.**
Were an IPC transfer to install beneath it anyway, the edge would hang beneath a
slot that cannot be revoked, so nothing could destroy the installed
capability. -/
theorem cdtNodeIsRevocable_false_revoke_refuses (st : SystemState) (node : SlotRef)
    (hNot : cdtNodeIsRevocable st node = false) (ec : Concurrency.CoreId)
    (st' : SystemState) : cspaceRevokeCdtFinalising ec node st ≠ .ok ((), st') := by
  intro hOk
  have hOcc := cspaceRevokeCdtFinalising_ok_implies_slot_occupied hOk
  unfold cdtNodeIsRevocable at hNot
  rw [hOcc] at hNot
  cases hNot

/-- **What a successful finalising revocation is: a run of finalising
deletes.** -/
theorem cspaceRevokeCdtFinalising_chain (ec : Concurrency.CoreId) (addr : CSpaceAddr)
    (st st' : SystemState) (h : cspaceRevokeCdtFinalising ec addr st = .ok ((), st')) :
    FinalisingDeleteChain ec st st' := by
  unfold cspaceRevokeCdtFinalising at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at h
    subst h
    exact revokeFirstChildLoop_chain ec _ _ _ st
  · split at h <;> cases h

/-- **The finalising revocation keeps whatever every finalising delete keeps.**
The consumers' one argument: the revocation is a chain of them. -/
theorem cspaceRevokeCdtFinalising_closed {ec : Concurrency.CoreId} {addr : CSpaceAddr}
    {st st' : SystemState} (Q : SystemState → Prop)
    (hDel : ∀ (c : CSpaceAddr) (s s' : SystemState), Q s →
      cspaceDeleteSlotFinalising ec c s = .ok ((), s') → Q s')
    (hFin : ∀ (target : Nat) (s : SystemState), Q s → Q (finaliseFinalObject target s))
    (hQ : Q st) (h : cspaceRevokeCdtFinalising ec addr st = .ok ((), st')) : Q st' :=
  (cspaceRevokeCdtFinalising_chain ec addr st st' h).closed Q hDel hFin hQ

/-- **The payoff: the finalising revocation keeps the teardown's state well
formed, and no page a capability it destroyed recorded survives it.**  Every
step is a finalising delete (`cspaceRevokeCdtFinalising_chain`), so each
destroyed capability's page is not live after the whole revocation
(`FinalisingDeleteChain.unmapped`). -/
theorem cspaceRevokeCdtFinalising_ok_unmapped (ec : Concurrency.CoreId) (addr : CSpaceAddr)
    (st st' : SystemState) (hW : teardownWellFormed st)
    (h : cspaceRevokeCdtFinalising ec addr st = .ok ((), st')) :
    teardownWellFormed st' ∧
      ∀ (s s2 : SystemState) (c : CSpaceAddr), FinalisingDeleteChain ec st s →
        cspaceDeleteSlotFinalising ec c s = .ok ((), s2) → FinalisingDeleteChain ec s2 st' →
        ∀ (cap : Capability), s.slotCapAt c = some cap →
        ∀ (p : MappedPage), capabilityMappedPage s cap = some p → mappedPageLive st' p = false :=
  ⟨((cspaceRevokeCdtFinalising_chain ec addr st st' h).wellFormed hW).1,
   fun _ _ _ hPre hD hRest cap hCap p hP =>
     FinalisingDeleteChain.unmapped (hPre.wellFormed hW).1 hD hRest cap hCap p hP⟩

end SeLe4n.Kernel
