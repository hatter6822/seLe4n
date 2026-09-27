-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Capability.Operations
import SeLe4n.Kernel.Architecture.PageTeardown
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
frame: a record gone stale removes nothing that is not its own.  Both then
**decide** that no destroyed capability's page survives (`livePagesCleared`) and
refuse otherwise — the check cannot fail on a well-formed state, and the payoff
theorems (`cspaceDeleteSlotFinalising_ok_unmapped`,
`cspaceRevokeCdtFinalising_ok_unmapped`) are read off it.

The one other way a capability can be destroyed is the destruction of the CNode
holding it; the retype of a CNode refuses while any slot holds a capability that
records a mapping (`CNode.holdsFrameMappingRecord`, `.revocationRequired`):
delete those capabilities first, which unmaps.

**Page tables (`v0.36.12`).**  A page table's install is recorded on the table
and in its root rather than on a capability, so what a destroying step owes it is
decided over the store: a table some capability named before the step and none
names after it (`pageTablesOrphaned`) has lost its **final** capability, and
seL4's `finaliseCap` → `unmapPageTable` takes it out of its address space.
`finaliseDestroyedCapabilities` is the composite both destroying arms run: it
detaches each orphaned table and every table beneath it from its root
(`detachPageTables`), removes the frame capabilities' recorded pages and the
pages that translated through the detached tables, and decides the result
(`pageTablesDetached`).  The detach writes roots only; the tables it takes out
keep a stale record, which `Architecture.pageTableInstallLive` reads as
installed nowhere.  The retype of a CNode holding a capability to an installed
table is refused for the same reason as a mapping record
(`Architecture.cnodeHoldsInstalledPageTableCap`).
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
-- §2  The teardown, checked
-- ============================================================================

/-- **Remove the destroyed capabilities' pages, then decide none survives.** -/
def finaliseFramePages (executingCore : Concurrency.CoreId) (pages : List MappedPage) :
    Kernel Unit :=
  fun st =>
    match unmapLivePages executingCore pages st with
    | .error e => .error e
    | .ok ((), st1) =>
      if !livePagesCleared st1 pages then .error .illegalState
      else .ok ((), st1)

/-- What a successful teardown is: the unmap pass, and the decided result. -/
theorem finaliseFramePages_ok (ec : Concurrency.CoreId) (pages : List MappedPage)
    (st st' : SystemState) (h : finaliseFramePages ec pages st = .ok ((), st')) :
    unmapLivePages ec pages st = .ok ((), st') ∧ livePagesCleared st' pages = true := by
  unfold finaliseFramePages at h
  cases hU : unmapLivePages ec pages st with
  | error e => rw [hU] at h; cases h
  | ok pr =>
    obtain ⟨u, st1⟩ := pr; cases u
    rw [hU] at h
    simp only at h
    cases hC : livePagesCleared st1 pages
    · rw [hC] at h; cases h
    · rw [hC] at h
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq,
        Prod.mk.injEq, true_and] at h
      subst h
      exact ⟨rfl, hC⟩

/-- **The teardown is a VSpace-root-only write** that keeps the scheduler and the
object table's invariant. -/
theorem finaliseFramePages_ok_frame (ec : Concurrency.CoreId) (pages : List MappedPage)
    (st st' : SystemState) (hObjInv : st.objects.invExt)
    (h : finaliseFramePages ec pages st = .ok ((), st')) :
    st'.objects.invExt ∧ vspaceRootOnlyWrite st st' ∧ st'.scheduler = st.scheduler :=
  unmapLivePages_ok_frame ec pages st st' hObjInv (finaliseFramePages_ok ec pages st st' h).1

-- ============================================================================
-- §2a  Page tables: destroying the last capability takes the table out
-- ============================================================================

/-- **The page tables a destroying step orphaned**, each with the install its
root holds: a table installed after the step (`pageTableInstallLive`), which some
capability named before the step (`pre`) and none names after it.  That is
seL4's `finaliseCap` condition for a page table — its **final** capability is
gone — and asking it of the whole store is what makes one answer serve both the
delete, which destroys one capability, and the revocation, which destroys a
state-discovered set.  A table another capability still names stays where it is:
the holder of that capability can still unmap it. -/
def pageTablesOrphaned (pre st : SystemState) : List (SeLe4n.ObjId × PageTableInstall) :=
  st.objects.fold (init := []) (fun acc id o =>
    match o with
    | .pageTable p =>
      match p.installedIn with
      | some inst =>
        if Architecture.pageTableInstallLive st id && !carvedSubtreeUnreferenced pre [id] &&
            carvedSubtreeUnreferenced st [id] then (id, inst) :: acc
        else acc
      | none => acc
    | _ => acc)

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
      match storeObject o.2.root (.vspaceRoot (root.withoutTablesBeneath o.2 o.1)) st with
      | .error e => .error e
      | .ok ((), st1) => detachPageTables rest st1

/-- **Each orphaned table is out of its root, and nothing translates through the
slot it held** — the teardown's result, decided. -/
def pageTablesDetached (st : SystemState) (orphans : List (SeLe4n.ObjId × PageTableInstall)) :
    Bool :=
  orphans.all fun o =>
    match st.getVSpaceRoot? o.2.root with
    | some root =>
      !root.tables.contains (o.2.slotFor o.1) && !Architecture.pageTableInUse root o.2
    | none => true

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
        cases hS : storeObject o.2.root (.vspaceRoot (root.withoutTablesBeneath o.2 o.1)) st with
        | error e => rw [hS] at h; cases h
        | ok pr =>
          obtain ⟨⟨⟩, st1⟩ := pr
          rw [hS] at h
          have hObj := (SystemState.getVSpaceRoot?_eq_some_iff st o.2.root root).mp hR
          have hInv1 := storeObject_preserves_objects_invExt _ _ _ _ hInv hS
          obtain ⟨hI2, hW2, hS2, hM2⟩ := detachPageTables_ok_frame rest st1 st' hInv1 h
          refine ⟨hI2, vspaceRootOnlyWrite.trans (fun oid => ?_) hW2,
            hS2.trans (storeObject_scheduler_eq _ _ _ _ hS),
            hM2.trans (storeObject_machine_eq _ _ _ _ hS)⟩
          by_cases hK : oid = o.2.root
          · subst hK
            exact Or.inr ⟨⟨root, hObj⟩, ⟨_, storeObject_objects_eq _ _ _ _ hInv hS⟩⟩
          · exact Or.inl (storeObject_objects_ne _ _ _ _ _ hK hInv hS)

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
        cases hS : storeObject o.2.root (.vspaceRoot (root.withoutTablesBeneath o.2 o.1)) st with
        | error e => rw [hS] at h; cases h
        | ok pr =>
          obtain ⟨⟨⟩, st1⟩ := pr
          rw [hS] at h
          obtain ⟨hS2, hM2⟩ := detachPageTables_ok_scheduler_machine rest st1 st' h
          exact ⟨hS2.trans (storeObject_scheduler_eq _ _ _ _ hS),
            hM2.trans (storeObject_machine_eq _ _ _ _ hS)⟩

/-- **Finalise what a destroying step destroyed**: take out the page tables it
orphaned, then remove the pages its frame capabilities recorded and the pages
that translated through those tables, then decide that no orphaned table is
still in its walk.  `pre` is the state before the step, `pages` what its
destroyed frame capabilities recorded. -/
def finaliseDestroyedCapabilities (executingCore : Concurrency.CoreId) (pre : SystemState)
    (pages : List MappedPage) : Kernel Unit :=
  fun st =>
    let orphans := pageTablesOrphaned pre st
    match detachPageTables orphans st with
    | .error e => .error e
    | .ok ((), st1) =>
      match finaliseFramePages executingCore (pages ++ orphanedTableMappings st orphans) st1 with
      | .error e => .error e
      | .ok ((), st2) =>
        if !pageTablesDetached st2 orphans then .error .illegalState
        else .ok ((), st2)

/-- What a successful finalisation is: the table detach, the page teardown, and
the decided result. -/
theorem finaliseDestroyedCapabilities_ok (ec : Concurrency.CoreId) (pre : SystemState)
    (pages : List MappedPage) (st st' : SystemState)
    (h : finaliseDestroyedCapabilities ec pre pages st = .ok ((), st')) :
    ∃ st1, detachPageTables (pageTablesOrphaned pre st) st = .ok ((), st1) ∧
      finaliseFramePages ec (pages ++ orphanedTableMappings st (pageTablesOrphaned pre st)) st1 =
        .ok ((), st') ∧
      pageTablesDetached st' (pageTablesOrphaned pre st) = true := by
  unfold finaliseDestroyedCapabilities at h
  simp only at h
  cases hD : detachPageTables (pageTablesOrphaned pre st) st with
  | error e => rw [hD] at h; cases h
  | ok pr =>
    obtain ⟨⟨⟩, st1⟩ := pr
    rw [hD] at h
    simp only at h
    cases hF : finaliseFramePages ec
        (pages ++ orphanedTableMappings st (pageTablesOrphaned pre st)) st1 with
    | error e => rw [hF] at h; cases h
    | ok pr2 =>
      obtain ⟨⟨⟩, st2⟩ := pr2
      rw [hF] at h
      simp only at h
      cases hC : pageTablesDetached st2 (pageTablesOrphaned pre st)
      · rw [hC] at h; cases h
      · rw [hC] at h
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq,
          Prod.mk.injEq, true_and] at h
        subst h
        exact ⟨st1, rfl, hF, hC⟩

/-- **The finalisation is a VSpace-root-only write** that keeps the scheduler and
the object table's invariant. -/
theorem finaliseDestroyedCapabilities_ok_frame (ec : Concurrency.CoreId) (pre : SystemState)
    (pages : List MappedPage) (st st' : SystemState) (hObjInv : st.objects.invExt)
    (h : finaliseDestroyedCapabilities ec pre pages st = .ok ((), st')) :
    st'.objects.invExt ∧ vspaceRootOnlyWrite st st' ∧ st'.scheduler = st.scheduler := by
  obtain ⟨st1, hD, hF, -⟩ := finaliseDestroyedCapabilities_ok ec pre pages st st' h
  obtain ⟨hI1, hW1, hS1, -⟩ := detachPageTables_ok_frame _ st st1 hObjInv hD
  obtain ⟨hI2, hW2, hS2⟩ := finaliseFramePages_ok_frame ec _ st1 st' hI1 hF
  exact ⟨hI2, hW1.trans hW2, hS2.trans hS1⟩

/-- **The payoff for frames**: no page a destroyed frame capability recorded
survives the finalisation. -/
theorem finaliseDestroyedCapabilities_ok_unmapped (ec : Concurrency.CoreId) (pre : SystemState)
    (pages : List MappedPage) (st st' : SystemState)
    (h : finaliseDestroyedCapabilities ec pre pages st = .ok ((), st')) :
    ∀ p ∈ pages, mappedPageLive st' p = false := by
  obtain ⟨st1, -, hF, -⟩ := finaliseDestroyedCapabilities_ok ec pre pages st st' h
  intro p hp
  exact livePagesCleared_spec (finaliseFramePages_ok ec _ _ _ hF).2 p (List.mem_append_left _ hp)

/-- **The payoff for page tables**: every table whose last capability the step
destroyed is out of its root, and nothing translates through the slot it held —
no mapping and no deeper table. -/
theorem finaliseDestroyedCapabilities_ok_tables (ec : Concurrency.CoreId) (pre : SystemState)
    (pages : List MappedPage) (st st' : SystemState)
    (h : finaliseDestroyedCapabilities ec pre pages st = .ok ((), st')) :
    ∀ o ∈ pageTablesOrphaned pre st, ∀ root, st'.getVSpaceRoot? o.2.root = some root →
      root.tables.contains (o.2.slotFor o.1) = false ∧
        Architecture.pageTableInUse root o.2 = false := by
  obtain ⟨-, -, -, hC⟩ := finaliseDestroyedCapabilities_ok ec pre pages st st' h
  intro o ho root hR
  have := List.all_eq_true.mp hC o ho
  rw [hR] at this
  simpa using this

-- ============================================================================
-- §3  The finalising delete
-- ============================================================================

/-- **`.cspaceDelete`: delete the capability in `addr`, then remove the mapping it
records.**  The page is read off the slot the delete destroys, on the state the
delete runs on; the delete writes only CNodes and the CDT, so the page is still
the one the destroyed capability named when the teardown runs. -/
def cspaceDeleteSlotFinalising (executingCore : Concurrency.CoreId) (addr : CSpaceAddr) :
    Kernel Unit :=
  fun st =>
    match cspaceDeleteSlot addr st with
    | .error e => .error e
    | .ok ((), st1) =>
      finaliseDestroyedCapabilities executingCore st (slotMappedPages st addr) st1

/-- What a successful finalising delete is: the delete, then the teardown of the
page the destroyed capability recorded. -/
theorem cspaceDeleteSlotFinalising_ok (ec : Concurrency.CoreId) (addr : CSpaceAddr)
    (st st' : SystemState) (h : cspaceDeleteSlotFinalising ec addr st = .ok ((), st')) :
    ∃ st1, cspaceDeleteSlot addr st = .ok ((), st1) ∧
      finaliseDestroyedCapabilities ec st (slotMappedPages st addr) st1 = .ok ((), st') := by
  unfold cspaceDeleteSlotFinalising at h
  cases hD : cspaceDeleteSlot addr st with
  | error e => rw [hD] at h; cases h
  | ok pr => obtain ⟨u, st1⟩ := pr; cases u; rw [hD] at h; exact ⟨st1, rfl, h⟩

/-- **The payoff: no mapping the deleted capability recorded survives it.**  If
the capability in `addr` recorded a mapping of a frame, that frame's page is not
mapped at the recorded address in the post-state. -/
theorem cspaceDeleteSlotFinalising_ok_unmapped (ec : Concurrency.CoreId) (addr : CSpaceAddr)
    (st st' : SystemState) (h : cspaceDeleteSlotFinalising ec addr st = .ok ((), st'))
    (cap : Capability) (hCap : SystemState.lookupSlotCap st addr = some cap)
    (p : MappedPage) (hP : capabilityMappedPage st cap = some p) :
    mappedPageLive st' p = false := by
  obtain ⟨_, -, hF⟩ := cspaceDeleteSlotFinalising_ok ec addr st st' h
  refine finaliseDestroyedCapabilities_ok_unmapped ec st _ _ st' hF p ?_
  simp [slotMappedPages, hCap, hP]

-- ============================================================================
-- §4  The finalising revocation
-- ============================================================================

/-- **`.cspaceRevoke`: revoke the capability in `addr`, then remove every mapping
a destroyed capability recorded.**  `cspaceRevokeCdt` reports the pages of
exactly the capabilities its traversal destroyed (`revokeCdtFoldBody_records`). -/
def cspaceRevokeCdtFinalising (executingCore : Concurrency.CoreId) (addr : CSpaceAddr) :
    Kernel Unit :=
  fun st =>
    match cspaceRevokeCdt addr st with
    | .error e => .error e
    | .ok (pages, st1) => finaliseDestroyedCapabilities executingCore st pages st1

/-- What a successful finalising revocation is: the revocation, and the
teardown of the pages its destroyed capabilities recorded. -/
theorem cspaceRevokeCdtFinalising_ok (ec : Concurrency.CoreId) (addr : CSpaceAddr)
    (st st' : SystemState) (h : cspaceRevokeCdtFinalising ec addr st = .ok ((), st')) :
    ∃ pages st1, cspaceRevokeCdt addr st = .ok (pages, st1) ∧
      finaliseDestroyedCapabilities ec st pages st1 = .ok ((), st') := by
  unfold cspaceRevokeCdtFinalising at h
  cases hR : cspaceRevokeCdt addr st with
  | error e => rw [hR] at h; cases h
  | ok pr =>
    obtain ⟨pages, st1⟩ := pr
    rw [hR] at h
    exact ⟨pages, st1, rfl, h⟩

/-- **The payoff: no reported page survives the revocation.**  With
`revokeCdtFoldBody_records` — each step reports the page of the
capability it destroys — this is the statement that a revoked frame capability's
mapping is gone. -/
theorem cspaceRevokeCdtFinalising_ok_unmapped (ec : Concurrency.CoreId) (addr : CSpaceAddr)
    (st st' : SystemState) (h : cspaceRevokeCdtFinalising ec addr st = .ok ((), st')) :
    ∃ pages, (∃ st1, cspaceRevokeCdt addr st = .ok (pages, st1)) ∧
      ∀ p ∈ pages, mappedPageLive st' p = false := by
  obtain ⟨pages, st1, hC, hF⟩ := cspaceRevokeCdtFinalising_ok ec addr st st' h
  exact ⟨pages, ⟨st1, hC⟩, finaliseDestroyedCapabilities_ok_unmapped ec st pages st1 st' hF⟩

end SeLe4n.Kernel
