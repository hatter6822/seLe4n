-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Architecture.PageTeardown
import SeLe4n.Kernel.Architecture.VSpaceInvariant

/-!
# The teardown clears what it lists

WS-ZA ZA5.3: the finalising teardown's results, proven.  The teardown unmaps
the pages a destroyed capability recorded (`unmapLivePagesState`) and takes the
page tables it orphaned out of their roots; seL4's `finaliseCap` cannot fail,
and neither can these steps, so what they achieve is a theorem over well-formed
states (`teardownWellFormed`) rather than a check run after the writes.

Every write the teardown makes stores a VSpace root that only lost entries or
tables (`vspaceRootsShrink`), which keeps the VSpace bundle
(`storeObject_shrunkRoot_preserves_vspaceInvariantBundle`) and can only make a
page stop being live (`mappedPageLive_of_shrink`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

-- ============================================================================
-- §1  What the results rest on
-- ============================================================================

/-- **The states the teardown's results hold over**: the object table and the
ASID table well formed, and the VSpace bundle — every root resolved by its own
ASID, every mapping table well formed (`vspaceMappingsWellFormed`).  Boot
establishes it and the VSpace operations and teardowns keep it; carrying it
across every kernel transition is a row of `docs/REGISTERED_DEBT.md` table C
("The finalising delete's and revoke's payoffs take the teardown's
well-formedness as a premise"). -/
def teardownWellFormed (st : SystemState) : Prop :=
  st.objects.invExt ∧ st.asidTable.invExtK ∧ Architecture.vspaceInvariantBundle st

/-- A state whose object and ASID tables are another's is well formed with it. -/
theorem teardownWellFormed_of_tables_eq {st st' : SystemState}
    (hO : st'.objects = st.objects) (hA : st'.asidTable = st.asidTable)
    (h : teardownWellFormed st) : teardownWellFormed st' := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨hO ▸ h1, hA ▸ h2, ?_⟩
  unfold Architecture.vspaceInvariantBundle Architecture.vspaceAsidRootsUnique
    Architecture.vspaceRootNonOverlap Architecture.asidTableConsistent
    Architecture.wxExclusiveInvariant Architecture.boundedAddressTranslation
    Architecture.vspaceCrossAsidIsolation Architecture.canonicalAddressInvariant
    Architecture.vspaceMappingsWellFormed at h3 ⊢
  rw [hO, hA]
  exact h3

/-- **A step that keeps the ASID table and every address-space root keeps the
state well formed**: the VSpace bundle reads nothing else. -/
theorem teardownWellFormed_of_roots_eq {st st' : SystemState} (hInv : st'.objects.invExt)
    (hA : st'.asidTable = st.asidTable)
    (hR : ∀ (oid : SeLe4n.ObjId) (r : VSpaceRoot),
      st'.objects[oid]? = some (KernelObject.vspaceRoot r) ↔
        st.objects[oid]? = some (KernelObject.vspaceRoot r))
    (h : teardownWellFormed st) : teardownWellFormed st' := by
  obtain ⟨-, h2, h3⟩ := h
  refine ⟨hInv, hA ▸ h2, ?_⟩
  unfold Architecture.vspaceInvariantBundle Architecture.vspaceAsidRootsUnique
    Architecture.vspaceRootNonOverlap Architecture.asidTableConsistent
    Architecture.wxExclusiveInvariant Architecture.boundedAddressTranslation
    Architecture.vspaceCrossAsidIsolation Architecture.canonicalAddressInvariant
    Architecture.vspaceMappingsWellFormed at h3 ⊢
  obtain ⟨c1, c2, ⟨c3a, c3b⟩, c4, c5, c6, c7, c8⟩ := h3
  refine ⟨fun o1 o2 r1 r2 h1 h2 => c1 o1 o2 r1 r2 ((hR _ _).1 h1) ((hR _ _).1 h2),
    fun o r h => c2 o r ((hR _ _).1 h), ⟨fun a o hT => ?_, fun o r h => ?_⟩,
    fun o r v p q h => c4 o r v p q ((hR _ _).1 h),
    fun o r v p q h => c5 o r v p q ((hR _ _).1 h),
    fun o1 o2 r1 r2 h1 h2 => c6 o1 o2 r1 r2 ((hR _ _).1 h1) ((hR _ _).1 h2),
    fun o r v p q h => c7 o r v p q ((hR _ _).1 h),
    fun o r h => c8 o r ((hR _ _).1 h)⟩
  · rw [hA] at hT
    obtain ⟨r, hr, ha⟩ := c3a a o hT
    exact ⟨r, (hR _ _).2 hr, ha⟩
  · rw [hA]; exact c3b o r ((hR _ _).1 h)

/-- **Every root after a step was a root before it, with no more**: the same
ASID, no address mapped to a new entry, the same mapping epochs, and no new
table slot.  What each of the teardown's writes does to the root it writes. -/
def vspaceRootsShrink (st st' : SystemState) : Prop :=
  ∀ (oid : SeLe4n.ObjId) (r' : VSpaceRoot), st'.objects[oid]? = some (.vspaceRoot r') →
    ∃ r : VSpaceRoot, st.objects[oid]? = some (.vspaceRoot r) ∧ r'.asid = r.asid ∧
      (∀ (v : SeLe4n.VAddr) (e : SeLe4n.PAddr × PagePermissions),
        r'.mappings[v]? = some e → r.mappings[v]? = some e) ∧
      r'.mappingEpochs = r.mappingEpochs ∧ (∀ s ∈ r'.tables, s ∈ r.tables)

theorem vspaceRootsShrink.refl (st : SystemState) : vspaceRootsShrink st st :=
  fun _ r' h => ⟨r', h, rfl, fun _ _ hm => hm, rfl, fun _ hs => hs⟩

theorem vspaceRootsShrink.trans {s1 s2 s3 : SystemState}
    (hShrink1 : vspaceRootsShrink s1 s2) (hShrink2 : vspaceRootsShrink s2 s3) :
    vspaceRootsShrink s1 s3 := by
  intro oid r3 h3
  obtain ⟨r2, h2, ha2, hm2, he2, ht2⟩ := hShrink2 oid r3 h3
  obtain ⟨r1, h1, ha1, hm1, he1, ht1⟩ := hShrink1 oid r2 h2
  exact ⟨r1, h1, ha2.trans ha1, fun v e hm => hm1 v e (hm2 v e hm), he2.trans he1,
    fun s hs => ht1 s (ht2 s hs)⟩

theorem vspaceRootsShrink_of_tables_eq {st st' : SystemState}
    (hO : st'.objects = st.objects) : vspaceRootsShrink st st' := by
  intro oid r' h
  rw [hO] at h
  exact vspaceRootsShrink.refl st oid r' h

/-- **A store of a root that only lost entries or tables shrinks the roots.** -/
theorem vspaceRootsShrink_of_store {st st' : SystemState} {rootId : SeLe4n.ObjId}
    {root root' : VSpaceRoot} (hObjInv : st.objects.invExt)
    (hObjRoot : st.objects[rootId]? = some (.vspaceRoot root))
    (hStore : storeObject rootId (.vspaceRoot root') st = .ok ((), st'))
    (hAsid : root'.asid = root.asid)
    (hSub : ∀ (v : SeLe4n.VAddr) (e : SeLe4n.PAddr × PagePermissions),
      root'.mappings[v]? = some e → root.mappings[v]? = some e)
    (hEp : root'.mappingEpochs = root.mappingEpochs)
    (hTab : ∀ s ∈ root'.tables, s ∈ root.tables) :
    vspaceRootsShrink st st' := by
  intro oid r' h
  by_cases hEq : oid = rootId
  · subst hEq
    rw [storeObject_objects_eq st st' _ _ hObjInv hStore] at h
    cases h
    exact ⟨root, hObjRoot, hAsid, hSub, hEp, hTab⟩
  · rw [storeObject_objects_ne st st' rootId oid _ hEq hObjInv hStore] at h
    exact vspaceRootsShrink.refl st oid r' h

-- ============================================================================
-- §2  Liveness only falls
-- ============================================================================

/-- **A root the ASID table names is the root its ASID resolves to.** -/
theorem resolveAsidRoot_of_root {st : SystemState} (hW : teardownWellFormed st)
    {oid : SeLe4n.ObjId} {r : VSpaceRoot} (h : st.objects[oid]? = some (.vspaceRoot r)) :
    Architecture.resolveAsidRoot st r.asid = some (oid, r) :=
  Architecture.resolveAsidRoot_of_asidTable_entry st r.asid oid r
    (hW.2.2.2.2.1.2 oid r h) h rfl

/-- **A page live after a shrinking step was live before it.** -/
theorem mappedPageLive_of_shrink {st st' : SystemState} (hW : teardownWellFormed st)
    (hS : vspaceRootsShrink st st') {p : MappedPage} (h : mappedPageLive st' p = true) :
    mappedPageLive st p = true := by
  unfold mappedPageLive at h ⊢
  cases hR : Architecture.resolveAsidRoot st' p.asid with
  | none => rw [hR] at h; cases h
  | some pr =>
    obtain ⟨rid, r'⟩ := pr
    rw [hR] at h
    obtain ⟨-, hObj', hAsid'⟩ :=
      Architecture.resolveAsidRoot_some_implies_obj st' p.asid rid r' hR
    obtain ⟨r, hObj, hAsid, hSub, hEp, -⟩ := hS rid r' hObj'
    have hR0 := resolveAsidRoot_of_root hW hObj
    rw [← hAsid, hAsid'] at hR0
    rw [hR0]
    simp only [Bool.and_eq_true, beq_iff_eq] at h ⊢
    obtain ⟨hL, hE⟩ := h
    refine ⟨?_, ?_⟩
    · cases hm : r'.lookup p.vaddr with
      | none => rw [hm] at hL; cases hL
      | some e =>
        rw [hm] at hL
        have : r.lookup p.vaddr = some e := hSub p.vaddr e hm
        rw [this]; exact hL
    · rw [← hEp]; exact hE

/-- **A page not live before a shrinking step is not live after it.** -/
theorem mappedPageLive_false_of_shrink {st st' : SystemState} (hW : teardownWellFormed st)
    (hS : vspaceRootsShrink st st') {p : MappedPage} (h : mappedPageLive st p = false) :
    mappedPageLive st' p = false := by
  cases h' : mappedPageLive st' p
  · rfl
  · rw [mappedPageLive_of_shrink hW hS h'] at h; cases h

-- ============================================================================
-- §3  One page's unmap
-- ============================================================================

/-- The unmap's later steps — the flush, the shootdown round, the drain and the
instruction-cache broadcast — write neither the object table nor the ASID
table: those are the store's. -/
theorem unmapPageState_tables {ec : Concurrency.CoreId} {asid : SeLe4n.ASID}
    {vaddr : SeLe4n.VAddr} {st : SystemState} {rid : SeLe4n.ObjId} {r r' : VSpaceRoot}
    (hR : Architecture.resolveAsidRoot st asid = some (rid, r))
    (hU : r.unmapPage vaddr = some r') :
    let sS := storeObjectState rid (.vspaceRoot r')
      (Architecture.recordPhysicalWrites st (Architecture.mappingStore? st r' vaddr).toList)
    (unmapPageState ec asid vaddr st).objects = sS.objects ∧
      (unmapPageState ec asid vaddr st).asidTable = sS.asidTable := by
  unfold unmapPageState
  rw [hR]
  simp only [hU]
  cases Architecture.unmapIcacheOperand st asid vaddr <;> exact ⟨rfl, rfl⟩

/-- **One page's unmap keeps the state well formed, shrinks its root, and the
ASID then resolves to the root without the page.** -/
theorem unmapPageState_wellFormed {ec : Concurrency.CoreId} {asid : SeLe4n.ASID}
    {vaddr : SeLe4n.VAddr} {st : SystemState} {rid : SeLe4n.ObjId} {r r' : VSpaceRoot}
    (hW : teardownWellFormed st)
    (hR : Architecture.resolveAsidRoot st asid = some (rid, r))
    (hU : r.unmapPage vaddr = some r') :
    teardownWellFormed (unmapPageState ec asid vaddr st) ∧
      vspaceRootsShrink st (unmapPageState ec asid vaddr st) ∧
      Architecture.resolveAsidRoot (unmapPageState ec asid vaddr st) asid = some (rid, r') := by
  obtain ⟨-, hObj, hAsidR⟩ := Architecture.resolveAsidRoot_some_implies_obj st asid rid r hR
  let sR := Architecture.recordPhysicalWrites st (Architecture.mappingStore? st r' vaddr).toList
  let sS := storeObjectState rid (.vspaceRoot r') sR
  have hWR : teardownWellFormed sR := teardownWellFormed_of_tables_eq rfl rfl hW
  have hObjR : sR.objects[rid]? = some (.vspaceRoot r) := hObj
  have hStore : storeObject rid (.vspaceRoot r') sR = .ok ((), sS) :=
    storeObject_eq_storeObjectState _ _ _
  have hK : r.mappings.invExtK := hW.2.2.2.2.2.2.2.2.2 rid r hObj
  have hAsid : r'.asid = r.asid := VSpaceRoot.unmapPage_asid_eq r r' vaddr hU
  have hSub := Architecture.VSpaceRoot.unmapPage_mappings_sub r r' vaddr hK hU
  have hRest : r'.mappingEpochs = r.mappingEpochs ∧ r'.tables = r.tables := by
    unfold VSpaceRoot.unmapPage at hU
    cases hm : r.mappings[vaddr]? with
    | none => rw [hm] at hU; cases hU
    | some _ => rw [hm] at hU; cases hU; exact ⟨rfl, rfl⟩
  obtain ⟨hB, hA⟩ := Architecture.storeObject_shrunkRoot_preserves_vspaceInvariantBundle
    sR sS rid r r' hWR.2.2 hWR.1 hWR.2.1 hObjR hAsid hSub
    (Architecture.VSpaceRoot.unmapPage_mappings_invExtK r r' vaddr hK hU) hStore
  have hWStored : teardownWellFormed sS :=
    ⟨storeObject_preserves_objects_invExt sR sS _ _ hWR.1 hStore, hA, hB⟩
  obtain ⟨hO, hT⟩ := unmapPageState_tables (ec := ec) hR hU
  have hW' : teardownWellFormed (unmapPageState ec asid vaddr st) :=
    teardownWellFormed_of_tables_eq hO hT hWStored
  have hShrink : vspaceRootsShrink st sS :=
    (vspaceRootsShrink_of_tables_eq (st := st) (st' := sR) rfl).trans
      (vspaceRootsShrink_of_store hWR.1 hObjR hStore hAsid hSub hRest.1
        (fun s hs => hRest.2 ▸ hs))
  have hObj' : (unmapPageState ec asid vaddr st).objects[rid]? = some (.vspaceRoot r') := by
    rw [hO]; exact storeObject_objects_eq sR sS rid _ hWR.1 hStore
  refine ⟨hW', hShrink.trans (vspaceRootsShrink_of_tables_eq hO), ?_⟩
  have := resolveAsidRoot_of_root hW' hObj'
  rwa [hAsid, hAsidR] at this

/-- **The page an unmap names is not live after it.** -/
theorem unmapPageState_clears {ec : Concurrency.CoreId} {st : SystemState} {p : MappedPage}
    {rid : SeLe4n.ObjId} {r r' : VSpaceRoot} (hW : teardownWellFormed st)
    (hR : Architecture.resolveAsidRoot st p.asid = some (rid, r))
    (hU : r.unmapPage p.vaddr = some r') :
    mappedPageLive (unmapPageState ec p.asid p.vaddr st) p = false := by
  obtain ⟨-, hObj, -⟩ := Architecture.resolveAsidRoot_some_implies_obj st p.asid rid r hR
  have hK : r.mappings.invExtK := hW.2.2.2.2.2.2.2.2.2 rid r hObj
  obtain ⟨-, -, hR'⟩ := unmapPageState_wellFormed (ec := ec) hW hR hU
  unfold mappedPageLive
  rw [hR']
  simp only [VSpaceRoot.lookup_unmapPage_eq_none r r' p.vaddr hK.1 hU]
  rfl

-- ============================================================================
-- §4  The unmap pass
-- ============================================================================

/-- **The unmap pass clears every page it lists**, keeps the state well formed,
and only shrinks roots — the result the finalising destroyers decided
afterwards, and refused on, before `v0.36.110`. -/
theorem unmapLivePagesState_clears (ec : Concurrency.CoreId) :
    ∀ (ps : List MappedPage) (st : SystemState), teardownWellFormed st →
      teardownWellFormed (unmapLivePagesState ec ps st) ∧
        vspaceRootsShrink st (unmapLivePagesState ec ps st) ∧
        ∀ p ∈ ps, mappedPageLive (unmapLivePagesState ec ps st) p = false
  | [], st, hW => ⟨hW, vspaceRootsShrink.refl st, fun _ h => by cases h⟩
  | p :: rest, st, hW => by
    unfold unmapLivePagesState
    split
    · next hL =>
      obtain ⟨rid, r, r', hR, hU⟩ := mappedPageLive_unmapPage hL
      obtain ⟨hW1, hS1, -⟩ := unmapPageState_wellFormed (ec := ec) hW hR hU
      have hC1 := unmapPageState_clears (ec := ec) hW hR hU
      obtain ⟨hW2, hS2, hC2⟩ := unmapLivePagesState_clears ec rest _ hW1
      refine ⟨hW2, hS1.trans hS2, fun q hq => ?_⟩
      rcases List.mem_cons.mp hq with rfl | hq
      · exact mappedPageLive_false_of_shrink hW1 hS2 hC1
      · exact hC2 q hq
    · next hL =>
      obtain ⟨hW2, hS2, hC2⟩ := unmapLivePagesState_clears ec rest st hW
      refine ⟨hW2, hS2, fun q hq => ?_⟩
      rcases List.mem_cons.mp hq with rfl | hq
      · exact mappedPageLive_false_of_shrink hW hS2 (by simpa using hL)
      · exact hC2 q hq

end SeLe4n.Kernel
