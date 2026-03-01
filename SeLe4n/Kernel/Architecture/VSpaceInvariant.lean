import SeLe4n.Kernel.Architecture.VSpace

/-!
# VSpace Invariant Bundle (WS-B1 / F-08 / TPI-D05)

This module defines the VSpace invariant components (ASID-root uniqueness, non-overlap)
and the composed bundle entrypoint. It contains both error-case and success-path
preservation theorems, as well as round-trip theorems closing TPI-001 from WS-C.

## Proof scope qualification (F-16)

**Substantive preservation theorems** (high assurance — prove invariant preservation
over *changed* state after a *successful* operation):
- `vspaceMapPage_success_preserves_vspaceInvariantBundle`
- `vspaceUnmapPage_success_preserves_vspaceInvariantBundle`

**Round-trip / functional-correctness theorems** (high assurance — prove semantic
contracts between VSpace operations, closing TPI-001 from WS-C):
- `vspaceLookup_after_map`
- `vspaceLookup_map_other`
- `vspaceLookup_after_unmap`
- `vspaceLookup_unmap_other`

**Error-case preservation theorems** (trivially true — the error path returns
unchanged state, so any pre-state invariant holds trivially in the post-state):
- `vspaceMapPage_error_asidNotBound_preserves_vspaceInvariantBundle`
- `vspaceUnmapPage_error_translationFault_preserves_vspaceInvariantBundle`

Error-case theorems are retained for proof-surface completeness and compositional
coverage, but they do not constitute meaningful security evidence.
-/

namespace SeLe4n.Kernel.Architecture

open SeLe4n.Model

/-- Every modeled VSpace root preserves deterministic non-overlap for virtual mappings. -/
def vspaceRootNonOverlap (st : SystemState) : Prop :=
  ∀ (oid : SeLe4n.ObjId) (root : VSpaceRoot),
    st.objects[oid]? = some (KernelObject.vspaceRoot root) →
    VSpaceRoot.noVirtualOverlap root

/-- WS-G3/F-P06: ASID table consistency — bidirectional agreement between
    `asidTable` and VSpaceRoot objects in the object store.

    **Soundness**: every `asidTable` entry points to a valid VSpaceRoot with matching ASID.
    **Completeness**: every VSpaceRoot object has its ASID registered in the table. -/
def asidTableConsistent (st : SystemState) : Prop :=
  (∀ asid oid, st.asidTable[asid]? = some oid →
    ∃ root, st.objects[oid]? = some (KernelObject.vspaceRoot root) ∧ root.asid = asid) ∧
  (∀ oid root, st.objects[oid]? = some (KernelObject.vspaceRoot root) →
    st.asidTable[root.asid]? = some oid)

/-- Bounded translation surface: all translated physical addresses are in the finite machine window.

**Status:** Forward declaration for WS-E6 (model completeness). Not yet integrated into
`vspaceInvariantBundle` or consumed by any preservation theorem. -/
def boundedAddressTranslation (st : SystemState) (bound : Nat) : Prop :=
  ∀ (oid : SeLe4n.ObjId) (root : VSpaceRoot) (v : SeLe4n.VAddr) (p : SeLe4n.PAddr),
    st.objects[oid]? = some (KernelObject.vspaceRoot root) →
    (v, p) ∈ root.mappings →
    p.toNat < bound

/-- WS-B1/WS-G3 architecture/VSpace invariant bundle entrypoint. -/
def vspaceInvariantBundle (st : SystemState) : Prop :=
  vspaceAsidRootsUnique st ∧ vspaceRootNonOverlap st ∧ asidTableConsistent st

-- ============================================================================
-- WS-G3: Shared asidTableConsistent preservation helper
-- ============================================================================

/-- WS-G3: After storing a VSpaceRoot whose ASID is preserved from the original,
    `asidTableConsistent` is preserved. Used by both map and unmap success-path
    preservation theorems to avoid proof duplication. -/
private theorem asidTableConsistent_of_storeObject_vspaceRoot
    (st st' : SystemState)
    (rootId : SeLe4n.ObjId) (root root' : VSpaceRoot)
    (hStore : storeObject rootId (.vspaceRoot root') st = .ok ((), st'))
    (hObjRoot : st.objects[rootId]? = some (KernelObject.vspaceRoot root))
    (hObjEq : st'.objects[rootId]? = some (.vspaceRoot root'))
    (hObjNe : ∀ oid, oid ≠ rootId → st'.objects[oid]? = st.objects[oid]?)
    (hAsidPreserved : root'.asid = root.asid)
    (hUniq : vspaceAsidRootsUnique st)
    (hConsist : asidTableConsistent st) :
    asidTableConsistent st' := by
  have hTableNew : st'.asidTable[root'.asid]? = some rootId :=
    storeObject_asidTable_vspaceRoot st st' rootId root' hStore
  have hTableNe : ∀ a, a ≠ root'.asid → st'.asidTable[a]? =
      (match st.objects[rootId]? with
       | some (.vspaceRoot oldRoot) => (st.asidTable.erase oldRoot.asid)[a]?
       | _ => st.asidTable[a]?) :=
    fun a hNe => storeObject_asidTable_vspaceRoot_ne st st' rootId root' a hNe hStore
  rcases hConsist with ⟨hSound, hComplete⟩
  constructor
  -- Soundness
  · intro a oid hLookup
    by_cases hAEq : a = root'.asid
    · subst hAEq
      rw [hTableNew] at hLookup
      cases hLookup
      exact ⟨root', hObjEq, rfl⟩
    · have hLookup' := hTableNe a hAEq
      rw [hLookup'] at hLookup
      simp only [hObjRoot] at hLookup
      have hAsidNeRoot : a ≠ root.asid := by
        rw [← hAsidPreserved]; exact hAEq
      rw [HashMap_getElem?_erase] at hLookup
      have hEraseNe : ¬((root.asid == a) = true) := by
        intro h; exact hAsidNeRoot (eq_of_beq h).symm
      simp only [hEraseNe] at hLookup
      rcases hSound a oid hLookup with ⟨r, hObjR, hAsidR⟩
      by_cases hOidEq : oid = rootId
      · subst hOidEq
        rw [hObjRoot] at hObjR; cases hObjR
        exfalso; exact hAEq (hAsidPreserved.trans hAsidR).symm
      · exact ⟨r, (hObjNe oid hOidEq).symm ▸ hObjR, hAsidR⟩
  -- Completeness
  · intro oid' r' hObjR
    by_cases hOidEq : oid' = rootId
    · subst hOidEq
      rw [hObjEq] at hObjR
      have hR'Eq := KernelObject.vspaceRoot.inj (Option.some.inj hObjR)
      subst hR'Eq
      exact hTableNew
    · rw [hObjNe oid' hOidEq] at hObjR
      have hPre := hComplete oid' r' hObjR
      have hAsidNe : r'.asid ≠ root.asid := by
        intro h
        have := hUniq oid' rootId r' root hObjR hObjRoot h
        exact hOidEq this
      by_cases hAEq : r'.asid = root'.asid
      · exact absurd (hAEq.trans hAsidPreserved) hAsidNe
      · rw [hTableNe r'.asid hAEq]
        simp only [hObjRoot]
        rw [HashMap_getElem?_erase]
        have hEraseNe : ¬((root.asid == r'.asid) = true) := by
          intro h; exact hAsidNe (eq_of_beq h).symm
        simp only [hEraseNe]
        exact hPre

-- ============================================================================
-- Error-case preservation (trivial — see F-16 classification above)
-- ============================================================================

theorem vspaceMapPage_error_asidNotBound_preserves_vspaceInvariantBundle
    (st : SystemState)
    (asid : SeLe4n.ASID)
    (vaddr : SeLe4n.VAddr)
    (paddr : SeLe4n.PAddr)
    (_hErr : vspaceMapPage asid vaddr paddr st = .error .asidNotBound) :
    vspaceInvariantBundle st → vspaceInvariantBundle st := by
  intro hInv
  exact hInv

theorem vspaceUnmapPage_error_translationFault_preserves_vspaceInvariantBundle
    (st : SystemState)
    (asid : SeLe4n.ASID)
    (vaddr : SeLe4n.VAddr)
    (_hErr : vspaceUnmapPage asid vaddr st = .error .translationFault) :
    vspaceInvariantBundle st → vspaceInvariantBundle st := by
  intro hInv
  exact hInv

-- ============================================================================
-- F-08 / TPI-D05: VSpace successful-operation invariant preservation
-- ============================================================================

/-- F-08/WS-G3: A successful `vspaceMapPage` preserves the VSpace invariant bundle.

    The proof decomposes into three obligations:
    1. ASID-root uniqueness is preserved because `mapPage` preserves the root's ASID.
    2. Non-overlap is preserved because `mapPage` only succeeds when no mapping
       for the target vaddr already exists.
    3. ASID table consistency is preserved because `storeObject` maintains the
       ASID table and `mapPage` preserves the root's ASID. -/
theorem vspaceMapPage_success_preserves_vspaceInvariantBundle
    (st st' : SystemState)
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) (paddr : SeLe4n.PAddr)
    (hInv : vspaceInvariantBundle st)
    (hStep : vspaceMapPage asid vaddr paddr st = .ok ((), st')) :
    vspaceInvariantBundle st' := by
  unfold vspaceMapPage at hStep
  cases hResolve : resolveAsidRoot st asid with
  | none => simp [hResolve] at hStep
  | some pair =>
      rcases pair with ⟨rootId, root⟩
      cases hMapRoot : root.mapPage vaddr paddr with
      | none => simp [hResolve, hMapRoot] at hStep
      | some root' =>
          have hStore : storeObject rootId (.vspaceRoot root') st = .ok ((), st') := by
            simpa [hResolve, hMapRoot] using hStep
          rcases resolveAsidRoot_some_implies_obj st asid rootId root hResolve with ⟨_, hObjRoot, hAsidRoot⟩
          have hObjEq : st'.objects[rootId]? = some (.vspaceRoot root') :=
            storeObject_objects_eq st st' rootId (.vspaceRoot root') hStore
          have hObjNe : ∀ oid, oid ≠ rootId → st'.objects[oid]? = st.objects[oid]? :=
            fun oid hNe => storeObject_objects_ne st st' rootId oid (.vspaceRoot root') hNe hStore
          have hAsidPreserved : root'.asid = root.asid :=
            VSpaceRoot.mapPage_asid_eq root root' vaddr paddr hMapRoot
          rcases hInv with ⟨hUniq, hNoOverlap, hConsist⟩
          refine ⟨?_, ?_, ?_⟩
          -- 1. vspaceAsidRootsUnique st'
          · intro oid₁ oid₂ r₁ r₂ hObj₁ hObj₂ hAsidEq
            by_cases h₁ : oid₁ = rootId <;> by_cases h₂ : oid₂ = rootId
            · exact h₁.trans h₂.symm
            · rw [h₁] at hObj₁
              rw [hObjEq] at hObj₁; cases hObj₁
              rw [hObjNe oid₂ h₂] at hObj₂
              exfalso
              have : rootId = oid₂ :=
                hUniq rootId oid₂ root r₂ hObjRoot hObj₂
                  (hAsidPreserved.symm ▸ hAsidEq)
              exact h₂ this.symm
            · rw [h₂] at hObj₂
              rw [hObjEq] at hObj₂; cases hObj₂
              rw [hObjNe oid₁ h₁] at hObj₁
              exfalso
              have : oid₁ = rootId :=
                hUniq oid₁ rootId r₁ root hObj₁ hObjRoot
                  (hAsidEq.trans hAsidPreserved)
              exact h₁ this
            · rw [hObjNe oid₁ h₁] at hObj₁
              rw [hObjNe oid₂ h₂] at hObj₂
              exact hUniq oid₁ oid₂ r₁ r₂ hObj₁ hObj₂ hAsidEq
          -- 2. vspaceRootNonOverlap st'
          · intro oid r hObj
            by_cases hEq : oid = rootId
            · rw [hEq] at hObj
              rw [hObjEq] at hObj; cases hObj
              exact VSpaceRoot.mapPage_noVirtualOverlap root root' vaddr paddr
                (hNoOverlap rootId root hObjRoot) hMapRoot
            · rw [hObjNe oid hEq] at hObj
              exact hNoOverlap oid r hObj
          -- 3. asidTableConsistent st' (via shared helper)
          · exact asidTableConsistent_of_storeObject_vspaceRoot
              st st' rootId root root' hStore hObjRoot hObjEq hObjNe hAsidPreserved hUniq hConsist

/-- F-08/WS-G3: A successful `vspaceUnmapPage` preserves the VSpace invariant bundle.

    The proof decomposes into three obligations:
    1. ASID-root uniqueness is preserved because `unmapPage` preserves the root's ASID.
    2. Non-overlap is preserved because `unmapPage` only removes entries,
       which cannot create new virtual-address conflicts.
    3. ASID table consistency is preserved because `storeObject` maintains the
       ASID table and `unmapPage` preserves the root's ASID. -/
theorem vspaceUnmapPage_success_preserves_vspaceInvariantBundle
    (st st' : SystemState)
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (hInv : vspaceInvariantBundle st)
    (hStep : vspaceUnmapPage asid vaddr st = .ok ((), st')) :
    vspaceInvariantBundle st' := by
  unfold vspaceUnmapPage at hStep
  cases hResolve : resolveAsidRoot st asid with
  | none => simp [hResolve] at hStep
  | some pair =>
      rcases pair with ⟨rootId, root⟩
      cases hUnmapRoot : root.unmapPage vaddr with
      | none => simp [hResolve, hUnmapRoot] at hStep
      | some root' =>
          have hStore : storeObject rootId (.vspaceRoot root') st = .ok ((), st') := by
            simpa [hResolve, hUnmapRoot] using hStep
          rcases resolveAsidRoot_some_implies_obj st asid rootId root hResolve with ⟨_, hObjRoot, hAsidRoot⟩
          have hObjEq : st'.objects[rootId]? = some (.vspaceRoot root') :=
            storeObject_objects_eq st st' rootId (.vspaceRoot root') hStore
          have hObjNe : ∀ oid, oid ≠ rootId → st'.objects[oid]? = st.objects[oid]? :=
            fun oid hNe => storeObject_objects_ne st st' rootId oid (.vspaceRoot root') hNe hStore
          have hAsidPreserved : root'.asid = root.asid :=
            VSpaceRoot.unmapPage_asid_eq root root' vaddr hUnmapRoot
          rcases hInv with ⟨hUniq, hNoOverlap, hConsist⟩
          refine ⟨?_, ?_, ?_⟩
          -- 1. vspaceAsidRootsUnique st'
          · intro oid₁ oid₂ r₁ r₂ hObj₁ hObj₂ hAsidEq
            by_cases h₁ : oid₁ = rootId <;> by_cases h₂ : oid₂ = rootId
            · exact h₁.trans h₂.symm
            · rw [h₁] at hObj₁
              rw [hObjEq] at hObj₁; cases hObj₁
              rw [hObjNe oid₂ h₂] at hObj₂
              exfalso
              have : rootId = oid₂ :=
                hUniq rootId oid₂ root r₂ hObjRoot hObj₂
                  (hAsidPreserved.symm ▸ hAsidEq)
              exact h₂ this.symm
            · rw [h₂] at hObj₂
              rw [hObjEq] at hObj₂; cases hObj₂
              rw [hObjNe oid₁ h₁] at hObj₁
              exfalso
              have : oid₁ = rootId :=
                hUniq oid₁ rootId r₁ root hObj₁ hObjRoot
                  (hAsidEq.trans hAsidPreserved)
              exact h₁ this
            · rw [hObjNe oid₁ h₁] at hObj₁
              rw [hObjNe oid₂ h₂] at hObj₂
              exact hUniq oid₁ oid₂ r₁ r₂ hObj₁ hObj₂ hAsidEq
          -- 2. vspaceRootNonOverlap st'
          · intro oid r hObj
            by_cases hEq : oid = rootId
            · rw [hEq] at hObj
              rw [hObjEq] at hObj; cases hObj
              exact VSpaceRoot.unmapPage_noVirtualOverlap root root' vaddr
                (hNoOverlap rootId root hObjRoot) hUnmapRoot
            · rw [hObjNe oid hEq] at hObj
              exact hNoOverlap oid r hObj
          -- 3. asidTableConsistent st' (via shared helper)
          · exact asidTableConsistent_of_storeObject_vspaceRoot
              st st' rootId root root' hStore hObjRoot hObjEq hObjNe hAsidPreserved hUniq hConsist

-- ============================================================================
-- TPI-D05 / TPI-001: VSpace round-trip theorems
-- ============================================================================

/-- TPI-001 round-trip #1: After a successful `vspaceMapPage`, `vspaceLookup` on the same
    ASID and vaddr returns the mapped physical address.

    WS-G3: Simplified — `resolveAsidRoot` uses `asidTable` directly, so no `objectIndexSetSync`
    hypothesis or objectIndex reasoning needed. -/
theorem vspaceLookup_after_map
    (st st' : SystemState)
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) (paddr : SeLe4n.PAddr)
    (_hInv : vspaceInvariantBundle st)
    (hStep : vspaceMapPage asid vaddr paddr st = .ok ((), st')) :
    vspaceLookup asid vaddr st' = .ok (paddr, st') := by
  unfold vspaceMapPage at hStep
  cases hResolve : resolveAsidRoot st asid with
  | none => simp [hResolve] at hStep
  | some pair =>
      rcases pair with ⟨rootId, root⟩
      cases hMapRoot : root.mapPage vaddr paddr with
      | none => simp [hResolve, hMapRoot] at hStep
      | some root' =>
          have hStore : storeObject rootId (.vspaceRoot root') st = .ok ((), st') := by
            simpa [hResolve, hMapRoot] using hStep
          rcases resolveAsidRoot_some_implies_obj st asid rootId root hResolve with ⟨_, _, hAsidRoot⟩
          have hAsidPreserved : root'.asid = root.asid :=
            VSpaceRoot.mapPage_asid_eq root root' vaddr paddr hMapRoot
          have hObjEq : st'.objects[rootId]? = some (.vspaceRoot root') :=
            storeObject_objects_eq st st' rootId (.vspaceRoot root') hStore
          -- WS-G3: Build post-state asidTable entry directly from storeObject lemma
          have hTablePost : st'.asidTable[root'.asid]? = some rootId :=
            storeObject_asidTable_vspaceRoot st st' rootId root' hStore
          have hAsidEq : root'.asid = asid := hAsidPreserved.trans hAsidRoot
          have hResolve' : resolveAsidRoot st' asid = some (rootId, root') :=
            resolveAsidRoot_of_asidTable_entry st' asid rootId root'
              (hAsidEq ▸ hTablePost) hObjEq hAsidEq
          have hLookupRoot' : root'.lookup vaddr = some paddr :=
            VSpaceRoot.lookup_mapPage_eq root root' vaddr paddr hMapRoot
          simp [vspaceLookup, hResolve', hLookupRoot']

/-- TPI-001 round-trip #2: A `vspaceMapPage` at vaddr does not affect `vspaceLookup` at
    a different vaddr'.

    WS-G3: Simplified — no `objectIndexSetSync` hypothesis needed. -/
theorem vspaceLookup_map_other
    (st st' : SystemState)
    (asid : SeLe4n.ASID) (vaddr vaddr' : SeLe4n.VAddr) (paddr : SeLe4n.PAddr)
    (hNe : vaddr ≠ vaddr')
    (_hInv : vspaceInvariantBundle st)
    (hStep : vspaceMapPage asid vaddr paddr st = .ok ((), st')) :
    (vspaceLookup asid vaddr' st').map Prod.fst = (vspaceLookup asid vaddr' st).map Prod.fst := by
  unfold vspaceMapPage at hStep
  cases hResolve : resolveAsidRoot st asid with
  | none => simp [hResolve] at hStep
  | some pair =>
      rcases pair with ⟨rootId, root⟩
      cases hMapRoot : root.mapPage vaddr paddr with
      | none => simp [hResolve, hMapRoot] at hStep
      | some root' =>
          have hStore : storeObject rootId (.vspaceRoot root') st = .ok ((), st') := by
            simpa [hResolve, hMapRoot] using hStep
          rcases resolveAsidRoot_some_implies_obj st asid rootId root hResolve with ⟨_, _, hAsidRoot⟩
          have hAsidPreserved : root'.asid = root.asid :=
            VSpaceRoot.mapPage_asid_eq root root' vaddr paddr hMapRoot
          have hObjEq : st'.objects[rootId]? = some (.vspaceRoot root') :=
            storeObject_objects_eq st st' rootId (.vspaceRoot root') hStore
          have hTablePost : st'.asidTable[root'.asid]? = some rootId :=
            storeObject_asidTable_vspaceRoot st st' rootId root' hStore
          have hAsidEq : root'.asid = asid := hAsidPreserved.trans hAsidRoot
          have hResolve' : resolveAsidRoot st' asid = some (rootId, root') :=
            resolveAsidRoot_of_asidTable_entry st' asid rootId root'
              (hAsidEq ▸ hTablePost) hObjEq hAsidEq
          have hLookupNe : root'.lookup vaddr' = root.lookup vaddr' :=
            VSpaceRoot.lookup_mapPage_ne root root' vaddr vaddr' paddr hNe hMapRoot
          simp [vspaceLookup, hResolve', hResolve, hLookupNe, Except.map]
          cases root.lookup vaddr' <;> rfl

/-- TPI-001 round-trip #3: After a successful `vspaceUnmapPage`, `vspaceLookup` on the
    unmapped vaddr returns a translation fault (no mapping).

    WS-G3: Simplified — no `objectIndexSetSync` hypothesis needed. -/
theorem vspaceLookup_after_unmap
    (st st' : SystemState)
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (_hInv : vspaceInvariantBundle st)
    (hStep : vspaceUnmapPage asid vaddr st = .ok ((), st')) :
    vspaceLookup asid vaddr st' = .error .translationFault := by
  unfold vspaceUnmapPage at hStep
  cases hResolve : resolveAsidRoot st asid with
  | none => simp [hResolve] at hStep
  | some pair =>
      rcases pair with ⟨rootId, root⟩
      cases hUnmapRoot : root.unmapPage vaddr with
      | none => simp [hResolve, hUnmapRoot] at hStep
      | some root' =>
          have hStore : storeObject rootId (.vspaceRoot root') st = .ok ((), st') := by
            simpa [hResolve, hUnmapRoot] using hStep
          rcases resolveAsidRoot_some_implies_obj st asid rootId root hResolve with ⟨_, _, hAsidRoot⟩
          have hAsidPreserved : root'.asid = root.asid :=
            VSpaceRoot.unmapPage_asid_eq root root' vaddr hUnmapRoot
          have hObjEq : st'.objects[rootId]? = some (.vspaceRoot root') :=
            storeObject_objects_eq st st' rootId (.vspaceRoot root') hStore
          have hTablePost : st'.asidTable[root'.asid]? = some rootId :=
            storeObject_asidTable_vspaceRoot st st' rootId root' hStore
          have hAsidEq : root'.asid = asid := hAsidPreserved.trans hAsidRoot
          have hResolve' : resolveAsidRoot st' asid = some (rootId, root') :=
            resolveAsidRoot_of_asidTable_entry st' asid rootId root'
              (hAsidEq ▸ hTablePost) hObjEq hAsidEq
          have hLookupNone : root'.lookup vaddr = none :=
            VSpaceRoot.lookup_unmapPage_eq_none root root' vaddr hUnmapRoot
          simp [vspaceLookup, hResolve', hLookupNone]

/-- TPI-001 round-trip #4: `vspaceUnmapPage` at vaddr does not affect `vspaceLookup` at
    a different vaddr'.

    WS-G3: Simplified — no `objectIndexSetSync` hypothesis needed. -/
theorem vspaceLookup_unmap_other
    (st st' : SystemState)
    (asid : SeLe4n.ASID) (vaddr vaddr' : SeLe4n.VAddr)
    (hNe : vaddr ≠ vaddr')
    (_hInv : vspaceInvariantBundle st)
    (hStep : vspaceUnmapPage asid vaddr st = .ok ((), st')) :
    (vspaceLookup asid vaddr' st').map Prod.fst = (vspaceLookup asid vaddr' st).map Prod.fst := by
  unfold vspaceUnmapPage at hStep
  cases hResolve : resolveAsidRoot st asid with
  | none => simp [hResolve] at hStep
  | some pair =>
      rcases pair with ⟨rootId, root⟩
      cases hUnmapRoot : root.unmapPage vaddr with
      | none => simp [hResolve, hUnmapRoot] at hStep
      | some root' =>
          have hStore : storeObject rootId (.vspaceRoot root') st = .ok ((), st') := by
            simpa [hResolve, hUnmapRoot] using hStep
          rcases resolveAsidRoot_some_implies_obj st asid rootId root hResolve with ⟨_, _, hAsidRoot⟩
          have hAsidPreserved : root'.asid = root.asid :=
            VSpaceRoot.unmapPage_asid_eq root root' vaddr hUnmapRoot
          have hObjEq : st'.objects[rootId]? = some (.vspaceRoot root') :=
            storeObject_objects_eq st st' rootId (.vspaceRoot root') hStore
          have hTablePost : st'.asidTable[root'.asid]? = some rootId :=
            storeObject_asidTable_vspaceRoot st st' rootId root' hStore
          have hAsidEq : root'.asid = asid := hAsidPreserved.trans hAsidRoot
          have hResolve' : resolveAsidRoot st' asid = some (rootId, root') :=
            resolveAsidRoot_of_asidTable_entry st' asid rootId root'
              (hAsidEq ▸ hTablePost) hObjEq hAsidEq
          have hLookupNe : root'.lookup vaddr' = root.lookup vaddr' :=
            VSpaceRoot.lookup_unmapPage_ne root root' vaddr vaddr' hNe hUnmapRoot
          simp [vspaceLookup, hResolve', hResolve, hLookupNe, Except.map]
          cases root.lookup vaddr' <;> rfl

end SeLe4n.Kernel.Architecture
