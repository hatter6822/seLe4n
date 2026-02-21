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
  ∀ oid root,
    st.objects oid = some (.vspaceRoot root) →
    VSpaceRoot.noVirtualOverlap root

/-- Bounded translation surface: all translated physical addresses are in the finite machine window. -/
def boundedAddressTranslation (st : SystemState) (bound : Nat) : Prop :=
  ∀ oid root v p,
    st.objects oid = some (.vspaceRoot root) →
    (v, p) ∈ root.mappings →
    p.toNat < bound

/-- WS-B1 architecture/VSpace invariant bundle entrypoint. -/
def vspaceInvariantBundle (st : SystemState) : Prop :=
  vspaceAsidRootsUnique st ∧ vspaceRootNonOverlap st

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

/-- F-08: A successful `vspaceMapPage` preserves the VSpace invariant bundle.

    The proof decomposes into two obligations:
    1. ASID-root uniqueness is preserved because `mapPage` preserves the root's ASID.
    2. Non-overlap is preserved because `mapPage` only succeeds when no mapping
       for the target vaddr already exists. -/
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
          rcases resolveAsidRoot_some_implies st asid rootId root hResolve with ⟨hObjRoot, hAsidRoot, _⟩
          have hObjEq : st'.objects rootId = some (.vspaceRoot root') :=
            storeObject_objects_eq st st' rootId (.vspaceRoot root') hStore
          have hObjNe : ∀ oid, oid ≠ rootId → st'.objects oid = st.objects oid :=
            fun oid hNe => storeObject_objects_ne st st' rootId oid (.vspaceRoot root') hNe hStore
          have hAsidPreserved : root'.asid = root.asid :=
            VSpaceRoot.mapPage_asid_eq root root' vaddr paddr hMapRoot
          rcases hInv with ⟨hUniq, hNoOverlap⟩
          refine ⟨?_, ?_⟩
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

/-- F-08: A successful `vspaceUnmapPage` preserves the VSpace invariant bundle.

    The proof decomposes into two obligations:
    1. ASID-root uniqueness is preserved because `unmapPage` preserves the root's ASID.
    2. Non-overlap is preserved because `unmapPage` only removes entries,
       which cannot create new virtual-address conflicts. -/
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
          rcases resolveAsidRoot_some_implies st asid rootId root hResolve with ⟨hObjRoot, hAsidRoot, _⟩
          have hObjEq : st'.objects rootId = some (.vspaceRoot root') :=
            storeObject_objects_eq st st' rootId (.vspaceRoot root') hStore
          have hObjNe : ∀ oid, oid ≠ rootId → st'.objects oid = st.objects oid :=
            fun oid hNe => storeObject_objects_ne st st' rootId oid (.vspaceRoot root') hNe hStore
          have hAsidPreserved : root'.asid = root.asid :=
            VSpaceRoot.unmapPage_asid_eq root root' vaddr hUnmapRoot
          rcases hInv with ⟨hUniq, hNoOverlap⟩
          refine ⟨?_, ?_⟩
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

-- ============================================================================
-- TPI-D05 / TPI-001: VSpace round-trip theorems
-- ============================================================================

/-- TPI-001 round-trip #1: After a successful `vspaceMapPage`, `vspaceLookup` on the same
    ASID and vaddr returns the mapped physical address. -/
theorem vspaceLookup_after_map
    (st st' : SystemState)
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) (paddr : SeLe4n.PAddr)
    (hInv : vspaceInvariantBundle st)
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
          rcases resolveAsidRoot_some_implies st asid rootId root hResolve with ⟨hObjRoot, hAsidRoot, hMemIdx⟩
          have hAsidPreserved : root'.asid = root.asid :=
            VSpaceRoot.mapPage_asid_eq root root' vaddr paddr hMapRoot
          -- Build post-state resolveAsidRoot result
          have hObjEq : st'.objects rootId = some (.vspaceRoot root') :=
            storeObject_objects_eq st st' rootId (.vspaceRoot root') hStore
          have hIdxEq : st'.objectIndex = st.objectIndex :=
            storeObject_objectIndex_eq_of_mem st st' rootId (.vspaceRoot root') hMemIdx hStore
          -- Prove post-state ASID uniqueness for resolveAsidRoot characterization
          have hInv' : vspaceInvariantBundle st' :=
            vspaceMapPage_success_preserves_vspaceInvariantBundle st st' asid vaddr paddr hInv
              (by simp [vspaceMapPage, hResolve, hMapRoot, hStore])
          have hResolve' : resolveAsidRoot st' asid = some (rootId, root') :=
            resolveAsidRoot_of_unique_root st' asid rootId root'
              hObjEq (hAsidPreserved.trans hAsidRoot) (hIdxEq ▸ hMemIdx) hInv'.1
          have hLookupRoot' : root'.lookup vaddr = some paddr :=
            VSpaceRoot.lookup_mapPage_eq root root' vaddr paddr hMapRoot
          simp [vspaceLookup, hResolve', hLookupRoot']

/-- TPI-001 round-trip #2: A `vspaceMapPage` at vaddr does not affect `vspaceLookup` at
    a different vaddr'. -/
theorem vspaceLookup_map_other
    (st st' : SystemState)
    (asid : SeLe4n.ASID) (vaddr vaddr' : SeLe4n.VAddr) (paddr : SeLe4n.PAddr)
    (hNe : vaddr ≠ vaddr')
    (hInv : vspaceInvariantBundle st)
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
          rcases resolveAsidRoot_some_implies st asid rootId root hResolve with ⟨hObjRoot, hAsidRoot, hMemIdx⟩
          have hAsidPreserved : root'.asid = root.asid :=
            VSpaceRoot.mapPage_asid_eq root root' vaddr paddr hMapRoot
          have hObjEq : st'.objects rootId = some (.vspaceRoot root') :=
            storeObject_objects_eq st st' rootId (.vspaceRoot root') hStore
          have hIdxEq : st'.objectIndex = st.objectIndex :=
            storeObject_objectIndex_eq_of_mem st st' rootId (.vspaceRoot root') hMemIdx hStore
          have hInv' : vspaceInvariantBundle st' :=
            vspaceMapPage_success_preserves_vspaceInvariantBundle st st' asid vaddr paddr hInv
              (by simp [vspaceMapPage, hResolve, hMapRoot, hStore])
          have hResolve' : resolveAsidRoot st' asid = some (rootId, root') :=
            resolveAsidRoot_of_unique_root st' asid rootId root'
              hObjEq (hAsidPreserved.trans hAsidRoot) (hIdxEq ▸ hMemIdx) hInv'.1
          have hLookupNe : root'.lookup vaddr' = root.lookup vaddr' :=
            VSpaceRoot.lookup_mapPage_ne root root' vaddr vaddr' paddr hNe hMapRoot
          simp [vspaceLookup, hResolve', hResolve, hLookupNe, Except.map]
          cases root.lookup vaddr' <;> rfl

/-- TPI-001 round-trip #3: After a successful `vspaceUnmapPage`, `vspaceLookup` on the
    unmapped vaddr returns a translation fault (no mapping). -/
theorem vspaceLookup_after_unmap
    (st st' : SystemState)
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (hInv : vspaceInvariantBundle st)
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
          rcases resolveAsidRoot_some_implies st asid rootId root hResolve with ⟨hObjRoot, hAsidRoot, hMemIdx⟩
          have hAsidPreserved : root'.asid = root.asid :=
            VSpaceRoot.unmapPage_asid_eq root root' vaddr hUnmapRoot
          have hObjEq : st'.objects rootId = some (.vspaceRoot root') :=
            storeObject_objects_eq st st' rootId (.vspaceRoot root') hStore
          have hIdxEq : st'.objectIndex = st.objectIndex :=
            storeObject_objectIndex_eq_of_mem st st' rootId (.vspaceRoot root') hMemIdx hStore
          have hInv' : vspaceInvariantBundle st' :=
            vspaceUnmapPage_success_preserves_vspaceInvariantBundle st st' asid vaddr hInv
              (by simp [vspaceUnmapPage, hResolve, hUnmapRoot, hStore])
          have hResolve' : resolveAsidRoot st' asid = some (rootId, root') :=
            resolveAsidRoot_of_unique_root st' asid rootId root'
              hObjEq (hAsidPreserved.trans hAsidRoot) (hIdxEq ▸ hMemIdx) hInv'.1
          have hLookupNone : root'.lookup vaddr = none :=
            VSpaceRoot.lookup_unmapPage_eq_none root root' vaddr hUnmapRoot
          simp [vspaceLookup, hResolve', hLookupNone]

/-- TPI-001 round-trip #4: `vspaceUnmapPage` at vaddr does not affect `vspaceLookup` at
    a different vaddr'. -/
theorem vspaceLookup_unmap_other
    (st st' : SystemState)
    (asid : SeLe4n.ASID) (vaddr vaddr' : SeLe4n.VAddr)
    (hNe : vaddr ≠ vaddr')
    (hInv : vspaceInvariantBundle st)
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
          rcases resolveAsidRoot_some_implies st asid rootId root hResolve with ⟨hObjRoot, hAsidRoot, hMemIdx⟩
          have hAsidPreserved : root'.asid = root.asid :=
            VSpaceRoot.unmapPage_asid_eq root root' vaddr hUnmapRoot
          have hObjEq : st'.objects rootId = some (.vspaceRoot root') :=
            storeObject_objects_eq st st' rootId (.vspaceRoot root') hStore
          have hIdxEq : st'.objectIndex = st.objectIndex :=
            storeObject_objectIndex_eq_of_mem st st' rootId (.vspaceRoot root') hMemIdx hStore
          have hInv' : vspaceInvariantBundle st' :=
            vspaceUnmapPage_success_preserves_vspaceInvariantBundle st st' asid vaddr hInv
              (by simp [vspaceUnmapPage, hResolve, hUnmapRoot, hStore])
          have hResolve' : resolveAsidRoot st' asid = some (rootId, root') :=
            resolveAsidRoot_of_unique_root st' asid rootId root'
              hObjEq (hAsidPreserved.trans hAsidRoot) (hIdxEq ▸ hMemIdx) hInv'.1
          have hLookupNe : root'.lookup vaddr' = root.lookup vaddr' :=
            VSpaceRoot.lookup_unmapPage_ne root root' vaddr vaddr' hNe hUnmapRoot
          simp [vspaceLookup, hResolve', hResolve, hLookupNe, Except.map]
          cases root.lookup vaddr' <;> rfl

end SeLe4n.Kernel.Architecture
