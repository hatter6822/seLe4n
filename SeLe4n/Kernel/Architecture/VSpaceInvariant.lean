/-!
# VSpace Invariant Preservation Proofs

This module contains invariant definitions and preservation theorems for the VSpace
(virtual address space) subsystem.

## Proof classification (WS-D3 / F-16)

**Substantive preservation theorems** (high assurance — prove invariant preservation
over *changed* state after a *successful* operation):
- `vspaceMapPage_success_preserves_vspaceInvariantBundle`
- `vspaceUnmapPage_success_preserves_vspaceInvariantBundle`

**Round-trip / functional-correctness theorems** (high assurance — prove semantic
contracts between VSpace operations):
- `vspaceLookup_after_map`
- `vspaceLookup_map_other`
- `vspaceLookup_after_unmap`

**Error-case preservation theorems** (trivially true — the error path returns
unchanged state, so any pre-state invariant holds trivially in the post-state):
- `vspaceMapPage_error_asidNotBound_preserves_vspaceInvariantBundle`
- `vspaceUnmapPage_error_translationFault_preserves_vspaceInvariantBundle`

Error-case theorems are retained for proof-surface completeness and compositional
coverage, but they do not constitute meaningful security evidence.
-/
import SeLe4n.Kernel.Architecture.VSpace

namespace SeLe4n.Kernel.Architecture

open SeLe4n.Model

/-- ASID roots in the bounded discovery window are unique. -/
def vspaceAsidRootsUnique (st : SystemState) : Prop :=
  ∀ oid₁ oid₂ root₁ root₂,
    st.objects oid₁ = some (.vspaceRoot root₁) →
    st.objects oid₂ = some (.vspaceRoot root₂) →
    root₁.asid = root₂.asid →
    oid₁ = oid₂

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
-- F-08 / TPI-D05: VSpace success-path invariant preservation
-- ============================================================================

/-- Helper: `storeObject` at `rootId` with a VSpace root preserves ASID uniqueness
when the new root has the same ASID as the original. -/
private theorem storeObject_vspaceRoot_preserves_asidRootsUnique
    (st st' : SystemState)
    (rootId : SeLe4n.ObjId)
    (oldRoot newRoot : VSpaceRoot)
    (hAsid : newRoot.asid = oldRoot.asid)
    (hOldObj : st.objects rootId = some (.vspaceRoot oldRoot))
    (hStore : storeObject rootId (.vspaceRoot newRoot) st = .ok ((), st'))
    (hUnique : vspaceAsidRootsUnique st) :
    vspaceAsidRootsUnique st' := by
  intro oid₁ oid₂ r₁ r₂ hObj₁ hObj₂ hAsidEq
  by_cases h₁ : oid₁ = rootId <;> by_cases h₂ : oid₂ = rootId
  · rw [h₁, h₂]
  · subst h₁
    have hR₁ : r₁ = newRoot := by
      have := storeObject_objects_eq st st' rootId (.vspaceRoot newRoot) hStore
      rw [this] at hObj₁; cases hObj₁; rfl
    have hR₂Orig : st.objects oid₂ = some (.vspaceRoot r₂) := by
      rw [storeObject_objects_ne st st' rootId oid₂ (.vspaceRoot newRoot) h₂ hStore] at hObj₂
      exact hObj₂
    subst hR₁
    rw [hAsid] at hAsidEq
    exact hUnique rootId oid₂ oldRoot r₂ hOldObj hR₂Orig hAsidEq
  · subst h₂
    have hR₂ : r₂ = newRoot := by
      have := storeObject_objects_eq st st' rootId (.vspaceRoot newRoot) hStore
      rw [this] at hObj₂; cases hObj₂; rfl
    have hR₁Orig : st.objects oid₁ = some (.vspaceRoot r₁) := by
      rw [storeObject_objects_ne st st' rootId oid₁ (.vspaceRoot newRoot) h₁ hStore] at hObj₁
      exact hObj₁
    subst hR₂
    rw [hAsid] at hAsidEq
    exact hUnique oid₁ rootId r₁ oldRoot hR₁Orig hOldObj hAsidEq
  · have hR₁Orig : st.objects oid₁ = some (.vspaceRoot r₁) := by
      rw [storeObject_objects_ne st st' rootId oid₁ (.vspaceRoot newRoot) h₁ hStore] at hObj₁
      exact hObj₁
    have hR₂Orig : st.objects oid₂ = some (.vspaceRoot r₂) := by
      rw [storeObject_objects_ne st st' rootId oid₂ (.vspaceRoot newRoot) h₂ hStore] at hObj₂
      exact hObj₂
    exact hUnique oid₁ oid₂ r₁ r₂ hR₁Orig hR₂Orig hAsidEq

/-- Helper: `storeObject` at `rootId` with a VSpace root preserves non-overlap when
the new root satisfies `noVirtualOverlap`. -/
private theorem storeObject_vspaceRoot_preserves_rootNonOverlap
    (st st' : SystemState)
    (rootId : SeLe4n.ObjId)
    (newRoot : VSpaceRoot)
    (hNewOverlap : VSpaceRoot.noVirtualOverlap newRoot)
    (hStore : storeObject rootId (.vspaceRoot newRoot) st = .ok ((), st'))
    (hNonOverlap : vspaceRootNonOverlap st) :
    vspaceRootNonOverlap st' := by
  intro oid root hObj
  by_cases hEq : oid = rootId
  · subst hEq
    have hR : root = newRoot := by
      have := storeObject_objects_eq st st' rootId (.vspaceRoot newRoot) hStore
      rw [this] at hObj; cases hObj; rfl
    subst hR
    exact hNewOverlap
  · have hOrig : st.objects oid = some (.vspaceRoot root) := by
      rw [storeObject_objects_ne st st' rootId oid (.vspaceRoot newRoot) hEq hStore] at hObj
      exact hObj
    exact hNonOverlap oid root hOrig

/-- A successful `vspaceMapPage` preserves the VSpace invariant bundle.

The proof decomposes the operation into `resolveAsidRoot` + `VSpaceRoot.mapPage` +
`storeObject`, then shows:
1. ASID uniqueness: the new root has the same ASID as the old root (by `mapPage_preserves_asid`).
2. Non-overlap: `mapPage` only succeeds when no existing mapping exists at `vaddr`,
   so adding the new entry preserves `noVirtualOverlap` (by `mapPage_preserves_noVirtualOverlap`). -/
theorem vspaceMapPage_success_preserves_vspaceInvariantBundle
    (st st' : SystemState)
    (asid : SeLe4n.ASID)
    (vaddr : SeLe4n.VAddr)
    (paddr : SeLe4n.PAddr)
    (hInv : vspaceInvariantBundle st)
    (hStep : vspaceMapPage asid vaddr paddr st = .ok ((), st')) :
    vspaceInvariantBundle st' := by
  rcases hInv with ⟨hUnique, hNonOverlap⟩
  unfold vspaceMapPage at hStep
  cases hResolve : resolveAsidRoot st asid with
  | none => simp [hResolve] at hStep
  | some pair =>
      rcases pair with ⟨rootId, root⟩
      cases hMap : root.mapPage vaddr paddr with
      | none => simp [hResolve, hMap] at hStep
      | some root' =>
          have hStore : storeObject rootId (.vspaceRoot root') st = .ok ((), st') := by
            simpa [hResolve, hMap] using hStep
          -- Extract the old root from resolveAsidRoot
          have hOldObj : st.objects rootId = some (.vspaceRoot root) := by
            unfold resolveAsidRoot at hResolve
            have := List.findSome?_eq_some.mp hResolve
            rcases this with ⟨_, _, hBody⟩
            split at hBody <;> simp_all
            split at hBody <;> simp_all
          have hAsid := VSpaceRoot.mapPage_preserves_asid root root' vaddr paddr hMap
          have hNewOverlap := VSpaceRoot.mapPage_preserves_noVirtualOverlap
            root root' vaddr paddr (hNonOverlap rootId root hOldObj) hMap
          refine ⟨?_, ?_⟩
          · exact storeObject_vspaceRoot_preserves_asidRootsUnique
              st st' rootId root root' hAsid hOldObj hStore hUnique
          · exact storeObject_vspaceRoot_preserves_rootNonOverlap
              st st' rootId root' hNewOverlap hStore hNonOverlap

/-- A successful `vspaceUnmapPage` preserves the VSpace invariant bundle.

The proof follows the same decomposition as the map case. Filtering the mapping list
preserves both ASID uniqueness and non-overlap (removing entries cannot create new
virtual-address conflicts). -/
theorem vspaceUnmapPage_success_preserves_vspaceInvariantBundle
    (st st' : SystemState)
    (asid : SeLe4n.ASID)
    (vaddr : SeLe4n.VAddr)
    (hInv : vspaceInvariantBundle st)
    (hStep : vspaceUnmapPage asid vaddr st = .ok ((), st')) :
    vspaceInvariantBundle st' := by
  rcases hInv with ⟨hUnique, hNonOverlap⟩
  unfold vspaceUnmapPage at hStep
  cases hResolve : resolveAsidRoot st asid with
  | none => simp [hResolve] at hStep
  | some pair =>
      rcases pair with ⟨rootId, root⟩
      cases hUnmap : root.unmapPage vaddr with
      | none => simp [hResolve, hUnmap] at hStep
      | some root' =>
          have hStore : storeObject rootId (.vspaceRoot root') st = .ok ((), st') := by
            simpa [hResolve, hUnmap] using hStep
          have hOldObj : st.objects rootId = some (.vspaceRoot root) := by
            unfold resolveAsidRoot at hResolve
            have := List.findSome?_eq_some.mp hResolve
            rcases this with ⟨_, _, hBody⟩
            split at hBody <;> simp_all
            split at hBody <;> simp_all
          have hAsid := VSpaceRoot.unmapPage_preserves_asid root root' vaddr hUnmap
          have hNewOverlap := VSpaceRoot.unmapPage_preserves_noVirtualOverlap
            root root' vaddr (hNonOverlap rootId root hOldObj) hUnmap
          refine ⟨?_, ?_⟩
          · exact storeObject_vspaceRoot_preserves_asidRootsUnique
              st st' rootId root root' hAsid hOldObj hStore hUnique
          · exact storeObject_vspaceRoot_preserves_rootNonOverlap
              st st' rootId root' hNewOverlap hStore hNonOverlap

-- ============================================================================
-- TPI-001 / TPI-D05: VSpace round-trip theorems
-- ============================================================================

/-- Helper: `resolveAsidRoot` after `storeObject` at the same rootId resolves to
the new root object. -/
private theorem resolveAsidRoot_after_storeObject
    (st st' : SystemState)
    (rootId : SeLe4n.ObjId)
    (root root' : VSpaceRoot)
    (hAsid : root'.asid = root.asid)
    (hResolve : resolveAsidRoot st root.asid = some (rootId, root))
    (hStore : storeObject rootId (.vspaceRoot root') st = .ok ((), st')) :
    resolveAsidRoot st' root.asid = some (rootId, root') := by
  unfold resolveAsidRoot at hResolve ⊢
  have hObjEq : st'.objects rootId = some (.vspaceRoot root') :=
    storeObject_objects_eq st st' rootId (.vspaceRoot root') hStore
  unfold storeObject at hStore
  cases hStore
  -- st'.objectIndex is either st.objectIndex or rootId :: st.objectIndex
  simp only
  -- We need to show findSome? returns (rootId, root') on the new objectIndex
  have hOrigFound := List.findSome?_eq_some.mp hResolve
  rcases hOrigFound with ⟨oid, hOidMem, hBody⟩
  -- The original resolveAsidRoot found rootId in the original objectIndex
  have hOidIsRoot : oid = rootId := by
    split at hBody <;> simp_all
    split at hBody <;> simp_all
    rename_i r _ _ hObj _ hAsidCheck
    have hRootInOld : st.objects oid = some (.vspaceRoot r) := hObj
    -- From the resolve, r.asid = root.asid and the found root is `root`
    have : (oid, r) = (rootId, root) := by
      simp at hBody; exact hBody
    exact this.1
  subst hOidIsRoot
  -- Now show findSome? on new index finds rootId with root'
  apply List.findSome?_eq_some.mpr
  by_cases hMem : rootId ∈ st.objectIndex
  · -- objectIndex unchanged
    simp [hMem]
    refine ⟨rootId, hOidMem, ?_⟩
    simp [hObjEq, hAsid]
  · -- objectIndex = rootId :: st.objectIndex
    simp [hMem]
    refine ⟨rootId, List.mem_cons_self _ _, ?_⟩
    simp [hObjEq, hAsid]

/-- Mapping a page and then looking it up yields the mapped physical address.

This is the first TPI-001 round-trip obligation carried forward from WS-C. -/
theorem vspaceLookup_after_map
    (st st' : SystemState)
    (asid : SeLe4n.ASID)
    (vaddr : SeLe4n.VAddr)
    (paddr : SeLe4n.PAddr)
    (hStep : vspaceMapPage asid vaddr paddr st = .ok ((), st')) :
    vspaceLookup asid vaddr st' = .ok (paddr, st') := by
  unfold vspaceMapPage at hStep
  cases hResolve : resolveAsidRoot st asid with
  | none => simp [hResolve] at hStep
  | some pair =>
      rcases pair with ⟨rootId, root⟩
      cases hMap : root.mapPage vaddr paddr with
      | none => simp [hResolve, hMap] at hStep
      | some root' =>
          have hStore : storeObject rootId (.vspaceRoot root') st = .ok ((), st') := by
            simpa [hResolve, hMap] using hStep
          have hAsid := VSpaceRoot.mapPage_preserves_asid root root' vaddr paddr hMap
          have hLookupRoot := VSpaceRoot.lookup_mapPage_eq root root' vaddr paddr hMap
          have hResolve' := resolveAsidRoot_after_storeObject
            st st' rootId root root' hAsid hResolve hStore
          unfold vspaceLookup
          rw [hResolve']
          simp [hLookupRoot]

/-- Mapping at `vaddr` does not affect lookup of a different virtual address `vaddr'`.

This is the second TPI-001 round-trip obligation carried forward from WS-C. -/
theorem vspaceLookup_map_other
    (st st' : SystemState)
    (asid : SeLe4n.ASID)
    (vaddr vaddr' : SeLe4n.VAddr)
    (paddr : SeLe4n.PAddr)
    (hNe : vaddr ≠ vaddr')
    (hStep : vspaceMapPage asid vaddr paddr st = .ok ((), st')) :
    vspaceLookup asid vaddr' st' = vspaceLookup asid vaddr' st := by
  unfold vspaceMapPage at hStep
  cases hResolve : resolveAsidRoot st asid with
  | none => simp [hResolve] at hStep
  | some pair =>
      rcases pair with ⟨rootId, root⟩
      cases hMap : root.mapPage vaddr paddr with
      | none => simp [hResolve, hMap] at hStep
      | some root' =>
          have hStore : storeObject rootId (.vspaceRoot root') st = .ok ((), st') := by
            simpa [hResolve, hMap] using hStep
          have hAsid := VSpaceRoot.mapPage_preserves_asid root root' vaddr paddr hMap
          have hLookupOther := VSpaceRoot.lookup_mapPage_other
            root root' vaddr vaddr' paddr hNe hMap
          have hResolve' := resolveAsidRoot_after_storeObject
            st st' rootId root root' hAsid hResolve hStore
          unfold vspaceLookup
          rw [hResolve, hResolve']
          simp [hLookupOther]

/-- After unmapping a page, looking up the same virtual address fails with `translationFault`.

This is the third TPI-001 round-trip obligation carried forward from WS-C. -/
theorem vspaceLookup_after_unmap
    (st st' : SystemState)
    (asid : SeLe4n.ASID)
    (vaddr : SeLe4n.VAddr)
    (hStep : vspaceUnmapPage asid vaddr st = .ok ((), st')) :
    vspaceLookup asid vaddr st' = .error .translationFault := by
  unfold vspaceUnmapPage at hStep
  cases hResolve : resolveAsidRoot st asid with
  | none => simp [hResolve] at hStep
  | some pair =>
      rcases pair with ⟨rootId, root⟩
      cases hUnmap : root.unmapPage vaddr with
      | none => simp [hResolve, hUnmap] at hStep
      | some root' =>
          have hStore : storeObject rootId (.vspaceRoot root') st = .ok ((), st') := by
            simpa [hResolve, hUnmap] using hStep
          have hAsid := VSpaceRoot.unmapPage_preserves_asid root root' vaddr hUnmap
          have hLookupNone := VSpaceRoot.lookup_unmapPage_eq_none root root' vaddr hUnmap
          have hResolve' := resolveAsidRoot_after_storeObject
            st st' rootId root root' hAsid hResolve hStore
          unfold vspaceLookup
          rw [hResolve']
          simp [hLookupNone]

end SeLe4n.Kernel.Architecture
