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
-- Error-preservation theorems (trivial, retained for surface completeness)
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
-- F-08 Shared infrastructure (WS-D3)
-- ============================================================================

/-- General helper: `findSome?` returning `some` implies the function returns `some` for some
element in the list. -/
private theorem findSome_some_exists {α β : Type} [DecidableEq β]
    (f : α → Option β) (l : List α) (b : β)
    (h : l.findSome? f = some b) : ∃ a, a ∈ l ∧ f a = some b := by
  induction l with
  | nil => simp [List.findSome?] at h
  | cons x xs ih =>
      simp only [List.findSome?] at h
      cases hfx : f x with
      | none =>
          rw [hfx] at h
          rcases ih h with ⟨a, hMem, hFa⟩
          exact ⟨a, List.Mem.tail x hMem, hFa⟩
      | some b' =>
          rw [hfx] at h
          cases h
          exact ⟨x, List.Mem.head xs, hfx⟩

/-- resolveAsidRoot returning `some` implies the root object is in the store with matching ASID. -/
theorem resolveAsidRoot_some_implies_object
    (st : SystemState)
    (asid : SeLe4n.ASID)
    (rootId : SeLe4n.ObjId)
    (root : VSpaceRoot)
    (hResolve : resolveAsidRoot st asid = some (rootId, root)) :
    st.objects rootId = some (KernelObject.vspaceRoot root) ∧ root.asid = asid := by
  unfold resolveAsidRoot at hResolve
  rcases findSome_some_exists _ st.objectIndex _ hResolve with ⟨oid, _, hMatch⟩
  cases hObj : st.objects oid with
  | none => simp [hObj] at hMatch
  | some obj =>
      cases obj with
      | tcb _ | cnode _ | endpoint _ | notification _ => simp [hObj] at hMatch
      | vspaceRoot r =>
          by_cases hAsid : r.asid = asid
          · simp [hObj, hAsid] at hMatch
            rcases hMatch with ⟨rfl, rfl⟩
            exact ⟨hObj, hAsid⟩
          · simp [hObj, hAsid] at hMatch

/-- `storeObject` writes the target id and preserves all other object lookups. -/
private theorem storeObject_objects_eq_at
    (st st' : SystemState) (id : SeLe4n.ObjId) (obj : KernelObject)
    (hStore : storeObject id obj st = .ok ((), st')) :
    st'.objects id = some obj := by
  unfold storeObject at hStore; cases hStore; simp

private theorem storeObject_objects_ne_at
    (st st' : SystemState) (id oid : SeLe4n.ObjId) (obj : KernelObject)
    (hNe : oid ≠ id)
    (hStore : storeObject id obj st = .ok ((), st')) :
    st'.objects oid = st.objects oid := by
  unfold storeObject at hStore; cases hStore; simp [hNe]

-- ============================================================================
-- F-08 Substantive preservation theorems (WS-D3)
-- ============================================================================

/-- Successful `vspaceMapPage` preserves the VSpace invariant bundle.

This is the F-08 substantive preservation obligation: a successful map operation
maintains ASID uniqueness (the ASID of the root is unchanged) and non-overlap
(mapPage only succeeds when the vaddr is unmapped, so no overlap is created). -/
theorem vspaceMapPage_preserves_vspaceInvariantBundle
    (st st' : SystemState)
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) (paddr : SeLe4n.PAddr)
    (hInv : vspaceInvariantBundle st)
    (hStep : vspaceMapPage asid vaddr paddr st = .ok ((), st')) :
    vspaceInvariantBundle st' := by
  rcases hInv with ⟨hAsidUniq, hNonOverlap⟩
  unfold vspaceMapPage at hStep
  cases hResolve : resolveAsidRoot st asid with
  | none => simp [hResolve] at hStep
  | some pair =>
      rcases pair with ⟨rootId, root⟩
      cases hMap : root.mapPage vaddr paddr with
      | none => simp [hResolve, hMap] at hStep
      | some root' =>
          simp [hResolve, hMap] at hStep
          rcases resolveAsidRoot_some_implies_object st asid rootId root hResolve with ⟨hRootObj, _⟩
          have hAsidPreserved := VSpaceRoot.mapPage_preserves_asid root root' vaddr paddr hMap
          have hNoOverlap' := VSpaceRoot.mapPage_preserves_noVirtualOverlap root root' vaddr paddr
            (hNonOverlap rootId root hRootObj) hMap
          have hObjEq := storeObject_objects_eq_at st st' rootId (KernelObject.vspaceRoot root') hStep
          have hObjNe : ∀ oid, oid ≠ rootId → st'.objects oid = st.objects oid :=
            fun oid hNe => storeObject_objects_ne_at st st' rootId oid (KernelObject.vspaceRoot root') hNe hStep
          refine ⟨?_, ?_⟩
          · -- ASID uniqueness
            intro oid₁ oid₂ r₁ r₂ hObj₁ hObj₂ hAsidEq
            by_cases hEq₁ : oid₁ = rootId <;> by_cases hEq₂ : oid₂ = rootId
            · rw [hEq₁, hEq₂]
            · rw [hEq₁] at hObj₁; rw [hObjEq] at hObj₁; cases hObj₁
              rw [hObjNe oid₂ hEq₂] at hObj₂
              rw [hAsidPreserved] at hAsidEq
              exact hEq₁.trans (hAsidUniq rootId oid₂ root r₂ hRootObj hObj₂ hAsidEq)
            · rw [hEq₂] at hObj₂; rw [hObjEq] at hObj₂; cases hObj₂
              rw [hObjNe oid₁ hEq₁] at hObj₁
              rw [hAsidPreserved] at hAsidEq
              exact (hEq₁ (hAsidUniq oid₁ rootId r₁ root hObj₁ hRootObj hAsidEq)).elim
            · rw [hObjNe oid₁ hEq₁] at hObj₁
              rw [hObjNe oid₂ hEq₂] at hObj₂
              exact hAsidUniq oid₁ oid₂ r₁ r₂ hObj₁ hObj₂ hAsidEq
          · -- Non-overlap
            intro oid r hObj
            by_cases hEq : oid = rootId
            · rw [hEq] at hObj; rw [hObjEq] at hObj; cases hObj; exact hNoOverlap'
            · rw [hObjNe oid hEq] at hObj; exact hNonOverlap oid r hObj

/-- Successful `vspaceUnmapPage` preserves the VSpace invariant bundle.

This is the F-08 substantive preservation obligation: a successful unmap
operation maintains ASID uniqueness (the ASID of the root is unchanged)
and non-overlap (unmapPage removes entries, which preserves non-overlap). -/
theorem vspaceUnmapPage_preserves_vspaceInvariantBundle
    (st st' : SystemState)
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (hInv : vspaceInvariantBundle st)
    (hStep : vspaceUnmapPage asid vaddr st = .ok ((), st')) :
    vspaceInvariantBundle st' := by
  rcases hInv with ⟨hAsidUniq, hNonOverlap⟩
  unfold vspaceUnmapPage at hStep
  cases hResolve : resolveAsidRoot st asid with
  | none => simp [hResolve] at hStep
  | some pair =>
      rcases pair with ⟨rootId, root⟩
      cases hUnmap : root.unmapPage vaddr with
      | none => simp [hResolve, hUnmap] at hStep
      | some root' =>
          simp [hResolve, hUnmap] at hStep
          rcases resolveAsidRoot_some_implies_object st asid rootId root hResolve with ⟨hRootObj, _⟩
          have hAsidPreserved := VSpaceRoot.unmapPage_preserves_asid root root' vaddr hUnmap
          have hNoOverlap' := VSpaceRoot.unmapPage_preserves_noVirtualOverlap root root' vaddr
            (hNonOverlap rootId root hRootObj) hUnmap
          have hObjEq := storeObject_objects_eq_at st st' rootId (KernelObject.vspaceRoot root') hStep
          have hObjNe : ∀ oid, oid ≠ rootId → st'.objects oid = st.objects oid :=
            fun oid hNe => storeObject_objects_ne_at st st' rootId oid (KernelObject.vspaceRoot root') hNe hStep
          refine ⟨?_, ?_⟩
          · -- ASID uniqueness
            intro oid₁ oid₂ r₁ r₂ hObj₁ hObj₂ hAsidEq
            by_cases hEq₁ : oid₁ = rootId <;> by_cases hEq₂ : oid₂ = rootId
            · rw [hEq₁, hEq₂]
            · rw [hEq₁] at hObj₁; rw [hObjEq] at hObj₁; cases hObj₁
              rw [hObjNe oid₂ hEq₂] at hObj₂
              rw [hAsidPreserved] at hAsidEq
              exact hEq₁.trans (hAsidUniq rootId oid₂ root r₂ hRootObj hObj₂ hAsidEq)
            · rw [hEq₂] at hObj₂; rw [hObjEq] at hObj₂; cases hObj₂
              rw [hObjNe oid₁ hEq₁] at hObj₁
              rw [hAsidPreserved] at hAsidEq
              exact (hEq₁ (hAsidUniq oid₁ rootId r₁ root hObj₁ hRootObj hAsidEq)).elim
            · rw [hObjNe oid₁ hEq₁] at hObj₁
              rw [hObjNe oid₂ hEq₂] at hObj₂
              exact hAsidUniq oid₁ oid₂ r₁ r₂ hObj₁ hObj₂ hAsidEq
          · -- Non-overlap
            intro oid r hObj
            by_cases hEq : oid = rootId
            · rw [hEq] at hObj; rw [hObjEq] at hObj; cases hObj; exact hNoOverlap'
            · rw [hObjNe oid hEq] at hObj; exact hNonOverlap oid r hObj

-- ============================================================================
-- TPI-001 Round-trip theorems (WS-D3)
-- ============================================================================

/-- After a successful map, looking up the mapped virtual address yields the
mapped physical address.

This is the forward direction of the TPI-001 map/lookup round-trip: if
`vspaceMapPage` succeeds, then an immediate `vspaceLookup` on the same ASID
and virtual address produces the expected physical address.

The proof relies on ASID-root uniqueness to ensure `resolveAsidRoot` on the
post-state resolves to the freshly-stored root object at the same rootId. -/
theorem vspaceLookup_after_mapPage
    (st st' : SystemState)
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) (paddr : SeLe4n.PAddr)
    (hInv : vspaceAsidRootsUnique st)
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
          simp [hResolve, hMap] at hStep
          rcases resolveAsidRoot_some_implies_object st asid rootId root hResolve with ⟨hRootObj, hRootAsid⟩
          have hLookupRoot' := VSpaceRoot.lookup_mapPage_eq root root' vaddr paddr hMap
          have hAsidPreserved := VSpaceRoot.mapPage_preserves_asid root root' vaddr paddr hMap
          -- The post-state has root' with root'.asid = asid at rootId
          -- vspaceLookup on post-state: resolveAsidRoot finds rootId → root', then root'.lookup vaddr = some paddr
          -- We reduce through vspaceLookup → resolveAsidRoot → findSome? on post-state
          -- Since the objects function and objectIndex in st' are determined by storeObject,
          -- and we know rootId is in objectIndex (it was already there since hRootObj shows an object existed),
          -- findSome? will find rootId and return (rootId, root')
          -- Then vspaceLookup matches root'.lookup vaddr = some paddr → .ok (paddr, st')
          unfold storeObject at hStep; cases hStep
          unfold vspaceLookup resolveAsidRoot
          -- Need to reason about findSome? on modified objectIndex and objects
          -- rootId must be in st.objectIndex for the original resolveAsidRoot to find it
          have hRootInIndex : rootId ∈ st.objectIndex := by
            unfold resolveAsidRoot at hResolve
            -- findSome? succeeded, so it found some element in the list where the function returned some
            rcases findSome_some_exists _ st.objectIndex _ hResolve with ⟨oid, hMem, hMatch⟩
            cases hObj : st.objects oid with
            | none => simp [hObj] at hMatch
            | some obj =>
                cases obj with
                | tcb _ | cnode _ | endpoint _ | notification _ => simp [hObj] at hMatch
                | vspaceRoot r =>
                    by_cases hAsid : r.asid = asid
                    · simp [hObj, hAsid] at hMatch
                      rcases hMatch with ⟨rfl, rfl⟩
                      exact hMem
                    · simp [hObj, hAsid] at hMatch
          -- Since rootId ∈ st.objectIndex, the objectIndex in post-state equals st.objectIndex
          simp [hRootInIndex]
          -- Now we need to show findSome? on st.objectIndex with the updated objects returns (rootId, root')
          -- and then root'.lookup vaddr = some paddr
          -- The key fact: with root'.asid = root.asid = asid, looking up rootId in updated objects
          -- gives vspaceRoot root' with asid = asid, so the function returns some (rootId, root')
          -- For all other oids, objects are unchanged
          -- By ASID uniqueness, no other oid has a root with the same ASID, so findSome? must return rootId first
          -- (actually, it returns the first match in the list, which was rootId originally)
          sorry

/-- Mapping a virtual address does not affect the translation of other virtual
addresses in the same address space.

This is the non-interference direction of TPI-001: mapping `vaddr` leaves
translations for `vaddr' ≠ vaddr` unchanged. -/
theorem vspaceLookup_mapPage_other
    (st st' : SystemState)
    (asid : SeLe4n.ASID) (vaddr vaddr' : SeLe4n.VAddr) (paddr paddr' : SeLe4n.PAddr)
    (hNe : vaddr ≠ vaddr')
    (hInv : vspaceAsidRootsUnique st)
    (hStep : vspaceMapPage asid vaddr paddr st = .ok ((), st'))
    (hLookup : vspaceLookup asid vaddr' st = .ok (paddr', st)) :
    vspaceLookup asid vaddr' st' = .ok (paddr', st') := by
  sorry

/-- After a successful unmap, looking up the unmapped virtual address yields a
translation fault.

This is the reverse direction of TPI-001: if `vspaceUnmapPage` succeeds, then
an immediate `vspaceLookup` on the same ASID and virtual address fails with
a translation fault. -/
theorem vspaceLookup_after_unmapPage
    (st st' : SystemState)
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (hInv : vspaceAsidRootsUnique st)
    (hStep : vspaceUnmapPage asid vaddr st = .ok ((), st')) :
    vspaceLookup asid vaddr st' = .error .translationFault := by
  sorry

end SeLe4n.Kernel.Architecture
