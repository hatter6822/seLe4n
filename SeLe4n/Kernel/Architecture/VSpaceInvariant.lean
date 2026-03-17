/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

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

/-- WS-H11/A-05/M-12: Bounded translation surface — all translated physical addresses
are within the finite machine window `[0, bound)`.

WS-H11: Integrated into `vspaceInvariantBundle`. Updated for enriched `(PAddr × PagePermissions)`. -/
def boundedAddressTranslation (st : SystemState) (bound : Nat) : Prop :=
  ∀ (oid : SeLe4n.ObjId) (root : VSpaceRoot) (v : SeLe4n.VAddr) (p : SeLe4n.PAddr) (perms : PagePermissions),
    st.objects[oid]? = some (KernelObject.vspaceRoot root) →
    root.mappings[v]? = some (p, perms) →
    p.toNat < bound

/-- WS-H11/H-02: W^X enforcement — no VSpaceRoot in the system has a mapping that is
both writable and executable. -/
def wxExclusiveInvariant (st : SystemState) : Prop :=
  ∀ (oid : SeLe4n.ObjId) (root : VSpaceRoot) (v : SeLe4n.VAddr) (p : SeLe4n.PAddr)
    (perms : PagePermissions),
    st.objects[oid]? = some (KernelObject.vspaceRoot root) →
    root.mappings[v]? = some (p, perms) →
    perms.wxCompliant = true

/-- WS-F6/D6/MED-07: Cross-ASID isolation — operations on one VSpaceRoot do not
affect another VSpaceRoot's mappings because distinct VSpaceRoot objects have
distinct ASIDs. This is the VSpace analog of non-interference: address spaces
for different processes are provably independent.

Combined with `vspaceAsidRootsUnique` (which ensures ASID → ObjId uniqueness)
and `storeObject_objects_ne` (which ensures storeObject only modifies the target),
this gives full cross-root isolation: if VSpaceRoot A is modified, VSpaceRoot B
(B ≠ A) is unchanged. -/
def vspaceCrossAsidIsolation (st : SystemState) : Prop :=
  ∀ (oidA oidB : SeLe4n.ObjId) (rootA rootB : VSpaceRoot),
    st.objects[oidA]? = some (.vspaceRoot rootA) →
    st.objects[oidB]? = some (.vspaceRoot rootB) →
    oidA ≠ oidB →
    rootA.asid ≠ rootB.asid

/-- WS-B1/WS-G3/WS-H11/WS-F6 architecture/VSpace invariant bundle entrypoint.

WS-H11: Enriched with `wxExclusiveInvariant` and `boundedAddressTranslation`.
WS-F6/D6: Extended from 5-tuple to 6-tuple with `vspaceCrossAsidIsolation`. -/
def vspaceInvariantBundle (st : SystemState) (bound : Nat := 2^52) : Prop :=
  vspaceAsidRootsUnique st ∧
  vspaceRootNonOverlap st ∧
  asidTableConsistent st ∧
  wxExclusiveInvariant st ∧
  boundedAddressTranslation st bound ∧
  vspaceCrossAsidIsolation st

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
    (perms : PagePermissions)
    (_hErr : vspaceMapPage asid vaddr paddr perms st = .error .asidNotBound) :
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
-- Helper lemmas for proof deduplication (WS-H11 audit refinement)
-- ============================================================================

/-- After a successful `mapPage`, the new root's mappings equal
    the old root's mappings with the new entry inserted. -/
private theorem VSpaceRoot.mapPage_mappings_insert
    (root root' : VSpaceRoot) (vaddr : SeLe4n.VAddr) (paddr : SeLe4n.PAddr)
    (perms : PagePermissions)
    (hMap : root.mapPage vaddr paddr perms = some root') :
    root'.mappings = root.mappings.insert vaddr (paddr, perms) := by
  unfold VSpaceRoot.mapPage at hMap
  cases hOld : root.mappings[vaddr]? with
  | some _ => simp [hOld] at hMap
  | none => simp [hOld] at hMap; cases hMap; rfl

/-- After a successful `unmapPage`, the new root's mappings equal
    the old root's mappings with the target entry erased. -/
private theorem VSpaceRoot.unmapPage_mappings_erase
    (root root' : VSpaceRoot) (vaddr : SeLe4n.VAddr)
    (hUnmap : root.unmapPage vaddr = some root') :
    root'.mappings = root.mappings.erase vaddr := by
  unfold VSpaceRoot.unmapPage at hUnmap
  cases hOld : root.mappings[vaddr]? with
  | none => simp [hOld] at hUnmap
  | some _ => simp [hOld] at hUnmap; cases hUnmap; rfl

/-- Recover a pre-state mapping from a post-erase lookup (for unmap proofs). -/
private theorem HashMap_lookup_of_erase_lookup
    (mappings : Std.HashMap SeLe4n.VAddr (SeLe4n.PAddr × PagePermissions))
    (vaddr v : SeLe4n.VAddr) (p : SeLe4n.PAddr) (pm : PagePermissions)
    (hErase : (mappings.erase vaddr)[v]? = some (p, pm)) :
    mappings[v]? = some (p, pm) := by
  by_cases hV : vaddr = v
  · subst hV; simp at hErase
  · have hBeq : ¬((vaddr == v) = true) := by intro h; exact hV (eq_of_beq h)
    simp only [Std.HashMap.getElem?_erase, hBeq] at hErase; exact hErase

-- ============================================================================
-- F-08 / TPI-D05: VSpace successful-operation invariant preservation
-- ============================================================================

/-- F-08/WS-G3/WS-H11: A successful `vspaceMapPage` preserves the VSpace invariant bundle.

    The proof decomposes into five obligations:
    1. ASID-root uniqueness is preserved because `mapPage` preserves the root's ASID.
    2. Non-overlap is preserved because `mapPage` only succeeds when no mapping
       for the target vaddr already exists.
    3. ASID table consistency is preserved because `storeObject` maintains the
       ASID table and `mapPage` preserves the root's ASID.
    4. W^X exclusivity is preserved because the operation guards on `perms.wxCompliant`.
    5. Bounded address translation is preserved (requires bound hypothesis on paddr). -/
theorem vspaceMapPage_success_preserves_vspaceInvariantBundle
    (st st' : SystemState)
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) (paddr : SeLe4n.PAddr)
    (perms : PagePermissions)
    (hInv : vspaceInvariantBundle st)
    (hBound : paddr.toNat < 2^52)
    (hStep : vspaceMapPage asid vaddr paddr perms st = .ok ((), st')) :
    vspaceInvariantBundle st' := by
  unfold vspaceMapPage at hStep
  cases hResolve : resolveAsidRoot st asid with
  | none => simp [hResolve] at hStep
  | some pair =>
      rcases pair with ⟨rootId, root⟩
      simp only [hResolve] at hStep
      by_cases hWx : perms.wxCompliant = true
      · simp only [hWx, Bool.not_true] at hStep
        cases hMapRoot : root.mapPage vaddr paddr perms with
        | none => simp [hMapRoot] at hStep
        | some root' =>
            have hStore : storeObject rootId (.vspaceRoot root') st = .ok ((), st') := by
              simpa [hMapRoot] using hStep
            rcases resolveAsidRoot_some_implies_obj st asid rootId root hResolve with ⟨_, hObjRoot, hAsidRoot⟩
            have hObjEq : st'.objects[rootId]? = some (.vspaceRoot root') :=
              storeObject_objects_eq st st' rootId (.vspaceRoot root') hStore
            have hObjNe : ∀ oid, oid ≠ rootId → st'.objects[oid]? = st.objects[oid]? :=
              fun oid hNe => storeObject_objects_ne st st' rootId oid (.vspaceRoot root') hNe hStore
            have hAsidPreserved : root'.asid = root.asid :=
              VSpaceRoot.mapPage_asid_eq root root' vaddr paddr perms hMapRoot
            rcases hInv with ⟨hUniq, hNoOverlap, hConsist, hWxInv, hBoundInv, hCrossAsid⟩
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
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
                exact VSpaceRoot.mapPage_noVirtualOverlap root root' vaddr paddr perms
                  (hNoOverlap rootId root hObjRoot) hMapRoot
              · rw [hObjNe oid hEq] at hObj
                exact hNoOverlap oid r hObj
            -- 3. asidTableConsistent st' (via shared helper)
            · exact asidTableConsistent_of_storeObject_vspaceRoot
                st st' rootId root root' hStore hObjRoot hObjEq hObjNe hAsidPreserved hUniq hConsist
            -- 4. wxExclusiveInvariant st'
            · intro oid r v p pm hObjR hMap
              have hInsert := VSpaceRoot.mapPage_mappings_insert root root' vaddr paddr perms hMapRoot
              by_cases hEq : oid = rootId
              · subst hEq; rw [hObjEq] at hObjR; cases hObjR
                rw [hInsert] at hMap
                by_cases hV : v = vaddr
                · subst hV
                  simp only [Std.HashMap.getElem?_insert, beq_self_eq_true, ↓reduceIte] at hMap
                  cases hMap; exact hWx
                · have hBeq : ¬((vaddr == v) = true) := by intro h; exact hV (eq_of_beq h).symm
                  simp only [Std.HashMap.getElem?_insert, hBeq] at hMap
                  exact hWxInv _ root v p pm hObjRoot hMap
              · rw [hObjNe oid hEq] at hObjR
                exact hWxInv oid r v p pm hObjR hMap
            -- 5. boundedAddressTranslation st'
            · intro oid r v p pm hObjR hMap
              have hInsert := VSpaceRoot.mapPage_mappings_insert root root' vaddr paddr perms hMapRoot
              by_cases hEq : oid = rootId
              · subst hEq; rw [hObjEq] at hObjR; cases hObjR
                rw [hInsert] at hMap
                by_cases hV : v = vaddr
                · subst hV
                  simp only [Std.HashMap.getElem?_insert, beq_self_eq_true, ↓reduceIte] at hMap
                  cases hMap; exact hBound
                · have hBeq : ¬((vaddr == v) = true) := by intro h; exact hV (eq_of_beq h).symm
                  simp only [Std.HashMap.getElem?_insert, hBeq] at hMap
                  exact hBoundInv _ root v p pm hObjRoot hMap
              · rw [hObjNe oid hEq] at hObjR
                exact hBoundInv oid r v p pm hObjR hMap
            -- 6. vspaceCrossAsidIsolation st'
            · intro oidA oidB rA rB hObjA hObjB hNeqAB
              by_cases hA : oidA = rootId <;> by_cases hB : oidB = rootId
              · exact absurd (hA.trans hB.symm) hNeqAB
              · rw [hA] at hObjA hNeqAB
                rw [hObjEq] at hObjA; cases hObjA
                rw [hObjNe oidB hB] at hObjB
                intro hEq
                apply hCrossAsid rootId oidB root rB hObjRoot hObjB hNeqAB
                rw [← hAsidPreserved]; exact hEq
              · rw [hB] at hObjB hNeqAB
                rw [hObjEq] at hObjB; cases hObjB
                rw [hObjNe oidA hA] at hObjA
                intro hEq
                have hNeqAB' : oidA ≠ rootId := fun h => hNeqAB (h.trans rfl)
                apply hCrossAsid oidA rootId rA root hObjA hObjRoot hNeqAB'
                rw [← hAsidPreserved]; exact hEq
              · rw [hObjNe oidA hA] at hObjA
                rw [hObjNe oidB hB] at hObjB
                exact hCrossAsid oidA oidB rA rB hObjA hObjB hNeqAB
      · have hWxF : perms.wxCompliant = false := by
          cases h : perms.wxCompliant <;> simp_all
        simp [hWxF] at hStep

/-- F-08/WS-G3/WS-H11: A successful `vspaceUnmapPage` preserves the VSpace invariant bundle.

    The proof decomposes into five obligations (unmap only removes entries,
    so W^X and bounded address preservation are straightforward). -/
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
          rcases hInv with ⟨hUniq, hNoOverlap, hConsist, hWxInv, hBoundInv, hCrossAsid⟩
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
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
          -- 4. wxExclusiveInvariant st' (unmap only removes entries — subset of pre-state mappings)
          · intro oid r v p pm hObjR hMap
            have hErase := VSpaceRoot.unmapPage_mappings_erase root root' vaddr hUnmapRoot
            by_cases hEq : oid = rootId
            · subst hEq; rw [hObjEq] at hObjR; cases hObjR
              have hRootMap := HashMap_lookup_of_erase_lookup root.mappings vaddr v p pm
                (hErase ▸ hMap)
              exact hWxInv _ root v p pm hObjRoot hRootMap
            · rw [hObjNe oid hEq] at hObjR
              exact hWxInv oid r v p pm hObjR hMap
          -- 5. boundedAddressTranslation st' (unmap only removes entries)
          · intro oid r v p pm hObjR hMap
            have hErase := VSpaceRoot.unmapPage_mappings_erase root root' vaddr hUnmapRoot
            by_cases hEq : oid = rootId
            · subst hEq; rw [hObjEq] at hObjR; cases hObjR
              have hRootMap := HashMap_lookup_of_erase_lookup root.mappings vaddr v p pm
                (hErase ▸ hMap)
              exact hBoundInv _ root v p pm hObjRoot hRootMap
            · rw [hObjNe oid hEq] at hObjR
              exact hBoundInv oid r v p pm hObjR hMap
          -- 6. vspaceCrossAsidIsolation st'
          · intro oidA oidB rA rB hObjA hObjB hNeqAB
            by_cases hA : oidA = rootId <;> by_cases hB : oidB = rootId
            · exact absurd (hA.trans hB.symm) hNeqAB
            · rw [hA] at hObjA hNeqAB
              rw [hObjEq] at hObjA; cases hObjA
              rw [hObjNe oidB hB] at hObjB
              intro hEq
              apply hCrossAsid rootId oidB root rB hObjRoot hObjB hNeqAB
              rw [← hAsidPreserved]; exact hEq
            · rw [hB] at hObjB hNeqAB
              rw [hObjEq] at hObjB; cases hObjB
              rw [hObjNe oidA hA] at hObjA
              intro hEq
              have hNeqAB' : oidA ≠ rootId := fun h => hNeqAB (h.trans rfl)
              apply hCrossAsid oidA rootId rA root hObjA hObjRoot hNeqAB'
              rw [← hAsidPreserved]; exact hEq
            · rw [hObjNe oidA hA] at hObjA
              rw [hObjNe oidB hB] at hObjB
              exact hCrossAsid oidA oidB rA rB hObjA hObjB hNeqAB

-- ============================================================================
-- TPI-D05 / TPI-001: VSpace round-trip theorems
-- ============================================================================

/-- TPI-001/WS-H11 round-trip #1: After a successful `vspaceMapPage`, `vspaceLookup` on the same
    ASID and vaddr returns the mapped physical address. -/
theorem vspaceLookup_after_map
    (st st' : SystemState)
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) (paddr : SeLe4n.PAddr)
    (perms : PagePermissions)
    (_hInv : vspaceInvariantBundle st)
    (hStep : vspaceMapPage asid vaddr paddr perms st = .ok ((), st')) :
    vspaceLookup asid vaddr st' = .ok (paddr, st') := by
  unfold vspaceMapPage at hStep
  cases hResolve : resolveAsidRoot st asid with
  | none => simp [hResolve] at hStep
  | some pair =>
      rcases pair with ⟨rootId, root⟩
      simp only [hResolve] at hStep
      by_cases hWx : perms.wxCompliant = true
      · simp only [hWx, Bool.not_true] at hStep
        cases hMapRoot : root.mapPage vaddr paddr perms with
        | none => simp [hMapRoot] at hStep
        | some root' =>
            have hStore : storeObject rootId (.vspaceRoot root') st = .ok ((), st') := by
              simpa [hMapRoot] using hStep
            rcases resolveAsidRoot_some_implies_obj st asid rootId root hResolve with ⟨_, _, hAsidRoot⟩
            have hAsidPreserved : root'.asid = root.asid :=
              VSpaceRoot.mapPage_asid_eq root root' vaddr paddr perms hMapRoot
            have hObjEq : st'.objects[rootId]? = some (.vspaceRoot root') :=
              storeObject_objects_eq st st' rootId (.vspaceRoot root') hStore
            have hTablePost : st'.asidTable[root'.asid]? = some rootId :=
              storeObject_asidTable_vspaceRoot st st' rootId root' hStore
            have hAsidEq : root'.asid = asid := hAsidPreserved.trans hAsidRoot
            have hResolve' : resolveAsidRoot st' asid = some (rootId, root') :=
              resolveAsidRoot_of_asidTable_entry st' asid rootId root'
                (hAsidEq ▸ hTablePost) hObjEq hAsidEq
            have hLookupRoot' : root'.lookupAddr vaddr = some paddr :=
              VSpaceRoot.lookupAddr_mapPage_eq root root' vaddr paddr perms hMapRoot
            simp [vspaceLookup, hResolve', hLookupRoot']
      · have hWxF : perms.wxCompliant = false := by cases perms.wxCompliant <;> simp_all
        simp only [hWxF, Bool.not_false, ite_true] at hStep
        exact nomatch hStep

/-- TPI-001/WS-H11 round-trip #2: A `vspaceMapPage` at vaddr does not affect `vspaceLookup` at
    a different vaddr'. -/
theorem vspaceLookup_map_other
    (st st' : SystemState)
    (asid : SeLe4n.ASID) (vaddr vaddr' : SeLe4n.VAddr) (paddr : SeLe4n.PAddr)
    (perms : PagePermissions)
    (hNe : vaddr ≠ vaddr')
    (_hInv : vspaceInvariantBundle st)
    (hStep : vspaceMapPage asid vaddr paddr perms st = .ok ((), st')) :
    (vspaceLookup asid vaddr' st').map Prod.fst = (vspaceLookup asid vaddr' st).map Prod.fst := by
  unfold vspaceMapPage at hStep
  cases hResolve : resolveAsidRoot st asid with
  | none => simp [hResolve] at hStep
  | some pair =>
      rcases pair with ⟨rootId, root⟩
      simp only [hResolve] at hStep
      by_cases hWx : perms.wxCompliant = true
      · simp only [hWx, Bool.not_true] at hStep
        cases hMapRoot : root.mapPage vaddr paddr perms with
        | none => simp [hMapRoot] at hStep
        | some root' =>
            have hStore : storeObject rootId (.vspaceRoot root') st = .ok ((), st') := by
              simpa [hMapRoot] using hStep
            rcases resolveAsidRoot_some_implies_obj st asid rootId root hResolve with ⟨_, _, hAsidRoot⟩
            have hAsidPreserved : root'.asid = root.asid :=
              VSpaceRoot.mapPage_asid_eq root root' vaddr paddr perms hMapRoot
            have hObjEq : st'.objects[rootId]? = some (.vspaceRoot root') :=
              storeObject_objects_eq st st' rootId (.vspaceRoot root') hStore
            have hTablePost : st'.asidTable[root'.asid]? = some rootId :=
              storeObject_asidTable_vspaceRoot st st' rootId root' hStore
            have hAsidEq : root'.asid = asid := hAsidPreserved.trans hAsidRoot
            have hResolve' : resolveAsidRoot st' asid = some (rootId, root') :=
              resolveAsidRoot_of_asidTable_entry st' asid rootId root'
                (hAsidEq ▸ hTablePost) hObjEq hAsidEq
            -- lookupAddr for a different vaddr' is unaffected
            have hLookupNe : root'.lookupAddr vaddr' = root.lookupAddr vaddr' := by
              simp [VSpaceRoot.lookupAddr,
                VSpaceRoot.lookup_mapPage_ne root root' vaddr vaddr' paddr perms hNe hMapRoot]
            simp [vspaceLookup, hResolve', hResolve, hLookupNe, Except.map]
            cases root.lookupAddr vaddr' <;> rfl
      · have hWxF : perms.wxCompliant = false := by cases perms.wxCompliant <;> simp_all
        simp only [hWxF, Bool.not_false, ite_true] at hStep
        exact nomatch hStep

/-- TPI-001 round-trip #3: After a successful `vspaceUnmapPage`, `vspaceLookup` on the
    unmapped vaddr returns a translation fault (no mapping). -/
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
          have hAddrNone : root'.lookupAddr vaddr = none := by
            simp [VSpaceRoot.lookupAddr, hLookupNone]
          simp [vspaceLookup, hResolve', hAddrNone]

/-- TPI-001 round-trip #4: `vspaceUnmapPage` at vaddr does not affect `vspaceLookup` at
    a different vaddr'. -/
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
          have hLookupNe : root'.lookupAddr vaddr' = root.lookupAddr vaddr' := by
            simp [VSpaceRoot.lookupAddr,
              VSpaceRoot.lookup_unmapPage_ne root root' vaddr vaddr' hNe hUnmapRoot]
          simp [vspaceLookup, hResolve', hResolve, hLookupNe, Except.map]
          cases root.lookupAddr vaddr' <;> rfl

-- ============================================================================
-- WS-H11/A-05: vspaceMapPageChecked preservation
-- ============================================================================

/-- WS-H11/A-05: `vspaceMapPageChecked` preserves the VSpace invariant bundle.
    The bounds check is enforced at runtime, so no external `hBound` hypothesis is needed —
    it is derived from the successful execution of the bounds guard. -/
theorem vspaceMapPageChecked_success_preserves_vspaceInvariantBundle
    (st st' : SystemState)
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) (paddr : SeLe4n.PAddr)
    (perms : PagePermissions)
    (hInv : vspaceInvariantBundle st)
    (hStep : vspaceMapPageChecked asid vaddr paddr perms st = .ok ((), st')) :
    vspaceInvariantBundle st' := by
  unfold vspaceMapPageChecked at hStep
  split at hStep
  · simp at hStep
  · rename_i hBoundNeg
    have hBound : paddr.toNat < 2^52 := by
      simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hBoundNeg
      unfold physicalAddressBound at hBoundNeg; omega
    exact vspaceMapPage_success_preserves_vspaceInvariantBundle
      st st' asid vaddr paddr perms hInv hBound hStep

/-- WS-H11/A-05: `vspaceMapPageChecked` error on out-of-bounds preserves invariant trivially. -/
theorem vspaceMapPageChecked_error_preserves_vspaceInvariantBundle
    (st : SystemState)
    (asid : SeLe4n.ASID)
    (vaddr : SeLe4n.VAddr)
    (paddr : SeLe4n.PAddr)
    (perms : PagePermissions)
    (_hErr : vspaceMapPageChecked asid vaddr paddr perms st = .error .addressOutOfBounds) :
    vspaceInvariantBundle st → vspaceInvariantBundle st := id

-- ============================================================================
-- WS-H11: vspaceLookupFull round-trip theorem
-- ============================================================================

/-- WS-H11: After a successful `vspaceMapPage`, `vspaceLookupFull` returns the full
    `(paddr, perms)` entry. -/
theorem vspaceLookupFull_after_map
    (st st' : SystemState)
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) (paddr : SeLe4n.PAddr)
    (perms : PagePermissions)
    (_hInv : vspaceInvariantBundle st)
    (hStep : vspaceMapPage asid vaddr paddr perms st = .ok ((), st')) :
    vspaceLookupFull asid vaddr st' = .ok ((paddr, perms), st') := by
  unfold vspaceMapPage at hStep
  cases hResolve : resolveAsidRoot st asid with
  | none => simp [hResolve] at hStep
  | some pair =>
      rcases pair with ⟨rootId, root⟩
      simp only [hResolve] at hStep
      by_cases hWx : perms.wxCompliant = true
      · simp only [hWx, Bool.not_true] at hStep
        cases hMapRoot : root.mapPage vaddr paddr perms with
        | none => simp [hMapRoot] at hStep
        | some root' =>
            have hStore : storeObject rootId (.vspaceRoot root') st = .ok ((), st') := by
              simpa [hMapRoot] using hStep
            rcases resolveAsidRoot_some_implies_obj st asid rootId root hResolve with ⟨_, _, hAsidRoot⟩
            have hAsidPreserved : root'.asid = root.asid :=
              VSpaceRoot.mapPage_asid_eq root root' vaddr paddr perms hMapRoot
            have hObjEq : st'.objects[rootId]? = some (.vspaceRoot root') :=
              storeObject_objects_eq st st' rootId (.vspaceRoot root') hStore
            have hTablePost : st'.asidTable[root'.asid]? = some rootId :=
              storeObject_asidTable_vspaceRoot st st' rootId root' hStore
            have hAsidEq : root'.asid = asid := hAsidPreserved.trans hAsidRoot
            have hResolve' : resolveAsidRoot st' asid = some (rootId, root') :=
              resolveAsidRoot_of_asidTable_entry st' asid rootId root'
                (hAsidEq ▸ hTablePost) hObjEq hAsidEq
            have hLookupRoot' : root'.lookup vaddr = some (paddr, perms) :=
              VSpaceRoot.lookup_mapPage_eq root root' vaddr paddr perms hMapRoot
            simp [vspaceLookupFull, hResolve', hLookupRoot']
      · have hWxF : perms.wxCompliant = false := by cases perms.wxCompliant <;> simp_all
        simp only [hWxF, Bool.not_false, ite_true] at hStep
        exact nomatch hStep

-- ============================================================================
-- ASID table agreement composition theorems (Issue 2 / Part C)
-- ============================================================================

/-- After a successful `vspaceMapPage`, `resolveAsidRoot` for the same ASID
    returns the updated root. This is the composition theorem connecting
    Part C (ASID consistency) with Part A (page table modification). -/
theorem vspaceMapPage_resolveAsidRoot_agreement
    (st st' : SystemState)
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) (paddr : SeLe4n.PAddr)
    (perms : PagePermissions)
    (hStep : vspaceMapPage asid vaddr paddr perms st = .ok ((), st')) :
    ∃ rootId root', resolveAsidRoot st' asid = some (rootId, root') := by
  unfold vspaceMapPage at hStep
  cases hResolve : resolveAsidRoot st asid with
  | none => simp [hResolve] at hStep
  | some pair =>
      rcases pair with ⟨rootId, root⟩
      simp only [hResolve] at hStep
      by_cases hWx : perms.wxCompliant = true
      · simp only [hWx, Bool.not_true] at hStep
        cases hMapRoot : root.mapPage vaddr paddr perms with
        | none => simp [hMapRoot] at hStep
        | some root' =>
            have hStore : storeObject rootId (.vspaceRoot root') st = .ok ((), st') := by
              simpa [hMapRoot] using hStep
            rcases resolveAsidRoot_some_implies_obj st asid rootId root hResolve with ⟨_, _, hAsidRoot⟩
            have hAsidPreserved : root'.asid = root.asid :=
              VSpaceRoot.mapPage_asid_eq root root' vaddr paddr perms hMapRoot
            have hObjEq : st'.objects[rootId]? = some (.vspaceRoot root') :=
              storeObject_objects_eq st st' rootId (.vspaceRoot root') hStore
            have hTablePost : st'.asidTable[root'.asid]? = some rootId :=
              storeObject_asidTable_vspaceRoot st st' rootId root' hStore
            have hAsidEq : root'.asid = asid := hAsidPreserved.trans hAsidRoot
            have hResolve' : resolveAsidRoot st' asid = some (rootId, root') :=
              resolveAsidRoot_of_asidTable_entry st' asid rootId root'
                (hAsidEq ▸ hTablePost) hObjEq hAsidEq
            exact ⟨rootId, root', hResolve'⟩
      · have hWxF : perms.wxCompliant = false := by cases perms.wxCompliant <;> simp_all
        simp only [hWxF, Bool.not_false, ite_true] at hStep
        exact nomatch hStep

/-- After a successful `vspaceUnmapPage`, `resolveAsidRoot` for the same ASID
    returns the updated root. -/
theorem vspaceUnmapPage_resolveAsidRoot_agreement
    (st st' : SystemState)
    (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr)
    (hStep : vspaceUnmapPage asid vaddr st = .ok ((), st')) :
    ∃ rootId root', resolveAsidRoot st' asid = some (rootId, root') := by
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
          exact ⟨rootId, root', hResolve'⟩

end SeLe4n.Kernel.Architecture
