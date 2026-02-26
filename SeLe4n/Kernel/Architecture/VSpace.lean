import SeLe4n.Model.State

/-!
# VSpace Operations

WS-C3 proof-surface note:

Determinism of pure Lean definitions is a meta-property of evaluation, so object-level
tautologies of the form `f x = f x` are not accepted as semantic evidence in this model.
VSpace semantic obligations are tracked via TPI-001 in
`docs/dev_history/audits/AUDIT_v0.9.32_TRACKED_PROOF_ISSUES.md`.

## F-17/WS-E6: O(n) data structure design rationale

`resolveAsidRoot` uses **linear search** over `objectIndex` (`List.findSome?`)
to locate the VSpace root bound to a given ASID. This is O(n) in the number
of tracked objects.

**Rationale:**
- The seLe4n model is a formal specification, not a production implementation.
  Model clarity and proof tractability take priority over algorithmic efficiency.
- Linear search over a `List` is straightforward to reason about in Lean 4:
  `List.findSome?` has simple inductive structure, enabling the key
  characterization lemma `resolveAsidRoot_of_unique_root` used in all VSpace
  round-trip theorems.
- The real seL4 kernel uses a dedicated ASID pool/table with O(1) lookup.
  Modeling this would add structure without improving proof coverage.

**Scope note:** The O(n) cost applies to model execution only (test harness,
`lake exe sele4n`). For the ~100-object test topologies used in CI, execution
time is negligible (<1ms per lookup). Should the model scale to thousands of
objects, the index can be replaced with a `Finmap ASID ObjId` or similar
indexed structure without changing the semantic interface.

**Future migration path:**
1. Replace `List ObjId` with `Finmap ASID ObjId` in `SystemState`.
2. Update `resolveAsidRoot` to direct lookup.
3. Adapt `resolveAsidRoot_some_implies` and `resolveAsidRoot_of_unique_root`
   to the new representation.
4. All downstream VSpace theorems should transfer unchanged (they depend only
   on the two characterization lemmas, not on the internal representation).
-/

namespace SeLe4n.Kernel.Architecture

open SeLe4n.Model

/-- Logical relation: object `rootId` is a VSpace root bound to `asid`. -/
def asidBoundToRoot (st : SystemState) (asid : SeLe4n.ASID) (rootId : SeLe4n.ObjId) : Prop :=
  ∃ root, st.objects rootId = some (.vspaceRoot root) ∧ root.asid = asid

/-- F-17/WS-E6: Locate one root object id carrying `asid` via linear search
over `objectIndex`. See module docstring for O(n) design rationale. -/
def resolveAsidRoot (st : SystemState) (asid : SeLe4n.ASID) : Option (SeLe4n.ObjId × VSpaceRoot) :=
  st.objectIndex.findSome? (fun oid =>
    match st.objects oid with
    | some (.vspaceRoot root) => if root.asid = asid then some (oid, root) else none
    | _ => none)

/-- Deterministic VSpace map transition with explicit failures. -/
def vspaceMapPage (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) (paddr : SeLe4n.PAddr) : Kernel Unit :=
  fun st =>
    match resolveAsidRoot st asid with
    | none => .error .asidNotBound
    | some (rootId, root) =>
        match root.mapPage vaddr paddr with
        | none => .error .mappingConflict
        | some root' =>
            storeObject rootId (.vspaceRoot root') st

/-- Deterministic VSpace unmap transition with explicit failures. -/
def vspaceUnmapPage (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) : Kernel Unit :=
  fun st =>
    match resolveAsidRoot st asid with
    | none => .error .asidNotBound
    | some (rootId, root) =>
        match root.unmapPage vaddr with
        | none => .error .translationFault
        | some root' =>
            storeObject rootId (.vspaceRoot root') st

/-- Deterministic VSpace translation helper with explicit failure on unresolved mappings. -/
def vspaceLookup (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) : Kernel SeLe4n.PAddr :=
  fun st =>
    match resolveAsidRoot st asid with
    | none => .error .asidNotBound
    | some (_, root) =>
        match root.lookup vaddr with
        | none => .error .translationFault
        | some paddr => .ok (paddr, st)

-- ============================================================================
-- resolveAsidRoot extraction and characterization lemmas (F-08 / TPI-001)
-- ============================================================================

/-- ASID roots in the bounded discovery window are unique. -/
def vspaceAsidRootsUnique (st : SystemState) : Prop :=
  ∀ oid₁ oid₂ root₁ root₂,
    st.objects oid₁ = some (.vspaceRoot root₁) →
    st.objects oid₂ = some (.vspaceRoot root₂) →
    root₁.asid = root₂.asid →
    oid₁ = oid₂

/-- Extract concrete object-store facts from a successful `resolveAsidRoot` result. -/
theorem resolveAsidRoot_some_implies
    (st : SystemState) (asid : SeLe4n.ASID)
    (rootId : SeLe4n.ObjId) (root : VSpaceRoot)
    (hResolve : resolveAsidRoot st asid = some (rootId, root)) :
    st.objects rootId = some (.vspaceRoot root) ∧ root.asid = asid ∧ rootId ∈ st.objectIndex := by
  unfold resolveAsidRoot at hResolve
  generalize st.objectIndex = idx at hResolve ⊢
  induction idx with
  | nil => simp [List.findSome?_nil] at hResolve
  | cons a rest ih =>
      simp only [List.findSome?_cons] at hResolve
      split at hResolve
      · next hMatch =>
        cases hObjA : st.objects a with
        | none => simp [hObjA] at hMatch
        | some obj =>
            cases obj with
            | vspaceRoot r =>
                simp only [hObjA] at hMatch
                split at hMatch
                · next hAsidEq =>
                  simp at hMatch
                  rcases hMatch with ⟨rfl, rfl⟩
                  simp at hResolve
                  rcases hResolve with ⟨rfl, rfl⟩
                  exact ⟨hObjA, hAsidEq, List.mem_cons_self⟩
                · simp at hMatch
            | tcb _ | cnode _ | endpoint _ | notification _ =>
                simp [hObjA] at hMatch
      · next hNone =>
        rcases ih hResolve with ⟨hObj, hAsid, hMem⟩
        exact ⟨hObj, hAsid, List.mem_cons_of_mem a hMem⟩

/-- Characterization lemma: given ASID-uniqueness, object-store membership, and objectIndex
    membership, `resolveAsidRoot` returns exactly the expected root.

    This is the key lemma enabling round-trip theorems for VSpace operations. -/
theorem resolveAsidRoot_of_unique_root
    (st : SystemState) (asid : SeLe4n.ASID)
    (rootId : SeLe4n.ObjId) (root : VSpaceRoot)
    (hObj : st.objects rootId = some (.vspaceRoot root))
    (hAsid : root.asid = asid)
    (hMem : rootId ∈ st.objectIndex)
    (hUniq : vspaceAsidRootsUnique st) :
    resolveAsidRoot st asid = some (rootId, root) := by
  unfold resolveAsidRoot
  generalize st.objectIndex = idx at hMem ⊢
  induction idx with
  | nil => exact absurd hMem List.not_mem_nil
  | cons a rest ih =>
      simp only [List.findSome?_cons]
      by_cases hEq : a = rootId
      · subst hEq
        simp [hObj, hAsid]
      · -- a ≠ rootId: show the function at a returns none (no VSpace root with this ASID)
        have hMemRest : rootId ∈ rest := by
          cases hMem with
          | head => exact absurd rfl hEq
          | tail _ h => exact h
        suffices hNone : (match st.objects a with
            | some (.vspaceRoot r) => if r.asid = asid then some (a, r) else none
            | _ => none) = none by
          simp [hNone]
          exact ih hMemRest
        cases hObjA : st.objects a with
        | none => simp
        | some obj =>
            cases obj with
            | vspaceRoot r =>
                simp
                intro hAsidR
                -- r.asid = asid and root.asid = asid, so by uniqueness a = rootId
                exact absurd (hUniq a rootId r root hObjA hObj (hAsidR.trans hAsid.symm)) hEq
            | tcb _ | cnode _ | endpoint _ | notification _ => simp

-- ============================================================================
-- storeObject preservation lemmas for VSpace operations
-- ============================================================================

/-- After `storeObject` at a rootId that was already in objectIndex, the objectIndex is unchanged. -/
theorem storeObject_objectIndex_eq_of_mem
    (st st' : SystemState) (id : SeLe4n.ObjId) (obj : KernelObject)
    (hMem : id ∈ st.objectIndex)
    (hStore : storeObject id obj st = .ok ((), st')) :
    st'.objectIndex = st.objectIndex := by
  unfold storeObject at hStore
  cases hStore
  simp [hMem]

end SeLe4n.Kernel.Architecture
