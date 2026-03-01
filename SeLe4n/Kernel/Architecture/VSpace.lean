import SeLe4n.Model.State

/-!
WS-C3 proof-surface note:

Determinism of pure Lean definitions is a meta-property of evaluation, so object-level
tautologies of the form `f x = f x` are not accepted as semantic evidence in this model.
VSpace semantic obligations are tracked via TPI-001 in
`docs/dev_history/audits/AUDIT_v0.9.32_TRACKED_PROOF_ISSUES.md`.
-/

namespace SeLe4n.Kernel.Architecture

open SeLe4n.Model

/-- Logical relation: object `rootId` is a VSpace root bound to `asid`. -/
def asidBoundToRoot (st : SystemState) (asid : SeLe4n.ASID) (rootId : SeLe4n.ObjId) : Prop :=
  ∃ root, st.objects[rootId]? = some (KernelObject.vspaceRoot root) ∧ root.asid = asid

/-- WS-G3/F-P06: Locate the root object id carrying `asid` via O(1) hash lookup.
    Falls back to object-store validation to ensure the entry is still a valid VSpaceRoot. -/
def resolveAsidRoot (st : SystemState) (asid : SeLe4n.ASID) : Option (SeLe4n.ObjId × VSpaceRoot) :=
  match st.asidTable[asid]? with
  | some oid =>
    match st.objects[oid]? with
    | some (.vspaceRoot root) => if root.asid = asid then some (oid, root) else none
    | _ => none
  | none => none

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
  ∀ (oid₁ oid₂ : SeLe4n.ObjId) (root₁ root₂ : VSpaceRoot),
    st.objects[oid₁]? = some (KernelObject.vspaceRoot root₁) →
    st.objects[oid₂]? = some (KernelObject.vspaceRoot root₂) →
    root₁.asid = root₂.asid →
    oid₁ = oid₂

/-- WS-G3: Extract concrete object-store and ASID table facts from a successful
    `resolveAsidRoot` result. Pure definitional — no invariant hypothesis needed. -/
theorem resolveAsidRoot_some_implies_obj
    (st : SystemState) (asid : SeLe4n.ASID)
    (rootId : SeLe4n.ObjId) (root : VSpaceRoot)
    (hResolve : resolveAsidRoot st asid = some (rootId, root)) :
    st.asidTable[asid]? = some rootId ∧
    st.objects[rootId]? = some (KernelObject.vspaceRoot root) ∧
    root.asid = asid := by
  unfold resolveAsidRoot at hResolve
  cases hTable : st.asidTable[asid]? with
  | none => simp [hTable] at hResolve
  | some oid =>
      simp only [hTable] at hResolve
      cases hObj : st.objects[oid]? with
      | none => simp [hObj] at hResolve
      | some obj =>
          cases obj with
          | vspaceRoot r =>
              simp only [hObj] at hResolve
              by_cases hAsidEq : r.asid = asid
              · simp only [hAsidEq, ite_true] at hResolve
                have hPairEq := Option.some.inj hResolve
                have hOidEq : oid = rootId := congrArg Prod.fst hPairEq
                have hRootEq : r = root := congrArg Prod.snd hPairEq
                subst hOidEq; subst hRootEq
                exact ⟨rfl, hObj, hAsidEq⟩
              · simp only [hAsidEq, ite_false] at hResolve; cases hResolve
          | tcb _ => simp [hObj] at hResolve
          | cnode _ => simp [hObj] at hResolve
          | endpoint _ => simp [hObj] at hResolve
          | notification _ => simp [hObj] at hResolve
          | untyped _ => simp [hObj] at hResolve

/-- WS-G3/F-P06: Characterization lemma — given the ASID table entry and object-store
    evidence, `resolveAsidRoot` returns exactly the expected root.

    This replaces `resolveAsidRoot_of_unique_root` — no ASID uniqueness or objectIndex
    membership needed, just the table entry and object-store facts. -/
theorem resolveAsidRoot_of_asidTable_entry
    (st : SystemState) (asid : SeLe4n.ASID)
    (rootId : SeLe4n.ObjId) (root : VSpaceRoot)
    (hTable : st.asidTable[asid]? = some rootId)
    (hObj : st.objects[rootId]? = some (KernelObject.vspaceRoot root))
    (hAsid : root.asid = asid) :
    resolveAsidRoot st asid = some (rootId, root) := by
  unfold resolveAsidRoot
  simp [hTable, hObj, hAsid]

-- ============================================================================
-- storeObject preservation lemmas for VSpace operations
-- ============================================================================

/-- After `storeObject` at a rootId that was already in objectIndex, the objectIndex is unchanged.
    Requires objectIndexSet to be consistent (contains id ↔ id ∈ objectIndex). -/
theorem storeObject_objectIndex_eq_of_mem
    (st st' : SystemState) (id : SeLe4n.ObjId) (obj : KernelObject)
    (_hMem : id ∈ st.objectIndex)
    (hSync : st.objectIndexSet.contains id = true)
    (hStore : storeObject id obj st = .ok ((), st')) :
    st'.objectIndex = st.objectIndex := by
  unfold storeObject at hStore
  cases hStore
  simp [hSync]

end SeLe4n.Kernel.Architecture
