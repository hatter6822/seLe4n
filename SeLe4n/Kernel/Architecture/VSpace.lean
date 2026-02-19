import SeLe4n.Model.State

/-!
WS-C3 proof-surface note:

Determinism of pure Lean definitions is a meta-property of evaluation, so object-level
tautologies of the form `f x = f x` are not accepted as semantic evidence in this model.
VSpace semantic obligations are tracked via TPI-001 in
`docs/audits/AUDIT_v0.9.32_TRACKED_PROOF_ISSUES.md`.
-/

namespace SeLe4n.Kernel.Architecture

open SeLe4n.Model

/-- Logical relation: object `rootId` is a VSpace root bound to `asid`. -/
def asidBoundToRoot (st : SystemState) (asid : SeLe4n.ASID) (rootId : SeLe4n.ObjId) : Prop :=
  ∃ root, st.objects rootId = some (.vspaceRoot root) ∧ root.asid = asid

/-- Locate one root object id carrying `asid` in the bounded discovery window. -/
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

end SeLe4n.Kernel.Architecture
