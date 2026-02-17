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
    p < bound

/-- WS-B1 architecture/VSpace invariant bundle entrypoint. -/
def vspaceInvariantBundle (st : SystemState) : Prop :=
  vspaceAsidRootsUnique st ∧ vspaceRootNonOverlap st

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

end SeLe4n.Kernel.Architecture
