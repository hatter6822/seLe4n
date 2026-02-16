import SeLe4n.Kernel.Lifecycle.Operations

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- M4-A step-3 identity invariant: lifecycle object-type metadata exactly tracks
object-store identity typing for each object id. -/
def lifecycleIdentityTypeExact (st : SystemState) : Prop :=
  SystemState.objectTypeMetadataConsistent st

/-- M4-A step-3 aliasing invariant: one object identity cannot carry conflicting lifecycle
object-type aliases. -/
def lifecycleIdentityNoTypeAliasConflict (st : SystemState) : Prop :=
  ∀ oid ty₁ ty₂,
    SystemState.lookupObjectTypeMeta st oid = some ty₁ →
    SystemState.lookupObjectTypeMeta st oid = some ty₂ →
    ty₁ = ty₂

/-- Identity/aliasing bundle used by lifecycle proofs before capability-reference composition. -/
def lifecycleIdentityAliasingInvariant (st : SystemState) : Prop :=
  lifecycleIdentityTypeExact st ∧ lifecycleIdentityNoTypeAliasConflict st

/-- M4-A step-3 capability-reference invariant: lifecycle slot-reference metadata exactly tracks
concrete capability-slot targets. -/
def lifecycleCapabilityRefExact (st : SystemState) : Prop :=
  SystemState.capabilityRefMetadataConsistent st

/-- M4-A step-3 capability-reference invariant: every metadata object-target reference is backed by
an actual slot capability carrying that same object target. -/
def lifecycleCapabilityRefObjectTargetBacked (st : SystemState) : Prop :=
  ∀ ref oid,
    SystemState.lookupCapabilityRefMeta st ref = some (.object oid) →
    ∃ cap, SystemState.lookupSlotCap st ref = some cap ∧ cap.target = .object oid

/-- Lifecycle capability-reference constraint bundle (separate from identity/aliasing constraints). -/
def lifecycleCapabilityReferenceInvariant (st : SystemState) : Prop :=
  lifecycleCapabilityRefExact st ∧ lifecycleCapabilityRefObjectTargetBacked st

/-- Full lifecycle invariant bundle for M4-A step-3 with explicit layering separation. -/
def lifecycleInvariantBundle (st : SystemState) : Prop :=
  lifecycleIdentityAliasingInvariant st ∧ lifecycleCapabilityReferenceInvariant st

theorem lifecycleIdentityNoTypeAliasConflict_of_exact
    (st : SystemState)
    (hExact : lifecycleIdentityTypeExact st) :
    lifecycleIdentityNoTypeAliasConflict st := by
  intro oid ty₁ ty₂ hTy₁ hTy₂
  cases hObj : st.objects oid with
  | none =>
      have hNone : SystemState.lookupObjectTypeMeta st oid = none := by
        simpa [lifecycleIdentityTypeExact, SystemState.objectTypeMetadataConsistent,
          SystemState.lookupObjectTypeMeta, hObj] using hExact oid
      rw [hNone] at hTy₁
      contradiction
  | some obj =>
      have hMeta : SystemState.lookupObjectTypeMeta st oid = some obj.objectType := by
        simpa [lifecycleIdentityTypeExact, SystemState.objectTypeMetadataConsistent,
          SystemState.lookupObjectTypeMeta, hObj] using hExact oid
      rw [hMeta] at hTy₁ hTy₂
      cases hTy₁
      cases hTy₂
      rfl

theorem lifecycleCapabilityRefObjectTargetBacked_of_exact
    (st : SystemState)
    (hExact : lifecycleCapabilityRefExact st) :
    lifecycleCapabilityRefObjectTargetBacked st := by
  intro ref oid hMeta
  rw [hExact ref] at hMeta
  cases hLookup : SystemState.lookupSlotCap st ref with
  | none => simp [hLookup] at hMeta
  | some cap =>
      have hTarget : cap.target = .object oid := by
        simpa [hLookup] using hMeta
      exact ⟨cap, rfl, hTarget⟩

theorem lifecycleInvariantBundle_of_metadata_consistent
    (st : SystemState)
    (hMeta : SystemState.lifecycleMetadataConsistent st) :
    lifecycleInvariantBundle st := by
  rcases hMeta with ⟨hObjType, hCapRef⟩
  refine ⟨?_, ?_⟩
  · exact ⟨hObjType, lifecycleIdentityNoTypeAliasConflict_of_exact st hObjType⟩
  · exact ⟨hCapRef, lifecycleCapabilityRefObjectTargetBacked_of_exact st hCapRef⟩

theorem lifecycleMetadataConsistent_of_lifecycleInvariantBundle
    (st : SystemState)
    (hInv : lifecycleInvariantBundle st) :
    SystemState.lifecycleMetadataConsistent st := by
  rcases hInv with ⟨hIdAlias, hCapRef⟩
  rcases hIdAlias with ⟨hObjType, _hAlias⟩
  rcases hCapRef with ⟨hCapRefExact, _hBacked⟩
  exact ⟨hObjType, hCapRefExact⟩

theorem lifecycleRetypeObject_preserves_lifecycleInvariantBundle
    (st st' : SystemState)
    (authority : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj : KernelObject)
    (hInv : lifecycleInvariantBundle st)
    (hStep : lifecycleRetypeObject authority target newObj st = .ok ((), st')) :
    lifecycleInvariantBundle st' := by
  rcases lifecycleRetypeObject_ok_as_storeObject st st' authority target newObj hStep with
    ⟨_, _, _, _, _, _, hStore⟩
  have hMeta : SystemState.lifecycleMetadataConsistent st :=
    lifecycleMetadataConsistent_of_lifecycleInvariantBundle st hInv
  have hMeta' : SystemState.lifecycleMetadataConsistent st' :=
    storeObject_preserves_lifecycleMetadataConsistent st st' target newObj hMeta hStore
  exact lifecycleInvariantBundle_of_metadata_consistent st' hMeta'

end SeLe4n.Kernel
