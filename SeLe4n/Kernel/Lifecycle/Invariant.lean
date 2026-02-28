import SeLe4n.Kernel.Lifecycle.Operations

/-!
# Lifecycle Invariant Preservation Proofs

This module contains invariant definitions and preservation theorems for the
lifecycle (object retype) subsystem, including identity/aliasing, capability-reference,
and stale-reference exclusion invariants.

## Proof scope qualification (F-16)

**Substantive preservation theorems** (high assurance — prove invariant preservation
over *changed* state after a *successful* operation):
- `lifecycleRetypeObject_preserves_lifecycleInvariantBundle`
- `lifecycleRetypeObject_preserves_lifecycleStaleReferenceExclusionInvariant`
- `lifecycleRetypeObject_preserves_lifecycleIdentityStaleReferenceInvariant`

**Structural / bridge theorems** (high assurance — prove decomposition and composition
relationships between invariant layers):
- `lifecycleIdentityNoTypeAliasConflict_of_exact`
- `lifecycleCapabilityRefObjectTargetBacked_of_exact`
- `lifecycleInvariantBundle_of_metadata_consistent`
- `lifecycleMetadataConsistent_of_lifecycleInvariantBundle`
- `lifecycleCapabilityRefObjectTargetTypeAligned_of_exact`
- `lifecycleCapabilityRefNoTypeAliasConflict_of_identity`
- `lifecycleStaleReferenceExclusionInvariant_of_lifecycleInvariantBundle`
- `lifecycleIdentityStaleReferenceInvariant_of_lifecycleInvariantBundle`

All theorems in this module are substantive: they prove structural decomposition
properties or invariant preservation over state modified by successful retype
operations. There are no error-case preservation theorems in this module.
-/

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

/-- M4-B stale-reference exclusion component: any object-target capability reference agrees with
object-type metadata whenever that object identity is present. -/
def lifecycleCapabilityRefObjectTargetTypeAligned (st : SystemState) : Prop :=
  ∀ ref oid obj,
    SystemState.lookupCapabilityRefMeta st ref = some (.object oid) →
    st.objects oid = some obj →
    SystemState.lookupObjectTypeMeta st oid = some obj.objectType

/-- M4-B stale-reference exclusion component: capability-object references inherit the same
identity non-aliasing guarantee used by lifecycle identity metadata. -/
def lifecycleCapabilityRefNoTypeAliasConflict (st : SystemState) : Prop :=
  ∀ ref oid ty₁ ty₂,
    SystemState.lookupCapabilityRefMeta st ref = some (.object oid) →
    SystemState.lookupObjectTypeMeta st oid = some ty₁ →
    SystemState.lookupObjectTypeMeta st oid = some ty₂ →
    ty₁ = ty₂

/-- M4-B stale-reference exclusion family built from narrow, composable components. -/
def lifecycleStaleReferenceExclusionInvariant (st : SystemState) : Prop :=
  lifecycleCapabilityRefObjectTargetBacked st ∧
    lifecycleCapabilityRefObjectTargetTypeAligned st ∧
    lifecycleCapabilityRefNoTypeAliasConflict st

/-- M4-B link point: stale-reference exclusion explicitly depends on identity/aliasing constraints
rather than replacing them with a monolithic definition. -/
def lifecycleIdentityStaleReferenceInvariant (st : SystemState) : Prop :=
  lifecycleIdentityAliasingInvariant st ∧ lifecycleStaleReferenceExclusionInvariant st

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

theorem lifecycleCapabilityRefObjectTargetTypeAligned_of_exact
    (st : SystemState)
    (hObjType : lifecycleIdentityTypeExact st) :
    lifecycleCapabilityRefObjectTargetTypeAligned st := by
  intro ref oid obj _hMeta hObj
  simpa [lifecycleIdentityTypeExact, SystemState.objectTypeMetadataConsistent,
    SystemState.lookupObjectTypeMeta, hObj] using hObjType oid

theorem lifecycleCapabilityRefNoTypeAliasConflict_of_identity
    (st : SystemState)
    (hAlias : lifecycleIdentityNoTypeAliasConflict st) :
    lifecycleCapabilityRefNoTypeAliasConflict st := by
  intro _ref oid ty₁ ty₂ _hMeta hTy₁ hTy₂
  exact hAlias oid ty₁ ty₂ hTy₁ hTy₂

theorem lifecycleStaleReferenceExclusionInvariant_of_lifecycleInvariantBundle
    (st : SystemState)
    (hInv : lifecycleInvariantBundle st) :
    lifecycleStaleReferenceExclusionInvariant st := by
  rcases hInv with ⟨hIdAlias, hCapRef⟩
  rcases hIdAlias with ⟨hObjType, hAlias⟩
  rcases hCapRef with ⟨_hCapRefExact, hBacked⟩
  refine ⟨hBacked, ?_, ?_⟩
  · exact lifecycleCapabilityRefObjectTargetTypeAligned_of_exact st hObjType
  · exact lifecycleCapabilityRefNoTypeAliasConflict_of_identity st hAlias

theorem lifecycleIdentityStaleReferenceInvariant_of_lifecycleInvariantBundle
    (st : SystemState)
    (hInv : lifecycleInvariantBundle st) :
    lifecycleIdentityStaleReferenceInvariant st := by
  refine ⟨hInv.1, lifecycleStaleReferenceExclusionInvariant_of_lifecycleInvariantBundle st hInv⟩

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

theorem lifecycleRetypeObject_preserves_lifecycleStaleReferenceExclusionInvariant
    (st st' : SystemState)
    (authority : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj : KernelObject)
    (hInv : lifecycleInvariantBundle st)
    (hStep : lifecycleRetypeObject authority target newObj st = .ok ((), st')) :
    lifecycleStaleReferenceExclusionInvariant st' := by
  have hBundle' : lifecycleInvariantBundle st' :=
    lifecycleRetypeObject_preserves_lifecycleInvariantBundle st st' authority target newObj hInv hStep
  exact lifecycleStaleReferenceExclusionInvariant_of_lifecycleInvariantBundle st' hBundle'

theorem lifecycleRetypeObject_preserves_lifecycleIdentityStaleReferenceInvariant
    (st st' : SystemState)
    (authority : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj : KernelObject)
    (hInv : lifecycleInvariantBundle st)
    (hStep : lifecycleRetypeObject authority target newObj st = .ok ((), st')) :
    lifecycleIdentityStaleReferenceInvariant st' := by
  have hBundle' : lifecycleInvariantBundle st' :=
    lifecycleRetypeObject_preserves_lifecycleInvariantBundle st st' authority target newObj hInv hStep
  exact lifecycleIdentityStaleReferenceInvariant_of_lifecycleInvariantBundle st' hBundle'

-- ============================================================================
-- WS-F2: Untyped Memory Model Invariants
-- ============================================================================

/-- WS-F2: Untyped watermark invariant — for every untyped object in the store,
its watermark does not exceed its region size. -/
def untypedWatermarkInvariant (st : SystemState) : Prop :=
  ∀ oid ut,
    st.objects oid = some (.untyped ut) →
    ut.watermarkValid

/-- WS-F2: Untyped children-within-watermark invariant — all child allocations
fit within the watermark (and thus within the region). -/
def untypedChildrenBoundsInvariant (st : SystemState) : Prop :=
  ∀ oid ut,
    st.objects oid = some (.untyped ut) →
    ut.childrenWithinWatermark

/-- WS-F2: Untyped children non-overlap invariant — no two child allocations
within the same untyped region overlap in their address ranges. -/
def untypedChildrenNonOverlapInvariant (st : SystemState) : Prop :=
  ∀ oid ut,
    st.objects oid = some (.untyped ut) →
    ut.childrenNonOverlap

/-- WS-F2: Untyped children unique-id invariant — children within each untyped
have distinct object identities. -/
def untypedChildrenUniqueIdsInvariant (st : SystemState) : Prop :=
  ∀ oid ut,
    st.objects oid = some (.untyped ut) →
    ut.childrenUniqueIds

/-- WS-F2: Combined untyped memory well-formedness invariant. -/
def untypedMemoryInvariant (st : SystemState) : Prop :=
  untypedWatermarkInvariant st ∧
  untypedChildrenBoundsInvariant st ∧
  untypedChildrenNonOverlapInvariant st ∧
  untypedChildrenUniqueIdsInvariant st

/-- WS-F2: The default (empty) state satisfies the untyped memory invariant
because no untyped objects exist. -/
theorem default_systemState_untypedMemoryInvariant :
    untypedMemoryInvariant (default : SystemState) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro oid ut hObj <;> simp at hObj

/-- WS-F2: `storeObject` at a non-untyped slot preserves watermark invariant
for all existing untyped objects at other ObjIds. -/
theorem storeObject_preserves_untypedWatermarkInvariant_ne
    (st st' : SystemState)
    (oid : SeLe4n.ObjId)
    (obj : KernelObject)
    (hInv : untypedWatermarkInvariant st)
    (hStep : storeObject oid obj st = .ok ((), st'))
    (uid : SeLe4n.ObjId)
    (hNe : uid ≠ oid)
    (ut : UntypedObject)
    (hUt : st'.objects uid = some (.untyped ut)) :
    ut.watermarkValid := by
  have hPrev : st'.objects uid = st.objects uid :=
    storeObject_objects_ne st st' oid uid obj hNe hStep
  rw [hPrev] at hUt
  exact hInv uid ut hUt

/-- WS-F2: `retypeFromUntyped` preserves lifecycle metadata consistency.
Both `storeObject` calls maintain metadata. -/
theorem retypeFromUntyped_preserves_lifecycleMetadataConsistent
    (st st' : SystemState)
    (authority : CSpaceAddr)
    (untypedId childId : SeLe4n.ObjId)
    (newObj : KernelObject)
    (allocSize : Nat)
    (hMeta : SystemState.lifecycleMetadataConsistent st)
    (hStep : retypeFromUntyped authority untypedId childId newObj allocSize st = .ok ((), st')) :
    SystemState.lifecycleMetadataConsistent st' := by
  rcases retypeFromUntyped_ok_decompose st st' authority untypedId childId newObj allocSize hStep with
    ⟨_ut, ut', _cap, stLookup, stUt, _offset, _hObj, _hNotDev,
     hLookup, _hAuth, _hAlloc, hStoreUt, hStoreChild⟩
  have hLookupSt : stLookup = st :=
    cspaceLookupSlot_ok_state_eq st authority _ stLookup hLookup
  rw [hLookupSt] at hStoreUt
  have hMetaUt : SystemState.lifecycleMetadataConsistent stUt :=
    storeObject_preserves_lifecycleMetadataConsistent st stUt untypedId (.untyped ut') hMeta hStoreUt
  exact storeObject_preserves_lifecycleMetadataConsistent stUt st' childId newObj hMetaUt hStoreChild

/-- WS-F2: `retypeFromUntyped` preserves the full lifecycle invariant bundle. -/
theorem retypeFromUntyped_preserves_lifecycleInvariantBundle
    (st st' : SystemState)
    (authority : CSpaceAddr)
    (untypedId childId : SeLe4n.ObjId)
    (newObj : KernelObject)
    (allocSize : Nat)
    (hInv : lifecycleInvariantBundle st)
    (hStep : retypeFromUntyped authority untypedId childId newObj allocSize st = .ok ((), st')) :
    lifecycleInvariantBundle st' := by
  have hMeta : SystemState.lifecycleMetadataConsistent st :=
    lifecycleMetadataConsistent_of_lifecycleInvariantBundle st hInv
  have hMeta' : SystemState.lifecycleMetadataConsistent st' :=
    retypeFromUntyped_preserves_lifecycleMetadataConsistent
      st st' authority untypedId childId newObj allocSize hMeta hStep
  exact lifecycleInvariantBundle_of_metadata_consistent st' hMeta'

end SeLe4n.Kernel
