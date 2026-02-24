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
-- M-09 (WS-E3): storeObject metadata sync correctness for type-changing stores
-- ============================================================================

/-- M-09 (WS-E3): `storeObject` correctly synchronizes lifecycle metadata with
the object store, even for type-changing stores. After storing object `obj` at
`id`, the lifecycle metadata at `id` exactly reflects `obj`'s type and
capability references. -/
theorem storeObject_metadata_sync_correct
    (st st' : SystemState)
    (id : SeLe4n.ObjId)
    (obj : KernelObject)
    (hStep : storeObject id obj st = .ok ((), st')) :
    st'.lifecycle.objectTypes id = some obj.objectType ∧
    (∀ ref : SlotRef,
      ref.cnode = id →
      st'.lifecycle.capabilityRefs ref =
        match obj with
        | .cnode cn => (cn.lookup ref.slot).map Capability.target
        | _ => none) ∧
    (∀ ref : SlotRef,
      ref.cnode ≠ id →
      st'.lifecycle.capabilityRefs ref = st.lifecycle.capabilityRefs ref) := by
  unfold storeObject at hStep
  cases hStep
  refine ⟨?_, ?_, ?_⟩
  · simp
  · intro ref hEq
    simp [hEq]
    cases obj <;> rfl
  · intro ref hNe
    simp [hNe]

/-- M-09 corollary: for non-CNode objects, all capability references at that
location are cleared after `storeObject`. This ensures no stale CNode references
remain when an object changes type from CNode to a different type. -/
theorem storeObject_nonCNode_clears_refs
    (st st' : SystemState)
    (id : SeLe4n.ObjId)
    (obj : KernelObject)
    (hStep : storeObject id obj st = .ok ((), st'))
    (hNotCNode : ∀ cn, obj ≠ .cnode cn)
    (ref : SlotRef)
    (hRef : ref.cnode = id) :
    st'.lifecycle.capabilityRefs ref = none := by
  rcases storeObject_metadata_sync_correct st st' id obj hStep with ⟨_, hCap, _⟩
  rw [hCap ref hRef]
  cases obj with
  | tcb _ => rfl
  | endpoint _ => rfl
  | notification _ => rfl
  | cnode cn => exact absurd rfl (hNotCNode cn)
  | vspaceRoot _ => rfl

-- ============================================================================
-- L-06 (WS-E3): Default SystemState satisfies lifecycle metadata consistency
-- ============================================================================

/-- L-06 (WS-E3): The default `SystemState` satisfies `lifecycleMetadataConsistent`.

This closes the base case of inductive invariant proofs: the initial system state
trivially satisfies metadata consistency because both the object store and
lifecycle metadata return `none` for every ID and slot reference. -/
theorem default_satisfies_lifecycleMetadataConsistent :
    SystemState.lifecycleMetadataConsistent (default : SystemState) := by
  refine ⟨fun oid => ?_, fun ref => ?_⟩
  · -- objectTypeMetadataConsistent: both sides reduce to none for default state
    simp [SystemState.lookupObjectTypeMeta]
    rfl
  · -- capabilityRefMetadataConsistent: both sides reduce to none for default state
    simp [SystemState.lookupCapabilityRefMeta, SystemState.lookupSlotCap, SystemState.lookupCNode]
    rfl

/-- L-06 corollary: The default `SystemState` satisfies the full
`lifecycleInvariantBundle`. -/
theorem default_satisfies_lifecycleInvariantBundle :
    lifecycleInvariantBundle (default : SystemState) :=
  lifecycleInvariantBundle_of_metadata_consistent default default_satisfies_lifecycleMetadataConsistent

end SeLe4n.Kernel
