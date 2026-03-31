/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

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
object-type aliases.

WS-F6/D1c: Reclassified as a structural lemma derivable from `lifecycleIdentityTypeExact`
(see `lifecycleIdentityNoTypeAliasConflict_of_exact`). This is a tautology: the same
deterministic lookup cannot return two different values. Retained for backward compatibility
with the `lifecycleIdentityAliasingInvariant` bundle and downstream proof surfaces. -/
def lifecycleIdentityNoTypeAliasConflict (st : SystemState) : Prop :=
  ∀ oid ty₁ ty₂,
    SystemState.lookupObjectTypeMeta st oid = some ty₁ →
    SystemState.lookupObjectTypeMeta st oid = some ty₂ →
    ty₁ = ty₂

/-- Identity/aliasing bundle used by lifecycle proofs before capability-reference composition.

WS-F6/D1c note: `lifecycleIdentityNoTypeAliasConflict` is derivable from
`lifecycleIdentityTypeExact` via `lifecycleIdentityNoTypeAliasConflict_of_exact`.
Both are retained in the bundle for backward compatibility, but auditors should note
that the second conjunct adds no independent assurance beyond the first. -/
def lifecycleIdentityAliasingInvariant (st : SystemState) : Prop :=
  lifecycleIdentityTypeExact st ∧ lifecycleIdentityNoTypeAliasConflict st

/-- M4-A step-3 capability-reference invariant: lifecycle slot-reference metadata exactly tracks
concrete capability-slot targets. -/
def lifecycleCapabilityRefExact (st : SystemState) : Prop :=
  SystemState.capabilityRefMetadataConsistent st

/-- M4-A step-3 capability-reference invariant: every metadata object-target reference is backed by
an actual slot capability carrying that same object target.

**W6-K (H-3 downgraded to LOW): Enforcement chain for metadata backing.**
This invariant is maintained by contract discipline, not automatic enforcement:
1. `lifecyclePreRetypeCleanup` orchestrates three cleanup steps —
   `cleanupTcbReferences`, `cleanupEndpointServiceRegistrations`, and
   `detachCNodeSlots` — clearing all scheduler/service/CDT references for the
   target object before any retype occurs.
2. `lifecycleRetypeObject` only creates new metadata after cleanup completes.
3. All retype paths go through `lifecycleRetypeDirectWithCleanup` which
   calls cleanup before retyping — there is no path that bypasses cleanup.
4. The `lifecycleRetypeObject_preserves_lifecycleInvariantBundle` theorem
   proves retype preserves the full invariant bundle (including this predicate),
   and the cleanup-before-retype ordering ensures no stale references remain.
The alternative (automatic enforcement via a runtime check before every metadata
write) was considered and rejected: it would add O(n) overhead per operation
with no additional safety, since the proof chain already guarantees correctness. -/
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
    st.objects[oid]? = some obj →
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
  cases hObj : st.objects[oid]? with
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
    (hObjInv : st.objects.invExt)
    (hObjTypesInv : st.lifecycle.objectTypes.invExt)
    (hStep : lifecycleRetypeObject authority target newObj st = .ok ((), st')) :
    lifecycleInvariantBundle st' := by
  rcases lifecycleRetypeObject_ok_as_storeObject st st' authority target newObj hStep with
    ⟨_, _, _, _, _, _, hStore⟩
  have hMeta : SystemState.lifecycleMetadataConsistent st :=
    lifecycleMetadataConsistent_of_lifecycleInvariantBundle st hInv
  have hMeta' : SystemState.lifecycleMetadataConsistent st' :=
    storeObject_preserves_lifecycleMetadataConsistent st st' target newObj hMeta hObjInv hObjTypesInv hStore
  exact lifecycleInvariantBundle_of_metadata_consistent st' hMeta'

theorem lifecycleRetypeObject_preserves_lifecycleStaleReferenceExclusionInvariant
    (st st' : SystemState)
    (authority : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj : KernelObject)
    (hInv : lifecycleInvariantBundle st)
    (hObjInv : st.objects.invExt)
    (hObjTypesInv : st.lifecycle.objectTypes.invExt)
    (hStep : lifecycleRetypeObject authority target newObj st = .ok ((), st')) :
    lifecycleStaleReferenceExclusionInvariant st' := by
  have hBundle' : lifecycleInvariantBundle st' :=
    lifecycleRetypeObject_preserves_lifecycleInvariantBundle st st' authority target newObj hInv hObjInv hObjTypesInv hStep
  exact lifecycleStaleReferenceExclusionInvariant_of_lifecycleInvariantBundle st' hBundle'

theorem lifecycleRetypeObject_preserves_lifecycleIdentityStaleReferenceInvariant
    (st st' : SystemState)
    (authority : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj : KernelObject)
    (hInv : lifecycleInvariantBundle st)
    (hObjInv : st.objects.invExt)
    (hObjTypesInv : st.lifecycle.objectTypes.invExt)
    (hStep : lifecycleRetypeObject authority target newObj st = .ok ((), st')) :
    lifecycleIdentityStaleReferenceInvariant st' := by
  have hBundle' : lifecycleInvariantBundle st' :=
    lifecycleRetypeObject_preserves_lifecycleInvariantBundle st st' authority target newObj hInv hObjInv hObjTypesInv hStep
  exact lifecycleIdentityStaleReferenceInvariant_of_lifecycleInvariantBundle st' hBundle'

-- ============================================================================
-- WS-F2: Untyped Memory Model Invariants
-- ============================================================================

/-- WS-F2: Untyped watermark invariant — for every untyped object in the store,
its watermark does not exceed its region size. -/
def untypedWatermarkInvariant (st : SystemState) : Prop :=
  ∀ (oid : SeLe4n.ObjId) (ut : UntypedObject),
    st.objects[oid]? = some (KernelObject.untyped ut) →
    ut.watermarkValid

/-- WS-F2: Untyped children-within-watermark invariant — all child allocations
fit within the watermark (and thus within the region). -/
def untypedChildrenBoundsInvariant (st : SystemState) : Prop :=
  ∀ (oid : SeLe4n.ObjId) (ut : UntypedObject),
    st.objects[oid]? = some (KernelObject.untyped ut) →
    ut.childrenWithinWatermark

/-- WS-F2: Untyped children non-overlap invariant — no two child allocations
within the same untyped region overlap in their address ranges. -/
def untypedChildrenNonOverlapInvariant (st : SystemState) : Prop :=
  ∀ (oid : SeLe4n.ObjId) (ut : UntypedObject),
    st.objects[oid]? = some (KernelObject.untyped ut) →
    ut.childrenNonOverlap

/-- WS-F2: Untyped children unique-id invariant — children within each untyped
have distinct object identities. -/
def untypedChildrenUniqueIdsInvariant (st : SystemState) : Prop :=
  ∀ (oid : SeLe4n.ObjId) (ut : UntypedObject),
    st.objects[oid]? = some (KernelObject.untyped ut) →
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
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (intro oid ut hObj; have h : (default : SystemState).objects[oid]? = none := RHTable_get?_empty 16 (by omega); rw [h] at hObj; exact absurd hObj (by simp))

/-- WS-F2: `storeObject` at a non-untyped slot preserves watermark invariant
for all existing untyped objects at other ObjIds. -/
theorem storeObject_preserves_untypedWatermarkInvariant_ne
    (st st' : SystemState)
    (oid : SeLe4n.ObjId)
    (obj : KernelObject)
    (hInv : untypedWatermarkInvariant st)
    (hObjInv : st.objects.invExt)
    (hStep : storeObject oid obj st = .ok ((), st'))
    (uid : SeLe4n.ObjId)
    (hNe : uid ≠ oid)
    (ut : UntypedObject)
    (hUt : st'.objects[uid]? = some (.untyped ut)) :
    ut.watermarkValid := by
  have hPrev : st'.objects[uid]? = st.objects[uid]? :=
    storeObject_objects_ne st st' oid uid obj hNe hObjInv hStep
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
    (hObjInv : st.objects.invExt)
    (hObjTypesInv : st.lifecycle.objectTypes.invExt)
    (hStep : retypeFromUntyped authority untypedId childId newObj allocSize st = .ok ((), st')) :
    SystemState.lifecycleMetadataConsistent st' := by
  rcases retypeFromUntyped_ok_decompose st st' authority untypedId childId newObj allocSize hStep with
    ⟨_ut, ut', _cap, stLookup, stUt, _offset, _hObj, _hNotDev, _hAllocSz,
     hLookup, _hAuth, _hAlloc, hStoreUt, hStoreChild⟩
  have hLookupSt : stLookup = st :=
    cspaceLookupSlot_ok_state_eq st authority _ stLookup hLookup
  rw [hLookupSt] at hStoreUt
  have hObjInvUt := storeObject_preserves_objects_invExt st stUt untypedId (.untyped ut') hObjInv hStoreUt
  have hObjTypesInvUt : stUt.lifecycle.objectTypes.invExt := by
    have hStoreUt' := hStoreUt
    unfold storeObject at hStoreUt'; cases hStoreUt'
    exact RHTable_insert_preserves_invExt st.lifecycle.objectTypes _ _ hObjTypesInv
  have hMetaUt : SystemState.lifecycleMetadataConsistent stUt :=
    storeObject_preserves_lifecycleMetadataConsistent st stUt untypedId (.untyped ut') hMeta hObjInv hObjTypesInv hStoreUt
  exact storeObject_preserves_lifecycleMetadataConsistent stUt st' childId newObj hMetaUt hObjInvUt hObjTypesInvUt hStoreChild

/-- WS-F2: `retypeFromUntyped` preserves the full lifecycle invariant bundle. -/
theorem retypeFromUntyped_preserves_lifecycleInvariantBundle
    (st st' : SystemState)
    (authority : CSpaceAddr)
    (untypedId childId : SeLe4n.ObjId)
    (newObj : KernelObject)
    (allocSize : Nat)
    (hInv : lifecycleInvariantBundle st)
    (hObjInv : st.objects.invExt)
    (hObjTypesInv : st.lifecycle.objectTypes.invExt)
    (hStep : retypeFromUntyped authority untypedId childId newObj allocSize st = .ok ((), st')) :
    lifecycleInvariantBundle st' := by
  have hMeta : SystemState.lifecycleMetadataConsistent st :=
    lifecycleMetadataConsistent_of_lifecycleInvariantBundle st hInv
  have hMeta' : SystemState.lifecycleMetadataConsistent st' :=
    retypeFromUntyped_preserves_lifecycleMetadataConsistent
      st st' authority untypedId childId newObj allocSize hMeta hObjInv hObjTypesInv hStep
  exact lifecycleInvariantBundle_of_metadata_consistent st' hMeta'

/-- WS-F2: `retypeFromUntyped` preserves the untyped memory invariant.
The source untyped's allocate operation preserves watermark validity,
children-within-watermark, non-overlap, and unique IDs (given freshness of
childId). Non-target untypeds are unchanged through both storeObject calls.
If `newObj` is itself an untyped, it must be well-formed. -/
theorem retypeFromUntyped_preserves_untypedMemoryInvariant
    (st st' : SystemState)
    (authority : CSpaceAddr)
    (untypedId childId : SeLe4n.ObjId)
    (newObj : KernelObject)
    (allocSize : Nat)
    (hInv : untypedMemoryInvariant st)
    (_hNe : childId ≠ untypedId)
    (hNewObjWF : ∀ ut_new, newObj = .untyped ut_new → ut_new.wellFormed)
    (hFresh : ∀ ut, st.objects[untypedId]? = some (.untyped ut) →
        ∀ c ∈ ut.children, c.objId ≠ childId)
    (hObjInv : st.objects.invExt)
    (hStep : retypeFromUntyped authority untypedId childId newObj allocSize st = .ok ((), st')) :
    untypedMemoryInvariant st' := by
  rcases hInv with ⟨hWM, hCB, hNO, hUI⟩
  rcases retypeFromUntyped_ok_decompose st st' authority untypedId childId newObj allocSize hStep with
    ⟨ut, ut', _cap, stLookup, stUt, offset, hObj, _hNotDev, _hAllocSz,
     hLookup, _hAuth, hAlloc, hStoreUt, hStoreChild⟩
  have hLookupSt : stLookup = st :=
    cspaceLookupSlot_ok_state_eq st authority _ stLookup hLookup
  rw [hLookupSt] at hStoreUt
  have hObjInvUt := storeObject_preserves_objects_invExt st stUt untypedId (.untyped ut') hObjInv hStoreUt
  -- Source untyped properties for ut
  have hUtWM : ut.watermarkValid := hWM untypedId ut hObj
  have hUtCB : ut.childrenWithinWatermark := hCB untypedId ut hObj
  have hUtNO : ut.childrenNonOverlap := hNO untypedId ut hObj
  have hUtUI : ut.childrenUniqueIds := hUI untypedId ut hObj
  -- After allocate, ut' is well-formed
  have hUt'WM := UntypedObject.allocate_preserves_watermarkValid ut ut' childId allocSize offset hUtWM hAlloc
  have hUt'CB := UntypedObject.allocate_preserves_childrenWithinWatermark ut ut' childId allocSize offset hUtCB hAlloc
  have hUt'NO := UntypedObject.allocate_preserves_childrenNonOverlap ut ut' childId allocSize offset hUtNO hUtCB hAlloc
  have hUt'UI := UntypedObject.allocate_preserves_childrenUniqueIds ut ut' childId allocSize offset hUtUI (hFresh ut hObj) hAlloc
  -- Helper: resolve post-state object at any oid through the two storeObject calls
  have resolve : ∀ oid utPost,
      st'.objects[oid]? = some (.untyped utPost) →
      (oid = childId ∧ newObj = .untyped utPost) ∨
      (oid ≠ childId ∧ oid = untypedId ∧ ut' = utPost) ∨
      (oid ≠ childId ∧ oid ≠ untypedId ∧ st.objects[oid]? = some (.untyped utPost)) := by
    intro oid utPost hObjPost
    by_cases hEqChild : oid = childId
    · left; constructor; exact hEqChild
      rw [hEqChild] at hObjPost
      have := storeObject_objects_eq stUt st' childId newObj hObjInvUt hStoreChild
      rw [this] at hObjPost; cases hObjPost; rfl
    · right
      rw [storeObject_objects_ne stUt st' childId oid newObj hEqChild hObjInvUt hStoreChild] at hObjPost
      by_cases hEqUt : oid = untypedId
      · left; refine ⟨hEqChild, hEqUt, ?_⟩
        rw [hEqUt] at hObjPost
        have := storeObject_objects_eq st stUt untypedId (.untyped ut') hObjInv hStoreUt
        rw [this] at hObjPost; cases hObjPost; rfl
      · right; exact ⟨hEqChild, hEqUt,
          (storeObject_objects_ne st stUt untypedId oid (.untyped ut') hEqUt hObjInv hStoreUt) ▸ hObjPost⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- untypedWatermarkInvariant
    intro oid utPost hObjPost
    rcases resolve oid utPost hObjPost with ⟨_, hNewEq⟩ | ⟨_, _, hUtEq⟩ | ⟨_, _, hPre⟩
    · exact (hNewObjWF utPost hNewEq).1
    · exact hUtEq ▸ hUt'WM
    · exact hWM oid utPost hPre
  · -- untypedChildrenBoundsInvariant
    intro oid utPost hObjPost
    rcases resolve oid utPost hObjPost with ⟨_, hNewEq⟩ | ⟨_, _, hUtEq⟩ | ⟨_, _, hPre⟩
    · exact (hNewObjWF utPost hNewEq).2.1
    · exact hUtEq ▸ hUt'CB
    · exact hCB oid utPost hPre
  · -- untypedChildrenNonOverlapInvariant
    intro oid utPost hObjPost
    rcases resolve oid utPost hObjPost with ⟨_, hNewEq⟩ | ⟨_, _, hUtEq⟩ | ⟨_, _, hPre⟩
    · exact (hNewObjWF utPost hNewEq).2.2.1
    · exact hUtEq ▸ hUt'NO
    · exact hNO oid utPost hPre
  · -- untypedChildrenUniqueIdsInvariant
    intro oid utPost hObjPost
    rcases resolve oid utPost hObjPost with ⟨_, hNewEq⟩ | ⟨_, _, hUtEq⟩ | ⟨_, _, hPre⟩
    · exact (hNewObjWF utPost hNewEq).2.2.2
    · exact hUtEq ▸ hUt'UI
    · exact hUI oid utPost hPre

/-- WS-H2/B-5: If `retypeFromUntyped` succeeds, then `childId ≠ untypedId`.
The self-overwrite guard (H-06) returns `childIdSelfOverwrite` when
`childId = untypedId`, so success implies they are distinct. -/
theorem retypeFromUntyped_ok_childId_ne
    (st st' : SystemState)
    (authority : CSpaceAddr)
    (untypedId childId : SeLe4n.ObjId)
    (newObj : KernelObject)
    (allocSize : Nat)
    (hStep : retypeFromUntyped authority untypedId childId newObj allocSize st = .ok ((), st')) :
    childId ≠ untypedId := by
  intro h
  unfold retypeFromUntyped at hStep
  cases hObj : st.objects[untypedId]? with
  | none => simp [hObj] at hStep
  | some obj =>
      cases obj with
      | tcb _ | endpoint _ | notification _ | cnode _ | vspaceRoot _ | schedContext _ =>
          simp [hObj] at hStep
      | untyped _ =>
          simp only [hObj] at hStep
          -- S4-B: discharge capacity check
          by_cases hCap : st.objectIndex.length ≥ maxObjects
          · simp [hCap] at hStep
          · simp only [hCap, ↓reduceIte] at hStep
            -- Self-overwrite guard fires: childId = untypedId → .error
            simp [h] at hStep

/-- WS-H2/B-5: If `retypeFromUntyped` succeeds, the childId is fresh among
the source untyped's existing children. The A-27 collision guard returns
`childIdCollision` when any existing child shares the childId, so success
implies freshness. This eliminates the manual `hFresh` proof obligation. -/
theorem retypeFromUntyped_ok_childId_fresh
    (st st' : SystemState)
    (authority : CSpaceAddr)
    (untypedId childId : SeLe4n.ObjId)
    (newObj : KernelObject)
    (allocSize : Nat)
    (hStep : retypeFromUntyped authority untypedId childId newObj allocSize st = .ok ((), st')) :
    ∀ ut, st.objects[untypedId]? = some (.untyped ut) →
      ∀ c ∈ ut.children, c.objId ≠ childId := by
  intro ut hObj c hMem hEq
  have hNe : childId ≠ untypedId :=
    retypeFromUntyped_ok_childId_ne st st' authority untypedId childId newObj allocSize hStep
  have hStep' := hStep
  unfold retypeFromUntyped at hStep'
  simp only [hObj] at hStep'
  -- S4-B: discharge capacity check
  have hCapF : ¬(st.objectIndex.length ≥ maxObjects) := by
    by_cases hCap : st.objectIndex.length ≥ maxObjects
    · simp [hCap] at hStep'
    · exact hCap
  simp only [hCapF, ↓reduceIte] at hStep'
  have hCollF : st.objects[childId]?.isSome = false := by
    cases h : st.objects[childId]?.isSome
    · rfl
    · simp only [hNe, ↓reduceIte, h, ↓reduceIte] at hStep'
      simp at hStep'
  have hFrF : (ut.children.any fun c => c.objId == childId) = false := by
    cases h : ut.children.any (fun c => c.objId == childId)
    · rfl
    · simp only [hNe, ↓reduceIte, hCollF, ↓reduceIte, h, ↓reduceIte] at hStep'
      simp at hStep'
  have hAny : (ut.children.any fun c' => c'.objId == childId) = true :=
    List.any_eq_true.mpr ⟨c, hMem, by simp [hEq]⟩
  rw [hAny] at hFrF
  simp at hFrF

/-- WS-H2/B-5: Auto-derivation variant of
`retypeFromUntyped_preserves_untypedMemoryInvariant` that eliminates the
manual `hNe` and `hFresh` proof obligations. Both conditions are derived
from the success of `retypeFromUntyped` via the H-06 self-overwrite guard
and A-27 child-collision guard respectively. Callers need only supply the
invariant precondition, the new-object well-formedness hypothesis, and the
success hypothesis. -/
theorem retypeFromUntyped_preserves_untypedMemoryInvariant_auto
    (st st' : SystemState)
    (authority : CSpaceAddr)
    (untypedId childId : SeLe4n.ObjId)
    (newObj : KernelObject)
    (allocSize : Nat)
    (hInv : untypedMemoryInvariant st)
    (hNewObjWF : ∀ ut_new, newObj = .untyped ut_new → ut_new.wellFormed)
    (hObjInv : st.objects.invExt)
    (hStep : retypeFromUntyped authority untypedId childId newObj allocSize st = .ok ((), st')) :
    untypedMemoryInvariant st' :=
  retypeFromUntyped_preserves_untypedMemoryInvariant
    st st' authority untypedId childId newObj allocSize hInv
    (retypeFromUntyped_ok_childId_ne st st' authority untypedId childId newObj allocSize hStep)
    hNewObjWF
    (retypeFromUntyped_ok_childId_fresh st st' authority untypedId childId newObj allocSize hStep)
    hObjInv
    hStep

-- ============================================================================
-- S6-D: Memory scrubbing preserves lifecycle invariants
-- ============================================================================

/-- S6-D: `scrubObjectMemory` preserves the lifecycle invariant bundle.

    Memory scrubbing only modifies `machine.memory` — it does not touch the
    object store, lifecycle metadata, capabilities, or slots. All lifecycle
    invariants (`lifecycleIdentityTypeExact`, `lifecycleCapabilityRefExact`,
    etc.) operate on `objects` and `lifecycle` fields, so they are trivially
    preserved. -/
theorem scrubObjectMemory_preserves_lifecycleInvariantBundle
    (st : SystemState) (objectId : SeLe4n.ObjId) (objType : KernelObjectType)
    (hInv : lifecycleInvariantBundle st) :
    lifecycleInvariantBundle (scrubObjectMemory st objectId objType) := by
  -- scrubObjectMemory only changes machine.memory; all fields that lifecycle
  -- invariants reference (objects, lifecycle, cdt) are definitionally equal
  have : (scrubObjectMemory st objectId objType).objects = st.objects :=
    scrubObjectMemory_objects_eq st objectId objType
  have : (scrubObjectMemory st objectId objType).lifecycle = st.lifecycle :=
    scrubObjectMemory_lifecycle_eq st objectId objType
  -- The invariant bundle only mentions objects/lifecycle/cdt fields which are
  -- unchanged by scrubObjectMemory. The scrubbed state's objects/lifecycle/cdt
  -- are definitionally equal to the original, so the invariant transfers directly.
  exact hInv

/-- S6-D: `scrubObjectMemory` preserves the stale-reference exclusion invariant. -/
theorem scrubObjectMemory_preserves_lifecycleStaleReferenceExclusionInvariant
    (st : SystemState) (objectId : SeLe4n.ObjId) (objType : KernelObjectType)
    (hInv : lifecycleStaleReferenceExclusionInvariant st) :
    lifecycleStaleReferenceExclusionInvariant (scrubObjectMemory st objectId objType) :=
  hInv

/-- S6-D: `scrubObjectMemory` preserves the full identity + stale-reference bundle. -/
theorem scrubObjectMemory_preserves_lifecycleIdentityStaleReferenceInvariant
    (st : SystemState) (objectId : SeLe4n.ObjId) (objType : KernelObjectType)
    (hInv : lifecycleIdentityStaleReferenceInvariant st) :
    lifecycleIdentityStaleReferenceInvariant (scrubObjectMemory st objectId objType) :=
  hInv

end SeLe4n.Kernel
