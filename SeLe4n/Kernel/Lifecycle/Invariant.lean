-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Lifecycle.Operations
import SeLe4n.Kernel.Lifecycle.Invariant.SuspendPreservation

/-!
# Lifecycle Invariant Preservation Proofs

This module contains invariant definitions and preservation theorems for the
lifecycle (object retype) subsystem: the identity/aliasing invariant over the
object-type metadata, the untyped-memory invariants, and their preservation
through retype and scrub.

## Proof scope qualification (F-16)

**Substantive preservation theorems** (high assurance — prove invariant preservation
over *changed* state after a *successful* operation):
- `retypeFromUntyped_preserves_lifecycleInvariantBundle`
- `retypeFromUntyped_preserves_untypedMemoryInvariant`

## `v0.35.78`: the capability-reference family is retired

Until `v0.35.78` this module carried a second layer — `lifecycleCapabilityRefExact`,
`lifecycleCapabilityRefObjectTargetBacked`, `lifecycleCapabilityRefReplyCapBacked`,
`lifecycleCapabilityRefObjectTargetTypeAligned`,
`lifecycleCapabilityRefNoTypeAliasConflict`, and the bundles
`lifecycleCapabilityReferenceInvariant`, `lifecycleStaleReferenceExclusionInvariant`
and `lifecycleIdentityStaleReferenceInvariant` built over them — every one stated
through `SystemState.lookupCapabilityRefMeta`, the "lifecycle metadata view" of a
capability slot's target.  That reader was *defined* as
`(lookupSlotCap st ref).map Capability.target`, a read of the object store, so
each predicate in the layer was a tautology (exactness: `x = x`; backing: a slot
that resolves resolves; type alignment and alias-freedom: instances of
`objectTypeMetadataConsistent` and of the determinism of a lookup) and every
theorem *about* the layer consumed no hypothesis.  The table the reader was named
for (`LifecycleMetadata.capabilityRefs`) is retired with it — see
`Model/State.lean` — and the one substantive fact the layer had restated,
reply-cap backing, is owned where it always was: the capability layer's
step-preserved `replyCapPointsToValidReply`.  The lifecycle bundle is therefore
its identity/aliasing layer, and a conjunct added to it is one this module can
preserve rather than one it can only restate.

All theorems in this module are substantive: they prove invariant preservation
over state modified by successful retype operations. There are no error-case
preservation theorems in this module.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- M4-A step-3 identity invariant: lifecycle object-type metadata exactly tracks
object-store identity typing for each object id. -/
def lifecycleIdentityTypeExact (st : SystemState) : Prop :=
  SystemState.objectTypeMetadataConsistent st

/-- Identity/aliasing bundle used by lifecycle proofs before capability-reference composition.

AN4-B (H-03): the previous formulation conjoined
`lifecycleIdentityNoTypeAliasConflict` (a tautology derivable from
`lifecycleIdentityTypeExact` — the same deterministic lookup cannot return
two different values). The redundant predicate has been removed; the bundle
is now a bare alias for `lifecycleIdentityTypeExact`. Legacy destructures
should project `hIdAlias` directly as the identity witness. -/
abbrev lifecycleIdentityAliasingInvariant (st : SystemState) : Prop :=
  lifecycleIdentityTypeExact st

/-- Full lifecycle invariant bundle for M4-A step-3.  Since `v0.35.78` it is the
identity/aliasing layer alone — the capability-reference layer it was conjoined
with was a family of tautologies (see the module docstring) — and it keeps its
name as the lifecycle subsystem's bundle: `proofLayerInvariantBundle` and
`serviceLifecycleCapabilityInvariantBundle` name it, and a conjunct the
subsystem earns joins it here. -/
def lifecycleInvariantBundle (st : SystemState) : Prop :=
  lifecycleIdentityAliasingInvariant st

-- AN4-B (H-03): `lifecycleIdentityNoTypeAliasConflict_of_exact` was the
-- implication witness bridging `lifecycleIdentityTypeExact` to the deleted
-- `lifecycleIdentityNoTypeAliasConflict` predicate. Because the redundant
-- predicate has been removed, the implication's target has disappeared and the
-- theorem is no longer needed. Proof-chain consumers now reason directly from
-- `lifecycleIdentityTypeExact`.

-- ============================================================================
-- WS-F2 / WS-ZA ZA5.4 part 13: Untyped Memory Model Invariants
-- ============================================================================

/-- WS-ZA ZA5.4 part 13: **free-index invariant** — every capability naming an
untyped holds a free index within the untyped's region.  The index is the
capability's (`Capability.freeIndex`, seL4's `capFreeIndex`), so the invariant
is stated over the slots that hold capabilities (`SystemState.slotCapAt`), as
seL4's `untyped_inc` is. -/
def untypedFreeIndexInvariant (st : SystemState) : Prop :=
  ∀ (r : SlotRef) (cap : Capability) (oid : SeLe4n.ObjId) (ut : UntypedObject),
    st.slotCapAt r = some cap → cap.target = .object oid →
    st.objects[oid]? = some (KernelObject.untyped ut) →
    ut.freeIndexValid cap.freeIndex

/-- WS-F2 / WS-ZA ZA5.4 part 13: **children-bounds invariant** — every child
carved from an untyped lies below the free index of every capability naming
it, so a carve at a capability's index lands on memory nothing carved holds. -/
def untypedChildrenBoundsInvariant (st : SystemState) : Prop :=
  ∀ (r : SlotRef) (cap : Capability) (oid : SeLe4n.ObjId) (ut : UntypedObject),
    st.slotCapAt r = some cap → cap.target = .object oid →
    st.objects[oid]? = some (KernelObject.untyped ut) →
    ut.childrenBelow cap.freeIndex

/-- WS-ZA ZA5.4 part 13: **sole-carver invariant** — of two slots naming one
untyped, one holds a full capability (its index at the region's end), so at most
one capability can carve from an untyped.  It is what a derivation keeps by
setting its untyped source full (seL4's `setUntypedCapAsFull`), and what makes
a carve through one capability unable to overlap a carve through another. -/
def untypedSoleCarverInvariant (st : SystemState) : Prop :=
  ∀ (r₁ r₂ : SlotRef) (cap₁ cap₂ : Capability) (oid : SeLe4n.ObjId) (ut : UntypedObject),
    r₁ ≠ r₂ → st.slotCapAt r₁ = some cap₁ → st.slotCapAt r₂ = some cap₂ →
    cap₁.target = .object oid → cap₂.target = .object oid →
    st.objects[oid]? = some (KernelObject.untyped ut) →
    cap₁.freeIndex = ut.regionSize ∨ cap₂.freeIndex = ut.regionSize

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
  untypedFreeIndexInvariant st ∧
  untypedChildrenBoundsInvariant st ∧
  untypedSoleCarverInvariant st ∧
  untypedChildrenNonOverlapInvariant st ∧
  untypedChildrenUniqueIdsInvariant st

/-- WS-F2: The default (empty) state satisfies the untyped memory invariant
because no untyped objects exist. -/
theorem default_systemState_untypedMemoryInvariant :
    untypedMemoryInvariant (default : SystemState) := by
  have hNone : ∀ oid : SeLe4n.ObjId, (default : SystemState).objects[oid]? = none :=
    fun _ => RHTable_get?_empty 16 (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro _ _ oid _ _ _ hObj; rw [hNone] at hObj; cases hObj
  · intro _ _ oid _ _ _ hObj; rw [hNone] at hObj; cases hObj
  · intro _ _ _ _ oid _ _ _ _ _ _ hObj; rw [hNone] at hObj; cases hObj
  · intro oid _ hObj; rw [hNone] at hObj; cases hObj
  · intro oid _ hObj; rw [hNone] at hObj; cases hObj

/-- A successful `cspaceLookupSlot` is a slot lookup that found the capability. -/
theorem cspaceLookupSlot_ok_lookupSlotCap {st st' : SystemState} {addr : CSpaceAddr}
    {cap : Capability} (h : cspaceLookupSlot addr st = .ok (cap, st')) :
    SystemState.lookupSlotCap st addr = some cap := by
  unfold cspaceLookupSlot at h
  cases hq : SystemState.lookupSlotCap st addr with
  | none => rw [hq] at h; exfalso; revert h; dsimp only; split <;> simp
  | some c =>
    rw [hq] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    rw [h.1]

/-- A free-index write preserves the object-type metadata. -/
theorem setCapFreeIndex_preserves_objectTypeMetadataConsistent {st : SystemState}
    {addr : CSpaceAddr} {idx : Nat} (h : SystemState.objectTypeMetadataConsistent st)
    (hInv : st.objects.invExt) (hT : st.lifecycle.objectTypes.invExt) :
    SystemState.objectTypeMetadataConsistent (setCapFreeIndex st addr idx) := by
  cases hO : st.objects[addr.cnode]? with
  | some o =>
    cases o with
    | cnode cn =>
      exact storeObject_preserves_objectTypeMetadataConsistent _ _ _ _ h hInv hT
        (setCapFreeIndex_eq_storeObject hO)
    | _ => unfold setCapFreeIndex SystemState.storeCNodeWith; rw [hO]; exact h
  | none => unfold setCapFreeIndex SystemState.storeCNodeWith; rw [hO]; exact h

/-- A store keeps the object-type table's invariant. -/
theorem storeObject_preserves_objectTypes_invExt {st st' : SystemState} {id : SeLe4n.ObjId}
    {obj : KernelObject} (hT : st.lifecycle.objectTypes.invExt)
    (h : storeObject id obj st = .ok ((), st')) : st'.lifecycle.objectTypes.invExt := by
  unfold storeObject at h; cases h
  exact RHTable_insert_preserves_invExt st.lifecycle.objectTypes _ _ hT

/-- WS-F2: `retypeFromUntyped` preserves lifecycle metadata consistency.
Both `storeObject` calls and the free-index write maintain metadata. -/
theorem retypeFromUntyped_preserves_objectTypeMetadataConsistent
    (st st' : SystemState)
    (authority : CSpaceAddr)
    (untypedId childId : SeLe4n.ObjId)
    (newObj : KernelObject)
    (allocSize : Nat)
    (hMeta : SystemState.objectTypeMetadataConsistent st)
    (hObjInv : st.objects.invExt)
    (hObjTypesInv : st.lifecycle.objectTypes.invExt)
    (hStep : retypeFromUntyped authority untypedId childId newObj allocSize st = .ok ((), st')) :
    SystemState.objectTypeMetadataConsistent st' := by
  rcases retypeFromUntyped_ok_decompose st st' authority untypedId childId newObj allocSize hStep with
    ⟨_ut, ut', _cap, stLookup, stUt, _offset, stCh, _hObj, _hNotDev, _hAllocSz,
     hLookup, _hAuth, _hAlloc, hStoreUt, hStoreChild, rfl⟩
  have hLookupSt : stLookup = st :=
    cspaceLookupSlot_ok_state_eq st authority _ stLookup hLookup
  rw [hLookupSt] at hStoreUt
  have hObjInvUt := storeObject_preserves_objects_invExt st stUt untypedId (.untyped ut') hObjInv hStoreUt
  have hObjTypesInvUt := storeObject_preserves_objectTypes_invExt hObjTypesInv hStoreUt
  have hMetaUt : SystemState.objectTypeMetadataConsistent stUt :=
    storeObject_preserves_objectTypeMetadataConsistent st stUt untypedId (.untyped ut') hMeta hObjInv hObjTypesInv hStoreUt
  have hMetaCh := storeObject_preserves_objectTypeMetadataConsistent stUt stCh childId newObj
    hMetaUt hObjInvUt hObjTypesInvUt hStoreChild
  exact setCapFreeIndex_preserves_objectTypeMetadataConsistent hMetaCh
    (storeObject_preserves_objects_invExt _ _ _ _ hObjInvUt hStoreChild)
    (storeObject_preserves_objectTypes_invExt hObjTypesInvUt hStoreChild)

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
    lifecycleInvariantBundle st' :=
  retypeFromUntyped_preserves_objectTypeMetadataConsistent
    st st' authority untypedId childId newObj allocSize hInv hObjInv hObjTypesInv hStep

/-- WS-F2 / WS-ZA ZA5.4 part 13: `retypeFromUntyped` preserves the untyped
memory invariant.  The carve is at the authority capability's free index, below
which every child lies (`untypedChildrenBoundsInvariant`), so the new child
overlaps none; the authority's index is advanced past it; and every other
capability naming the untyped is full (`untypedSoleCarverInvariant`, since the
authority's index is below the region's end), so the new child lies below its
index too.  The new object holds no capability (`hNewSlots`) and no capability
names its id yet (`hChildUnnamed`), so it is named by no capability after the
carve; if it is itself an untyped, it must be well-formed. -/
theorem retypeFromUntyped_preserves_untypedMemoryInvariant
    (st st' : SystemState)
    (authority : CSpaceAddr)
    (untypedId childId : SeLe4n.ObjId)
    (newObj : KernelObject)
    (allocSize : Nat)
    (hInv : untypedMemoryInvariant st)
    (hNe : childId ≠ untypedId)
    (hNewObjWF : ∀ ut_new, newObj = .untyped ut_new → ut_new.wellFormed)
    (hNewSlots : ∀ s, newObj.slotCap s = none)
    (hChildUnnamed : ∀ r cap, st.slotCapAt r = some cap → cap.target ≠ .object childId)
    (hFresh : ∀ ut, st.objects[untypedId]? = some (.untyped ut) →
        ∀ c ∈ ut.children, c.objId ≠ childId)
    (hObjInv : st.objects.invExt)
    (hStep : retypeFromUntyped authority untypedId childId newObj allocSize st = .ok ((), st')) :
    untypedMemoryInvariant st' := by
  rcases hInv with ⟨hFI, hCB, hSC, hNO, hUI⟩
  have hFreshId := retypeFromUntyped_childId_fresh authority untypedId childId newObj allocSize
    st st' hStep
  rcases retypeFromUntyped_ok_decompose st st' authority untypedId childId newObj allocSize hStep with
    ⟨ut, ut', cap, stLookup, stUt, offset, stCh, hObj, _hNotDev, _hAllocSz,
     hLookup, hAuth, hAlloc, hStoreUt, hStoreChild, rfl⟩
  have hLookupSt : stLookup = st :=
    cspaceLookupSlot_ok_state_eq st authority _ stLookup hLookup
  rw [hLookupSt] at hStoreUt hLookup
  have hObjInvUt := storeObject_preserves_objects_invExt _ _ _ _ hObjInv hStoreUt
  have hObjInvCh := storeObject_preserves_objects_invExt _ _ _ _ hObjInvUt hStoreChild
  -- The authority slot and its capability.
  obtain ⟨cnA, hObjA, hLkA⟩ := SystemState.lookupSlotCap_cnode (cspaceLookupSlot_ok_lookupSlotCap hLookup)
  have hSlotA : st.slotCapAt authority = some cap := by
    rw [SystemState.slotCapAt_of_object hObjA]; exact hLkA
  have hTgt : cap.target = .object untypedId := by
    unfold lifecycleRetypeAuthority at hAuth
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hAuth
    exact hAuth.1
  have hCan := ((UntypedObject.allocate_some_iff ut cap.freeIndex childId allocSize _).mp hAlloc).1
  simp only [UntypedObject.canAllocate, Bool.and_eq_true, decide_eq_true_eq] at hCan
  have hIdxNe : cap.freeIndex ≠ ut.regionSize := by omega
  have hRegion := UntypedObject.allocate_preserves_region ut ut' cap.freeIndex childId allocSize
    offset hAlloc
  have hNeAU : authority.cnode ≠ untypedId := by
    intro h; rw [h, hObj] at hObjA; cases hObjA
  have hNeAC : authority.cnode ≠ childId := by
    intro h; rw [← h, hObjA] at hFreshId; cases hFreshId
  have hObjACh : stCh.objects[authority.cnode]? = some (.cnode cnA) := by
    rw [storeObject_objects_ne _ _ _ _ _ hNeAC hObjInvUt hStoreChild,
      storeObject_objects_ne _ _ _ _ _ hNeAU hObjInv hStoreUt, hObjA]
  -- Where an untyped of the post-state came from.
  have resolve : ∀ oid u,
      (setCapFreeIndex stCh authority (cap.freeIndex + allocSize)).objects[oid]? =
        some (.untyped u) →
      (oid = childId ∧ newObj = .untyped u) ∨ (oid = untypedId ∧ u = ut') ∨
      (oid ≠ childId ∧ oid ≠ untypedId ∧ st.objects[oid]? = some (.untyped u)) := by
    intro oid u hPost
    by_cases hA : oid = authority.cnode
    · rw [hA, setCapFreeIndex_objects_self hObjInvCh hObjACh] at hPost; cases hPost
    rw [setCapFreeIndex_objects_ne hObjInvCh hA] at hPost
    by_cases hC : oid = childId
    · left; rw [hC, storeObject_objects_eq _ _ _ _ hObjInvUt hStoreChild] at hPost
      cases hPost; exact ⟨hC, rfl⟩
    rw [storeObject_objects_ne _ _ _ _ _ hC hObjInvUt hStoreChild] at hPost
    by_cases hU : oid = untypedId
    · right; left; rw [hU, storeObject_objects_eq _ _ _ _ hObjInv hStoreUt] at hPost
      cases hPost; exact ⟨hU, rfl⟩
    right; right
    exact ⟨hC, hU, by rwa [storeObject_objects_ne _ _ _ _ _ hU hObjInv hStoreUt] at hPost⟩
  -- Where a capability of the post-state came from.
  have slots : ∀ r c,
      (setCapFreeIndex stCh authority (cap.freeIndex + allocSize)).slotCapAt r = some c →
      (r = authority ∧ c = cap.withFreeIndex (cap.freeIndex + allocSize)) ∨
      (r ≠ authority ∧ st.slotCapAt r = some c) := by
    intro r c hR
    by_cases hA : r.cnode = authority.cnode
    · have hO' := setCapFreeIndex_objects_self (idx := cap.freeIndex + allocSize) hObjInvCh hObjACh
      rw [← hA] at hO'
      rw [SystemState.slotCapAt_of_object hO'] at hR
      simp only [KernelObject.slotCap] at hR
      by_cases hS : r.slot = authority.slot
      · left
        have hr : r = authority := by
          rw [← SlotRef.mk_cnode_slot r, ← SlotRef.mk_cnode_slot authority, hA, hS]
        rw [hS, CNode.setFreeIndex_of_lookup hLkA,
          CNode.lookup_insert_eq _ _ _ (CNode.slotsUnique_holds _)
            (CNode.slotAddressable_of_lookup _ _ _ hLkA)] at hR
        cases hR; exact ⟨hr, rfl⟩
      · right
        rw [CNode.lookup_setFreeIndex_ne _ _ (Ne.symm hS)] at hR
        refine ⟨fun h => hS (h ▸ rfl), ?_⟩
        rw [SystemState.slotCapAt_of_object (hA ▸ hObjA)]; exact hR
    · right
      refine ⟨fun h => hA (h ▸ rfl), ?_⟩
      unfold SystemState.slotCapAt SystemState.getObject? at hR ⊢
      rw [setCapFreeIndex_objects_ne hObjInvCh hA] at hR
      by_cases hC : r.cnode = childId
      · rw [hC, storeObject_objects_eq _ _ _ _ hObjInvUt hStoreChild] at hR
        simp [hNewSlots] at hR
      rw [storeObject_objects_ne _ _ _ _ _ hC hObjInvUt hStoreChild] at hR
      by_cases hU : r.cnode = untypedId
      · rw [hU, storeObject_objects_eq _ _ _ _ hObjInv hStoreUt] at hR
        simp [KernelObject.slotCap] at hR
      rw [storeObject_objects_ne _ _ _ _ _ hU hObjInv hStoreUt] at hR
      exact hR
  -- The advanced capability names the untyped.
  have hTgtA : ∀ oid, (cap.withFreeIndex (cap.freeIndex + allocSize)).target = .object oid →
      oid = untypedId := by
    intro oid h; rw [Capability.withFreeIndex_target, hTgt] at h; cases h; rfl
  -- No capability of the post-state names the child.
  have hNotChild : ∀ r c, (setCapFreeIndex stCh authority (cap.freeIndex + allocSize)).slotCapAt r
      = some c → c.target ≠ .object childId := by
    intro r c hR hT
    rcases slots r c hR with ⟨_, rfl⟩ | ⟨_, hPre⟩
    · exact hNe (hTgtA _ hT)
    · exact hChildUnnamed r c hPre hT
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- untypedFreeIndexInvariant
    intro r c oid u hR hT hO
    rcases resolve oid u hO with ⟨hC, _⟩ | ⟨hU, hUe⟩ | ⟨_, hU, hPre⟩
    · exact absurd (hC ▸ hT) (hNotChild r c hR)
    · rw [hUe]; unfold UntypedObject.freeIndexValid; rw [hRegion.2]
      rcases slots r c hR with ⟨_, rfl⟩ | ⟨_, hPre'⟩
      · simp only [Capability.withFreeIndex_freeIndex]; exact hCan.2
      · exact hFI r c untypedId ut hPre' (hU ▸ hT) hObj
    · rcases slots r c hR with ⟨_, rfl⟩ | ⟨_, hPre'⟩
      · exact absurd (hTgtA _ hT) hU
      · exact hFI r c oid u hPre' hT hPre
  · -- untypedChildrenBoundsInvariant
    intro r c oid u hR hT hO
    rcases resolve oid u hO with ⟨hC, _⟩ | ⟨hU, hUe⟩ | ⟨_, hU, hPre⟩
    · exact absurd (hC ▸ hT) (hNotChild r c hR)
    · rw [hUe]
      rcases slots r c hR with ⟨_, rfl⟩ | ⟨hNeA, hPre'⟩
      · simp only [Capability.withFreeIndex_freeIndex]
        exact UntypedObject.allocate_preserves_childrenBelow ut ut' _ childId allocSize offset
          (hCB authority cap untypedId ut hSlotA hTgt hObj) hAlloc
      · have hT' : c.target = .object untypedId := hU ▸ hT
        have hFull : c.freeIndex = ut.regionSize := by
          rcases hSC authority r cap c untypedId ut (Ne.symm hNeA) hSlotA hPre' hTgt hT' hObj
            with h | h
          · exact absurd h hIdxNe
          · exact h
        exact UntypedObject.allocate_preserves_childrenBelow_full ut ut' _ childId allocSize offset
          c.freeIndex (hCB r c untypedId ut hPre' hT' hObj) (by omega) hAlloc
    · rcases slots r c hR with ⟨_, rfl⟩ | ⟨_, hPre'⟩
      · exact absurd (hTgtA _ hT) hU
      · exact hCB r c oid u hPre' hT hPre
  · -- untypedSoleCarverInvariant
    intro r₁ r₂ c₁ c₂ oid u hNe12 h1 h2 t1 t2 hO
    rcases resolve oid u hO with ⟨hC, _⟩ | ⟨hU, hUe⟩ | ⟨_, hU, hPre⟩
    · exact absurd (hC ▸ t1) (hNotChild r₁ c₁ h1)
    · rw [hUe, hRegion.2]
      have t1' : c₁.target = .object untypedId := hU ▸ t1
      have t2' : c₂.target = .object untypedId := hU ▸ t2
      rcases slots r₁ c₁ h1 with ⟨hr₁, rfl⟩ | ⟨hNe₁, hP₁⟩ <;>
        rcases slots r₂ c₂ h2 with ⟨hr₂, rfl⟩ | ⟨hNe₂, hP₂⟩
      · exact absurd (hr₁.trans hr₂.symm) hNe12
      · rcases hSC authority r₂ cap c₂ untypedId ut (Ne.symm hNe₂) hSlotA hP₂ hTgt t2' hObj
          with h | h
        · exact absurd h hIdxNe
        · exact Or.inr h
      · rcases hSC authority r₁ cap c₁ untypedId ut (Ne.symm hNe₁) hSlotA hP₁ hTgt t1' hObj
          with h | h
        · exact absurd h hIdxNe
        · exact Or.inl h
      · exact hSC r₁ r₂ c₁ c₂ untypedId ut hNe12 hP₁ hP₂ t1' t2' hObj
    · rcases slots r₁ c₁ h1 with ⟨_, rfl⟩ | ⟨_, hP₁⟩
      · exact absurd (hTgtA _ t1) hU
      rcases slots r₂ c₂ h2 with ⟨_, rfl⟩ | ⟨_, hP₂⟩
      · exact absurd (hTgtA _ t2) hU
      exact hSC r₁ r₂ c₁ c₂ oid u hNe12 hP₁ hP₂ t1 t2 hPre
  · -- untypedChildrenNonOverlapInvariant
    intro oid u hO
    rcases resolve oid u hO with ⟨_, hNewEq⟩ | ⟨_, hUe⟩ | ⟨_, _, hPre⟩
    · exact (hNewObjWF u hNewEq).2.1
    · rw [hUe]
      exact UntypedObject.allocate_preserves_childrenNonOverlap ut ut' _ childId allocSize offset
        (hNO untypedId ut hObj) (hCB authority cap untypedId ut hSlotA hTgt hObj) hAlloc
    · exact hNO oid u hPre
  · -- untypedChildrenUniqueIdsInvariant
    intro oid u hO
    rcases resolve oid u hO with ⟨_, hNewEq⟩ | ⟨_, hUe⟩ | ⟨_, _, hPre⟩
    · exact (hNewObjWF u hNewEq).2.2
    · rw [hUe]
      exact UntypedObject.allocate_preserves_childrenUniqueIds ut ut' _ childId allocSize offset
        (hUI untypedId ut hObj) (hFresh ut hObj) hAlloc
    · exact hUI oid u hPre

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
  unfold retypeFromUntyped SystemState.getObject? at hStep
  cases hObj : st.objects[untypedId]? with
  | none => simp [hObj] at hStep
  | some obj =>
      cases obj with
      | tcb _ | endpoint _ | notification _ | cnode _ | vspaceRoot _ | schedContext _ | reply _ | frame _ | pageTable _ =>
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
  unfold retypeFromUntyped SystemState.getObject? at hStep'
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
success hypothesis (and the two facts about the new object's capabilities). -/
theorem retypeFromUntyped_preserves_untypedMemoryInvariant_auto
    (st st' : SystemState)
    (authority : CSpaceAddr)
    (untypedId childId : SeLe4n.ObjId)
    (newObj : KernelObject)
    (allocSize : Nat)
    (hInv : untypedMemoryInvariant st)
    (hNewObjWF : ∀ ut_new, newObj = .untyped ut_new → ut_new.wellFormed)
    (hNewSlots : ∀ s, newObj.slotCap s = none)
    (hChildUnnamed : ∀ r cap, st.slotCapAt r = some cap → cap.target ≠ .object childId)
    (hObjInv : st.objects.invExt)
    (hStep : retypeFromUntyped authority untypedId childId newObj allocSize st = .ok ((), st')) :
    untypedMemoryInvariant st' :=
  retypeFromUntyped_preserves_untypedMemoryInvariant
    st st' authority untypedId childId newObj allocSize hInv
    (retypeFromUntyped_ok_childId_ne st st' authority untypedId childId newObj allocSize hStep)
    hNewObjWF hNewSlots hChildUnnamed
    (retypeFromUntyped_ok_childId_fresh st st' authority untypedId childId newObj allocSize hStep)
    hObjInv
    hStep

-- ============================================================================
-- S6-D: Memory scrubbing preserves lifecycle invariants
-- ============================================================================

end SeLe4n.Kernel
