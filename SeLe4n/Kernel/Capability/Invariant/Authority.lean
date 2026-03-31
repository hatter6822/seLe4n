/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Capability.Invariant.Defs

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- Core delete authority reduction (no CDT guard). -/
private theorem cspaceDeleteSlotCore_authority_reduction
    (st st' : SystemState)
    (addr : CSpaceAddr)
    (hSlotUniq : cspaceSlotUnique st)
    (hObjInv : st.objects.invExt)
    (hStep : cspaceDeleteSlotCore addr st = .ok ((), st')) :
    SystemState.lookupSlotCap st' addr = none := by
  rcases addr with ⟨cnodeId, slot⟩
  simp only [cspaceDeleteSlotCore] at hStep
  cases hObj : st.objects[cnodeId]? with
  | none => simp [hObj] at hStep
  | some obj =>
      cases obj with
      | tcb tcb => simp [hObj] at hStep
      | endpoint ep => simp [hObj] at hStep
      | notification ntfn => simp [hObj] at hStep
      | vspaceRoot root => simp [hObj] at hStep
      | untyped _ => simp [hObj] at hStep
      | schedContext _ => simp [hObj] at hStep
      | cnode cn =>
          have hUniq := hSlotUniq cnodeId cn hObj
          simp [hObj] at hStep
          cases hStep
          simp only [SystemState.lookupSlotCap, SystemState.lookupCNode,
            RHTable_getElem?_eq_get?, SystemState.detachSlotFromCdt_objects_eq]
          rw [RHTable_getElem?_insert st.objects _ _ hObjInv]
          simp [CNode.lookup_remove_eq_none cn slot hUniq]

/-- Delete transition authority reduction clause (guarded wrapper). -/
private theorem cspaceDeleteSlot_authority_reduction
    (st st' : SystemState)
    (addr : CSpaceAddr)
    (hSlotUniq : cspaceSlotUnique st)
    (hObjInv : st.objects.invExt)
    (hStep : cspaceDeleteSlot addr st = .ok ((), st')) :
    SystemState.lookupSlotCap st' addr = none := by
  simp only [cspaceDeleteSlot] at hStep
  split at hStep
  · simp at hStep
  · exact cspaceDeleteSlotCore_authority_reduction st st' addr hSlotUniq hObjInv hStep

/-- Revoke transition authority reduction clause: no sibling slot in the same CNode may retain
the revoked target. -/
theorem cspaceRevoke_local_target_reduction
    (st st' : SystemState)
    (addr : CSpaceAddr)
    (parent : Capability)
    (hSlotUniq : cspaceSlotUnique st)
    (hObjInv : st.objects.invExt)
    (hStep : cspaceRevoke addr st = .ok ((), st'))
    (hParent : cspaceLookupSlot addr st = .ok (parent, st))
    (slot : SeLe4n.Slot)
    (cap : Capability)
    (hLookup : SystemState.lookupSlotCap st' { cnode := addr.cnode, slot := slot } = some cap)
    (hTarget : cap.target = parent.target) :
    slot = addr.slot := by
  unfold cspaceRevoke at hStep
  rw [hParent] at hStep
  cases hObj : st.objects[addr.cnode]? with
  | none => simp [hObj] at hStep
  | some obj =>
      cases obj with
      | tcb tcb => simp [hObj] at hStep
      | endpoint ep => simp [hObj] at hStep
      | notification ntfn => simp [hObj] at hStep
      | vspaceRoot root => simp [hObj] at hStep
      | untyped _ => simp [hObj] at hStep
      | schedContext _ => simp [hObj] at hStep
      | cnode cn =>
          let revokedObj := KernelObject.cnode (cn.revokeTargetLocal addr.slot parent.target)
          let storedState : SystemState :=
            { st with
              objects := st.objects.insert addr.cnode revokedObj,
              objectIndex :=
                if st.objectIndexSet.contains addr.cnode then st.objectIndex else addr.cnode :: st.objectIndex,
              objectIndexSet := st.objectIndexSet.insert addr.cnode,
              lifecycle :=
                {
                  st.lifecycle with
                    objectTypes := st.lifecycle.objectTypes.insert addr.cnode revokedObj.objectType
                    capabilityRefs :=
                      let cleared := st.lifecycle.capabilityRefs.filter (fun ref _ => ref.cnode ≠ addr.cnode)
                      (cn.revokeTargetLocal addr.slot parent.target).slots.fold (init := cleared)
                        fun refs slot cap => refs.insert { cnode := addr.cnode, slot := slot } cap.target
                }
            }
          -- M-P01: After fused revoke, extract objects equality via storeObject + revokeAndClearRefsState
          cases hStore : storeObject addr.cnode (.cnode (cn.revokeTargetLocal addr.slot parent.target)) st with
          | error e => simp [hObj, hStore] at hStep
          | ok pair =>
            obtain ⟨_, stMid⟩ := pair
            simp [hObj, hStore] at hStep
            -- M-P01: Objects are preserved through revokeAndClearRefsState (only lifecycle changes)
            have hObjEq : st'.objects = storedState.objects := by
              have hFused := revokeAndClearRefsState_preserves_objects cn addr.slot parent.target addr.cnode stMid
              unfold storeObject at hStore; cases hStore; simp_all [storedState, revokedObj]
            have hLookupStored :
                SystemState.lookupSlotCap storedState { cnode := addr.cnode, slot := slot } = some cap := by
              have hEq := SystemState.lookupSlotCap_eq_of_objects_eq st' storedState
                { cnode := addr.cnode, slot := slot } hObjEq
              simpa [hEq] using hLookup
            have hUniq := hSlotUniq addr.cnode cn hObj
            -- Extract that the filtered table lookup succeeds at `slot`
            have hFilterLookup : (cn.revokeTargetLocal addr.slot parent.target).lookup slot = some cap := by
              simp only [storedState, revokedObj, SystemState.lookupSlotCap, SystemState.lookupCNode,
                RHTable_getElem?_eq_get?] at hLookupStored
              rw [RHTable_getElem?_insert st.objects _ _ hObjInv] at hLookupStored
              simp [CNode.lookup] at hLookupStored
              exact hLookupStored
            -- Convert to get? form for RHTable bridge lemmas
            have hFilterGet : (cn.slots.filter (fun s c => s == addr.slot || !(c.target == parent.target))).get? slot = some cap := by
              rw [CNode.revokeTargetLocal, CNode.lookup] at hFilterLookup; exact hFilterLookup
            -- By filter_get_pred, the predicate holds for (slot, cap)
            have hPredTrue := SeLe4n.Kernel.RobinHood.RHTable.filter_get_pred cn.slots
              (fun s c => s == addr.slot || !(c.target == parent.target)) slot cap hUniq.1 hFilterGet
            -- hPredTrue : (slot == addr.slot || !(cap.target == parent.target)) = true
            by_cases hSlot : slot = addr.slot
            · exact hSlot
            · exfalso
              simp [hSlot, hTarget] at hPredTrue

theorem cspaceLookupSlot_preserves_state
    (st st' : SystemState)
    (addr : CSpaceAddr)
    (cap : Capability)
    (hStep : cspaceLookupSlot addr st = .ok (cap, st')) :
    st' = st := by
  unfold cspaceLookupSlot at hStep
  cases hLookup : SystemState.lookupSlotCap st addr with
  | none =>
      cases hObj : st.objects[addr.cnode]? with
      | none => simp [hLookup, hObj] at hStep
      | some obj =>
          cases obj <;> simp [hLookup, hObj] at hStep
  | some foundCap =>
      simp [hLookup] at hStep
      exact hStep.2.symm

private theorem cspaceInsertSlot_lookup_eq
    (st st' : SystemState)
    (addr : CSpaceAddr)
    (cap : Capability)
    (hSlotUniq : cspaceSlotUnique st)
    (hObjInv : st.objects.invExt)
    (hStep : cspaceInsertSlot addr cap st = .ok ((), st')) :
    cspaceLookupSlot addr st' = .ok (cap, st') := by
  rcases addr with ⟨cnodeId, slot⟩
  cases hObj : st.objects[cnodeId]? with
  | none => simp [cspaceInsertSlot, hObj] at hStep
  | some obj =>
      cases obj with
      | tcb tcb => simp [cspaceInsertSlot, hObj] at hStep
      | endpoint ep => simp [cspaceInsertSlot, hObj] at hStep
      | notification ntfn => simp [cspaceInsertSlot, hObj] at hStep
      | vspaceRoot root => simp [cspaceInsertSlot, hObj] at hStep
      | untyped _ => simp [cspaceInsertSlot, hObj] at hStep
      | schedContext _ => simp [cspaceInsertSlot, hObj] at hStep
      | cnode cn =>
          have hUniq := hSlotUniq cnodeId cn hObj
          simp [cspaceInsertSlot, hObj] at hStep
          cases hLookupGuard : cn.lookup slot with
          | some _ => simp [hLookupGuard] at hStep
          | none =>
              simp [hLookupGuard] at hStep
              cases hStep
              simp only [cspaceLookupSlot, SystemState.lookupSlotCap, SystemState.lookupCNode,
                RHTable_getElem?_eq_get?]
              rw [RHTable_getElem?_insert st.objects _ _ hObjInv]
              simp [CNode.lookup_insert_eq cn slot cap hUniq]

theorem cspaceInsertSlot_establishes_ownsSlot
    (st st' : SystemState)
    (addr : CSpaceAddr)
    (cap : Capability)
    (hSlotUniq : cspaceSlotUnique st)
    (hObjInv : st.objects.invExt)
    (hStep : cspaceInsertSlot addr cap st = .ok ((), st')) :
    SystemState.ownsSlot st' addr.cnode addr := by
  have hLookup : cspaceLookupSlot addr st' = .ok (cap, st') :=
    cspaceInsertSlot_lookup_eq st st' addr cap hSlotUniq hObjInv hStep
  exact cspaceLookupSlot_ok_implies_ownsSlot st' addr cap hLookup

theorem cspaceDeleteSlotCore_lookup_eq_none
    (st st' : SystemState)
    (addr : CSpaceAddr)
    (hSlotUniq : cspaceSlotUnique st)
    (hObjInv : st.objects.invExt)
    (hStep : cspaceDeleteSlotCore addr st = .ok ((), st')) :
    cspaceLookupSlot addr st' = .error .invalidCapability := by
  rcases addr with ⟨cnodeId, slot⟩
  simp only [cspaceDeleteSlotCore] at hStep
  cases hObj : st.objects[cnodeId]? with
  | none => simp [hObj] at hStep
  | some obj =>
      cases obj with
      | tcb tcb => simp [hObj] at hStep
      | endpoint ep => simp [hObj] at hStep
      | notification ntfn => simp [hObj] at hStep
      | vspaceRoot root => simp [hObj] at hStep
      | untyped _ => simp [hObj] at hStep
      | schedContext _ => simp [hObj] at hStep
      | cnode cn =>
          have hUniq := hSlotUniq cnodeId cn hObj
          simp [hObj] at hStep
          cases hStep
          simp only [cspaceLookupSlot, SystemState.lookupSlotCap, SystemState.lookupCNode,
            RHTable_getElem?_eq_get?, SystemState.detachSlotFromCdt_objects_eq]
          rw [RHTable_getElem?_insert st.objects _ _ hObjInv]
          simp [CNode.lookup_remove_eq_none cn slot hUniq]

theorem cspaceDeleteSlot_lookup_eq_none
    (st st' : SystemState)
    (addr : CSpaceAddr)
    (hSlotUniq : cspaceSlotUnique st)
    (hObjInv : st.objects.invExt)
    (hStep : cspaceDeleteSlot addr st = .ok ((), st')) :
    cspaceLookupSlot addr st' = .error .invalidCapability := by
  simp only [cspaceDeleteSlot] at hStep
  split at hStep
  · simp at hStep
  · exact cspaceDeleteSlotCore_lookup_eq_none st st' addr hSlotUniq hObjInv hStep

theorem cspaceRevoke_preserves_source
    (st st' : SystemState)
    (addr : CSpaceAddr)
    (hSlotUniq : cspaceSlotUnique st)
    (hObjInv : st.objects.invExt)
    (hStep : cspaceRevoke addr st = .ok ((), st')) :
    ∃ cap, cspaceLookupSlot addr st' = .ok (cap, st') := by
  unfold cspaceRevoke at hStep
  cases hLookup : cspaceLookupSlot addr st with
  | error e => simp [hLookup] at hStep
  | ok pair =>
      rcases pair with ⟨parent, st1⟩
      have hSt1 : st1 = st := cspaceLookupSlot_preserves_state st st1 addr parent hLookup
      subst st1
      cases hObj : st.objects[addr.cnode]? with
      | none => simp [hLookup, hObj] at hStep
      | some obj =>
          cases obj with
          | tcb tcb => simp [hLookup, hObj] at hStep
          | endpoint ep => simp [hLookup, hObj] at hStep
          | notification ntfn => simp [hLookup, hObj] at hStep
          | vspaceRoot root => simp [hLookup, hObj] at hStep
          | untyped _ => simp [hLookup, hObj] at hStep
          | schedContext _ => simp [hLookup, hObj] at hStep
          | cnode cn =>
              have hUniq := hSlotUniq addr.cnode cn hObj
              let revokedObj := KernelObject.cnode (cn.revokeTargetLocal addr.slot parent.target)
              let storedState : SystemState :=
                { st with
                  objects := st.objects.insert addr.cnode revokedObj,
                  objectIndex :=
                    if st.objectIndexSet.contains addr.cnode then st.objectIndex else addr.cnode :: st.objectIndex,
                  objectIndexSet := st.objectIndexSet.insert addr.cnode,
                  lifecycle :=
                    {
                      st.lifecycle with
                        objectTypes := st.lifecycle.objectTypes.insert addr.cnode revokedObj.objectType
                        capabilityRefs :=
                          let cleared := st.lifecycle.capabilityRefs.filter (fun ref _ => ref.cnode ≠ addr.cnode)
                          (cn.revokeTargetLocal addr.slot parent.target).slots.fold (init := cleared)
                            fun refs slot cap => refs.insert { cnode := addr.cnode, slot := slot } cap.target
                    }
                }
              -- M-P01: After fused revoke, extract objects equality
              cases hStore : storeObject addr.cnode (.cnode (cn.revokeTargetLocal addr.slot parent.target)) st with
              | error e => simp [hLookup, hObj, hStore] at hStep
              | ok pair =>
                obtain ⟨_, stMid⟩ := pair
                simp [hLookup, hObj, hStore] at hStep
                -- M-P01: Objects are preserved through revokeAndClearRefsState (only lifecycle changes)
                have hObjEq : st'.objects = storedState.objects := by
                  have hFused := revokeAndClearRefsState_preserves_objects cn addr.slot parent.target addr.cnode stMid
                  unfold storeObject at hStore; cases hStore; simp_all [storedState, revokedObj]
                have hCap : SystemState.lookupSlotCap st addr = some parent :=
                  (cspaceLookupSlot_ok_iff_lookupSlotCap st addr parent).1 hLookup
                have hRevokePres := CNode.lookup_revokeTargetLocal_source_eq_lookup cn addr.slot parent.target hUniq
                have hCapStored : SystemState.lookupSlotCap storedState addr = some parent := by
                  simp only [storedState, revokedObj, SystemState.lookupSlotCap, SystemState.lookupCNode,
                    RHTable_getElem?_eq_get?]
                  rw [RHTable_getElem?_insert st.objects _ _ hObjInv]
                  simp only [SystemState.lookupSlotCap, SystemState.lookupCNode] at hCap
                  simpa [hRevokePres, hObj] using hCap
                have hCapFinal : SystemState.lookupSlotCap st' addr = some parent := by
                  have hEq := SystemState.lookupSlotCap_eq_of_objects_eq st' storedState addr hObjEq
                  simpa [hEq] using hCapStored
                refine ⟨parent, ?_⟩
                exact (cspaceLookupSlot_ok_iff_lookupSlotCap st' addr parent).2 hCapFinal

private theorem mintDerivedCap_attenuates
    (parent child : Capability)
    (rights : AccessRightSet)
    (badge : Option SeLe4n.Badge)
    (hMint : mintDerivedCap parent rights badge = .ok child) :
    capAttenuates parent child := by
  by_cases hSubset : rightsSubset rights parent.rights = true
  · simp [mintDerivedCap, hSubset] at hMint
    cases hMint
    constructor
    · rfl
    · exact rightsSubset_sound rights parent.rights hSubset
  · simp [mintDerivedCap, hSubset] at hMint

-- ============================================================================
-- F-06 / TPI-D04: Badge-override safety in cspaceMint
-- ============================================================================

/-- Badge override does not affect rights attenuation: a minted capability's rights
are always a subset of the parent's rights, regardless of what badge is supplied.

This is a direct consequence of `mintDerivedCap` checking `rightsSubset` before
constructing the child capability and setting `child.target = parent.target`
unconditionally. -/
theorem mintDerivedCap_rights_attenuated_with_badge_override
    (parent child : Capability)
    (rights : AccessRightSet)
    (badge : Option SeLe4n.Badge)
    (hMint : mintDerivedCap parent rights badge = .ok child) :
    ∀ right, right ∈ child.rights → right ∈ parent.rights := by
  have hAtt := mintDerivedCap_attenuates parent child rights badge hMint
  exact hAtt.2

/-- Badge override preserves target identity: a minted capability always names the
same target as the parent, regardless of the badge supplied. Badge override cannot
enable a capability holder to access objects outside the authority granted by the
parent capability.

This is the core F-06 safety property: badge is metadata that affects notification
signaling semantics, not capability authority scope. -/
theorem mintDerivedCap_target_preserved_with_badge_override
    (parent child : Capability)
    (rights : AccessRightSet)
    (badge : Option SeLe4n.Badge)
    (hMint : mintDerivedCap parent rights badge = .ok child) :
    child.target = parent.target := by
  have hAtt := mintDerivedCap_attenuates parent child rights badge hMint
  exact hAtt.1

theorem cspaceMint_child_attenuates
    (st st' : SystemState)
    (src dst : CSpaceAddr)
    (rights : AccessRightSet)
    (badge : Option SeLe4n.Badge)
    (hSlotUniq : cspaceSlotUnique st)
    (hObjInv : st.objects.invExt)
    (hStep : cspaceMint src dst rights badge st = .ok ((), st')) :
    ∃ parent child,
      cspaceLookupSlot src st = .ok (parent, st) ∧
      cspaceLookupSlot dst st' = .ok (child, st') ∧
      capAttenuates parent child := by
  unfold cspaceMint at hStep
  cases hSrc : cspaceLookupSlot src st with
  | error e => simp [hSrc] at hStep
  | ok pair =>
      rcases pair with ⟨parent, st1⟩
      have hSt1 : st1 = st := cspaceLookupSlot_preserves_state st st1 src parent hSrc
      subst st1
      cases hMint : mintDerivedCap parent rights badge with
      | error e => simp [hSrc, hMint] at hStep
      | ok child =>
          have hAtt : capAttenuates parent child :=
            mintDerivedCap_attenuates parent child rights badge hMint
          have hInsert : cspaceInsertSlot dst child st = .ok ((), st') := by
            simpa [hSrc, hMint] using hStep
          refine ⟨parent, child, ?_, ?_, hAtt⟩
          · rfl
          · exact cspaceInsertSlot_lookup_eq st st' dst child hSlotUniq hObjInv hInsert

/-- Composed badge-override safety for `cspaceMint`: after a successful mint with
arbitrary badge override, the derived capability in the destination slot has the
same target as the parent and attenuated rights.

This theorem witnesses the full F-06 obligation at the kernel-operation level:
badge override in `cspaceMint` cannot escalate privilege. -/
theorem cspaceMint_badge_override_safe
    (st st' : SystemState)
    (src dst : CSpaceAddr)
    (rights : AccessRightSet)
    (badge : Option SeLe4n.Badge)
    (hSlotUniq : cspaceSlotUnique st)
    (hObjInv : st.objects.invExt)
    (hStep : cspaceMint src dst rights badge st = .ok ((), st')) :
    ∃ parent child,
      cspaceLookupSlot src st = .ok (parent, st) ∧
      cspaceLookupSlot dst st' = .ok (child, st') ∧
      child.target = parent.target ∧
      (∀ right, right ∈ child.rights → right ∈ parent.rights) := by
  rcases cspaceMint_child_attenuates st st' src dst rights badge hSlotUniq hObjInv hStep with
    ⟨parent, child, hSrc, hDst, hAtt⟩
  exact ⟨parent, child, hSrc, hDst, hAtt.1, hAtt.2⟩

-- ============================================================================
-- WS-E2 / H-03: Badge/notification routing consistency
-- ============================================================================

/-- (H-03) `mintDerivedCap` propagates the explicitly provided badge to the
derived capability when rights are sufficient. -/
theorem mintDerivedCap_badge_propagated
    (parent : Capability) (rights : AccessRightSet) (badge : Option SeLe4n.Badge)
    (child : Capability)
    (hMint : mintDerivedCap parent rights badge = .ok child) :
    child.badge = badge := by
  unfold mintDerivedCap at hMint
  split at hMint
  · cases hMint; rfl
  · exact absurd hMint (by simp)

/-- (H-03) `cspaceMint` stores a child capability whose badge equals the requested badge.
This is the operation-level badge consistency witness. -/
theorem cspaceMint_child_badge_preserved
    (st st' : SystemState)
    (src dst : CSpaceAddr)
    (rights : AccessRightSet)
    (badge : SeLe4n.Badge)
    (hSlotUniq : cspaceSlotUnique st)
    (hObjInv : st.objects.invExt)
    (hStep : cspaceMint src dst rights (some badge) st = .ok ((), st')) :
    ∃ child,
      cspaceLookupSlot dst st' = .ok (child, st') ∧
      child.badge = some badge := by
  unfold cspaceMint at hStep
  cases hSrc : cspaceLookupSlot src st with
  | error e => simp [hSrc] at hStep
  | ok pair =>
      rcases pair with ⟨parent, st1⟩
      have hSt1 := cspaceLookupSlot_preserves_state st st1 src parent hSrc
      subst st1
      simp [hSrc] at hStep
      cases hMint : mintDerivedCap parent rights (some badge) with
      | error e => simp [hMint] at hStep
      | ok child =>
          simp [hMint] at hStep
          have hDst := cspaceInsertSlot_lookup_eq st st' dst child hSlotUniq hObjInv hStep
          refine ⟨child, hDst, ?_⟩
          unfold mintDerivedCap at hMint
          by_cases hRights : rightsSubset rights parent.rights
          · simp [hRights] at hMint; cases hMint; rfl
          · simp [hRights] at hMint

/-- (H-03) When a notification has no waiters and no pending badge, signaling with badge `b`
stores `ofNatMasked b.val` as the pending badge (word-bounded).
WS-F5/D1c: Updated to reflect word-bounded badge storage via `ofNatMasked`. -/
theorem notificationSignal_badge_stored_fresh
    (st st' : SystemState)
    (notifId : SeLe4n.ObjId)
    (badge : SeLe4n.Badge)
    (ntfn : Notification)
    (hObj : st.objects[notifId]? = some (.notification ntfn))
    (hNoWaiters : ntfn.waitingThreads = [])
    (hNoPending : ntfn.pendingBadge = none)
    (hObjInv : st.objects.invExt)
    (hSignal : notificationSignal notifId badge st = .ok ((), st')) :
    ∃ ntfn',
      st'.objects[notifId]? = some (.notification ntfn') ∧
      ntfn'.pendingBadge = some (SeLe4n.Badge.ofNatMasked badge.toNat) := by
  unfold notificationSignal at hSignal
  simp [hObj, hNoWaiters, hNoPending] at hSignal
  exact ⟨{ state := .active, waitingThreads := [],
           pendingBadge := some (SeLe4n.Badge.ofNatMasked badge.toNat) },
    by rw [← storeObject_objects_eq st st' notifId _ hObjInv hSignal], rfl⟩

/-- (H-03) When `notificationWait` returns `some badge`, that badge was the pending
badge of the notification object in the pre-state. -/
theorem notificationWait_recovers_pending_badge
    (st st' : SystemState)
    (notifId : SeLe4n.ObjId)
    (waiter : SeLe4n.ThreadId)
    (badge : SeLe4n.Badge)
    (hObjInv : st.objects.invExt)
    (hWait : notificationWait notifId waiter st = .ok (some badge, st')) :
    ∃ ntfn,
      st.objects[notifId]? = some (.notification ntfn) ∧
      ntfn.pendingBadge = some badge := by
  unfold notificationWait at hWait
  cases hObj : st.objects[notifId]? with
  | none => simp [hObj] at hWait
  | some obj =>
      cases obj with
      | notification ntfn =>
          refine ⟨ntfn, rfl, ?_⟩
          simp only [hObj] at hWait
          cases hPending : ntfn.pendingBadge with
          | none =>
              exfalso; simp only [hPending] at hWait
              -- WS-G7: match on lookupTcb
              cases hLk : lookupTcb st waiter with
              | none => simp [hLk] at hWait
              | some tcb =>
                simp only [hLk] at hWait
                split at hWait
                · simp at hWait
                · revert hWait
                  cases hStore : storeObject notifId _ st with
                  | error e => simp
                  | ok pair =>
                      simp only []
                      have hLk' := lookupTcb_preserved_by_storeObject_notification hLk hObj hObjInv hStore
                      simp only [storeTcbIpcState_fromTcb_eq hLk']
                      intro hWait
                      revert hWait
                      cases storeTcbIpcState pair.2 waiter _ with
                      | error e => simp
                      | ok st2 =>
                          simp only [Except.ok.injEq, Prod.mk.injEq]
                          intro ⟨h, _⟩
                          exact absurd h (by simp)
          | some b =>
              simp only [hPending] at hWait
              let newNtfn : Notification :=
                { state := .idle, waitingThreads := [], pendingBadge := none }
              revert hWait
              cases hStore : storeObject notifId (.notification newNtfn) st with
              | error e => simp
              | ok pair =>
                  simp only []
                  intro hWait
                  revert hWait
                  cases storeTcbIpcState pair.2 waiter .ready with
                  | error e => simp
                  | ok st2 =>
                      simp only [Except.ok.injEq, Prod.mk.injEq]
                      intro ⟨hBadgeEq, _⟩
                      exact hBadgeEq
      | tcb _ | endpoint _ | cnode _ | vspaceRoot _ | untyped _ | schedContext _ => simp [hObj] at hWait

/-- (H-03) End-to-end badge routing consistency.

Composition of badge preservation through the full minting → signaling → waiting
path. When a capability is minted with explicit badge `b`, and that badge is
signaled to an idle notification, and a waiter collects the notification, the
recovered badge equals the word-bounded form of `b`.
WS-F5/D1c: Updated to reflect word-bounded badge storage via `ofNatMasked`. -/
theorem badge_notification_routing_consistent
    (st₁ st₂ st₃ st₄ : SystemState)
    (src dst : CSpaceAddr)
    (rights : AccessRightSet)
    (badge : SeLe4n.Badge)
    (notifId : SeLe4n.ObjId)
    (waiter : SeLe4n.ThreadId)
    (ntfn : Notification)
    (_hMint : cspaceMint src dst rights (some badge) st₁ = .ok ((), st₂))
    (hNtfnObj : st₂.objects[notifId]? = some (.notification ntfn))
    (hNoWaiters : ntfn.waitingThreads = [])
    (hNoPending : ntfn.pendingBadge = none)
    (hObjInv2 : st₂.objects.invExt)
    (hSignal : notificationSignal notifId badge st₂ = .ok ((), st₃))
    (hObjInv3 : st₃.objects.invExt)
    (recoveredBadge : SeLe4n.Badge)
    (hWait : notificationWait notifId waiter st₃ = .ok (some recoveredBadge, st₄)) :
    recoveredBadge = SeLe4n.Badge.ofNatMasked badge.toNat := by
  rcases notificationSignal_badge_stored_fresh st₂ st₃ notifId badge ntfn
    hNtfnObj hNoWaiters hNoPending hObjInv2 hSignal with ⟨ntfn', hNtfn'Obj, hNtfn'Badge⟩
  rcases notificationWait_recovers_pending_badge st₃ st₄ notifId waiter recoveredBadge hObjInv3 hWait
    with ⟨ntfn'', hNtfn''Obj, hNtfn''Badge⟩
  rw [hNtfn'Obj] at hNtfn''Obj
  cases hNtfn''Obj
  rw [hNtfn'Badge] at hNtfn''Badge
  exact (Option.some.inj hNtfn''Badge).symm

/-- (H-03) Badge OR-merge is idempotent — signaling the same badge twice yields the same
pending badge as signaling it once (since `b ||| b = b` for bitwise OR).
WS-F5/D1c: Updated to use word-bounded `Badge.bor`. -/
theorem badge_merge_idempotent
    (badge : SeLe4n.Badge) :
    SeLe4n.Badge.bor badge badge = SeLe4n.Badge.ofNatMasked badge.toNat := by
  simp [SeLe4n.Badge.bor, SeLe4n.Badge.toNat, Nat.or_self]

-- ============================================================================
-- WS-E2 / C-01: Derivation infrastructure for reformulated invariants
-- ============================================================================

/-- Derive `cspaceLookupSound` from `cspaceSlotUnique` for any state.

WS-G5: With HashMap-backed slots, `CNode.lookup` delegates directly to
`HashMap.getElem?`, making lookup completeness trivial by definition.
The bridge from `slotsUnique` to `lookupSound` is now immediate. -/
theorem cspaceLookupSound_of_cspaceSlotUnique
    (st : SystemState) (_hUniq : cspaceSlotUnique st) :
    cspaceLookupSound st := by
  intro cnodeId cn slot cap hObj hLookup
  simp [SystemState.lookupSlotCap, SystemState.lookupCNode, hObj, CNode.lookup]
  exact hLookup

/-- WS-E2 / H-01: Transfer `cspaceSlotUnique` across a non-CNode `storeObject`.

When `storeObject` writes a non-CNode object, all CNode entries in the store are
preserved from the pre-state and uniqueness transfers directly. -/
theorem cspaceSlotUnique_of_storeObject_nonCNode
    (st st' : SystemState) (oid : SeLe4n.ObjId) (obj : KernelObject)
    (hUniq : cspaceSlotUnique st)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject oid obj st = .ok ((), st'))
    (hNotCNode : ∀ cn, obj ≠ .cnode cn) :
    cspaceSlotUnique st' := by
  intro cnodeId cn hObj
  by_cases hEq : cnodeId = oid
  · rw [hEq] at hObj
    have hEqObj := storeObject_objects_eq st st' oid obj hObjInv hStore
    rw [hEqObj] at hObj
    have : obj = .cnode cn := by injection hObj
    exact absurd this (hNotCNode cn)
  · have hPre := storeObject_objects_ne st st' oid cnodeId obj hEq hObjInv hStore
    rw [hPre] at hObj
    exact hUniq cnodeId cn hObj

/-- WS-E2 / H-01: Transfer `cspaceSlotUnique` across a CNode `storeObject`,
given that the new CNode satisfies `slotsUnique`. -/
theorem cspaceSlotUnique_of_storeObject_cnode
    (st st' : SystemState) (oid : SeLe4n.ObjId) (cn' : CNode)
    (hUniq : cspaceSlotUnique st)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject oid (.cnode cn') st = .ok ((), st'))
    (hNewUniq : cn'.slotsUnique) :
    cspaceSlotUnique st' := by
  intro cnodeId cn hObj
  by_cases hEq : cnodeId = oid
  · subst hEq
    have := storeObject_objects_eq st st' cnodeId (.cnode cn') hObjInv hStore
    rw [this] at hObj
    cases hObj
    exact hNewUniq
  · have hPre := storeObject_objects_ne st st' oid cnodeId (.cnode cn') hEq hObjInv hStore
    rw [hPre] at hObj
    exact hUniq cnodeId cn hObj

/-- WS-E2 / H-01: Transfer `cspaceSlotUnique` across endpoint-object stores. -/
theorem cspaceSlotUnique_of_endpoint_store
    (st st' : SystemState) (oid : SeLe4n.ObjId) (ep : Endpoint)
    (hUniq : cspaceSlotUnique st)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject oid (.endpoint ep) st = .ok ((), st')) :
    cspaceSlotUnique st' :=
  cspaceSlotUnique_of_storeObject_nonCNode st st' oid (.endpoint ep) hUniq hObjInv hStore
    (fun cn h => by cases h)

/-- WS-E2 / H-01: Transfer `cspaceSlotUnique` when objects are unchanged. -/
theorem cspaceSlotUnique_of_objects_eq
    (st st' : SystemState)
    (hUniq : cspaceSlotUnique st)
    (hObjEq : st'.objects = st.objects) :
    cspaceSlotUnique st' := by
  intro cnodeId cn hObj
  exact hUniq cnodeId cn (by rwa [hObjEq] at hObj)

-- ============================================================================
-- WS-F6/D1: Operation Correctness Lemmas
-- Reclassified from capabilityInvariantBundle — these are operation properties,
-- not state invariants. Retained as standalone theorems.
-- ============================================================================

theorem cspaceAttenuationRule_holds :
    cspaceAttenuationRule := by
  intro parent child rights badge hMint
  exact mintDerivedCap_attenuates parent child rights badge hMint


theorem lifecycleAuthorityMonotonicity_holds (st : SystemState)
    (hSlotUniq : cspaceSlotUnique st)
    (hObjInv : st.objects.invExt) :
    lifecycleAuthorityMonotonicity st := by
  refine ⟨?_, ?_⟩
  · intro addr st' hDelete
    exact cspaceDeleteSlot_authority_reduction st st' addr hSlotUniq hObjInv hDelete
  · intro addr st' parent hRevoke hParent slot cap hLookup hTarget
    exact cspaceRevoke_local_target_reduction st st' addr parent hSlotUniq hObjInv hRevoke hParent slot cap hLookup hTarget

/-- Establish the capability invariant bundle from a slot-index uniqueness witness.
Unlike the prior tautological version, this requires a genuine hypothesis:
the caller must supply evidence that all CNodes have unique slot keys.
(WS-E2 / C-01 + H-01 remediation) -/
theorem capabilityInvariantBundle_of_slotUnique
    (st : SystemState)
    (hUnique : cspaceSlotUnique st)
    (hBounded : cspaceSlotCountBounded st)
    (hComp : cdtCompleteness st)
    (hAcyclic : cdtAcyclicity st)
    (hDepth : cspaceDepthConsistent st)
    (hObjInv : st.objects.invExt) :
    capabilityInvariantBundle st :=
  ⟨hUnique, cspaceLookupSound_of_cspaceSlotUnique st hUnique,
    hBounded, hComp, hAcyclic, hDepth, hObjInv⟩

