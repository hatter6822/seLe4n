import SeLe4n.Kernel.Capability.Invariant.Definitions

/-!
# Capability Structural Properties

Authority reduction, attenuation, badge-override safety (F-06/TPI-D04),
badge/notification routing consistency (H-03), and derivation infrastructure.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

theorem cspaceDeleteSlot_authority_reduction
    (st st' : SystemState)
    (addr : CSpaceAddr)
    (hStep : cspaceDeleteSlot addr st = .ok ((), st')) :
    SystemState.lookupSlotCap st' addr = none := by
  rcases addr with ⟨cnodeId, slot⟩
  cases hObj : st.objects cnodeId with
  | none => simp [cspaceDeleteSlot, hObj] at hStep
  | some obj =>
      cases obj with
      | tcb tcb => simp [cspaceDeleteSlot, hObj] at hStep
      | endpoint ep => simp [cspaceDeleteSlot, hObj] at hStep
      | notification ntfn => simp [cspaceDeleteSlot, hObj] at hStep
      | vspaceRoot root => simp [cspaceDeleteSlot, hObj] at hStep
      | cnode cn =>

          simp [cspaceDeleteSlot, hObj] at hStep
          cases hStep
          simp [SystemState.lookupSlotCap, SystemState.lookupCNode, CNode.lookup_remove_eq_none]

/-- Revoke transition authority reduction clause: no sibling slot in the same CNode may retain
the revoked target. -/
theorem cspaceRevoke_local_target_reduction
    (st st' : SystemState)
    (addr : CSpaceAddr)
    (parent : Capability)
    (hStep : cspaceRevoke addr st = .ok ((), st'))
    (hParent : cspaceLookupSlot addr st = .ok (parent, st))
    (slot : SeLe4n.Slot)
    (cap : Capability)
    (hLookup : SystemState.lookupSlotCap st' { cnode := addr.cnode, slot := slot } = some cap)
    (hTarget : cap.target = parent.target) :
    slot = addr.slot := by
  unfold cspaceRevoke at hStep
  rw [hParent] at hStep
  cases hObj : st.objects addr.cnode with
  | none => simp [hObj] at hStep
  | some obj =>
      cases obj with
      | tcb tcb => simp [hObj] at hStep
      | endpoint ep => simp [hObj] at hStep
      | notification ntfn => simp [hObj] at hStep
      | vspaceRoot root => simp [hObj] at hStep
      | cnode cn =>

          let revokedRefs : List SlotRef :=
            (cn.slots.filter (fun entry => entry.fst ≠ addr.slot ∧ entry.snd.target = parent.target)).map
              (fun entry => { cnode := addr.cnode, slot := entry.fst })
          let storedState : SystemState :=
            { st with
              objects :=
                fun oid =>
                  if oid = addr.cnode then
                    some (KernelObject.cnode (cn.revokeTargetLocal addr.slot parent.target))
                  else
                    st.objects oid,
              objectIndex :=
                if addr.cnode ∈ st.objectIndex then st.objectIndex else addr.cnode :: st.objectIndex,
              lifecycle :=
                {
                  st.lifecycle with
                    objectTypes :=
                      fun oid =>
                        if oid = addr.cnode then
                          some (KernelObject.cnode (cn.revokeTargetLocal addr.slot parent.target)).objectType
                        else
                          st.lifecycle.objectTypes oid
                    capabilityRefs := fun ref =>
                      if ref.cnode = addr.cnode then
                        ((cn.revokeTargetLocal addr.slot parent.target).lookup ref.slot).map Capability.target
                      else
                        st.lifecycle.capabilityRefs ref
                }
            }
          have hStepClear : clearCapabilityRefs revokedRefs storedState = .ok ((), st') := by
            simpa [revokedRefs, storedState, storeObject, hObj] using hStep
          have hObjEq : st'.objects = storedState.objects :=
            clearCapabilityRefs_preserves_objects storedState st' revokedRefs hStepClear
          have hLookupStored :
              SystemState.lookupSlotCap storedState { cnode := addr.cnode, slot := slot } = some cap := by
            have hEq := SystemState.lookupSlotCap_eq_of_objects_eq st' storedState
              { cnode := addr.cnode, slot := slot } hObjEq
            simpa [hEq] using hLookup
          simp [storedState, SystemState.lookupSlotCap, SystemState.lookupCNode,
            CNode.lookup, CNode.revokeTargetLocal] at hLookupStored
          rcases hLookupStored with ⟨slot', hFind⟩
          have hPred :
              ((decide (slot' = addr.slot) || !decide (cap.target = parent.target)) &&
                decide (slot' = slot)) = true := by
            have hPredRaw := List.find?_some
              (p := fun entry : SeLe4n.Slot × Capability =>
                (decide (entry.fst = addr.slot) || !decide (entry.snd.target = parent.target)) &&
                  decide (entry.fst = slot))
              (a := (slot', cap)) hFind
            simpa using hPredRaw
          have hSplit :
              (decide (slot' = addr.slot) || !decide (cap.target = parent.target)) = true ∧
              decide (slot' = slot) = true := by
            simpa [Bool.and_eq_true] using hPred
          have hEqSlot : slot' = slot := by
            simpa using hSplit.2
          have hOrProp : slot' = addr.slot ∨ cap.target ≠ parent.target := by
            simpa using hSplit.1
          by_cases hSlot : slot = addr.slot
          · exact hSlot
          · have hNotTarget : cap.target ≠ parent.target := by
              rcases hOrProp with hSrc | hNe
              · exfalso
                exact hSlot (hEqSlot.symm.trans hSrc)
              · exact hNe
            exact False.elim (hNotTarget hTarget)

theorem cspaceLookupSlot_preserves_state
    (st st' : SystemState)
    (addr : CSpaceAddr)
    (cap : Capability)
    (hStep : cspaceLookupSlot addr st = .ok (cap, st')) :
    st' = st := by
  unfold cspaceLookupSlot at hStep
  cases hLookup : SystemState.lookupSlotCap st addr with
  | none =>
      cases hObj : st.objects addr.cnode with
      | none => simp [hLookup, hObj] at hStep
      | some obj =>
          cases obj <;> simp [hLookup, hObj] at hStep
  | some foundCap =>
      simp [hLookup] at hStep
      exact hStep.2.symm

theorem cspaceInsertSlot_lookup_eq
    (st st' : SystemState)
    (addr : CSpaceAddr)
    (cap : Capability)
    (hStep : cspaceInsertSlot addr cap st = .ok ((), st')) :
    cspaceLookupSlot addr st' = .ok (cap, st') := by
  rcases addr with ⟨cnodeId, slot⟩
  cases hObj : st.objects cnodeId with
  | none => simp [cspaceInsertSlot, hObj] at hStep
  | some obj =>
      cases obj with
      | tcb tcb => simp [cspaceInsertSlot, hObj] at hStep
      | endpoint ep => simp [cspaceInsertSlot, hObj] at hStep
      | notification ntfn => simp [cspaceInsertSlot, hObj] at hStep
      | vspaceRoot root => simp [cspaceInsertSlot, hObj] at hStep
      | cnode cn =>

          simp [cspaceInsertSlot, hObj] at hStep
          cases hStep
          simp [cspaceLookupSlot, SystemState.lookupSlotCap, SystemState.lookupCNode, CNode.lookup, CNode.insert]

theorem cspaceInsertSlot_establishes_ownsSlot
    (st st' : SystemState)
    (addr : CSpaceAddr)
    (cap : Capability)
    (hStep : cspaceInsertSlot addr cap st = .ok ((), st')) :
    SystemState.ownsSlot st' addr.cnode addr := by
  have hLookup : cspaceLookupSlot addr st' = .ok (cap, st') :=
    cspaceInsertSlot_lookup_eq st st' addr cap hStep
  exact cspaceLookupSlot_ok_implies_ownsSlot st' addr cap hLookup

theorem cspaceDeleteSlot_lookup_eq_none
    (st st' : SystemState)
    (addr : CSpaceAddr)
    (hStep : cspaceDeleteSlot addr st = .ok ((), st')) :
    cspaceLookupSlot addr st' = .error .invalidCapability := by
  rcases addr with ⟨cnodeId, slot⟩
  cases hObj : st.objects cnodeId with
  | none => simp [cspaceDeleteSlot, hObj] at hStep
  | some obj =>
      cases obj with
      | tcb tcb => simp [cspaceDeleteSlot, hObj] at hStep
      | endpoint ep => simp [cspaceDeleteSlot, hObj] at hStep
      | notification ntfn => simp [cspaceDeleteSlot, hObj] at hStep
      | vspaceRoot root => simp [cspaceDeleteSlot, hObj] at hStep
      | cnode cn =>

          simp [cspaceDeleteSlot, hObj] at hStep
          cases hStep
          simp [cspaceLookupSlot, SystemState.lookupSlotCap, SystemState.lookupCNode,
            CNode.lookup_remove_eq_none]

theorem cspaceRevoke_preserves_source
    (st st' : SystemState)
    (addr : CSpaceAddr)
    (hStep : cspaceRevoke addr st = .ok ((), st')) :
    ∃ cap, cspaceLookupSlot addr st' = .ok (cap, st') := by
  unfold cspaceRevoke at hStep
  cases hLookup : cspaceLookupSlot addr st with
  | error e => simp [hLookup] at hStep
  | ok pair =>
      rcases pair with ⟨parent, st1⟩
      have hSt1 : st1 = st := cspaceLookupSlot_preserves_state st st1 addr parent hLookup
      subst st1
      cases hObj : st.objects addr.cnode with
      | none => simp [hLookup, hObj] at hStep
      | some obj =>
          cases obj with
          | tcb tcb => simp [hLookup, hObj] at hStep
          | endpoint ep => simp [hLookup, hObj] at hStep
          | notification ntfn => simp [hLookup, hObj] at hStep
          | vspaceRoot root => simp [hLookup, hObj] at hStep
          | cnode cn =>

              let revokedRefs : List SlotRef :=
                (cn.slots.filter (fun entry => entry.fst ≠ addr.slot ∧ entry.snd.target = parent.target)).map
                  (fun entry => { cnode := addr.cnode, slot := entry.fst })
              let storedState : SystemState :=
                { st with
                  objects :=
                    fun oid =>
                      if oid = addr.cnode then
                        some (KernelObject.cnode (cn.revokeTargetLocal addr.slot parent.target))
                      else
                        st.objects oid,
                  objectIndex :=
                    if addr.cnode ∈ st.objectIndex then st.objectIndex else addr.cnode :: st.objectIndex,
                  lifecycle :=
                    {
                      st.lifecycle with
                        objectTypes :=
                          fun oid =>
                            if oid = addr.cnode then
                              some (KernelObject.cnode (cn.revokeTargetLocal addr.slot parent.target)).objectType
                            else
                              st.lifecycle.objectTypes oid
                        capabilityRefs := fun ref =>
                          if ref.cnode = addr.cnode then
                            ((cn.revokeTargetLocal addr.slot parent.target).lookup ref.slot).map Capability.target
                          else
                            st.lifecycle.capabilityRefs ref
                    }
                }
              have hStepClear : clearCapabilityRefs revokedRefs storedState = .ok ((), st') := by
                simpa [revokedRefs, storedState, storeObject, hLookup, hObj] using hStep
              have hObjEq : st'.objects = storedState.objects :=
                clearCapabilityRefs_preserves_objects storedState st' revokedRefs hStepClear
              have hCap : SystemState.lookupSlotCap st addr = some parent :=
                (cspaceLookupSlot_ok_iff_lookupSlotCap st addr parent).1 hLookup
              have hCapStored : SystemState.lookupSlotCap storedState addr = some parent := by
                simpa [storedState, SystemState.lookupSlotCap, SystemState.lookupCNode,
                  CNode.lookup_revokeTargetLocal_source_eq_lookup, hObj] using hCap
              have hCapFinal : SystemState.lookupSlotCap st' addr = some parent := by
                have hEq := SystemState.lookupSlotCap_eq_of_objects_eq st' storedState addr hObjEq
                simpa [hEq] using hCapStored
              refine ⟨parent, ?_⟩
              exact (cspaceLookupSlot_ok_iff_lookupSlotCap st' addr parent).2 hCapFinal

theorem mintDerivedCap_attenuates
    (parent child : Capability)
    (rights : List AccessRight)
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
    (rights : List AccessRight)
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
    (rights : List AccessRight)
    (badge : Option SeLe4n.Badge)
    (hMint : mintDerivedCap parent rights badge = .ok child) :
    child.target = parent.target := by
  have hAtt := mintDerivedCap_attenuates parent child rights badge hMint
  exact hAtt.1

theorem cspaceMint_child_attenuates
    (st st' : SystemState)
    (src dst : CSpaceAddr)
    (rights : List AccessRight)
    (badge : Option SeLe4n.Badge)
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
          · exact cspaceInsertSlot_lookup_eq st st' dst child hInsert

/-- Composed badge-override safety for `cspaceMint`: after a successful mint with
arbitrary badge override, the derived capability in the destination slot has the
same target as the parent and attenuated rights.

This theorem witnesses the full F-06 obligation at the kernel-operation level:
badge override in `cspaceMint` cannot escalate privilege. -/
theorem cspaceMint_badge_override_safe
    (st st' : SystemState)
    (src dst : CSpaceAddr)
    (rights : List AccessRight)
    (badge : Option SeLe4n.Badge)
    (hStep : cspaceMint src dst rights badge st = .ok ((), st')) :
    ∃ parent child,
      cspaceLookupSlot src st = .ok (parent, st) ∧
      cspaceLookupSlot dst st' = .ok (child, st') ∧
      child.target = parent.target ∧
      (∀ right, right ∈ child.rights → right ∈ parent.rights) := by
  rcases cspaceMint_child_attenuates st st' src dst rights badge hStep with
    ⟨parent, child, hSrc, hDst, hAtt⟩
  exact ⟨parent, child, hSrc, hDst, hAtt.1, hAtt.2⟩

-- ============================================================================
-- WS-E2 / H-03: Badge/notification routing consistency
-- ============================================================================

/-- (H-03) `mintDerivedCap` propagates the explicitly provided badge to the
derived capability when rights are sufficient. -/
theorem mintDerivedCap_badge_propagated
    (parent : Capability) (rights : List AccessRight) (badge : Option SeLe4n.Badge)
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
    (rights : List AccessRight)
    (badge : SeLe4n.Badge)
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
          have hDst := cspaceInsertSlot_lookup_eq st st' dst child hStep
          refine ⟨child, hDst, ?_⟩
          unfold mintDerivedCap at hMint
          by_cases hRights : rightsSubset rights parent.rights
          · simp [hRights] at hMint; cases hMint; rfl
          · simp [hRights] at hMint

/-- (H-03) When a notification has no waiters and no pending badge, signaling with badge `b`
stores exactly `b` as the pending badge. -/
theorem notificationSignal_badge_stored_fresh
    (st st' : SystemState)
    (notifId : SeLe4n.ObjId)
    (badge : SeLe4n.Badge)
    (ntfn : Notification)
    (hObj : st.objects notifId = some (.notification ntfn))
    (hNoWaiters : ntfn.waitingThreads = [])
    (hNoPending : ntfn.pendingBadge = none)
    (hSignal : notificationSignal notifId badge st = .ok ((), st')) :
    ∃ ntfn',
      st'.objects notifId = some (.notification ntfn') ∧
      ntfn'.pendingBadge = some badge := by
  unfold notificationSignal at hSignal
  simp [hObj, hNoWaiters, hNoPending] at hSignal
  exact ⟨{ state := .active, waitingThreads := [], pendingBadge := some badge },
    by rw [← storeObject_objects_eq st st' notifId _ hSignal], rfl⟩

/-- (H-03) When `notificationWait` returns `some badge`, that badge was the pending
badge of the notification object in the pre-state. -/
theorem notificationWait_recovers_pending_badge
    (st st' : SystemState)
    (notifId : SeLe4n.ObjId)
    (waiter : SeLe4n.ThreadId)
    (badge : SeLe4n.Badge)
    (hWait : notificationWait notifId waiter st = .ok (some badge, st')) :
    ∃ ntfn,
      st.objects notifId = some (.notification ntfn) ∧
      ntfn.pendingBadge = some badge := by
  unfold notificationWait at hWait
  cases hObj : st.objects notifId with
  | none => simp [hObj] at hWait
  | some obj =>
      cases obj with
      | notification ntfn =>
          refine ⟨ntfn, rfl, ?_⟩
          simp only [hObj] at hWait
          cases hPending : ntfn.pendingBadge with
          | none =>
              exfalso; simp only [hPending] at hWait
              split at hWait
              · simp at hWait
              · revert hWait
                cases hStore : storeObject notifId _ st with
                | error e => simp
                | ok pair =>
                    simp only []
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
      | tcb _ | endpoint _ | cnode _ | vspaceRoot _ => simp [hObj] at hWait

/-- (H-03) End-to-end badge routing consistency.

Composition of badge preservation through the full minting → signaling → waiting
path. When a capability is minted with explicit badge `b`, and that badge is
signaled to an idle notification, and a waiter collects the notification, the
recovered badge is exactly `b`. This closes the H-03 badge-override safety gap. -/
theorem badge_notification_routing_consistent
    (st₁ st₂ st₃ st₄ : SystemState)
    (src dst : CSpaceAddr)
    (rights : List AccessRight)
    (badge : SeLe4n.Badge)
    (notifId : SeLe4n.ObjId)
    (waiter : SeLe4n.ThreadId)
    (ntfn : Notification)
    (_hMint : cspaceMint src dst rights (some badge) st₁ = .ok ((), st₂))
    (hNtfnObj : st₂.objects notifId = some (.notification ntfn))
    (hNoWaiters : ntfn.waitingThreads = [])
    (hNoPending : ntfn.pendingBadge = none)
    (hSignal : notificationSignal notifId badge st₂ = .ok ((), st₃))
    (recoveredBadge : SeLe4n.Badge)
    (hWait : notificationWait notifId waiter st₃ = .ok (some recoveredBadge, st₄)) :
    recoveredBadge = badge := by
  rcases notificationSignal_badge_stored_fresh st₂ st₃ notifId badge ntfn
    hNtfnObj hNoWaiters hNoPending hSignal with ⟨ntfn', hNtfn'Obj, hNtfn'Badge⟩
  rcases notificationWait_recovers_pending_badge st₃ st₄ notifId waiter recoveredBadge hWait
    with ⟨ntfn'', hNtfn''Obj, hNtfn''Badge⟩
  rw [hNtfn'Obj] at hNtfn''Obj
  cases hNtfn''Obj
  rw [hNtfn'Badge] at hNtfn''Badge
  exact (Option.some.inj hNtfn''Badge).symm

/-- (H-03) Badge OR-merge is idempotent — signaling the same badge twice yields the same
pending badge as signaling it once (since `b ||| b = b` for bitwise OR). -/
theorem badge_merge_idempotent
    (badge : SeLe4n.Badge) :
    SeLe4n.Badge.ofNat (badge.toNat ||| badge.toNat) = badge := by
  simp [Nat.or_self, SeLe4n.Badge.ofNat, SeLe4n.Badge.toNat]

-- ============================================================================
-- WS-E2 / C-01: Derivation infrastructure for reformulated invariants
-- ============================================================================

/-- Derive `cspaceLookupSound` from `cspaceSlotUnique` for any state.

This bridge theorem connects the two reformulated invariant components: lookup
completeness follows from slot-index uniqueness because `CNode.mem_lookup_of_slotsUnique`
requires uniqueness to guarantee that `find?` returns the expected entry. -/
theorem cspaceLookupSound_of_cspaceSlotUnique
    (st : SystemState) (hUniq : cspaceSlotUnique st) :
    cspaceLookupSound st := by
  intro cnodeId cn slot cap hObj hMem
  have hU := hUniq cnodeId cn hObj
  simp [SystemState.lookupSlotCap, SystemState.lookupCNode, hObj]
  exact CNode.mem_lookup_of_slotsUnique cn slot cap hU hMem

/-- WS-E2 / H-01: Transfer `cspaceSlotUnique` across a non-CNode `storeObject`.

When `storeObject` writes a non-CNode object, all CNode entries in the store are
preserved from the pre-state and uniqueness transfers directly. -/
theorem cspaceSlotUnique_of_storeObject_nonCNode
    (st st' : SystemState) (oid : SeLe4n.ObjId) (obj : KernelObject)
    (hUniq : cspaceSlotUnique st)
    (hStore : storeObject oid obj st = .ok ((), st'))
    (hNotCNode : ∀ cn, obj ≠ .cnode cn) :
    cspaceSlotUnique st' := by
  intro cnodeId cn hObj
  by_cases hEq : cnodeId = oid
  · rw [hEq] at hObj
    have hEqObj := storeObject_objects_eq st st' oid obj hStore
    rw [hEqObj] at hObj
    have : obj = .cnode cn := by injection hObj
    exact absurd this (hNotCNode cn)
  · have hPre := storeObject_objects_ne st st' oid cnodeId obj hEq hStore
    rw [hPre] at hObj
    exact hUniq cnodeId cn hObj

/-- WS-E2 / H-01: Transfer `cspaceSlotUnique` across a CNode `storeObject`,
given that the new CNode satisfies `slotsUnique`. -/
theorem cspaceSlotUnique_of_storeObject_cnode
    (st st' : SystemState) (oid : SeLe4n.ObjId) (cn' : CNode)
    (hUniq : cspaceSlotUnique st)
    (hStore : storeObject oid (.cnode cn') st = .ok ((), st'))
    (hNewUniq : cn'.slotsUnique) :
    cspaceSlotUnique st' := by
  intro cnodeId cn hObj
  by_cases hEq : cnodeId = oid
  · subst hEq
    have := storeObject_objects_eq st st' cnodeId (.cnode cn') hStore
    rw [this] at hObj
    cases hObj
    exact hNewUniq
  · have hPre := storeObject_objects_ne st st' oid cnodeId (.cnode cn') hEq hStore
    rw [hPre] at hObj
    exact hUniq cnodeId cn hObj

/-- WS-E2 / H-01: Transfer `cspaceSlotUnique` across endpoint-object stores. -/
theorem cspaceSlotUnique_of_endpoint_store
    (st st' : SystemState) (oid : SeLe4n.ObjId) (ep : Endpoint)
    (hUniq : cspaceSlotUnique st)
    (hStore : storeObject oid (.endpoint ep) st = .ok ((), st')) :
    cspaceSlotUnique st' :=
  cspaceSlotUnique_of_storeObject_nonCNode st st' oid (.endpoint ep) hUniq hStore
    (fun cn h => by cases h)

/-- WS-E2 / H-01: Transfer `cspaceSlotUnique` when objects are unchanged. -/
theorem cspaceSlotUnique_of_objects_eq
    (st st' : SystemState)
    (hUniq : cspaceSlotUnique st)
    (hObjEq : st'.objects = st.objects) :
    cspaceSlotUnique st' := by
  intro cnodeId cn hObj
  exact hUniq cnodeId cn (by rwa [hObjEq] at hObj)

theorem cspaceAttenuationRule_holds :
    cspaceAttenuationRule := by
  intro parent child rights badge hMint
  exact mintDerivedCap_attenuates parent child rights badge hMint


theorem lifecycleAuthorityMonotonicity_holds (st : SystemState) :
    lifecycleAuthorityMonotonicity st := by
  refine ⟨?_, ?_⟩
  · intro addr st' hDelete
    exact cspaceDeleteSlot_authority_reduction st st' addr hDelete
  · intro addr st' parent hRevoke hParent slot cap hLookup hTarget
    exact cspaceRevoke_local_target_reduction st st' addr parent hRevoke hParent slot cap hLookup hTarget

/-- Establish the capability invariant bundle from a slot-index uniqueness witness.
Unlike the prior tautological version, this requires a genuine hypothesis:
the caller must supply evidence that all CNodes have unique slot keys.
(WS-E2 / C-01 + H-01 remediation) -/
theorem capabilityInvariantBundle_of_slotUnique
    (st : SystemState)
    (hUnique : cspaceSlotUnique st) :
    capabilityInvariantBundle st :=
  ⟨hUnique, cspaceLookupSound_of_cspaceSlotUnique st hUnique, cspaceAttenuationRule_holds,
    lifecycleAuthorityMonotonicity_holds st⟩

end SeLe4n.Kernel
