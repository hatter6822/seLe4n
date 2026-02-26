import SeLe4n.Kernel.IPC.Invariant
import SeLe4n.Kernel.Lifecycle.Invariant

/-!
# Capability Invariant Preservation Proofs (M2)

This module defines the capability invariant components, the composed bundle entrypoint,
and transition-level preservation theorems for CSpace operations. It also contains
cross-subsystem composed bundles (M3, M3.5, M4-A).

## Proof scope qualification (F-16, WS-E2 C-01/H-01/H-03)

**Non-trivial invariant components** (WS-E2 / C-01 — reformulated from tautological):
- `cspaceSlotUnique`: CNode slot-index uniqueness — each slot index maps to at most
  one capability within every CNode in the system state. This is a structural invariant
  that depends on `CNode.insert` removing duplicates before prepending.
- `cspaceLookupSound`: Lookup completeness — every capability entry in a CNode's slot
  list is retrievable via `lookupSlotCap`. This property is non-trivial because
  `List.find?` returns only the first match; it requires `cspaceSlotUnique` to hold.

**Compositional preservation proofs** (WS-E2 / H-01 — refactored from re-prove):
All preservation proofs now derive post-state invariant components from pre-state
components through the operation's specific state transformation. For CNode-modifying
operations, the proof traces CNode slot-index uniqueness through `CNode.insert_slotsUnique`,
`CNode.remove_slotsUnique`, or `CNode.revokeTargetLocal_slotsUnique`. For operations that
don't modify CNodes, the proof uses object-store frame conditions to transfer the
pre-state invariant directly.

**Badge/notification routing consistency** (WS-E2 / H-03):
- `mintDerivedCap_badge_propagated`: badge faithfully stored in minted capability
- `cspaceMint_child_badge_preserved`: operation-level badge consistency
- `notificationSignal_badge_stored_fresh`: badge stored in notification
- `notificationWait_recovers_pending_badge`: badge delivered to waiter
- `badge_notification_routing_consistent`: end-to-end chain
- `badge_merge_idempotent`: badge OR-merge idempotency

**Substantive preservation theorems** (high assurance — prove invariant preservation
over *changed* state after a *successful* operation, using pre-state invariant
components compositionally):
- `cspaceMint_preserves_capabilityInvariantBundle`
- `cspaceInsertSlot_preserves_capabilityInvariantBundle`
- `cspaceDeleteSlot_preserves_capabilityInvariantBundle`
- `cspaceRevoke_preserves_capabilityInvariantBundle`
- `lifecycleRetypeObject_preserves_capabilityInvariantBundle`
- `lifecycleRevokeDeleteRetype_preserves_capabilityInvariantBundle`
- all `endpointSend/AwaitReceive/Receive_preserves_capabilityInvariantBundle`
- composed bundle preservation theorems (`m3IpcSeed`, `m35`, `m4a`)

**Badge-override safety theorems** (high assurance — F-06 / TPI-D04):
- `mintDerivedCap_rights_attenuated_with_badge_override`
- `mintDerivedCap_target_preserved_with_badge_override`
- `cspaceMint_badge_override_safe`

**Structural / functional-correctness theorems** (high assurance):
- `mintDerivedCap_attenuates`
- `cspaceMint_child_attenuates`
- `cspaceDeleteSlot_authority_reduction`
- `cspaceRevoke_local_target_reduction`
- `cspaceRevoke_preserves_source`

**Error-case preservation theorems** (trivially true — the error path returns
unchanged state, so any pre-state invariant holds trivially in the post-state):
- `lifecycleRevokeDeleteRetype_error_preserves_m4aLifecycleInvariantBundle`
- `cspaceLookupSlot_preserves_capabilityInvariantBundle` (read-only, no mutation)

Error-case theorems are retained for proof-surface completeness and compositional
coverage, but they do not constitute meaningful security evidence.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- CNode slot-index uniqueness across all CNodes in the system state.

WS-E2 / C-01 reformulation: this is a non-trivial structural invariant. Each slot
index within a CNode maps to at most one capability. Without this, `CNode.lookup`
(which uses `List.find?`) could return a different capability than what was stored
at a given slot index, because `find?` returns only the first match.

This invariant is maintained by `CNode.insert` (which removes the old entry before
prepending), `CNode.remove` (which only filters), and `CNode.revokeTargetLocal`
(which only filters). -/
def cspaceSlotUnique (st : SystemState) : Prop :=
  ∀ cnodeId cn,
    st.objects cnodeId = some (.cnode cn) →
    cn.slotsUnique

/-- Lookup completeness: every capability entry in a CNode's slot list is retrievable
via `lookupSlotCap`.

WS-E2 / C-01 reformulation: this is non-trivial because `CNode.lookup` uses
`List.find?`, which returns only the first match for a given slot index. If duplicate
slot indices existed (violating `cspaceSlotUnique`), later entries would be
unretrievable. This property holds if and only if `cspaceSlotUnique` holds. -/
def cspaceLookupSound (st : SystemState) : Prop :=
  ∀ cnodeId cn slot cap,
    st.objects cnodeId = some (.cnode cn) →
    (slot, cap) ∈ cn.slots →
    SystemState.lookupSlotCap st { cnode := cnodeId, slot := slot } = some cap

/-- Attenuation rule component used by the M2 capability invariant bundle. -/
def cspaceAttenuationRule : Prop :=
  ∀ parent child rights badge,
    mintDerivedCap parent rights badge = .ok child →
    capAttenuates parent child

/-- Lifecycle-transition authority monotonicity obligations for the active slice.

This models transition-local non-escalation constraints:
1. delete cannot leave authority in the deleted slot,
2. local revoke cannot leave sibling authority to the revoked target.

Direct mint/derive attenuation remains the dedicated `cspaceAttenuationRule` bundle component. -/
def lifecycleAuthorityMonotonicity (st : SystemState) : Prop :=
  (∀ addr st',
      cspaceDeleteSlot addr st = .ok ((), st') →
      SystemState.lookupSlotCap st' addr = none) ∧
  (∀ addr st' parent,
      cspaceRevoke addr st = .ok ((), st') →
      cspaceLookupSlot addr st = .ok (parent, st) →
      ∀ slot cap,
        SystemState.lookupSlotCap st' { cnode := addr.cnode, slot := slot } = some cap →
        cap.target = parent.target →
        slot = addr.slot)

/-- Composed capability invariant bundle entrypoint.

The active lifecycle slice extends the M2 foundation bundle with explicit lifecycle-transition
authority obligations (`delete`/`revoke`) so lifecycle preservation can be stated against a
single invariant entrypoint. -/
def capabilityInvariantBundle (st : SystemState) : Prop :=
  cspaceSlotUnique st ∧ cspaceLookupSound st ∧ cspaceAttenuationRule ∧
    lifecycleAuthorityMonotonicity st

/-- M4-B bridge bundle: ties stale-reference exclusion to lifecycle transition authority
monotonicity so composition proofs can depend on a single named assumption. -/
def lifecycleCapabilityStaleAuthorityInvariant (st : SystemState) : Prop :=
  lifecycleStaleReferenceExclusionInvariant st ∧ lifecycleAuthorityMonotonicity st

theorem lifecycleCapabilityStaleAuthorityInvariant_of_bundles
    (st : SystemState)
    (hLifecycle : lifecycleInvariantBundle st)
    (hCap : capabilityInvariantBundle st) :
    lifecycleCapabilityStaleAuthorityInvariant st := by
  refine ⟨lifecycleStaleReferenceExclusionInvariant_of_lifecycleInvariantBundle st hLifecycle, ?_⟩
  exact hCap.2.2.2

/-- Delete transition authority reduction clause. -/
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
          cases hLookupGuard : cn.lookup slot with
          | some _ => simp [hLookupGuard] at hStep
          | none =>
              simp [hLookupGuard] at hStep
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
private theorem cspaceSlotUnique_of_endpoint_store
    (st st' : SystemState) (oid : SeLe4n.ObjId) (ep : Endpoint)
    (hUniq : cspaceSlotUnique st)
    (hStore : storeObject oid (.endpoint ep) st = .ok ((), st')) :
    cspaceSlotUnique st' :=
  cspaceSlotUnique_of_storeObject_nonCNode st st' oid (.endpoint ep) hUniq hStore
    (fun cn h => by cases h)

/-- WS-E2 / H-01: Transfer `cspaceSlotUnique` when objects are unchanged. -/
private theorem cspaceSlotUnique_of_objects_eq
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

theorem cspaceLookupSlot_preserves_capabilityInvariantBundle
    (st st' : SystemState)
    (addr : CSpaceAddr)
    (cap : Capability)
    (hInv : capabilityInvariantBundle st)
    (hStep : cspaceLookupSlot addr st = .ok (cap, st')) :
    capabilityInvariantBundle st' := by
  have hEq : st' = st := cspaceLookupSlot_preserves_state st st' addr cap hStep
  subst hEq
  simpa using hInv

/-- WS-E2 / H-01: Compositional preservation of `cspaceInsertSlot`.
Uses pre-state `cspaceSlotUnique` + `CNode.insert_slotsUnique` to derive post-state
uniqueness, rather than re-proving from scratch. -/
theorem cspaceInsertSlot_preserves_capabilityInvariantBundle
    (st st' : SystemState)
    (addr : CSpaceAddr)
    (cap : Capability)
    (hInv : capabilityInvariantBundle st)
    (hStep : cspaceInsertSlot addr cap st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  rcases hInv with ⟨hUnique, _hSound, hAttRule, _hLifecycle⟩
  -- Compositionally derive post-state uniqueness (WS-E2 / H-01)
  have hUnique' : cspaceSlotUnique st' := by
    intro cnodeId cn hObj
    by_cases hEq : cnodeId = addr.cnode
    · -- Modified CNode: derive uniqueness via CNode.insert_slotsUnique
      unfold cspaceInsertSlot at hStep
      rw [hEq] at hObj
      cases hPre : st.objects addr.cnode with
      | none => simp [hPre] at hStep
      | some preObj =>
        cases preObj with
        | tcb _ | endpoint _ | notification _ | vspaceRoot _ => simp [hPre] at hStep
        | cnode preCn =>
          simp [hPre] at hStep
          -- WS-E4/H-02: case split on occupied-slot guard
          cases hLookup : preCn.lookup addr.slot with
          | some _ => simp [hLookup] at hStep
          | none =>
            simp [hLookup] at hStep
            cases hStore : storeObject addr.cnode (.cnode (preCn.insert addr.slot cap)) st with
            | error e => cases hStore
            | ok pair =>
              obtain ⟨_, stMid⟩ := pair
              simp [hStore] at hStep
              have hObjRef := storeCapabilityRef_preserves_objects stMid st' addr (some cap.target) hStep
              have hObjMid := storeObject_objects_eq st stMid addr.cnode
                (.cnode (preCn.insert addr.slot cap)) hStore
              have hFinal : st'.objects addr.cnode = some (.cnode (preCn.insert addr.slot cap)) := by
                rw [← hObjMid]; exact congrFun hObjRef addr.cnode
              rw [hFinal] at hObj; cases hObj
              exact CNode.insert_slotsUnique preCn addr.slot cap (hUnique addr.cnode preCn hPre)
    · -- Unmodified CNodes: transfer directly from pre-state
      have hPreObj := cspaceInsertSlot_preserves_objects_ne st st' addr cap cnodeId hEq hStep
      rw [hPreObj] at hObj
      exact hUnique cnodeId cn hObj
  exact ⟨hUnique', cspaceLookupSound_of_cspaceSlotUnique st' hUnique', hAttRule,
    lifecycleAuthorityMonotonicity_holds st'⟩

theorem cspaceMint_preserves_capabilityInvariantBundle
    (st st' : SystemState)
    (src dst : CSpaceAddr)
    (rights : List AccessRight)
    (badge : Option SeLe4n.Badge)
    (hInv : capabilityInvariantBundle st)
    (hStep : cspaceMint src dst rights badge st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
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
          have hInsert : cspaceInsertSlot dst child st = .ok ((), st') := by
            simpa [hSrc, hMint] using hStep
          exact cspaceInsertSlot_preserves_capabilityInvariantBundle st st' dst child hInv hInsert

/-- WS-E2 / H-01: Compositional preservation of `cspaceDeleteSlot`.
Uses pre-state `cspaceSlotUnique` + `CNode.remove_slotsUnique` to derive post-state
uniqueness. -/
theorem cspaceDeleteSlot_preserves_capabilityInvariantBundle
    (st st' : SystemState)
    (addr : CSpaceAddr)
    (hInv : capabilityInvariantBundle st)
    (hStep : cspaceDeleteSlot addr st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  rcases hInv with ⟨hUnique, _hSound, hAttRule, _hLifecycle⟩
  have hUnique' : cspaceSlotUnique st' := by
    intro cnodeId cn hObj
    unfold cspaceDeleteSlot at hStep
    cases hPre : st.objects addr.cnode with
    | none => simp [hPre] at hStep
    | some preObj =>
      cases preObj with
      | tcb _ | endpoint _ | notification _ | vspaceRoot _ => simp [hPre] at hStep
      | cnode preCn =>
        simp [hPre] at hStep
        cases hStore : storeObject addr.cnode (.cnode (preCn.remove addr.slot)) st with
        | error e => cases hStore
        | ok pair =>
          obtain ⟨_, stMid⟩ := pair
          simp [hStore] at hStep
          have hObjRef := storeCapabilityRef_preserves_objects stMid st' addr none hStep
          by_cases hEq : cnodeId = addr.cnode
          · rw [hEq] at hObj
            have hObjMid := storeObject_objects_eq st stMid addr.cnode
              (.cnode (preCn.remove addr.slot)) hStore
            have : st'.objects addr.cnode = some (.cnode (preCn.remove addr.slot)) := by
              rw [← hObjMid]; exact congrFun hObjRef addr.cnode
            rw [this] at hObj; cases hObj
            exact CNode.remove_slotsUnique preCn addr.slot (hUnique addr.cnode preCn hPre)
          · have hObjMid := storeObject_objects_ne st stMid addr.cnode cnodeId
              (.cnode (preCn.remove addr.slot)) hEq hStore
            have : st'.objects cnodeId = st.objects cnodeId := by
              rw [← hObjMid]; exact congrFun hObjRef cnodeId
            rw [this] at hObj
            exact hUnique cnodeId cn hObj
  exact ⟨hUnique', cspaceLookupSound_of_cspaceSlotUnique st' hUnique', hAttRule,
    lifecycleAuthorityMonotonicity_holds st'⟩

/-- WS-E2 / H-01: Compositional preservation of `cspaceRevoke`.
Uses pre-state `cspaceSlotUnique` + `CNode.revokeTargetLocal_slotsUnique` to derive
post-state uniqueness. -/
theorem cspaceRevoke_preserves_capabilityInvariantBundle
    (st st' : SystemState)
    (addr : CSpaceAddr)
    (hInv : capabilityInvariantBundle st)
    (hStep : cspaceRevoke addr st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  rcases hInv with ⟨hUnique, _hSound, hAttRule, _hLifecycle⟩
  have hUnique' : cspaceSlotUnique st' := by
    intro cnodeId cn hObj
    unfold cspaceRevoke at hStep
    cases hLookup : cspaceLookupSlot addr st with
    | error e => simp [hLookup] at hStep
    | ok pair =>
      rcases pair with ⟨parent, st1⟩
      have hSt1 : st1 = st := cspaceLookupSlot_preserves_state st st1 addr parent hLookup
      subst st1
      cases hPre : st.objects addr.cnode with
      | none => simp [hLookup, hPre] at hStep
      | some preObj =>
        cases preObj with
        | tcb _ | endpoint _ | notification _ | vspaceRoot _ => simp [hLookup, hPre] at hStep
        | cnode preCn =>
          simp [hLookup, hPre] at hStep
          cases hStore : storeObject addr.cnode
            (.cnode (preCn.revokeTargetLocal addr.slot parent.target)) st with
          | error e => cases hStore
          | ok pair =>
            obtain ⟨_, stMid⟩ := pair
            simp [hStore] at hStep
            have hObjRef := clearCapabilityRefs_preserves_objects stMid st' _ hStep
            by_cases hEq : cnodeId = addr.cnode
            · rw [hEq] at hObj
              have hObjMid := storeObject_objects_eq st stMid addr.cnode
                (.cnode (preCn.revokeTargetLocal addr.slot parent.target)) hStore
              have : st'.objects addr.cnode =
                  some (.cnode (preCn.revokeTargetLocal addr.slot parent.target)) := by
                rw [← hObjMid]; exact congrFun hObjRef addr.cnode
              rw [this] at hObj; cases hObj
              exact CNode.revokeTargetLocal_slotsUnique preCn addr.slot parent.target
                (hUnique addr.cnode preCn hPre)
            · have hObjMid := storeObject_objects_ne st stMid addr.cnode cnodeId
                (.cnode (preCn.revokeTargetLocal addr.slot parent.target)) hEq hStore
              have : st'.objects cnodeId = st.objects cnodeId := by
                rw [← hObjMid]; exact congrFun hObjRef cnodeId
              rw [this] at hObj
              exact hUnique cnodeId cn hObj
  exact ⟨hUnique', cspaceLookupSound_of_cspaceSlotUnique st' hUnique', hAttRule,
    lifecycleAuthorityMonotonicity_holds st'⟩

-- ============================================================================
-- WS-E4/C-02: Preservation theorems for new capability operations
-- ============================================================================

/-- WS-E4/C-02: cspaceCopy preserves capabilityInvariantBundle.
Copy composes cspaceLookupSlot + cspaceInsertSlot, both of which preserve the bundle,
plus a CDT update that only touches the cdt field. -/
theorem cspaceCopy_preserves_capabilityInvariantBundle
    (st st' : SystemState)
    (src dst : CSpaceAddr)
    (hInv : capabilityInvariantBundle st)
    (hStep : cspaceCopy src dst st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  unfold cspaceCopy at hStep
  cases hSrc : cspaceLookupSlot src st with
  | error e => simp [hSrc] at hStep
  | ok pair =>
      rcases pair with ⟨cap, st1⟩
      have hSt1 : st1 = st := cspaceLookupSlot_preserves_state st st1 src cap hSrc
      subst st1
      cases hInsert : cspaceInsertSlot dst cap st with
      | error e => simp [hSrc, hInsert] at hStep
      | ok pair2 =>
          rcases pair2 with ⟨_, st2⟩
          simp [hSrc, hInsert] at hStep
          cases hStep
          -- st' = { st2 with cdt := ... }, capabilityInvariantBundle only depends on objects/lifecycle
          have hBundleSt2 := cspaceInsertSlot_preserves_capabilityInvariantBundle st st2 dst cap hInv hInsert
          -- CDT update doesn't change objects; extract cspaceSlotUnique and reconstruct bundle
          rcases hBundleSt2 with ⟨hU2, _, hAtt2, _⟩
          exact ⟨hU2, cspaceLookupSound_of_cspaceSlotUnique _ hU2, hAtt2,
            lifecycleAuthorityMonotonicity_holds _⟩

/-- WS-E4/C-02: cspaceMove preserves capabilityInvariantBundle.
Move composes lookup + insert + delete, all of which preserve the bundle. -/
theorem cspaceMove_preserves_capabilityInvariantBundle
    (st st' : SystemState)
    (src dst : CSpaceAddr)
    (hInv : capabilityInvariantBundle st)
    (hStep : cspaceMove src dst st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  unfold cspaceMove at hStep
  cases hSrc : cspaceLookupSlot src st with
  | error e => simp [hSrc] at hStep
  | ok pair =>
      rcases pair with ⟨cap, st1⟩
      have hSt1 : st1 = st := cspaceLookupSlot_preserves_state st st1 src cap hSrc
      subst st1
      cases hInsert : cspaceInsertSlot dst cap st with
      | error e => simp [hSrc, hInsert] at hStep
      | ok pair2 =>
          rcases pair2 with ⟨_, st2⟩
          cases hDelete : cspaceDeleteSlot src st2 with
          | error e => simp [hSrc, hInsert, hDelete] at hStep
          | ok pair3 =>
              rcases pair3 with ⟨_, st3⟩
              simp [hSrc, hInsert, hDelete] at hStep
              cases hStep
              have hBundleSt2 := cspaceInsertSlot_preserves_capabilityInvariantBundle st st2 dst cap hInv hInsert
              have hBundleSt3 := cspaceDeleteSlot_preserves_capabilityInvariantBundle st2 st3 src hBundleSt2 hDelete
              -- CDT reparent doesn't change objects; extract cspaceSlotUnique and reconstruct
              rcases hBundleSt3 with ⟨hU3, _, hAtt3, _⟩
              exact ⟨hU3, cspaceLookupSound_of_cspaceSlotUnique _ hU3, hAtt3,
                lifecycleAuthorityMonotonicity_holds _⟩

/-- WS-E4/C-03: cspaceMintWithCdt preserves capabilityInvariantBundle.
Composes cspaceMint (already proven) + CDT edge addition. -/
theorem cspaceMintWithCdt_preserves_capabilityInvariantBundle
    (st st' : SystemState)
    (src dst : CSpaceAddr)
    (rights : List AccessRight)
    (badge : Option SeLe4n.Badge)
    (hInv : capabilityInvariantBundle st)
    (hStep : cspaceMintWithCdt src dst rights badge st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  unfold cspaceMintWithCdt at hStep
  cases hMint : cspaceMint src dst rights badge st with
  | error e => simp [hMint] at hStep
  | ok pair =>
      rcases pair with ⟨_, st1⟩
      simp [hMint] at hStep
      cases hStep
      -- CDT addEdge doesn't change objects; extract cspaceSlotUnique and reconstruct
      have hBundle := cspaceMint_preserves_capabilityInvariantBundle st st1 src dst rights badge hInv hMint
      rcases hBundle with ⟨hU1, _, hAtt1, _⟩
      exact ⟨hU1, cspaceLookupSound_of_cspaceSlotUnique _ hU1, hAtt1,
        lifecycleAuthorityMonotonicity_holds _⟩

-- ============================================================================
-- WS-E4: Preservation theorems for endpointReply
-- ============================================================================

/-- WS-E4/M-12: endpointReply preserves capabilityInvariantBundle.
Reply stores a TCB (not a CNode), so CSpace invariants are preserved. -/
theorem endpointReply_preserves_capabilityInvariantBundle
    (st st' : SystemState)
    (target : SeLe4n.ThreadId)
    (hInv : capabilityInvariantBundle st)
    (hStep : endpointReply target st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  rcases hInv with ⟨hUnique, _hSound, hAttRule, _hLifecycle⟩
  unfold endpointReply at hStep
  cases hLookup : lookupTcb st target with
  | none => simp [hLookup] at hStep
  | some tcb =>
      simp [hLookup] at hStep
      cases hIpc : tcb.ipcState with
      | ready => simp [hIpc] at hStep
      | blockedOnSend _ => simp [hIpc] at hStep
      | blockedOnReceive _ => simp [hIpc] at hStep
      | blockedOnNotification _ => simp [hIpc] at hStep
      | blockedOnReply epId =>
          simp [hIpc] at hStep
          cases hTcb : storeTcbIpcState st target .ready with
          | error e => simp [hTcb] at hStep
          | ok st1 =>
              simp [hTcb] at hStep; cases hStep
              -- storeTcbIpcState only writes TCBs, so CNode objects are unchanged
              have hU1 : cspaceSlotUnique st1 := by
                intro cnodeId cn hCn1
                exact hUnique cnodeId cn (storeTcbIpcState_cnode_backward st st1 target .ready cnodeId cn hTcb hCn1)
              have hU := cspaceSlotUnique_of_objects_eq st1 (ensureRunnable st1 target)
                hU1 (ensureRunnable_preserves_objects st1 target)
              exact ⟨hU, cspaceLookupSound_of_cspaceSlotUnique _ hU, hAttRule,
                lifecycleAuthorityMonotonicity_holds _⟩

/-- M3 composed bundle entrypoint: M1 scheduler + M2 capability + M3 IPC. -/
def m3IpcSeedInvariantBundle (st : SystemState) : Prop :=
  schedulerInvariantBundle st ∧ capabilityInvariantBundle st ∧ ipcInvariant st

/-- Named M3.5 coherence component: runnable threads stay IPC-ready. -/
def ipcSchedulerRunnableReadyComponent (st : SystemState) : Prop :=
  runnableThreadIpcReady st

/-- Named M3.5 coherence component: send-blocked threads are not runnable. -/
def ipcSchedulerBlockedSendComponent (st : SystemState) : Prop :=
  blockedOnSendNotRunnable st

/-- Named M3.5 coherence component: receive-blocked threads are not runnable. -/
def ipcSchedulerBlockedReceiveComponent (st : SystemState) : Prop :=
  blockedOnReceiveNotRunnable st

/-- Named M3.5 aggregate coherence component for IPC+scheduler interaction. -/
def ipcSchedulerCoherenceComponent (st : SystemState) : Prop :=
  ipcSchedulerRunnableReadyComponent st ∧
  ipcSchedulerBlockedSendComponent st ∧
  ipcSchedulerBlockedReceiveComponent st

theorem ipcSchedulerCoherenceComponent_iff_contractPredicates (st : SystemState) :
    ipcSchedulerCoherenceComponent st ↔ ipcSchedulerContractPredicates st := by
  rfl

/-- M3.5 composed bundle entrypoint layered over the M3 IPC seed bundle.

This is the step-4 composition target for active-slice endpoint/scheduler coupling. -/
def m35IpcSchedulerInvariantBundle (st : SystemState) : Prop :=
  m3IpcSeedInvariantBundle st ∧ ipcSchedulerCoherenceComponent st

/-- M4-A composed bundle entrypoint:
M3.5 IPC+scheduler composition plus lifecycle metadata/invariant obligations. -/
def m4aLifecycleInvariantBundle (st : SystemState) : Prop :=
  m35IpcSchedulerInvariantBundle st ∧ lifecycleInvariantBundle st

theorem lifecycleRetypeObject_preserves_schedulerInvariantBundle
    (st st' : SystemState)
    (authority : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj : KernelObject)
    (hInv : schedulerInvariantBundle st)
    (hCurrentValid : currentThreadValid st')
    (hStep : lifecycleRetypeObject authority target newObj st = .ok ((), st')) :
    schedulerInvariantBundle st' := by
  rcases lifecycleRetypeObject_ok_as_storeObject st st' authority target newObj hStep with
    ⟨_, _, _, _, _, _, hStore⟩
  have hSchedEq : st'.scheduler = st.scheduler :=
    lifecycle_storeObject_scheduler_eq st st' target newObj hStore
  rcases hInv with ⟨hQueue, hRunUnique, _hCurrent⟩
  exact ⟨by simpa [hSchedEq] using hQueue, by simpa [hSchedEq] using hRunUnique, hCurrentValid⟩

/-- WS-E2 / H-01: Compositional preservation of `lifecycleRetypeObject`.
Requires new CNode objects to have unique slots (analogous to existing
`hNewObjEndpointInv` / `hNewObjNotificationInv` side conditions on IPC proofs). -/
theorem lifecycleRetypeObject_preserves_capabilityInvariantBundle
    (st st' : SystemState)
    (authority : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj : KernelObject)
    (hInv : capabilityInvariantBundle st)
    (hNewObjCNodeUniq : ∀ cn, newObj = .cnode cn → cn.slotsUnique)
    (hStep : lifecycleRetypeObject authority target newObj st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  rcases hInv with ⟨hUnique, _hSound, hAttRule, _hLifecycle⟩
  have hUnique' : cspaceSlotUnique st' := by
    rcases lifecycleRetypeObject_ok_as_storeObject st st' authority target newObj hStep with
      ⟨_, _, _, _, _, _, hStore⟩
    intro cnodeId cn hObj
    by_cases hEq : cnodeId = target
    · rw [hEq] at hObj
      have hObjAtTarget := lifecycle_storeObject_objects_eq st st' target newObj hStore
      rw [hObjAtTarget] at hObj
      cases newObj with
      | cnode _ => cases hObj; exact hNewObjCNodeUniq cn rfl
      | tcb _ | endpoint _ | notification _ | vspaceRoot _ => cases hObj
    · have hPreserved := lifecycleRetypeObject_ok_lookup_preserved_ne st st' authority target
        cnodeId newObj hEq hStep
      rw [hPreserved] at hObj
      exact hUnique cnodeId cn hObj
  exact ⟨hUnique', cspaceLookupSound_of_cspaceSlotUnique st' hUnique', hAttRule,
    lifecycleAuthorityMonotonicity_holds st'⟩

theorem lifecycleRetypeObject_preserves_ipcInvariant
    (st st' : SystemState)
    (authority : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj : KernelObject)
    (hInv : ipcInvariant st)
    (hNewObjEndpointInv : ∀ ep, newObj = .endpoint ep → endpointInvariant ep)
    (hNewObjNotificationInv : ∀ ntfn, newObj = .notification ntfn → notificationInvariant ntfn)
    (hStep : lifecycleRetypeObject authority target newObj st = .ok ((), st')) :
    ipcInvariant st' := by
  rcases hInv with ⟨hEndpointInv, hNotificationInv⟩
  refine ⟨?_, ?_⟩
  · intro oid ep hEndpoint
    by_cases hEq : oid = target
    · subst hEq
      have hObjAtTarget : st'.objects oid = some newObj := by
        rcases lifecycleRetypeObject_ok_as_storeObject st st' authority oid newObj hStep with
          ⟨_, _, _, _, _, _, hStore⟩
        exact lifecycle_storeObject_objects_eq st st' oid newObj hStore
      have hSomeEq : some newObj = some (.endpoint ep) := by
        simpa [hObjAtTarget] using hEndpoint
      have hNewObjEq : newObj = .endpoint ep := by
        injection hSomeEq
      exact hNewObjEndpointInv ep hNewObjEq
    · have hPreserved : st'.objects oid = st.objects oid :=
        lifecycleRetypeObject_ok_lookup_preserved_ne st st' authority target oid newObj hEq hStep
      have hEndpointSt : st.objects oid = some (.endpoint ep) := by simpa [hPreserved] using hEndpoint
      exact hEndpointInv oid ep hEndpointSt
  · intro oid ntfn hNtfn
    by_cases hEq : oid = target
    · subst hEq
      have hObjAtTarget : st'.objects oid = some newObj := by
        rcases lifecycleRetypeObject_ok_as_storeObject st st' authority oid newObj hStep with
          ⟨_, _, _, _, _, _, hStore⟩
        exact lifecycle_storeObject_objects_eq st st' oid newObj hStore
      have hSomeEq : some newObj = some (.notification ntfn) := by
        simpa [hObjAtTarget] using hNtfn
      have hNewObjEq : newObj = .notification ntfn := by
        injection hSomeEq
      exact hNewObjNotificationInv ntfn hNewObjEq
    · have hPreserved : st'.objects oid = st.objects oid :=
        lifecycleRetypeObject_ok_lookup_preserved_ne st st' authority target oid newObj hEq hStep
      have hNtfnSt : st.objects oid = some (.notification ntfn) := by simpa [hPreserved] using hNtfn
      exact hNotificationInv oid ntfn hNtfnSt

theorem lifecycleRetypeObject_preserves_m3IpcSeedInvariantBundle
    (st st' : SystemState)
    (authority : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj : KernelObject)
    (hInv : m3IpcSeedInvariantBundle st)
    (hNewObjEndpointInv : ∀ ep, newObj = .endpoint ep → endpointInvariant ep)
    (hNewObjNotificationInv : ∀ ntfn, newObj = .notification ntfn → notificationInvariant ntfn)
    (hNewObjCNodeUniq : ∀ cn, newObj = .cnode cn → cn.slotsUnique)
    (hCurrentValid : currentThreadValid st')
    (hStep : lifecycleRetypeObject authority target newObj st = .ok ((), st')) :
    m3IpcSeedInvariantBundle st' := by
  rcases hInv with ⟨hSched, hCap, hIpc⟩
  refine ⟨?_, ?_, ?_⟩
  · exact lifecycleRetypeObject_preserves_schedulerInvariantBundle st st' authority target newObj hSched
      hCurrentValid hStep
  · exact lifecycleRetypeObject_preserves_capabilityInvariantBundle st st' authority target newObj hCap
      hNewObjCNodeUniq hStep
  · exact lifecycleRetypeObject_preserves_ipcInvariant st st' authority target newObj hIpc hNewObjEndpointInv hNewObjNotificationInv hStep

theorem lifecycleRetypeObject_preserves_m4aLifecycleInvariantBundle
    (st st' : SystemState)
    (authority : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj : KernelObject)
    (hInv : m4aLifecycleInvariantBundle st)
    (hNewObjEndpointInv : ∀ ep, newObj = .endpoint ep → endpointInvariant ep)
    (hNewObjNotificationInv : ∀ ntfn, newObj = .notification ntfn → notificationInvariant ntfn)
    (hNewObjCNodeUniq : ∀ cn, newObj = .cnode cn → cn.slotsUnique)
    (hCurrentValid : currentThreadValid st')
    (hCoherence' : ipcSchedulerCoherenceComponent st')
    (hStep : lifecycleRetypeObject authority target newObj st = .ok ((), st')) :
    m4aLifecycleInvariantBundle st' := by
  rcases hInv with ⟨hM35, hLifecycle⟩
  rcases hM35 with ⟨hM3, _hCoherence⟩
  have hM3' : m3IpcSeedInvariantBundle st' :=
    lifecycleRetypeObject_preserves_m3IpcSeedInvariantBundle st st' authority target newObj hM3
      hNewObjEndpointInv hNewObjNotificationInv hNewObjCNodeUniq hCurrentValid hStep
  have hLifecycle' : lifecycleInvariantBundle st' :=
    SeLe4n.Kernel.lifecycleRetypeObject_preserves_lifecycleInvariantBundle st st' authority target
      newObj hLifecycle hStep
  exact ⟨⟨hM3', hCoherence'⟩, hLifecycle'⟩


theorem lifecycleRevokeDeleteRetype_preserves_capabilityInvariantBundle
    (st st' : SystemState)
    (authority cleanup : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj : KernelObject)
    (hInv : capabilityInvariantBundle st)
    (hNewObjCNodeUniq : ∀ cn, newObj = .cnode cn → cn.slotsUnique)
    (hStep : lifecycleRevokeDeleteRetype authority cleanup target newObj st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  rcases lifecycleRevokeDeleteRetype_ok_implies_staged_steps st st' authority cleanup target newObj hStep with
    ⟨stRevoked, stDeleted, _hNe, hRevoke, hDelete, _hLookupDeleted, hRetype⟩
  have hRevoked : capabilityInvariantBundle stRevoked :=
    cspaceRevoke_preserves_capabilityInvariantBundle st stRevoked cleanup hInv hRevoke
  have hDeleted : capabilityInvariantBundle stDeleted :=
    cspaceDeleteSlot_preserves_capabilityInvariantBundle stRevoked stDeleted cleanup hRevoked hDelete
  exact lifecycleRetypeObject_preserves_capabilityInvariantBundle stDeleted st' authority target newObj
    hDeleted hNewObjCNodeUniq hRetype

theorem lifecycleRevokeDeleteRetype_preserves_lifecycleCapabilityStaleAuthorityInvariant
    (st st' : SystemState)
    (authority cleanup : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj : KernelObject)
    (hCap : capabilityInvariantBundle st)
    (hNewObjCNodeUniq : ∀ cn, newObj = .cnode cn → cn.slotsUnique)
    (hLifecycleAfterCleanup :
      ∀ stRevoked stDeleted,
        cspaceRevoke cleanup st = .ok ((), stRevoked) →
        cspaceDeleteSlot cleanup stRevoked = .ok ((), stDeleted) →
        cspaceLookupSlot cleanup stDeleted = .error .invalidCapability →
        lifecycleInvariantBundle stDeleted)
    (hStep : lifecycleRevokeDeleteRetype authority cleanup target newObj st = .ok ((), st')) :
    lifecycleCapabilityStaleAuthorityInvariant st' := by
  rcases lifecycleRevokeDeleteRetype_ok_implies_staged_steps st st' authority cleanup target newObj hStep with
    ⟨stRevoked, stDeleted, _hNe, hRevoke, hDelete, hLookupDeleted, hRetype⟩
  have hCap' : capabilityInvariantBundle st' :=
    lifecycleRevokeDeleteRetype_preserves_capabilityInvariantBundle st st' authority cleanup target
      newObj hCap hNewObjCNodeUniq hStep
  have hLifecycleDeleted : lifecycleInvariantBundle stDeleted :=
    hLifecycleAfterCleanup stRevoked stDeleted hRevoke hDelete hLookupDeleted
  have hLifecycle' : lifecycleInvariantBundle st' :=
    SeLe4n.Kernel.lifecycleRetypeObject_preserves_lifecycleInvariantBundle stDeleted st' authority target
      newObj hLifecycleDeleted hRetype
  exact lifecycleCapabilityStaleAuthorityInvariant_of_bundles st' hLifecycle' hCap'

theorem lifecycleRevokeDeleteRetype_error_preserves_m4aLifecycleInvariantBundle
    (st : SystemState)
    (authority cleanup : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj : KernelObject)
    (hAlias : authority = cleanup)
    (hInv : m4aLifecycleInvariantBundle st) :
    m4aLifecycleInvariantBundle st := by
  have _hExpected : lifecycleRevokeDeleteRetype authority cleanup target newObj st = .error .illegalState :=
    lifecycleRevokeDeleteRetype_error_authority_cleanup_alias st authority cleanup target newObj hAlias
  exact hInv

/-- WS-E3/H-09: storeTcbIpcState stores a TCB (not a CNode), so cspaceSlotUnique is preserved. -/
private theorem cspaceSlotUnique_of_storeTcbIpcState
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (hUniq : cspaceSlotUnique st)
    (hStep : storeTcbIpcState st tid ipc = .ok st') :
    cspaceSlotUnique st' := by
  unfold storeTcbIpcState at hStep
  cases hLookup : lookupTcb st tid with
  | none =>
    have hImpossible : False := by
      simpa [storeTcbIpcState, hLookup] using hStep
    exact False.elim hImpossible
  | some tcb =>
    simp only [hLookup] at hStep
    cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc }) st with
    | error e => cases hStore
    | ok pair =>
      simp only [hStore] at hStep
      have := Except.ok.inj hStep; subst this
      exact cspaceSlotUnique_of_storeObject_nonCNode st pair.2 tid.toObjId _ hUniq hStore
        (fun cn h => by cases h)

/-- WS-E3/H-09: cspaceSlotUnique through storeObject + storeTcbIpcState + removeRunnable chain. -/
private theorem cspaceSlotUnique_through_blocking_path
    (st st1 st2 : SystemState) (endpointId : SeLe4n.ObjId) (target : SeLe4n.ThreadId)
    (ipc : ThreadIpcState) (ep : Endpoint)
    (hUniq : cspaceSlotUnique st)
    (hStore : storeObject endpointId (.endpoint ep) st = .ok ((), st1))
    (hTcb : storeTcbIpcState st1 target ipc = .ok st2) :
    cspaceSlotUnique (removeRunnable st2 target) :=
  cspaceSlotUnique_of_objects_eq st2 (removeRunnable st2 target)
    (cspaceSlotUnique_of_storeTcbIpcState st1 st2 target ipc
      (cspaceSlotUnique_of_endpoint_store st st1 endpointId ep hUniq hStore)
      hTcb) rfl

/-- WS-E3/H-09: cspaceSlotUnique through storeObject + storeTcbIpcState + ensureRunnable chain. -/
private theorem cspaceSlotUnique_through_handshake_path
    (st st1 st2 : SystemState) (endpointId : SeLe4n.ObjId) (target : SeLe4n.ThreadId)
    (ep : Endpoint)
    (hUniq : cspaceSlotUnique st)
    (hStore : storeObject endpointId (.endpoint ep) st = .ok ((), st1))
    (hTcb : storeTcbIpcState st1 target .ready = .ok st2) :
    cspaceSlotUnique (ensureRunnable st2 target) :=
  cspaceSlotUnique_of_objects_eq st2 (ensureRunnable st2 target)
    (cspaceSlotUnique_of_storeTcbIpcState st1 st2 target .ready
      (cspaceSlotUnique_of_endpoint_store st st1 endpointId ep hUniq hStore)
      hTcb) (ensureRunnable_preserves_objects st2 target)

/-- WS-E2 / H-01: Compositional preservation of `endpointSend`.
WS-E3/H-09: Updated for multi-step chain (storeObject → storeTcbIpcState → removeRunnable/ensureRunnable).
Endpoint and TCB stores do not affect CNodes, so capability invariants transfer. -/
theorem endpointSend_preserves_capabilityInvariantBundle
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hInv : capabilityInvariantBundle st)
    (hStep : endpointSend endpointId sender st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  rcases hInv with ⟨hUnique, _hSound, hAttRule, _hLifecycle⟩
  obtain ⟨ep, hObj⟩ := endpointSend_ok_implies_endpoint_object st st' endpointId sender hStep
  cases hState : ep.state with
  | idle =>
    simp [endpointSend, hObj, hState] at hStep; revert hStep
    cases hStore : storeObject endpointId _ st with
    | error e => simp
    | ok pair =>
      simp only []
      cases hTcb : storeTcbIpcState pair.2 sender _ with
      | error e => simp
      | ok st2 =>
        simp only [Except.ok.injEq, Prod.mk.injEq]; intro ⟨_, hEq⟩; subst hEq
        have hU := cspaceSlotUnique_through_blocking_path st pair.2 st2 endpointId sender _ _ hUnique hStore hTcb
        exact ⟨hU, cspaceLookupSound_of_cspaceSlotUnique _ hU, hAttRule, lifecycleAuthorityMonotonicity_holds _⟩
  | send =>
    simp [endpointSend, hObj, hState] at hStep; revert hStep
    cases hStore : storeObject endpointId _ st with
    | error e => simp
    | ok pair =>
      simp only []
      cases hTcb : storeTcbIpcState pair.2 sender _ with
      | error e => simp
      | ok st2 =>
        simp only [Except.ok.injEq, Prod.mk.injEq]; intro ⟨_, hEq⟩; subst hEq
        have hU := cspaceSlotUnique_through_blocking_path st pair.2 st2 endpointId sender _ _ hUnique hStore hTcb
        exact ⟨hU, cspaceLookupSound_of_cspaceSlotUnique _ hU, hAttRule, lifecycleAuthorityMonotonicity_holds _⟩
  | receive =>
    simp [endpointSend, hObj, hState] at hStep
    cases hQueue : ep.queue <;> cases hWait : ep.waitingReceiver <;> simp [hQueue, hWait] at hStep
    case nil.some receiver =>
      revert hStep
      cases hStore : storeObject endpointId _ st with
      | error e => simp
      | ok pair =>
        simp only []
        cases hTcb : storeTcbIpcState pair.2 receiver _ with
        | error e => simp
        | ok st2 =>
          simp only [Except.ok.injEq, Prod.mk.injEq]; intro ⟨_, hEq⟩; subst hEq
          have hU := cspaceSlotUnique_through_handshake_path st pair.2 st2 endpointId receiver _ hUnique hStore hTcb
          exact ⟨hU, cspaceLookupSound_of_cspaceSlotUnique _ hU, hAttRule, lifecycleAuthorityMonotonicity_holds _⟩

/-- WS-E2 / H-01: Compositional preservation of `endpointAwaitReceive`. -/
theorem endpointAwaitReceive_preserves_capabilityInvariantBundle
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId)
    (hInv : capabilityInvariantBundle st)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  rcases hInv with ⟨hUnique, _hSound, hAttRule, _hLifecycle⟩
  obtain ⟨ep, hObj⟩ := endpointAwaitReceive_ok_implies_endpoint_object st st' endpointId receiver hStep
  simp [endpointAwaitReceive, hObj] at hStep
  cases hState : ep.state <;> simp [hState] at hStep
  case idle =>
    cases hQueue : ep.queue <;> simp [hQueue] at hStep
    case nil =>
      cases hWait : ep.waitingReceiver <;> simp [hWait] at hStep
      case none =>
        revert hStep
        cases hStore : storeObject endpointId _ st with
        | error e => simp
        | ok pair =>
          simp only []
          cases hTcb : storeTcbIpcState pair.2 receiver _ with
          | error e => simp
          | ok st2 =>
            simp only [Except.ok.injEq, Prod.mk.injEq]; intro ⟨_, hEq⟩; subst hEq
            have hU := cspaceSlotUnique_through_blocking_path st pair.2 st2 endpointId receiver _ _ hUnique hStore hTcb
            exact ⟨hU, cspaceLookupSound_of_cspaceSlotUnique _ hU, hAttRule, lifecycleAuthorityMonotonicity_holds _⟩

/-- WS-E2 / H-01: Compositional preservation of `endpointReceive`. -/
theorem endpointReceive_preserves_capabilityInvariantBundle
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hInv : capabilityInvariantBundle st)
    (hStep : endpointReceive endpointId st = .ok (sender, st')) :
    capabilityInvariantBundle st' := by
  rcases hInv with ⟨hUnique, _hSound, hAttRule, _hLifecycle⟩
  obtain ⟨ep, hObj⟩ := endpointReceive_ok_implies_endpoint_object st st' endpointId sender hStep
  cases hState : ep.state with
  | idle => simp [endpointReceive, hObj, hState] at hStep
  | receive => simp [endpointReceive, hObj, hState] at hStep
  | send =>
    cases hQueue : ep.queue with
    | nil =>
      cases hWait : ep.waitingReceiver <;> simp [endpointReceive, hObj, hState, hQueue, hWait] at hStep
    | cons hd tl =>
      cases hWait : ep.waitingReceiver with
      | some _ => simp [endpointReceive, hObj, hState, hQueue, hWait] at hStep
      | none =>
        unfold endpointReceive at hStep; simp only [hObj, hState, hQueue, hWait] at hStep
        revert hStep
        cases hStore : storeObject endpointId _ st with
        | error e => simp
        | ok pair =>
          simp only []
          cases hTcb : storeTcbIpcState pair.2 hd _ with
          | error e => simp
          | ok st2 =>
            simp only [Except.ok.injEq, Prod.mk.injEq]; intro ⟨hSenderEq, hStEq⟩
            subst hStEq; subst hSenderEq
            have hU := cspaceSlotUnique_through_handshake_path st pair.2 st2 endpointId hd _ hUnique hStore hTcb
            exact ⟨hU, cspaceLookupSound_of_cspaceSlotUnique _ hU, hAttRule, lifecycleAuthorityMonotonicity_holds _⟩

theorem endpointSend_preserves_m3IpcSeedInvariantBundle
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hInv : m3IpcSeedInvariantBundle st)
    (hStep : endpointSend endpointId sender st = .ok ((), st')) :
    m3IpcSeedInvariantBundle st' := by
  rcases hInv with ⟨hSched, hCap, hIpc⟩
  refine ⟨?_, ?_, ?_⟩
  · exact endpointSend_preserves_schedulerInvariantBundle st st' endpointId sender hSched hStep
  · exact endpointSend_preserves_capabilityInvariantBundle st st' endpointId sender hCap hStep
  · exact endpointSend_preserves_ipcInvariant st st' endpointId sender hIpc hStep

theorem endpointAwaitReceive_preserves_m3IpcSeedInvariantBundle
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId)
    (hInv : m3IpcSeedInvariantBundle st)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st')) :
    m3IpcSeedInvariantBundle st' := by
  rcases hInv with ⟨hSched, hCap, hIpc⟩
  refine ⟨?_, ?_, ?_⟩
  · exact endpointAwaitReceive_preserves_schedulerInvariantBundle st st' endpointId receiver hSched hStep
  · exact endpointAwaitReceive_preserves_capabilityInvariantBundle st st' endpointId receiver hCap hStep
  · exact endpointAwaitReceive_preserves_ipcInvariant st st' endpointId receiver hIpc hStep

theorem endpointReceive_preserves_m3IpcSeedInvariantBundle
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hInv : m3IpcSeedInvariantBundle st)
    (hStep : endpointReceive endpointId st = .ok (sender, st')) :
    m3IpcSeedInvariantBundle st' := by
  rcases hInv with ⟨hSched, hCap, hIpc⟩
  refine ⟨?_, ?_, ?_⟩
  · exact endpointReceive_preserves_schedulerInvariantBundle st st' endpointId sender hSched hStep
  · exact endpointReceive_preserves_capabilityInvariantBundle st st' endpointId sender hCap hStep
  · exact endpointReceive_preserves_ipcInvariant st st' endpointId sender hIpc hStep

theorem endpointSend_preserves_m35IpcSchedulerInvariantBundle
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hInv : m35IpcSchedulerInvariantBundle st)
    (hStep : endpointSend endpointId sender st = .ok ((), st')) :
    m35IpcSchedulerInvariantBundle st' := by
  rcases hInv with ⟨hM3Seed, hIpcSched⟩
  have hContract : ipcSchedulerContractPredicates st :=
    (ipcSchedulerCoherenceComponent_iff_contractPredicates st).1 hIpcSched
  refine ⟨?_, ?_⟩
  · exact endpointSend_preserves_m3IpcSeedInvariantBundle st st' endpointId sender hM3Seed hStep
  · exact (ipcSchedulerCoherenceComponent_iff_contractPredicates st').2
      (endpointSend_preserves_ipcSchedulerContractPredicates st st' endpointId sender hContract hStep)

theorem endpointAwaitReceive_preserves_m35IpcSchedulerInvariantBundle
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId)
    (hInv : m35IpcSchedulerInvariantBundle st)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st')) :
    m35IpcSchedulerInvariantBundle st' := by
  rcases hInv with ⟨hM3Seed, hIpcSched⟩
  have hContract : ipcSchedulerContractPredicates st :=
    (ipcSchedulerCoherenceComponent_iff_contractPredicates st).1 hIpcSched
  refine ⟨?_, ?_⟩
  · exact endpointAwaitReceive_preserves_m3IpcSeedInvariantBundle st st' endpointId receiver hM3Seed hStep
  · exact (ipcSchedulerCoherenceComponent_iff_contractPredicates st').2
      (endpointAwaitReceive_preserves_ipcSchedulerContractPredicates st st' endpointId receiver hContract hStep)

theorem endpointReceive_preserves_m35IpcSchedulerInvariantBundle
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hInv : m35IpcSchedulerInvariantBundle st)
    (hStep : endpointReceive endpointId st = .ok (sender, st')) :
    m35IpcSchedulerInvariantBundle st' := by
  rcases hInv with ⟨hM3Seed, hIpcSched⟩
  have hContract : ipcSchedulerContractPredicates st :=
    (ipcSchedulerCoherenceComponent_iff_contractPredicates st).1 hIpcSched
  refine ⟨?_, ?_⟩
  · exact endpointReceive_preserves_m3IpcSeedInvariantBundle st st' endpointId sender hM3Seed hStep
  · exact (ipcSchedulerCoherenceComponent_iff_contractPredicates st').2
      (endpointReceive_preserves_ipcSchedulerContractPredicates st st' endpointId sender hContract hStep)

end SeLe4n.Kernel
