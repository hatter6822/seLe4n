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
- `lifecycleRevokeDeleteRetype_error_preserves_lifecycleCompositionInvariantBundle`
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
  ∀ (cnodeId : SeLe4n.ObjId) (cn : CNode),
    st.objects[cnodeId]? = some (KernelObject.cnode cn) →
    cn.slotsUnique

/-- Lookup completeness: every capability stored in a CNode's slot HashMap is
retrievable via `lookupSlotCap`.

WS-G5: With HashMap-backed slots, lookup completeness is direct — `CNode.lookup`
delegates to `HashMap.getElem?`, which is the canonical accessor. The property
is trivially true by the identity `CNode.lookup slot = cn.slots[slot]?`. -/
def cspaceLookupSound (st : SystemState) : Prop :=
  ∀ (cnodeId : SeLe4n.ObjId) (cn : CNode) (slot : SeLe4n.Slot) (cap : Capability),
    st.objects[cnodeId]? = some (KernelObject.cnode cn) →
    cn.lookup slot = some cap →
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
  cases hObj : st.objects[cnodeId]? with
  | none => simp [cspaceDeleteSlot, hObj] at hStep
  | some obj =>
      cases obj with
      | tcb tcb => simp [cspaceDeleteSlot, hObj] at hStep
      | endpoint ep => simp [cspaceDeleteSlot, hObj] at hStep
      | notification ntfn => simp [cspaceDeleteSlot, hObj] at hStep
      | vspaceRoot root => simp [cspaceDeleteSlot, hObj] at hStep
      | untyped _ => simp [cspaceDeleteSlot, hObj] at hStep
      | cnode cn =>

          simp [cspaceDeleteSlot, hObj] at hStep
          cases hStep
          simp [SystemState.lookupSlotCap, SystemState.lookupCNode, SystemState.detachSlotFromCdt_objects_eq, CNode.lookup_remove_eq_none]

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
  cases hObj : st.objects[addr.cnode]? with
  | none => simp [hObj] at hStep
  | some obj =>
      cases obj with
      | tcb tcb => simp [hObj] at hStep
      | endpoint ep => simp [hObj] at hStep
      | notification ntfn => simp [hObj] at hStep
      | vspaceRoot root => simp [hObj] at hStep
      | untyped _ => simp [hObj] at hStep
      | cnode cn =>

                    -- WS-G5: revokedRefs via HashMap.fold — single O(m) pass.
          let revokedRefs : List SlotRef :=
            cn.slots.fold (fun acc s c =>
              if s != addr.slot && c.target == parent.target then
                { cnode := addr.cnode, slot := s } :: acc
              else acc) []
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
          -- WS-G5: With HashMap-backed slots, CNode.lookup delegates to getElem?.
          -- Extract that the filtered HashMap lookup succeeds at `slot`.
          have hFilterLookup : (cn.revokeTargetLocal addr.slot parent.target).lookup slot = some cap := by
            simp [storedState, revokedObj, SystemState.lookupSlotCap, SystemState.lookupCNode,
              CNode.lookup] at hLookupStored
            exact hLookupStored
          -- revokeTargetLocal filters with: fun s c => s == addr.slot || !(c.target == parent.target)
          have hMemFilter : slot ∈ cn.slots.filter (fun s c => s == addr.slot || !(c.target == parent.target)) := by
            rw [CNode.revokeTargetLocal, CNode.lookup] at hFilterLookup
            exact Std.HashMap.mem_iff_isSome_getElem?.mpr (by simp [hFilterLookup])
          -- By mem_filter, the filter predicate holds for the stored key and value.
          have ⟨hMemOrig, hPredTrue⟩ := Std.HashMap.mem_filter.mp hMemFilter
          -- Normalize: getKey slot ≈ slot, and the stored value cn.slots[slot] = cap
          have hKeyEq : cn.slots.getKey slot hMemOrig = slot := eq_of_beq (Std.HashMap.getKey_beq hMemOrig)
          have hValEq : cn.slots[slot] = cap := by
            have h1 := @Std.HashMap.getElem_filter _ _ _ _ cn.slots _ _ _ slot hMemFilter
            have h2 := Std.HashMap.getElem?_eq_some_getElem hMemFilter
            rw [h1] at h2
            rw [CNode.revokeTargetLocal, CNode.lookup] at hFilterLookup
            rw [hFilterLookup] at h2
            exact (Option.some.inj h2).symm
          rw [hKeyEq, hValEq] at hPredTrue
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

theorem cspaceInsertSlot_lookup_eq
    (st st' : SystemState)
    (addr : CSpaceAddr)
    (cap : Capability)
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
  cases hObj : st.objects[cnodeId]? with
  | none => simp [cspaceDeleteSlot, hObj] at hStep
  | some obj =>
      cases obj with
      | tcb tcb => simp [cspaceDeleteSlot, hObj] at hStep
      | endpoint ep => simp [cspaceDeleteSlot, hObj] at hStep
      | notification ntfn => simp [cspaceDeleteSlot, hObj] at hStep
      | vspaceRoot root => simp [cspaceDeleteSlot, hObj] at hStep
      | untyped _ => simp [cspaceDeleteSlot, hObj] at hStep
      | cnode cn =>

          simp [cspaceDeleteSlot, hObj] at hStep
          cases hStep
          simp [cspaceLookupSlot, SystemState.lookupSlotCap, SystemState.lookupCNode,
            SystemState.detachSlotFromCdt_objects_eq, CNode.lookup_remove_eq_none]

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
      cases hObj : st.objects[addr.cnode]? with
      | none => simp [hLookup, hObj] at hStep
      | some obj =>
          cases obj with
          | tcb tcb => simp [hLookup, hObj] at hStep
          | endpoint ep => simp [hLookup, hObj] at hStep
          | notification ntfn => simp [hLookup, hObj] at hStep
          | vspaceRoot root => simp [hLookup, hObj] at hStep
          | untyped _ => simp [hLookup, hObj] at hStep
          | cnode cn =>

              -- WS-G5: revokedRefs via HashMap.fold — single O(m) pass.
              let revokedRefs : List SlotRef :=
                cn.slots.fold (fun acc s c =>
                  if s != addr.slot && c.target == parent.target then
                    { cnode := addr.cnode, slot := s } :: acc
                  else acc) []
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
                simpa [storedState, revokedObj, SystemState.lookupSlotCap, SystemState.lookupCNode,
                  Std.HashMap.getElem?_insert, CNode.lookup_revokeTargetLocal_source_eq_lookup, hObj] using hCap
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
    (hObj : st.objects[notifId]? = some (.notification ntfn))
    (hNoWaiters : ntfn.waitingThreads = [])
    (hNoPending : ntfn.pendingBadge = none)
    (hSignal : notificationSignal notifId badge st = .ok ((), st')) :
    ∃ ntfn',
      st'.objects[notifId]? = some (.notification ntfn') ∧
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
      | tcb _ | endpoint _ | cnode _ | vspaceRoot _ | untyped _ => simp [hObj] at hWait

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
    (hNtfnObj : st₂.objects[notifId]? = some (.notification ntfn))
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
      cases hPre : st.objects[addr.cnode]? with
      | none => simp [hPre] at hStep
      | some preObj =>
        cases preObj with
        | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ => simp [hPre] at hStep
        | cnode preCn =>
          simp [hPre] at hStep
          -- WS-E4/H-02: case split on occupied-slot guard
          cases hLookup : preCn.lookup addr.slot with
          | some _ => simp [hLookup] at hStep
          | none =>
            simp [hLookup] at hStep
            cases hStore : storeObject addr.cnode (.cnode (preCn.insert addr.slot cap)) st with
            | error e => simp [hStore] at hStep
            | ok pair =>
              obtain ⟨_, stMid⟩ := pair
              simp [hStore] at hStep
              have hObjRef := storeCapabilityRef_preserves_objects stMid st' addr (some cap.target) hStep
              have hObjMid := storeObject_objects_eq st stMid addr.cnode
                (.cnode (preCn.insert addr.slot cap)) hStore
              have hFinal : st'.objects[addr.cnode]? = some (.cnode (preCn.insert addr.slot cap)) := by
                rw [← hObjMid]; exact congrArg (·[addr.cnode]?) hObjRef
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
    cases hPre : st.objects[addr.cnode]? with
    | none => simp [hPre] at hStep
    | some preObj =>
      cases preObj with
      | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ => simp [hPre] at hStep
      | cnode preCn =>
        simp [hPre] at hStep
        cases hStore : storeObject addr.cnode (.cnode (preCn.remove addr.slot)) st with
        | error e => simp [hStore] at hStep
        | ok pair =>
          obtain ⟨_, stMid⟩ := pair
          cases hRef : storeCapabilityRef addr none stMid with
          | error e => simp [hStore, hRef] at hStep
          | ok pairRef =>
            obtain ⟨_, stRef⟩ := pairRef
            simp [hStore, hRef] at hStep
            cases hStep
            have hObjRef : stRef.objects = stMid.objects :=
              storeCapabilityRef_preserves_objects stMid stRef addr none hRef
            have hObjDetach : (SystemState.detachSlotFromCdt stRef addr).objects = stRef.objects :=
              SystemState.detachSlotFromCdt_objects_eq stRef addr
            by_cases hEq : cnodeId = addr.cnode
            · rw [hEq] at hObj
              have hObjMid := storeObject_objects_eq st stMid addr.cnode
                (.cnode (preCn.remove addr.slot)) hStore
              have : (SystemState.detachSlotFromCdt stRef addr).objects[addr.cnode]? =
                  some (.cnode (preCn.remove addr.slot)) := by
                rw [hObjDetach, hObjRef, ← hObjMid]
              rw [this] at hObj; cases hObj
              exact CNode.remove_slotsUnique preCn addr.slot (hUnique addr.cnode preCn hPre)
            · have hObjMid := storeObject_objects_ne st stMid addr.cnode cnodeId
                (.cnode (preCn.remove addr.slot)) hEq hStore
              have : (SystemState.detachSlotFromCdt stRef addr).objects[cnodeId]? = st.objects[cnodeId]? := by
                rw [hObjDetach, hObjRef, ← hObjMid]
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
      cases hPre : st.objects[addr.cnode]? with
      | none => simp [hLookup, hPre] at hStep
      | some preObj =>
        cases preObj with
        | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ => simp [hLookup, hPre] at hStep
        | cnode preCn =>
          simp [hLookup, hPre] at hStep
          cases hStore : storeObject addr.cnode
            (.cnode (preCn.revokeTargetLocal addr.slot parent.target)) st with
          | error e => simp [hStore] at hStep
          | ok pair =>
            obtain ⟨_, stMid⟩ := pair
            simp [hStore] at hStep
            have hObjRef := clearCapabilityRefs_preserves_objects stMid st' _ hStep
            by_cases hEq : cnodeId = addr.cnode
            · rw [hEq] at hObj
              have hObjMid := storeObject_objects_eq st stMid addr.cnode
                (.cnode (preCn.revokeTargetLocal addr.slot parent.target)) hStore
              have : st'.objects[addr.cnode]? =
                  some (.cnode (preCn.revokeTargetLocal addr.slot parent.target)) := by
                rw [← hObjMid]; exact congrArg (·[addr.cnode]?) hObjRef
              rw [this] at hObj; cases hObj
              exact CNode.revokeTargetLocal_slotsUnique preCn addr.slot parent.target
                (hUnique addr.cnode preCn hPre)
            · have hObjMid := storeObject_objects_ne st stMid addr.cnode cnodeId
                (.cnode (preCn.revokeTargetLocal addr.slot parent.target)) hEq hStore
              have : st'.objects[cnodeId]? = st.objects[cnodeId]? := by
                rw [← hObjMid]; exact congrArg (·[cnodeId]?) hObjRef
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
          have hBundleSt2 := cspaceInsertSlot_preserves_capabilityInvariantBundle st st2 dst cap hInv hInsert
          rcases hBundleSt2 with ⟨hU2, _, hAtt2, _⟩
          cases hEnsSrc : SystemState.ensureCdtNodeForSlot st2 src with
          | mk srcNode stSrc =>
              cases hEnsDst : SystemState.ensureCdtNodeForSlot stSrc dst with
              | mk dstNode stDst =>
                  simp [hSrc, hInsert, hEnsSrc, hEnsDst] at hStep
                  cases hStep
                  have hObjSrc : stSrc.objects = st2.objects := by
                    simpa [hEnsSrc] using SystemState.ensureCdtNodeForSlot_objects_eq st2 src
                  have hObjDst : stDst.objects = stSrc.objects := by
                    simpa [hEnsDst] using SystemState.ensureCdtNodeForSlot_objects_eq stSrc dst
                  have hObjFinal : ({ stDst with cdt := stDst.cdt.addEdge srcNode dstNode .copy }).objects = st2.objects := by
                    simp [hObjDst, hObjSrc]
                  have hU' := cspaceSlotUnique_of_objects_eq st2 { stDst with cdt := stDst.cdt.addEdge srcNode dstNode .copy } hU2 hObjFinal
                  exact ⟨hU', cspaceLookupSound_of_cspaceSlotUnique _ hU', hAtt2,
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
              have hBundleSt2 := cspaceInsertSlot_preserves_capabilityInvariantBundle st st2 dst cap hInv hInsert
              have hBundleSt3 := cspaceDeleteSlot_preserves_capabilityInvariantBundle st2 st3 src hBundleSt2 hDelete
              rcases hBundleSt3 with ⟨hU3, _, hAtt3, _⟩
              -- Node-stable move only updates CDT/mapping fields, never objects.
              cases hNode : SystemState.lookupCdtNodeOfSlot st2 src with
              | none =>
                  simp [hSrc, hInsert, hDelete, hNode] at hStep
                  cases hStep
                  exact ⟨hU3, cspaceLookupSound_of_cspaceSlotUnique _ hU3, hAtt3,
                    lifecycleAuthorityMonotonicity_holds _⟩
              | some srcNode =>
                  simp [hSrc, hInsert, hDelete, hNode] at hStep
                  cases hStep
                  have hObjEq : (SystemState.attachSlotToCdtNode st3 dst srcNode).objects = st3.objects :=
                    SystemState.attachSlotToCdtNode_objects_eq st3 dst srcNode
                  have hU' := cspaceSlotUnique_of_objects_eq st3
                    (SystemState.attachSlotToCdtNode st3 dst srcNode)
                    hU3 hObjEq
                  exact ⟨hU', cspaceLookupSound_of_cspaceSlotUnique _ hU', hAtt3,
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
      have hBundle := cspaceMint_preserves_capabilityInvariantBundle st st1 src dst rights badge hInv hMint
      rcases hBundle with ⟨hU1, _, hAtt1, _⟩
      cases hEnsSrc : SystemState.ensureCdtNodeForSlot st1 src with
      | mk srcNode stSrc =>
          cases hEnsDst : SystemState.ensureCdtNodeForSlot stSrc dst with
          | mk dstNode stDst =>
              simp [hMint, hEnsSrc, hEnsDst] at hStep
              cases hStep
              have hObjSrc : stSrc.objects = st1.objects := by
                simpa [hEnsSrc] using SystemState.ensureCdtNodeForSlot_objects_eq st1 src
              have hObjDst : stDst.objects = stSrc.objects := by
                simpa [hEnsDst] using SystemState.ensureCdtNodeForSlot_objects_eq stSrc dst
              have hObjFinal : ({ stDst with cdt := stDst.cdt.addEdge srcNode dstNode .mint }).objects = st1.objects := by
                simp [hObjDst, hObjSrc]
              have hU' := cspaceSlotUnique_of_objects_eq st1 { stDst with cdt := stDst.cdt.addEdge srcNode dstNode .mint } hU1 hObjFinal
              exact ⟨hU', cspaceLookupSound_of_cspaceSlotUnique _ hU', hAtt1,
                lifecycleAuthorityMonotonicity_holds _⟩

-- ============================================================================
-- WS-F4/F-06: cspaceMutate preservation
-- ============================================================================

/-- WS-F4/F-06: cspaceMutate preserves capabilityInvariantBundle.
Mutate composes cspaceLookupSlot (read-only) + cn.insert (which preserves
slotsUnique) + storeObject + storeCapabilityRef. -/
theorem cspaceMutate_preserves_capabilityInvariantBundle
    (st st' : SystemState)
    (addr : CSpaceAddr)
    (rights : List AccessRight)
    (badge : Option SeLe4n.Badge)
    (hInv : capabilityInvariantBundle st)
    (hStep : cspaceMutate addr rights badge st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  rcases hInv with ⟨hUnique, _hSound, hAttRule, _hLifecycle⟩
  have hUnique' : cspaceSlotUnique st' := by
    intro cnodeId cn hObj
    -- Revert hStep to decompose the definition via goal-level case splits
    revert hStep; unfold cspaceMutate
    cases hLookup : cspaceLookupSlot addr st with
    | error e => simp
    | ok pair =>
      rcases pair with ⟨cap, st1⟩
      have hSt1 : st1 = st := cspaceLookupSlot_preserves_state st st1 addr cap hLookup
      subst st1
      by_cases hRights : rightsSubset rights cap.rights
      · simp only [hRights, ite_true]
        cases hPre : st.objects[addr.cnode]? with
        | none => simp
        | some preObj =>
          cases preObj with
          | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ => simp
          | cnode preCn =>
            simp only []
            cases hStore : storeObject addr.cnode
              (.cnode (preCn.insert addr.slot
                { cap with rights := rights, badge := badge.orElse (fun _ => cap.badge) })) st with
            | error e => simp
            | ok pair =>
              obtain ⟨_, stMid⟩ := pair
              simp only []
              intro hStep
              by_cases hEq : cnodeId = addr.cnode
              · rw [hEq] at hObj
                have hObjRef := storeCapabilityRef_preserves_objects stMid st' addr
                  (some cap.target) hStep
                have hObjMid := storeObject_objects_eq st stMid addr.cnode
                  (.cnode (preCn.insert addr.slot
                    { cap with rights := rights, badge := badge.orElse (fun _ => cap.badge) })) hStore
                have hFinal : st'.objects[addr.cnode]? =
                    some (.cnode (preCn.insert addr.slot
                      { cap with rights := rights, badge := badge.orElse (fun _ => cap.badge) })) := by
                  rw [← hObjMid]; exact congrArg (·[addr.cnode]?) hObjRef
                rw [hFinal] at hObj; cases hObj
                exact CNode.insert_slotsUnique preCn addr.slot _
                  (hUnique addr.cnode preCn hPre)
              · have hObjMid := storeObject_objects_ne st stMid addr.cnode cnodeId
                  (.cnode (preCn.insert addr.slot
                    { cap with rights := rights, badge := badge.orElse (fun _ => cap.badge) })) hEq hStore
                have hObjRef := storeCapabilityRef_preserves_objects stMid st' addr
                  (some cap.target) hStep
                have hFinal : st'.objects[cnodeId]? = st.objects[cnodeId]? := by
                  rw [← hObjMid]; exact congrArg (·[cnodeId]?) hObjRef
                rw [hFinal] at hObj
                exact hUnique cnodeId cn hObj
      · simp [hRights]
  exact ⟨hUnique', cspaceLookupSound_of_cspaceSlotUnique st' hUnique', hAttRule,
    lifecycleAuthorityMonotonicity_holds st'⟩

-- ============================================================================
-- WS-F4/F-06: cspaceRevokeCdt and cspaceRevokeCdtStrict preservation
-- ============================================================================

/-- Helper: CDT-only state updates preserve capabilityInvariantBundle. -/
private theorem capabilityInvariantBundle_of_cdt_update
    (st : SystemState) (cdt' : CapDerivationTree)
    (hInv : capabilityInvariantBundle st) :
    capabilityInvariantBundle { st with cdt := cdt' } := by
  rcases hInv with ⟨hU, _, hA, _⟩
  have hObjEq : ({ st with cdt := cdt' } : SystemState).objects = st.objects := rfl
  exact ⟨cspaceSlotUnique_of_objects_eq st _ hU hObjEq,
    cspaceLookupSound_of_cspaceSlotUnique _ (cspaceSlotUnique_of_objects_eq st _ hU hObjEq),
    hA, lifecycleAuthorityMonotonicity_holds _⟩

/-- Fold body function for cspaceRevokeCdt: processes one CDT descendant node. -/
private def revokeCdtFoldBody
    (acc : Except KernelError (Unit × SystemState)) (node : CdtNodeId) :
    Except KernelError (Unit × SystemState) :=
  match acc with
  | .error e => .error e
  | .ok ((), stAcc) =>
      match SystemState.lookupCdtSlotOfNode stAcc node with
      | none => .ok ((), { stAcc with cdt := stAcc.cdt.removeNode node })
      | some descAddr =>
          match cspaceDeleteSlot descAddr stAcc with
          | .error _ => .ok ((), { stAcc with cdt := stAcc.cdt.removeNode node })
          | .ok ((), stDel) =>
              let stDetached := SystemState.detachSlotFromCdt stDel descAddr
              .ok ((), { stDetached with cdt := stDetached.cdt.removeNode node })

/-- Single fold step preserves capabilityInvariantBundle. -/
private theorem revokeCdtFoldBody_preserves
    (stAcc stNext : SystemState) (node : CdtNodeId)
    (hInv : capabilityInvariantBundle stAcc)
    (hStep : revokeCdtFoldBody (.ok ((), stAcc)) node = .ok ((), stNext)) :
    capabilityInvariantBundle stNext := by
  unfold revokeCdtFoldBody at hStep
  cases hSlot : SystemState.lookupCdtSlotOfNode stAcc node with
  | none =>
    simp [hSlot] at hStep; cases hStep
    exact capabilityInvariantBundle_of_cdt_update stAcc _ hInv
  | some descAddr =>
    simp [hSlot] at hStep
    cases hDel : cspaceDeleteSlot descAddr stAcc with
    | error _ =>
      simp [hDel] at hStep; cases hStep
      exact capabilityInvariantBundle_of_cdt_update stAcc _ hInv
    | ok pair =>
      obtain ⟨_, stDel⟩ := pair
      simp [hDel] at hStep; cases hStep
      have hDelInv := cspaceDeleteSlot_preserves_capabilityInvariantBundle stAcc stDel descAddr hInv hDel
      have hDetachObj := SystemState.detachSlotFromCdt_objects_eq stDel descAddr
      rcases hDelInv with ⟨hU2, _, hA2, _⟩
      have hDetachInv : capabilityInvariantBundle (SystemState.detachSlotFromCdt stDel descAddr) :=
        ⟨cspaceSlotUnique_of_objects_eq stDel _ hU2 hDetachObj,
         cspaceLookupSound_of_cspaceSlotUnique _ (cspaceSlotUnique_of_objects_eq stDel _ hU2 hDetachObj),
         hA2, lifecycleAuthorityMonotonicity_holds _⟩
      exact capabilityInvariantBundle_of_cdt_update _ _ hDetachInv

/-- Error propagation: revokeCdtFoldBody propagates errors unchanged. -/
private theorem revokeCdtFoldBody_error (e : KernelError) (node : CdtNodeId) :
    revokeCdtFoldBody (.error e) node = .error e := by
  unfold revokeCdtFoldBody; rfl

/-- Fold error propagation: foldl revokeCdtFoldBody starting from error stays error. -/
private theorem revokeCdtFoldBody_foldl_error
    (nodes : List CdtNodeId) (e : KernelError) :
    nodes.foldl revokeCdtFoldBody (.error e) = .error e := by
  induction nodes with
  | nil => rfl
  | cons node rest ih => simp [List.foldl, revokeCdtFoldBody_error, ih]

/-- Fold induction: cspaceRevokeCdt fold preserves capabilityInvariantBundle. -/
private theorem revokeCdtFold_preserves
    (nodes : List CdtNodeId)
    (stInit stFinal : SystemState)
    (hInv : capabilityInvariantBundle stInit)
    (hFold : nodes.foldl revokeCdtFoldBody (.ok ((), stInit)) = .ok ((), stFinal)) :
    capabilityInvariantBundle stFinal := by
  induction nodes generalizing stInit stFinal with
  | nil =>
    simp [List.foldl] at hFold; cases hFold; exact hInv
  | cons node rest ih =>
    simp only [List.foldl] at hFold
    -- Case split on whether the step succeeds or errors
    cases hStep : revokeCdtFoldBody (.ok ((), stInit)) node with
    | error e =>
      rw [hStep, revokeCdtFoldBody_foldl_error] at hFold; simp at hFold
    | ok val =>
      obtain ⟨_, stMid⟩ := val
      rw [hStep] at hFold
      exact ih stMid stFinal (revokeCdtFoldBody_preserves stInit stMid node hInv hStep) hFold

/-- WS-F4/F-06: cspaceRevokeCdt preserves capabilityInvariantBundle.
Composes cspaceRevoke (proven) + fold over CDT descendants. -/
theorem cspaceRevokeCdt_preserves_capabilityInvariantBundle
    (st st' : SystemState)
    (addr : CSpaceAddr)
    (hInv : capabilityInvariantBundle st)
    (hStep : cspaceRevokeCdt addr st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  unfold cspaceRevokeCdt at hStep
  split at hStep
  · simp at hStep
  · rename_i stLocal hRevoke
    have hLocalInv := cspaceRevoke_preserves_capabilityInvariantBundle st stLocal addr hInv hRevoke
    split at hStep
    · simp at hStep; cases hStep; exact hLocalInv
    · rename_i rootNode hLookup
      -- hStep has the fold result; the inline lambda is definitionally equal to revokeCdtFoldBody
      change (stLocal.cdt.descendantsOf rootNode).foldl revokeCdtFoldBody
          (.ok ((), stLocal)) = .ok ((), st') at hStep
      exact revokeCdtFold_preserves _ stLocal st' hLocalInv hStep

/-- WS-F4/F-06: cspaceRevokeCdtStrict preserves capabilityInvariantBundle.
The strict variant composes cspaceRevoke + a fold that only does cspaceDeleteSlot
and CDT operations, same as the non-strict variant. -/
theorem cspaceRevokeCdtStrict_preserves_capabilityInvariantBundle
    (st st' : SystemState)
    (addr : CSpaceAddr)
    (report : RevokeCdtStrictReport)
    (hInv : capabilityInvariantBundle st)
    (hStep : cspaceRevokeCdtStrict addr st = .ok (report, st')) :
    capabilityInvariantBundle st' := by
  unfold cspaceRevokeCdtStrict at hStep
  split at hStep
  · simp at hStep
  · rename_i stLocal hRevoke
    have hLocalInv := cspaceRevoke_preserves_capabilityInvariantBundle st stLocal addr hInv hRevoke
    split at hStep
    · -- No CDT root: stLocal is the final state
      simp at hStep; obtain ⟨_, rfl⟩ := hStep; exact hLocalInv
    · -- CDT root found: fold processes descendants
      rename_i rootNode _hLookup
      -- The fold produces (report, stFinal) from a pure total step function,
      -- so we need to show the fold preserves the invariant through each step.
      -- Each step either: (a) does nothing (firstFailure already set),
      -- (b) removes a CDT node (objects unchanged), (c) deletes a slot + detaches CDT,
      -- or (d) records a failure + removes CDT node.
      -- In all cases, CNode objects are either unchanged or go through cspaceDeleteSlot.
      suffices h : ∀ (nodes : List CdtNodeId) (rep : RevokeCdtStrictReport) (stAcc : SystemState),
          capabilityInvariantBundle stAcc →
          capabilityInvariantBundle (nodes.foldl (fun acc node =>
            let (report, stCur) := acc
            match report.firstFailure with
            | some _ => (report, stCur)
            | none =>
                match SystemState.lookupCdtSlotOfNode stCur node with
                | none => (report, { stCur with cdt := stCur.cdt.removeNode node })
                | some descAddr =>
                    match cspaceDeleteSlot descAddr stCur with
                    | .error err =>
                        ({ report with firstFailure := some {
                            offendingNode := node, offendingSlot := some descAddr, error := err } },
                         { stCur with cdt := stCur.cdt.removeNode node })
                    | .ok ((), stDel) =>
                        let stDetached := SystemState.detachSlotFromCdt stDel descAddr
                        ({ report with deletedSlots := descAddr :: report.deletedSlots },
                         { stDetached with cdt := stDetached.cdt.removeNode node })
          ) (rep, stAcc)).2 by
        simp at hStep
        have hInvFold := h (stLocal.cdt.descendantsOf rootNode)
          { deletedSlots := [], firstFailure := none } stLocal hLocalInv
        obtain ⟨_, hStEq⟩ := hStep
        rw [← hStEq]; exact hInvFold
      intro nodes
      induction nodes with
      | nil => intro rep stAcc hI; simpa [List.foldl] using hI
      | cons node rest ih =>
        intro rep stAcc hI
        simp only [List.foldl]
        cases rep.firstFailure with
        | some _ => exact ih rep stAcc hI
        | none =>
          cases hSlot : SystemState.lookupCdtSlotOfNode stAcc node with
          | none =>
            simp
            exact ih rep { stAcc with cdt := stAcc.cdt.removeNode node }
              (capabilityInvariantBundle_of_cdt_update stAcc _ hI)
          | some descAddr =>
            simp
            cases hDel : cspaceDeleteSlot descAddr stAcc with
            | error err =>
              simp
              exact ih _ { stAcc with cdt := stAcc.cdt.removeNode node }
                (capabilityInvariantBundle_of_cdt_update stAcc _ hI)
            | ok pair =>
              obtain ⟨_, stDel⟩ := pair
              simp
              have hDelInv := cspaceDeleteSlot_preserves_capabilityInvariantBundle stAcc stDel
                descAddr hI hDel
              have hDetachObj := SystemState.detachSlotFromCdt_objects_eq stDel descAddr
              rcases hDelInv with ⟨hU2, _, hA2, _⟩
              have hDetachInv : capabilityInvariantBundle (SystemState.detachSlotFromCdt stDel descAddr) :=
                ⟨cspaceSlotUnique_of_objects_eq stDel _ hU2 hDetachObj,
                 cspaceLookupSound_of_cspaceSlotUnique _ (cspaceSlotUnique_of_objects_eq stDel _ hU2 hDetachObj),
                 hA2, lifecycleAuthorityMonotonicity_holds _⟩
              exact ih _ _ (capabilityInvariantBundle_of_cdt_update _ _ hDetachInv)

-- ============================================================================
-- WS-E4: Preservation theorems for endpointReply
-- ============================================================================

/-- WS-F1/WS-E4/M-12: endpointReply preserves capabilityInvariantBundle.
Reply stores a TCB with message (not a CNode), so CSpace invariants are preserved.
Updated for WS-F1 message transfer. -/
theorem endpointReply_preserves_capabilityInvariantBundle
    (st st' : SystemState)
    (target : SeLe4n.ThreadId)
    (msg : IpcMessage)
    (hInv : capabilityInvariantBundle st)
    (hStep : endpointReply target msg st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  rcases hInv with ⟨hUnique, _hSound, hAttRule, _hLifecycle⟩
  unfold endpointReply at hStep
  cases hLookup : lookupTcb st target with
  | none => simp [hLookup] at hStep
  | some tcb =>
      simp only [hLookup] at hStep
      cases hIpc : tcb.ipcState with
      | ready => simp [hIpc] at hStep
      | blockedOnSend _ => simp [hIpc] at hStep
      | blockedOnReceive _ => simp [hIpc] at hStep
      | blockedOnNotification _ => simp [hIpc] at hStep
      | blockedOnReply epId =>
          simp only [hIpc] at hStep
          cases hTcb : storeTcbIpcStateAndMessage st target .ready (some msg) with
          | error e => simp [hTcb] at hStep
          | ok st1 =>
              simp only [hTcb, Except.ok.injEq, Prod.mk.injEq] at hStep
              obtain ⟨_, hStEq⟩ := hStep; subst hStEq
              -- storeTcbIpcStateAndMessage only writes TCBs, so CNode objects are unchanged
              have hCnodeBackward : ∀ (cnodeId : SeLe4n.ObjId) (cn : CNode),
                  st1.objects[cnodeId]? = some (.cnode cn) → st.objects[cnodeId]? = some (.cnode cn) := by
                intro cnodeId cn hCn1
                by_cases hEq : cnodeId = target.toObjId
                · -- At target.toObjId, storeTcbIpcStateAndMessage wrote a TCB, not a CNode
                  subst hEq
                  have hTargetTcb : ∃ tcb', st.objects[target.toObjId]? = some (.tcb tcb') := by
                    unfold lookupTcb at hLookup; cases hObj : st.objects[target.toObjId]? with
                    | none => simp [hObj] at hLookup
                    | some obj => cases obj with
                      | tcb t => exact ⟨t, rfl⟩
                      | _ => simp [hObj] at hLookup
                  have hTcbPost := storeTcbIpcStateAndMessage_tcb_exists_at_target st st1 target .ready (some msg) hTcb hTargetTcb
                  rcases hTcbPost with ⟨tcb', hTcb'⟩
                  rw [hTcb'] at hCn1; cases hCn1
                · rw [storeTcbIpcStateAndMessage_preserves_objects_ne st st1 target .ready (some msg) cnodeId hEq hTcb] at hCn1; exact hCn1
              have hU1 : cspaceSlotUnique st1 := by
                intro cnodeId cn hCn1; exact hUnique cnodeId cn (hCnodeBackward cnodeId cn hCn1)
              have hU := cspaceSlotUnique_of_objects_eq st1 (ensureRunnable st1 target)
                hU1 (ensureRunnable_preserves_objects st1 target)
              exact ⟨hU, cspaceLookupSound_of_cspaceSlotUnique _ hU, hAttRule,
                lifecycleAuthorityMonotonicity_holds _⟩

/-- M3 composed bundle entrypoint: M1 scheduler + M2 capability + M3 IPC. -/
def coreIpcInvariantBundle (st : SystemState) : Prop :=
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
def ipcSchedulerCouplingInvariantBundle (st : SystemState) : Prop :=
  coreIpcInvariantBundle st ∧ ipcSchedulerCoherenceComponent st

/-- M4-A composed bundle entrypoint:
M3.5 IPC+scheduler composition plus lifecycle metadata/invariant obligations. -/
def lifecycleCompositionInvariantBundle (st : SystemState) : Prop :=
  ipcSchedulerCouplingInvariantBundle st ∧ lifecycleInvariantBundle st

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
      | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ => cases hObj
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
      have hObjAtTarget : st'.objects[oid]? = some newObj := by
        rcases lifecycleRetypeObject_ok_as_storeObject st st' authority oid newObj hStep with
          ⟨_, _, _, _, _, _, hStore⟩
        exact lifecycle_storeObject_objects_eq st st' oid newObj hStore
      have hSomeEq : some newObj = some (.endpoint ep) := by
        simpa [hObjAtTarget] using hEndpoint
      have hNewObjEq : newObj = .endpoint ep := by
        injection hSomeEq
      exact hNewObjEndpointInv ep hNewObjEq
    · have hPreserved : st'.objects[oid]? = st.objects[oid]? :=
        lifecycleRetypeObject_ok_lookup_preserved_ne st st' authority target oid newObj hEq hStep
      have hEndpointSt : st.objects[oid]? = some (.endpoint ep) := by simpa [hPreserved] using hEndpoint
      exact hEndpointInv oid ep hEndpointSt
  · intro oid ntfn hNtfn
    by_cases hEq : oid = target
    · subst hEq
      have hObjAtTarget : st'.objects[oid]? = some newObj := by
        rcases lifecycleRetypeObject_ok_as_storeObject st st' authority oid newObj hStep with
          ⟨_, _, _, _, _, _, hStore⟩
        exact lifecycle_storeObject_objects_eq st st' oid newObj hStore
      have hSomeEq : some newObj = some (.notification ntfn) := by
        simpa [hObjAtTarget] using hNtfn
      have hNewObjEq : newObj = .notification ntfn := by
        injection hSomeEq
      exact hNewObjNotificationInv ntfn hNewObjEq
    · have hPreserved : st'.objects[oid]? = st.objects[oid]? :=
        lifecycleRetypeObject_ok_lookup_preserved_ne st st' authority target oid newObj hEq hStep
      have hNtfnSt : st.objects[oid]? = some (.notification ntfn) := by simpa [hPreserved] using hNtfn
      exact hNotificationInv oid ntfn hNtfnSt

theorem lifecycleRetypeObject_preserves_coreIpcInvariantBundle
    (st st' : SystemState)
    (authority : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj : KernelObject)
    (hInv : coreIpcInvariantBundle st)
    (hNewObjEndpointInv : ∀ ep, newObj = .endpoint ep → endpointInvariant ep)
    (hNewObjNotificationInv : ∀ ntfn, newObj = .notification ntfn → notificationInvariant ntfn)
    (hNewObjCNodeUniq : ∀ cn, newObj = .cnode cn → cn.slotsUnique)
    (hCurrentValid : currentThreadValid st')
    (hStep : lifecycleRetypeObject authority target newObj st = .ok ((), st')) :
    coreIpcInvariantBundle st' := by
  rcases hInv with ⟨hSched, hCap, hIpc⟩
  refine ⟨?_, ?_, ?_⟩
  · exact lifecycleRetypeObject_preserves_schedulerInvariantBundle st st' authority target newObj hSched
      hCurrentValid hStep
  · exact lifecycleRetypeObject_preserves_capabilityInvariantBundle st st' authority target newObj hCap
      hNewObjCNodeUniq hStep
  · exact lifecycleRetypeObject_preserves_ipcInvariant st st' authority target newObj hIpc hNewObjEndpointInv hNewObjNotificationInv hStep

theorem lifecycleRetypeObject_preserves_lifecycleCompositionInvariantBundle
    (st st' : SystemState)
    (authority : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj : KernelObject)
    (hInv : lifecycleCompositionInvariantBundle st)
    (hNewObjEndpointInv : ∀ ep, newObj = .endpoint ep → endpointInvariant ep)
    (hNewObjNotificationInv : ∀ ntfn, newObj = .notification ntfn → notificationInvariant ntfn)
    (hNewObjCNodeUniq : ∀ cn, newObj = .cnode cn → cn.slotsUnique)
    (hCurrentValid : currentThreadValid st')
    (hCoherence' : ipcSchedulerCoherenceComponent st')
    (hStep : lifecycleRetypeObject authority target newObj st = .ok ((), st')) :
    lifecycleCompositionInvariantBundle st' := by
  rcases hInv with ⟨hM35, hLifecycle⟩
  rcases hM35 with ⟨hM3, _hCoherence⟩
  have hM3' : coreIpcInvariantBundle st' :=
    lifecycleRetypeObject_preserves_coreIpcInvariantBundle st st' authority target newObj hM3
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

theorem lifecycleRevokeDeleteRetype_error_preserves_lifecycleCompositionInvariantBundle
    (st : SystemState)
    (authority cleanup : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj : KernelObject)
    (hAlias : authority = cleanup)
    (hInv : lifecycleCompositionInvariantBundle st) :
    lifecycleCompositionInvariantBundle st := by
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
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc }) st with
    | error e => simp [hStore] at hStep
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

theorem endpointSend_preserves_coreIpcInvariantBundle
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hInv : coreIpcInvariantBundle st)
    (hStep : endpointSend endpointId sender st = .ok ((), st')) :
    coreIpcInvariantBundle st' := by
  rcases hInv with ⟨hSched, hCap, hIpc⟩
  refine ⟨?_, ?_, ?_⟩
  · exact endpointSend_preserves_schedulerInvariantBundle st st' endpointId sender hSched hStep
  · exact endpointSend_preserves_capabilityInvariantBundle st st' endpointId sender hCap hStep
  · exact endpointSend_preserves_ipcInvariant st st' endpointId sender hIpc hStep

theorem endpointAwaitReceive_preserves_coreIpcInvariantBundle
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId)
    (hInv : coreIpcInvariantBundle st)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st')) :
    coreIpcInvariantBundle st' := by
  rcases hInv with ⟨hSched, hCap, hIpc⟩
  refine ⟨?_, ?_, ?_⟩
  · exact endpointAwaitReceive_preserves_schedulerInvariantBundle st st' endpointId receiver hSched hStep
  · exact endpointAwaitReceive_preserves_capabilityInvariantBundle st st' endpointId receiver hCap hStep
  · exact endpointAwaitReceive_preserves_ipcInvariant st st' endpointId receiver hIpc hStep

theorem endpointReceive_preserves_coreIpcInvariantBundle
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hInv : coreIpcInvariantBundle st)
    (hStep : endpointReceive endpointId st = .ok (sender, st')) :
    coreIpcInvariantBundle st' := by
  rcases hInv with ⟨hSched, hCap, hIpc⟩
  refine ⟨?_, ?_, ?_⟩
  · exact endpointReceive_preserves_schedulerInvariantBundle st st' endpointId sender hSched hStep
  · exact endpointReceive_preserves_capabilityInvariantBundle st st' endpointId sender hCap hStep
  · exact endpointReceive_preserves_ipcInvariant st st' endpointId sender hIpc hStep

theorem endpointSend_preserves_ipcSchedulerCouplingInvariantBundle
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hInv : ipcSchedulerCouplingInvariantBundle st)
    (hStep : endpointSend endpointId sender st = .ok ((), st')) :
    ipcSchedulerCouplingInvariantBundle st' := by
  rcases hInv with ⟨hM3Seed, hIpcSched⟩
  have hContract : ipcSchedulerContractPredicates st :=
    (ipcSchedulerCoherenceComponent_iff_contractPredicates st).1 hIpcSched
  refine ⟨?_, ?_⟩
  · exact endpointSend_preserves_coreIpcInvariantBundle st st' endpointId sender hM3Seed hStep
  · exact (ipcSchedulerCoherenceComponent_iff_contractPredicates st').2
      (endpointSend_preserves_ipcSchedulerContractPredicates st st' endpointId sender hContract hStep)

theorem endpointAwaitReceive_preserves_ipcSchedulerCouplingInvariantBundle
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId)
    (hInv : ipcSchedulerCouplingInvariantBundle st)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st')) :
    ipcSchedulerCouplingInvariantBundle st' := by
  rcases hInv with ⟨hM3Seed, hIpcSched⟩
  have hContract : ipcSchedulerContractPredicates st :=
    (ipcSchedulerCoherenceComponent_iff_contractPredicates st).1 hIpcSched
  refine ⟨?_, ?_⟩
  · exact endpointAwaitReceive_preserves_coreIpcInvariantBundle st st' endpointId receiver hM3Seed hStep
  · exact (ipcSchedulerCoherenceComponent_iff_contractPredicates st').2
      (endpointAwaitReceive_preserves_ipcSchedulerContractPredicates st st' endpointId receiver hContract hStep)

theorem endpointReceive_preserves_ipcSchedulerCouplingInvariantBundle
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hInv : ipcSchedulerCouplingInvariantBundle st)
    (hStep : endpointReceive endpointId st = .ok (sender, st')) :
    ipcSchedulerCouplingInvariantBundle st' := by
  rcases hInv with ⟨hM3Seed, hIpcSched⟩
  have hContract : ipcSchedulerContractPredicates st :=
    (ipcSchedulerCoherenceComponent_iff_contractPredicates st).1 hIpcSched
  refine ⟨?_, ?_⟩
  · exact endpointReceive_preserves_coreIpcInvariantBundle st st' endpointId sender hM3Seed hStep
  · exact (ipcSchedulerCoherenceComponent_iff_contractPredicates st').2
      (endpointReceive_preserves_ipcSchedulerContractPredicates st st' endpointId sender hContract hStep)

end SeLe4n.Kernel
