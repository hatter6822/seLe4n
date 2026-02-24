import SeLe4n.Kernel.IPC.Invariant
import SeLe4n.Kernel.Lifecycle.Invariant

/-!
# Capability Invariant Preservation Proofs (M2)

This module defines the capability invariant components, the composed bundle entrypoint,
and transition-level preservation theorems for CSpace operations. It also contains
cross-subsystem composed bundles (M3, M3.5, M4-A).

## Proof scope qualification (F-16)

**Substantive preservation theorems** (high assurance — prove invariant preservation
over *changed* state after a *successful* operation):
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

/-- Slot-level uniqueness/no-alias policy: lookup is deterministic for each slot address. -/
def cspaceSlotUnique (st : SystemState) : Prop :=
  ∀ addr cap₁ cap₂ st₁ st₂,
    cspaceLookupSlot addr st = .ok (cap₁, st₁) →
    cspaceLookupSlot addr st = .ok (cap₂, st₂) →
    cap₁ = cap₂

/-- Lookup soundness policy: successful lookup corresponds to concrete `(cnode, slot)` content. -/
def cspaceLookupSound (st : SystemState) : Prop :=
  ∀ addr cap st',
    cspaceLookupSlot addr st = .ok (cap, st') →
    st' = st ∧ SystemState.ownsSlot st addr.cnode addr ∧
      SystemState.lookupSlotCap st addr = some cap

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

/-- WS-E2 / C-01: Structural CNode slot-key uniqueness across all CNodes in the object store.

This is a genuine, non-tautological invariant that states every CNode object in the kernel's
object store has unique slot keys. Together with the meta-properties `cspaceSlotUnique` and
`cspaceLookupSound`, this provides a complete slot-uniqueness story:
- `cspaceSlotUnique` / `cspaceLookupSound` hold by construction (meta-properties of `cspaceLookupSlot`)
- `cspaceCNodeSlotsNoDup` holds by structural induction over CNode mutations (genuine invariant) -/
def cspaceCNodeSlotsNoDup (st : SystemState) : Prop :=
  ∀ oid cn, st.objects oid = some (.cnode cn) → cn.slotsNoDup

/-- Composed capability invariant bundle entrypoint.

The active lifecycle slice extends the M2 foundation bundle with explicit lifecycle-transition
authority obligations (`delete`/`revoke`) so lifecycle preservation can be stated against a
single invariant entrypoint.

WS-E2/C-01: The 5th component `cspaceCNodeSlotsNoDup` lifts the structural CNode slot-key
uniqueness guarantee from object-level to system-level. -/
def capabilityInvariantBundle (st : SystemState) : Prop :=
  cspaceSlotUnique st ∧ cspaceLookupSound st ∧ cspaceAttenuationRule ∧
    lifecycleAuthorityMonotonicity st ∧ cspaceCNodeSlotsNoDup st

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
  exact hCap.2.2.2.1

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
-- WS-E2 / H-03: Badge propagation correctness theorems
-- ============================================================================

/-- H-03 core: `mintDerivedCap` propagates the supplied badge value into the child capability. -/
theorem mintDerivedCap_badge_propagated
    (parent child : Capability)
    (rights : List AccessRight)
    (badge : Option SeLe4n.Badge)
    (hMint : mintDerivedCap parent rights badge = .ok child) :
    child.badge = badge := by
  by_cases hSubset : rightsSubset rights parent.rights = true
  · simp [mintDerivedCap, hSubset] at hMint
    cases hMint
    rfl
  · simp [mintDerivedCap, hSubset] at hMint

/-- H-03: Badge OR-merge is idempotent — signaling the same badge twice yields the same pending
badge as signaling it once (since `b ||| b = b` for bitwise OR). -/
theorem badge_merge_idempotent
    (badge : SeLe4n.Badge) :
    SeLe4n.Badge.ofNat (badge.toNat ||| badge.toNat) = badge := by
  simp [Nat.or_self, SeLe4n.Badge.ofNat, SeLe4n.Badge.toNat]

/-- H-03: When a notification has no pending badge, `notificationSignal` with a fresh badge
sets the pending badge to exactly that badge (identity case of the OR-merge). -/
theorem notificationSignal_fresh_badge_identity
    (st st' : SystemState)
    (notificationId : SeLe4n.ObjId)
    (badge : SeLe4n.Badge)
    (ntfn : Notification)
    (hObj : st.objects notificationId = some (.notification ntfn))
    (hWaiters : ntfn.waitingThreads = [])
    (hNoPending : ntfn.pendingBadge = none)
    (hStep : notificationSignal notificationId badge st = .ok ((), st')) :
    st'.objects notificationId =
      some (.notification { state := .active, waitingThreads := [], pendingBadge := some badge }) := by
  unfold notificationSignal at hStep
  simp [hObj, hWaiters, hNoPending, storeObject] at hStep
  cases hStep
  simp

/-- H-03 end-to-end: After a successful `cspaceMint` with an explicit badge, the minted
capability in the destination slot carries that badge, and the badge value is consistent
with the notification signaling path — i.e., the badge that would be delivered via
`notificationSignal` matches the badge recorded in the minted capability. -/
theorem cspaceMint_badge_notification_consistent
    (st st' : SystemState)
    (src dst : CSpaceAddr)
    (rights : List AccessRight)
    (badge : Option SeLe4n.Badge)
    (hStep : cspaceMint src dst rights badge st = .ok ((), st')) :
    ∃ parent child,
      cspaceLookupSlot src st = .ok (parent, st) ∧
      cspaceLookupSlot dst st' = .ok (child, st') ∧
      child.badge = badge ∧
      child.target = parent.target := by
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
          have hBadge := mintDerivedCap_badge_propagated parent child rights badge hMint
          have hTarget := mintDerivedCap_target_preserved_with_badge_override parent child rights badge hMint
          have hInsert : cspaceInsertSlot dst child st = .ok ((), st') := by
            simpa [hSrc, hMint] using hStep
          have hLookup := cspaceInsertSlot_lookup_eq st st' dst child hInsert
          exact ⟨parent, child, rfl, hLookup, hBadge, hTarget⟩

theorem cspaceSlotUnique_holds (st : SystemState) :
    cspaceSlotUnique st := by
  intro addr cap₁ cap₂ st₁ st₂ h₁ h₂
  have hSt₁ : st₁ = st := cspaceLookupSlot_preserves_state st st₁ addr cap₁ h₁
  have hSt₂ : st₂ = st := cspaceLookupSlot_preserves_state st st₂ addr cap₂ h₂
  subst st₁
  subst st₂
  have hEq : (.ok (cap₁, st) : Except KernelError (Capability × SystemState)) = .ok (cap₂, st) := by
    simpa [h₁] using h₂
  cases hEq
  rfl

theorem cspaceLookupSound_holds (st : SystemState) :
    cspaceLookupSound st := by
  intro addr cap st' hStep
  have hEq : st' = st := cspaceLookupSlot_preserves_state st st' addr cap hStep
  have hOk : cspaceLookupSlot addr st = .ok (cap, st) := by simpa [hEq] using hStep
  have hCap : SystemState.lookupSlotCap st addr = some cap :=
    (cspaceLookupSlot_ok_iff_lookupSlotCap st addr cap).1 hOk
  have hOwn : SystemState.ownsSlot st addr.cnode addr :=
    cspaceLookupSlot_ok_implies_ownsSlot st addr cap hOk
  exact ⟨hEq, hOwn, hCap⟩

theorem cspaceLookupSound_implies_ownsSlot
    (st : SystemState)
    (hSound : cspaceLookupSound st)
    (addr : CSpaceAddr)
    (cap : Capability)
    (st' : SystemState)
    (hStep : cspaceLookupSlot addr st = .ok (cap, st')) :
    SystemState.ownsSlot st addr.cnode addr := by
  exact (hSound addr cap st' hStep).2.1

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

/-- WS-E2/C-01: Constructor for the capability invariant bundle given the genuine
`cspaceCNodeSlotsNoDup` component. The meta-property components are derived automatically. -/
theorem capabilityInvariantBundle_of_slotsNoDup
    (st : SystemState)
    (hNoDup : cspaceCNodeSlotsNoDup st) :
    capabilityInvariantBundle st := by
  exact ⟨cspaceSlotUnique_holds st, cspaceLookupSound_holds st, cspaceAttenuationRule_holds,
    lifecycleAuthorityMonotonicity_holds st, hNoDup⟩

-- ============================================================================
-- WS-E2 / H-01: Compositional storeObject preservation for CNode slot NoDup
-- ============================================================================

/-- Generic storeObject preservation for `cspaceCNodeSlotsNoDup`: if the stored object at `id`
either (a) is not a CNode, or (b) is a CNode that satisfies `slotsNoDup`, then the system-level
NoDup property is preserved. -/
theorem storeObject_preserves_cspaceCNodeSlotsNoDup
    (st st' : SystemState)
    (id : SeLe4n.ObjId)
    (obj : KernelObject)
    (hNoDup : cspaceCNodeSlotsNoDup st)
    (hStore : storeObject id obj st = .ok ((), st'))
    (hObj : ∀ cn, obj = .cnode cn → cn.slotsNoDup) :
    cspaceCNodeSlotsNoDup st' := by
  intro oid cn hOidCn
  by_cases hEq : oid = id
  · subst hEq
    have hObjEq : st'.objects oid = some obj := storeObject_objects_eq st st' oid obj hStore
    rw [hObjEq] at hOidCn
    cases hOidCn
    exact hObj cn rfl
  · have hPreserved : st'.objects oid = st.objects oid :=
      storeObject_objects_ne st st' id oid obj hEq hStore
    rw [hPreserved] at hOidCn
    exact hNoDup oid cn hOidCn

/-- Specialization: storing a non-CNode object (endpoint, notification, tcb, vspaceRoot)
trivially preserves `cspaceCNodeSlotsNoDup`. -/
theorem storeObject_nonCNode_preserves_cspaceCNodeSlotsNoDup
    (st st' : SystemState)
    (id : SeLe4n.ObjId)
    (obj : KernelObject)
    (hNoDup : cspaceCNodeSlotsNoDup st)
    (hStore : storeObject id obj st = .ok ((), st'))
    (hNotCNode : ∀ cn, obj ≠ .cnode cn) :
    cspaceCNodeSlotsNoDup st' := by
  exact storeObject_preserves_cspaceCNodeSlotsNoDup st st' id obj hNoDup hStore
    (fun cn hEq => absurd hEq (hNotCNode cn))

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

/-- WS-E2/H-01: Compositional — derives post-state NoDup from pre-state via `insert_preserves_slotsNoDup`. -/
theorem cspaceInsertSlot_preserves_cspaceCNodeSlotsNoDup
    (st st' : SystemState)
    (addr : CSpaceAddr)
    (cap : Capability)
    (hNoDup : cspaceCNodeSlotsNoDup st)
    (hStep : cspaceInsertSlot addr cap st = .ok ((), st')) :
    cspaceCNodeSlotsNoDup st' := by
  intro oid cn' hOidCn
  unfold cspaceInsertSlot at hStep
  cases hObj : st.objects addr.cnode with
  | none => simp [hObj] at hStep
  | some obj =>
      cases obj with
      | tcb _ | endpoint _ | notification _ | vspaceRoot _ => simp [hObj] at hStep
      | cnode cn =>
          simp [hObj] at hStep
          cases hStore : storeObject addr.cnode (.cnode (cn.insert addr.slot cap)) st with
          | error e => simp [hStore] at hStep
          | ok pair =>
              obtain ⟨_, stMid⟩ := pair
              simp [hStore] at hStep
              have hRefObjs := storeCapabilityRef_preserves_objects stMid st' addr (some cap.target) hStep
              rw [hRefObjs] at hOidCn
              by_cases hEq : oid = addr.cnode
              · subst hEq
                have hObjEq := storeObject_objects_eq st stMid addr.cnode
                  (.cnode (cn.insert addr.slot cap)) hStore
                rw [hObjEq] at hOidCn
                cases hOidCn
                exact CNode.insert_preserves_slotsNoDup cn addr.slot cap (hNoDup addr.cnode cn hObj)
              · have hPreserved := storeObject_objects_ne st stMid addr.cnode oid
                  (.cnode (cn.insert addr.slot cap)) hEq hStore
                rw [hPreserved] at hOidCn
                exact hNoDup oid cn' hOidCn

theorem cspaceInsertSlot_preserves_capabilityInvariantBundle
    (st st' : SystemState)
    (addr : CSpaceAddr)
    (cap : Capability)
    (hInv : capabilityInvariantBundle st)
    (hStep : cspaceInsertSlot addr cap st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  rcases hInv with ⟨_hUnique, _hSound, hAttRule, _hLifecycle, hNoDup⟩
  exact ⟨cspaceSlotUnique_holds st', cspaceLookupSound_holds st', hAttRule,
    lifecycleAuthorityMonotonicity_holds st',
    cspaceInsertSlot_preserves_cspaceCNodeSlotsNoDup st st' addr cap hNoDup hStep⟩

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

/-- WS-E2/H-01: Compositional — derives post-state NoDup from pre-state via `remove_preserves_slotsNoDup`. -/
theorem cspaceDeleteSlot_preserves_cspaceCNodeSlotsNoDup
    (st st' : SystemState)
    (addr : CSpaceAddr)
    (hNoDup : cspaceCNodeSlotsNoDup st)
    (hStep : cspaceDeleteSlot addr st = .ok ((), st')) :
    cspaceCNodeSlotsNoDup st' := by
  intro oid cn' hOidCn
  unfold cspaceDeleteSlot at hStep
  cases hObj : st.objects addr.cnode with
  | none => simp [hObj] at hStep
  | some obj =>
      cases obj with
      | tcb _ | endpoint _ | notification _ | vspaceRoot _ => simp [hObj] at hStep
      | cnode cn =>
          simp [hObj] at hStep
          cases hStore : storeObject addr.cnode (.cnode (cn.remove addr.slot)) st with
          | error e => simp [hStore] at hStep
          | ok pair =>
              obtain ⟨_, stMid⟩ := pair
              simp [hStore] at hStep
              have hRefObjs := storeCapabilityRef_preserves_objects stMid st' addr none hStep
              rw [hRefObjs] at hOidCn
              by_cases hEq : oid = addr.cnode
              · subst hEq
                have hObjEq := storeObject_objects_eq st stMid addr.cnode
                  (.cnode (cn.remove addr.slot)) hStore
                rw [hObjEq] at hOidCn
                cases hOidCn
                exact CNode.remove_preserves_slotsNoDup cn addr.slot (hNoDup addr.cnode cn hObj)
              · have hPreserved := storeObject_objects_ne st stMid addr.cnode oid
                  (.cnode (cn.remove addr.slot)) hEq hStore
                rw [hPreserved] at hOidCn
                exact hNoDup oid cn' hOidCn

theorem cspaceDeleteSlot_preserves_capabilityInvariantBundle
    (st st' : SystemState)
    (addr : CSpaceAddr)
    (hInv : capabilityInvariantBundle st)
    (hStep : cspaceDeleteSlot addr st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  rcases hInv with ⟨_hUnique, _hSound, hAttRule, _hLifecycle, hNoDup⟩
  exact ⟨cspaceSlotUnique_holds st', cspaceLookupSound_holds st', hAttRule,
    lifecycleAuthorityMonotonicity_holds st',
    cspaceDeleteSlot_preserves_cspaceCNodeSlotsNoDup st st' addr hNoDup hStep⟩

/-- WS-E2/H-01: Compositional — derives post-state NoDup from pre-state via
`revokeTargetLocal_preserves_slotsNoDup` + `clearCapabilityRefs` frame. -/
theorem cspaceRevoke_preserves_capabilityInvariantBundle
    (st st' : SystemState)
    (addr : CSpaceAddr)
    (hInv : capabilityInvariantBundle st)
    (hStep : cspaceRevoke addr st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  rcases hInv with ⟨_hUnique, _hSound, hAttRule, _hLifecycle, hNoDup⟩
  refine ⟨cspaceSlotUnique_holds st', cspaceLookupSound_holds st', hAttRule,
    lifecycleAuthorityMonotonicity_holds st', ?_⟩
  -- cspaceRevoke does: lookup → storeObject (revokeTargetLocal) → clearCapabilityRefs
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
          | tcb _ | endpoint _ | notification _ | vspaceRoot _ => simp [hLookup, hObj] at hStep
          | cnode cn =>
              simp [hLookup, hObj] at hStep
              -- Extract the storeObject + clearCapabilityRefs composition
              cases hStore : storeObject addr.cnode (.cnode (cn.revokeTargetLocal addr.slot parent.target)) st with
              | error e => simp [hStore] at hStep
              | ok pair =>
                  obtain ⟨_, stStored⟩ := pair
                  simp [hStore] at hStep
                  have hObjStored : st'.objects = stStored.objects :=
                    clearCapabilityRefs_preserves_objects stStored st' _ hStep
                  intro oid cn' hOidCn
                  rw [hObjStored] at hOidCn
                  by_cases hEq : oid = addr.cnode
                  · subst hEq
                    have hObjEq := storeObject_objects_eq st stStored addr.cnode
                      (.cnode (cn.revokeTargetLocal addr.slot parent.target)) hStore
                    rw [hObjEq] at hOidCn
                    cases hOidCn
                    exact CNode.revokeTargetLocal_preserves_slotsNoDup cn addr.slot parent.target
                      (hNoDup addr.cnode cn hObj)
                  · have hPreserved := storeObject_objects_ne st stStored addr.cnode oid
                      (.cnode (cn.revokeTargetLocal addr.slot parent.target)) hEq hStore
                    rw [hPreserved] at hOidCn
                    exact hNoDup oid cn' hOidCn


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

/-- WS-E2/H-01: Compositional — requires newObj CNode NoDup hypothesis for the 5th component. -/
theorem lifecycleRetypeObject_preserves_capabilityInvariantBundle
    (st st' : SystemState)
    (authority : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj : KernelObject)
    (hInv : capabilityInvariantBundle st)
    (hNewObjCNodeNoDup : ∀ cn, newObj = .cnode cn → cn.slotsNoDup)
    (hStep : lifecycleRetypeObject authority target newObj st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  rcases hInv with ⟨_hUnique, _hSound, hAttRule, _hLifecycle, hNoDup⟩
  refine ⟨cspaceSlotUnique_holds st', cspaceLookupSound_holds st', hAttRule,
    lifecycleAuthorityMonotonicity_holds st', ?_⟩
  rcases lifecycleRetypeObject_ok_as_storeObject st st' authority target newObj hStep with
    ⟨_, _, _, _, _, _, hStore⟩
  exact storeObject_preserves_cspaceCNodeSlotsNoDup st st' target newObj hNoDup hStore hNewObjCNodeNoDup

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
    (hNewObjCNodeNoDup : ∀ cn, newObj = .cnode cn → cn.slotsNoDup)
    (hCurrentValid : currentThreadValid st')
    (hStep : lifecycleRetypeObject authority target newObj st = .ok ((), st')) :
    m3IpcSeedInvariantBundle st' := by
  rcases hInv with ⟨hSched, hCap, hIpc⟩
  refine ⟨?_, ?_, ?_⟩
  · exact lifecycleRetypeObject_preserves_schedulerInvariantBundle st st' authority target newObj hSched
      hCurrentValid hStep
  · exact lifecycleRetypeObject_preserves_capabilityInvariantBundle st st' authority target newObj hCap
      hNewObjCNodeNoDup hStep
  · exact lifecycleRetypeObject_preserves_ipcInvariant st st' authority target newObj hIpc hNewObjEndpointInv hNewObjNotificationInv hStep

theorem lifecycleRetypeObject_preserves_m4aLifecycleInvariantBundle
    (st st' : SystemState)
    (authority : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj : KernelObject)
    (hInv : m4aLifecycleInvariantBundle st)
    (hNewObjEndpointInv : ∀ ep, newObj = .endpoint ep → endpointInvariant ep)
    (hNewObjNotificationInv : ∀ ntfn, newObj = .notification ntfn → notificationInvariant ntfn)
    (hNewObjCNodeNoDup : ∀ cn, newObj = .cnode cn → cn.slotsNoDup)
    (hCurrentValid : currentThreadValid st')
    (hCoherence' : ipcSchedulerCoherenceComponent st')
    (hStep : lifecycleRetypeObject authority target newObj st = .ok ((), st')) :
    m4aLifecycleInvariantBundle st' := by
  rcases hInv with ⟨hM35, hLifecycle⟩
  rcases hM35 with ⟨hM3, _hCoherence⟩
  have hM3' : m3IpcSeedInvariantBundle st' :=
    lifecycleRetypeObject_preserves_m3IpcSeedInvariantBundle st st' authority target newObj hM3
      hNewObjEndpointInv hNewObjNotificationInv hNewObjCNodeNoDup hCurrentValid hStep
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
    (hNewObjCNodeNoDup : ∀ cn, newObj = .cnode cn → cn.slotsNoDup)
    (hStep : lifecycleRevokeDeleteRetype authority cleanup target newObj st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  rcases lifecycleRevokeDeleteRetype_ok_implies_staged_steps st st' authority cleanup target newObj hStep with
    ⟨stRevoked, stDeleted, _hNe, hRevoke, hDelete, _hLookupDeleted, hRetype⟩
  have hRevoked : capabilityInvariantBundle stRevoked :=
    cspaceRevoke_preserves_capabilityInvariantBundle st stRevoked cleanup hInv hRevoke
  have hDeleted : capabilityInvariantBundle stDeleted :=
    cspaceDeleteSlot_preserves_capabilityInvariantBundle stRevoked stDeleted cleanup hRevoked hDelete
  exact lifecycleRetypeObject_preserves_capabilityInvariantBundle stDeleted st' authority target newObj
    hDeleted hNewObjCNodeNoDup hRetype

theorem lifecycleRevokeDeleteRetype_preserves_lifecycleCapabilityStaleAuthorityInvariant
    (st st' : SystemState)
    (authority cleanup : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj : KernelObject)
    (hCap : capabilityInvariantBundle st)
    (hNewObjCNodeNoDup : ∀ cn, newObj = .cnode cn → cn.slotsNoDup)
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
    lifecycleRevokeDeleteRetype_preserves_capabilityInvariantBundle st st' authority cleanup target newObj
      hCap hNewObjCNodeNoDup hStep
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

/-- WS-E2/H-01: Compositional — endpoint stores cannot modify CNodes, so NoDup is preserved trivially. -/
theorem endpointSend_preserves_capabilityInvariantBundle
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hInv : capabilityInvariantBundle st)
    (hStep : endpointSend endpointId sender st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  rcases hInv with ⟨_hUnique, _hSound, hAttRule, _hLifecycle, hNoDup⟩
  refine ⟨cspaceSlotUnique_holds st', cspaceLookupSound_holds st', hAttRule,
    lifecycleAuthorityMonotonicity_holds st', ?_⟩
  rcases endpointSend_ok_as_storeObject st st' endpointId sender hStep with ⟨ep', hStore⟩
  exact storeObject_nonCNode_preserves_cspaceCNodeSlotsNoDup st st' endpointId (.endpoint ep') hNoDup
    hStore (fun cn h => by cases h)

/-- WS-E2/H-01: Compositional — endpoint stores cannot modify CNodes, so NoDup is preserved trivially. -/
theorem endpointAwaitReceive_preserves_capabilityInvariantBundle
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId)
    (hInv : capabilityInvariantBundle st)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  rcases hInv with ⟨_hUnique, _hSound, hAttRule, _hLifecycle, hNoDup⟩
  refine ⟨cspaceSlotUnique_holds st', cspaceLookupSound_holds st', hAttRule,
    lifecycleAuthorityMonotonicity_holds st', ?_⟩
  rcases endpointAwaitReceive_ok_as_storeObject st st' endpointId receiver hStep with ⟨ep', hStore⟩
  exact storeObject_nonCNode_preserves_cspaceCNodeSlotsNoDup st st' endpointId (.endpoint ep') hNoDup
    hStore (fun cn h => by cases h)

/-- WS-E2/H-01: Compositional — endpoint stores cannot modify CNodes, so NoDup is preserved trivially. -/
theorem endpointReceive_preserves_capabilityInvariantBundle
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hInv : capabilityInvariantBundle st)
    (hStep : endpointReceive endpointId st = .ok (sender, st')) :
    capabilityInvariantBundle st' := by
  rcases hInv with ⟨_hUnique, _hSound, hAttRule, _hLifecycle, hNoDup⟩
  refine ⟨cspaceSlotUnique_holds st', cspaceLookupSound_holds st', hAttRule,
    lifecycleAuthorityMonotonicity_holds st', ?_⟩
  rcases endpointReceive_ok_as_storeObject st st' endpointId sender hStep with ⟨ep', hStore⟩
  exact storeObject_nonCNode_preserves_cspaceCNodeSlotsNoDup st st' endpointId (.endpoint ep') hNoDup
    hStore (fun cn h => by cases h)

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
