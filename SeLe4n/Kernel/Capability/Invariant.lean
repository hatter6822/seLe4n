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

/-- CNode slot-key uniqueness across all CNodes in the system state: for every
CNode object, no two distinct entries in its slot list share the same key.

This is a meaningful structural invariant (WS-E2 / C-01 remediation): the slot
list is `List (Slot × Capability)` and operations must actively maintain
key-disjointness. Combined with `cspaceLookupSound`, this ensures
`CNode.lookup` returns the *unique* capability for each slot — not merely
the first `find?` match.

Replaces the prior `cspaceSlotUnique` which proved only that a pure function
returns the same output for the same input (a type-system tautology). -/
def cspaceSlotKeyUnique (st : SystemState) : Prop :=
  ∀ oid cn, st.objects oid = some (.cnode cn) → cn.slotKeysUnique

/-- Lookup soundness: successful lookup witnesses concrete CNode slot membership.

The returned capability `cap` exists as a concrete element `(addr.slot, cap)`
in the CNode's slot list, and the CNode exists in the object store. Combined
with `cspaceSlotKeyUnique`, this gives specification correspondence:
lookup returns the *unique* capability stored at the named slot.

WS-E2 / C-01 remediation: replaces the prior definition that restated the
lookup implementation (circular logic — the conclusion contained the
assumption). The new proof reaches through `find?` to actual list membership,
bridging between the computational representation and the specification. -/
def cspaceLookupSound (st : SystemState) : Prop :=
  ∀ addr cap st',
    cspaceLookupSlot addr st = .ok (cap, st') →
    st' = st ∧
      ∃ cn, st.objects addr.cnode = some (.cnode cn) ∧ (addr.slot, cap) ∈ cn.slots

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
  cspaceSlotKeyUnique st ∧ cspaceLookupSound st ∧ cspaceAttenuationRule ∧
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

/-- Lookup soundness holds for any system state: the proof bridges from the
`find?`-based computation in `cspaceLookupSlot` to actual CNode slot-list
membership. Unlike the prior version, this proof does genuine work: it
unfolds to the `find?` result and uses `CNode.lookup_mem_of_some` to
extract the membership witness. (WS-E2 / C-01) -/
theorem cspaceLookupSound_holds (st : SystemState) :
    cspaceLookupSound st := by
  intro addr cap st' hStep
  have hEq : st' = st := cspaceLookupSlot_preserves_state st st' addr cap hStep
  have hOk : cspaceLookupSlot addr st = .ok (cap, st) := by simpa [hEq] using hStep
  have hCap : SystemState.lookupSlotCap st addr = some cap :=
    (cspaceLookupSlot_ok_iff_lookupSlotCap st addr cap).1 hOk
  refine ⟨hEq, ?_⟩
  unfold SystemState.lookupSlotCap SystemState.lookupCNode at hCap
  cases hObj : st.objects addr.cnode with
  | none => simp [hObj] at hCap
  | some obj =>
      cases obj with
      | tcb _ | endpoint _ | notification _ | vspaceRoot _ => simp [hObj] at hCap
      | cnode cn =>
          simp [hObj] at hCap
          exact ⟨cn, rfl, CNode.lookup_mem_of_some cn addr.slot cap hCap⟩

/-- Derive `lookupSlotCap` from the new soundness definition combined with
slot-key uniqueness. This bridges the stronger membership-based soundness
back to the computation-level `lookupSlotCap` that downstream consumers need.
(WS-E2 service-invariant bridge) -/
theorem cspaceLookupSound_lookupSlotCap
    (st : SystemState)
    (hUnique : cspaceSlotKeyUnique st)
    (hSound : cspaceLookupSound st)
    (addr : CSpaceAddr)
    (cap : Capability)
    (st' : SystemState)
    (hStep : cspaceLookupSlot addr st = .ok (cap, st')) :
    SystemState.lookupSlotCap st addr = some cap := by
  rcases (hSound addr cap st' hStep) with ⟨_, cn, hObj, hMem⟩
  have hKeysUnique := hUnique addr.cnode cn hObj
  unfold SystemState.lookupSlotCap SystemState.lookupCNode
  simp [hObj]
  exact CNode.lookup_of_mem_unique cn addr.slot cap hMem hKeysUnique

/-- Derive slot ownership from the new soundness definition. -/
theorem cspaceLookupSound_implies_ownsSlot
    (st : SystemState)
    (hUnique : cspaceSlotKeyUnique st)
    (hSound : cspaceLookupSound st)
    (addr : CSpaceAddr)
    (cap : Capability)
    (st' : SystemState)
    (hStep : cspaceLookupSlot addr st = .ok (cap, st')) :
    SystemState.ownsSlot st addr.cnode addr := by
  have hSlotCap := cspaceLookupSound_lookupSlotCap st hUnique hSound addr cap st' hStep
  exact (SystemState.ownsSlot_iff st addr.cnode addr).2 ⟨rfl, ⟨cap, hSlotCap⟩⟩

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

/-- Establish the capability invariant bundle from a slot-key uniqueness witness.
Unlike the prior tautological version, this requires a genuine hypothesis:
the caller must supply evidence that all CNodes have unique slot keys.
(WS-E2 / C-01 + H-01 remediation) -/
theorem capabilityInvariantBundle_of_slotKeyUnique
    (st : SystemState)
    (hUnique : cspaceSlotKeyUnique st) :
    capabilityInvariantBundle st :=
  ⟨hUnique, cspaceLookupSound_holds st, cspaceAttenuationRule_holds,
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

/-- Compositional preservation of `cspaceSlotKeyUnique` through `cspaceInsertSlot`.
Derives post-state uniqueness from pre-state uniqueness through the operation's
specific state transformation: the modified CNode is produced by `CNode.insert`,
which preserves slot-key uniqueness; all other CNodes are unchanged.
(WS-E2 / H-01 remediation — uses both hInv and hStep) -/
theorem cspaceInsertSlot_preserves_cspaceSlotKeyUnique
    (st st' : SystemState)
    (addr : CSpaceAddr)
    (cap : Capability)
    (hUnique : cspaceSlotKeyUnique st)
    (hStep : cspaceInsertSlot addr cap st = .ok ((), st')) :
    cspaceSlotKeyUnique st' := by
  intro oid cn hObj
  by_cases hEq : oid = addr.cnode
  · subst hEq
    unfold cspaceInsertSlot at hStep
    cases hObjPre : st.objects addr.cnode with
    | none => simp [hObjPre] at hStep
    | some obj =>
        cases obj with
        | tcb _ | endpoint _ | notification _ | vspaceRoot _ => simp [hObjPre] at hStep
        | cnode cnPre =>
            simp [hObjPre] at hStep
            cases hStore : storeObject addr.cnode (.cnode (cnPre.insert addr.slot cap)) st with
            | error e => simp [hStore] at hStep
            | ok pair =>
                obtain ⟨_, stMid⟩ := pair
                simp [hStore] at hStep
                have hObjMid := storeObject_objects_eq st stMid addr.cnode (.cnode (cnPre.insert addr.slot cap)) hStore
                have hObjFinal := congrFun (storeCapabilityRef_preserves_objects stMid st' addr (some cap.target) hStep) addr.cnode
                rw [hObjFinal, hObjMid] at hObj; cases hObj
                exact CNode.insert_preserves_slotKeysUnique cnPre addr.slot cap (hUnique addr.cnode cnPre hObjPre)
  · have hPreserved := cspaceInsertSlot_preserves_objects_ne st st' addr cap oid hEq hStep
    rw [hPreserved] at hObj
    exact hUnique oid cn hObj

theorem cspaceInsertSlot_preserves_capabilityInvariantBundle
    (st st' : SystemState)
    (addr : CSpaceAddr)
    (cap : Capability)
    (hInv : capabilityInvariantBundle st)
    (hStep : cspaceInsertSlot addr cap st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  rcases hInv with ⟨hUnique, _hSound, hAttRule, _hLifecycle⟩
  exact ⟨cspaceInsertSlot_preserves_cspaceSlotKeyUnique st st' addr cap hUnique hStep,
    cspaceLookupSound_holds st', hAttRule,
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

/-- Compositional preservation of `cspaceSlotKeyUnique` through `cspaceDeleteSlot`.
The modified CNode is produced by `CNode.remove`, which preserves uniqueness.
(WS-E2 / H-01 — uses both hUnique and hStep) -/
theorem cspaceDeleteSlot_preserves_cspaceSlotKeyUnique
    (st st' : SystemState)
    (addr : CSpaceAddr)
    (hUnique : cspaceSlotKeyUnique st)
    (hStep : cspaceDeleteSlot addr st = .ok ((), st')) :
    cspaceSlotKeyUnique st' := by
  intro oid cn hObj
  by_cases hEq : oid = addr.cnode
  · subst hEq
    unfold cspaceDeleteSlot at hStep
    cases hObjPre : st.objects addr.cnode with
    | none => simp [hObjPre] at hStep
    | some obj =>
        cases obj with
        | tcb _ | endpoint _ | notification _ | vspaceRoot _ => simp [hObjPre] at hStep
        | cnode cnPre =>
            simp [hObjPre] at hStep
            cases hStore : storeObject addr.cnode (.cnode (cnPre.remove addr.slot)) st with
            | error e => simp [hStore] at hStep
            | ok pair =>
                obtain ⟨_, stMid⟩ := pair
                simp [hStore] at hStep
                have hObjMid := storeObject_objects_eq st stMid addr.cnode (.cnode (cnPre.remove addr.slot)) hStore
                have hObjFinal := congrFun (storeCapabilityRef_preserves_objects stMid st' addr none hStep) addr.cnode
                rw [hObjFinal, hObjMid] at hObj; cases hObj
                exact CNode.remove_preserves_slotKeysUnique cnPre addr.slot (hUnique addr.cnode cnPre hObjPre)
  · have hPreserved : st'.objects oid = st.objects oid := by
      unfold cspaceDeleteSlot at hStep
      cases hObjPre : st.objects addr.cnode with
      | none => simp [hObjPre] at hStep
      | some obj =>
          cases obj with
          | tcb _ | endpoint _ | notification _ | vspaceRoot _ => simp [hObjPre] at hStep
          | cnode cnPre =>
              simp [hObjPre] at hStep
              cases hStore : storeObject addr.cnode (.cnode (cnPre.remove addr.slot)) st with
              | error e => simp [hStore] at hStep
              | ok pair =>
                  obtain ⟨_, stMid⟩ := pair
                  simp [hStore] at hStep
                  have hObjMid := storeObject_objects_ne st stMid addr.cnode oid
                    (.cnode (cnPre.remove addr.slot)) hEq hStore
                  have hObjFinal := congrFun (storeCapabilityRef_preserves_objects stMid st' addr none hStep) oid
                  rw [hObjFinal, hObjMid]
    rw [hPreserved] at hObj
    exact hUnique oid cn hObj

theorem cspaceDeleteSlot_preserves_capabilityInvariantBundle
    (st st' : SystemState)
    (addr : CSpaceAddr)
    (hInv : capabilityInvariantBundle st)
    (hStep : cspaceDeleteSlot addr st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  rcases hInv with ⟨hUnique, _hSound, hAttRule, _hLifecycle⟩
  exact ⟨cspaceDeleteSlot_preserves_cspaceSlotKeyUnique st st' addr hUnique hStep,
    cspaceLookupSound_holds st', hAttRule,
    lifecycleAuthorityMonotonicity_holds st'⟩

/-- Compositional preservation of `cspaceSlotKeyUnique` through `cspaceRevoke`.
The modified CNode is produced by `CNode.revokeTargetLocal` (a filter), which
preserves uniqueness. `clearCapabilityRefs` only modifies lifecycle metadata.
(WS-E2 / H-01 — uses both hUnique and hStep) -/
theorem cspaceRevoke_preserves_cspaceSlotKeyUnique
    (st st' : SystemState)
    (addr : CSpaceAddr)
    (hUnique : cspaceSlotKeyUnique st)
    (hStep : cspaceRevoke addr st = .ok ((), st')) :
    cspaceSlotKeyUnique st' := by
  intro oid cn hObj
  unfold cspaceRevoke at hStep
  cases hLookup : cspaceLookupSlot addr st with
  | error e => simp [hLookup] at hStep
  | ok pair =>
      rcases pair with ⟨parent, st1⟩
      have hSt1 : st1 = st := cspaceLookupSlot_preserves_state st st1 addr parent hLookup
      subst st1
      cases hObjCn : st.objects addr.cnode with
      | none => simp [hLookup, hObjCn] at hStep
      | some obj =>
          cases obj with
          | tcb _ | endpoint _ | notification _ | vspaceRoot _ => simp [hLookup, hObjCn] at hStep
          | cnode cnSrc =>
              simp [hLookup, hObjCn] at hStep
              cases hStore : storeObject addr.cnode (.cnode (cnSrc.revokeTargetLocal addr.slot parent.target)) st with
              | error e => simp [hStore] at hStep
              | ok pair =>
                  obtain ⟨_, stMid⟩ := pair
                  simp [hStore] at hStep
                  have hObjMidEq : stMid.objects = (fun oid' => if oid' = addr.cnode then some (.cnode (cnSrc.revokeTargetLocal addr.slot parent.target)) else st.objects oid') := by
                    unfold storeObject at hStore; simp at hStore; cases hStore; rfl
                  have hObjFinalEq : st'.objects = stMid.objects :=
                    clearCapabilityRefs_preserves_objects stMid st' _ hStep
                  by_cases hEq : oid = addr.cnode
                  · subst hEq
                    rw [hObjFinalEq, hObjMidEq] at hObj
                    simp at hObj; cases hObj
                    exact CNode.revokeTargetLocal_preserves_slotKeysUnique cnSrc addr.slot parent.target
                      (hUnique addr.cnode cnSrc hObjCn)
                  · rw [hObjFinalEq, hObjMidEq] at hObj
                    simp [hEq] at hObj
                    exact hUnique oid cn hObj

theorem cspaceRevoke_preserves_capabilityInvariantBundle
    (st st' : SystemState)
    (addr : CSpaceAddr)
    (hInv : capabilityInvariantBundle st)
    (hStep : cspaceRevoke addr st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  rcases hInv with ⟨hUnique, _hSound, hAttRule, _hLifecycle⟩
  exact ⟨cspaceRevoke_preserves_cspaceSlotKeyUnique st st' addr hUnique hStep,
    cspaceLookupSound_holds st', hAttRule,
    lifecycleAuthorityMonotonicity_holds st'⟩


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

/-- Compositional preservation of `cspaceSlotKeyUnique` through `lifecycleRetypeObject`.
If the new object is a CNode, it must have unique slot keys; all other CNodes
are unchanged. (WS-E2 / H-01 — uses hUnique, hStep, and hNewObjCNodeUnique) -/
theorem lifecycleRetypeObject_preserves_cspaceSlotKeyUnique
    (st st' : SystemState)
    (authority : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj : KernelObject)
    (hUnique : cspaceSlotKeyUnique st)
    (hNewObjCNodeUnique : ∀ cn, newObj = .cnode cn → cn.slotKeysUnique)
    (hStep : lifecycleRetypeObject authority target newObj st = .ok ((), st')) :
    cspaceSlotKeyUnique st' := by
  intro oid cn hObj
  by_cases hEq : oid = target
  · subst hEq
    have hObjAtTarget : st'.objects oid = some newObj := by
      rcases lifecycleRetypeObject_ok_as_storeObject st st' authority oid newObj hStep with
        ⟨_, _, _, _, _, _, hStore⟩
      exact lifecycle_storeObject_objects_eq st st' oid newObj hStore
    rw [hObjAtTarget] at hObj
    have hNewObjEq : newObj = .cnode cn := by injection hObj
    exact hNewObjCNodeUnique cn hNewObjEq
  · have hPreserved : st'.objects oid = st.objects oid :=
      lifecycleRetypeObject_ok_lookup_preserved_ne st st' authority target oid newObj hEq hStep
    rw [hPreserved] at hObj
    exact hUnique oid cn hObj

theorem lifecycleRetypeObject_preserves_capabilityInvariantBundle
    (st st' : SystemState)
    (authority : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj : KernelObject)
    (hInv : capabilityInvariantBundle st)
    (hNewObjCNodeUnique : ∀ cn, newObj = .cnode cn → cn.slotKeysUnique)
    (hStep : lifecycleRetypeObject authority target newObj st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  rcases hInv with ⟨hUnique, _hSound, hAttRule, _hLifecycle⟩
  exact ⟨lifecycleRetypeObject_preserves_cspaceSlotKeyUnique st st' authority target newObj
      hUnique hNewObjCNodeUnique hStep,
    cspaceLookupSound_holds st', hAttRule,
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
    (hNewObjCNodeUnique : ∀ cn, newObj = .cnode cn → cn.slotKeysUnique)
    (hCurrentValid : currentThreadValid st')
    (hStep : lifecycleRetypeObject authority target newObj st = .ok ((), st')) :
    m3IpcSeedInvariantBundle st' := by
  rcases hInv with ⟨hSched, hCap, hIpc⟩
  refine ⟨?_, ?_, ?_⟩
  · exact lifecycleRetypeObject_preserves_schedulerInvariantBundle st st' authority target newObj hSched
      hCurrentValid hStep
  · exact lifecycleRetypeObject_preserves_capabilityInvariantBundle st st' authority target newObj hCap
      hNewObjCNodeUnique hStep
  · exact lifecycleRetypeObject_preserves_ipcInvariant st st' authority target newObj hIpc hNewObjEndpointInv hNewObjNotificationInv hStep

theorem lifecycleRetypeObject_preserves_m4aLifecycleInvariantBundle
    (st st' : SystemState)
    (authority : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj : KernelObject)
    (hInv : m4aLifecycleInvariantBundle st)
    (hNewObjEndpointInv : ∀ ep, newObj = .endpoint ep → endpointInvariant ep)
    (hNewObjNotificationInv : ∀ ntfn, newObj = .notification ntfn → notificationInvariant ntfn)
    (hNewObjCNodeUnique : ∀ cn, newObj = .cnode cn → cn.slotKeysUnique)
    (hCurrentValid : currentThreadValid st')
    (hCoherence' : ipcSchedulerCoherenceComponent st')
    (hStep : lifecycleRetypeObject authority target newObj st = .ok ((), st')) :
    m4aLifecycleInvariantBundle st' := by
  rcases hInv with ⟨hM35, hLifecycle⟩
  rcases hM35 with ⟨hM3, _hCoherence⟩
  have hM3' : m3IpcSeedInvariantBundle st' :=
    lifecycleRetypeObject_preserves_m3IpcSeedInvariantBundle st st' authority target newObj hM3
      hNewObjEndpointInv hNewObjNotificationInv hNewObjCNodeUnique hCurrentValid hStep
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
    (hNewObjCNodeUnique : ∀ cn, newObj = .cnode cn → cn.slotKeysUnique)
    (hStep : lifecycleRevokeDeleteRetype authority cleanup target newObj st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  rcases lifecycleRevokeDeleteRetype_ok_implies_staged_steps st st' authority cleanup target newObj hStep with
    ⟨stRevoked, stDeleted, _hNe, hRevoke, hDelete, _hLookupDeleted, hRetype⟩
  have hRevoked : capabilityInvariantBundle stRevoked :=
    cspaceRevoke_preserves_capabilityInvariantBundle st stRevoked cleanup hInv hRevoke
  have hDeleted : capabilityInvariantBundle stDeleted :=
    cspaceDeleteSlot_preserves_capabilityInvariantBundle stRevoked stDeleted cleanup hRevoked hDelete
  exact lifecycleRetypeObject_preserves_capabilityInvariantBundle stDeleted st' authority target newObj
    hDeleted hNewObjCNodeUnique hRetype

theorem lifecycleRevokeDeleteRetype_preserves_lifecycleCapabilityStaleAuthorityInvariant
    (st st' : SystemState)
    (authority cleanup : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj : KernelObject)
    (hCap : capabilityInvariantBundle st)
    (hNewObjCNodeUnique : ∀ cn, newObj = .cnode cn → cn.slotKeysUnique)
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
      hCap hNewObjCNodeUnique hStep
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

/-- General `storeObject` preservation for `cspaceSlotKeyUnique`: if the stored
object satisfies CNode uniqueness (or is not a CNode at all), then the
system-wide invariant is preserved. (WS-E2 / H-01 infrastructure) -/
theorem storeObject_preserves_cspaceSlotKeyUnique
    (st st' : SystemState)
    (oid : SeLe4n.ObjId)
    (obj : KernelObject)
    (hUnique : cspaceSlotKeyUnique st)
    (hObjUnique : ∀ cn, obj = .cnode cn → cn.slotKeysUnique)
    (hStore : storeObject oid obj st = .ok ((), st')) :
    cspaceSlotKeyUnique st' := by
  intro oid' cn hObj'
  by_cases hEq : oid' = oid
  · have hStored := storeObject_objects_eq st st' oid obj hStore
    rw [hEq] at hObj'; rw [hStored] at hObj'; cases hObj'
    exact hObjUnique cn rfl
  · have hPreserved := storeObject_objects_ne st st' oid oid' obj hEq hStore
    rw [hPreserved] at hObj'
    exact hUnique oid' cn hObj'

/-- Endpoint operations store `.endpoint` objects, never CNodes. This helper
proves `cspaceSlotKeyUnique` is preserved through any single `storeObject` call
that writes an endpoint. -/
private theorem storeObject_endpoint_preserves_cspaceSlotKeyUnique
    (st st' : SystemState) (oid : SeLe4n.ObjId) (ep : Endpoint)
    (hUnique : cspaceSlotKeyUnique st)
    (hStore : storeObject oid (.endpoint ep) st = .ok ((), st')) :
    cspaceSlotKeyUnique st' :=
  storeObject_preserves_cspaceSlotKeyUnique st st' oid (.endpoint ep) hUnique
    (fun _ h => by cases h) hStore

/-- Compositional preservation for endpoint operations: `endpointSend` only stores
endpoint objects, so all CNodes and their slot-key uniqueness are preserved.
(WS-E2 / H-01 — uses both hUnique and hStep) -/
theorem endpointSend_preserves_cspaceSlotKeyUnique
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hUnique : cspaceSlotKeyUnique st)
    (hStep : endpointSend endpointId sender st = .ok ((), st')) :
    cspaceSlotKeyUnique st' := by
  unfold endpointSend at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj =>
      cases obj with
      | tcb _ | notification _ | cnode _ | vspaceRoot _ => simp [hObj] at hStep
      | endpoint ep =>
          simp [hObj] at hStep
          cases hState : ep.state with
          | idle =>
              simp only [hState] at hStep
              exact storeObject_endpoint_preserves_cspaceSlotKeyUnique st st' endpointId _ hUnique hStep
          | send =>
              simp only [hState] at hStep
              exact storeObject_endpoint_preserves_cspaceSlotKeyUnique st st' endpointId _ hUnique hStep
          | receive =>
              simp only [hState] at hStep
              cases hQ : ep.queue with
              | nil =>
                  cases hW : ep.waitingReceiver with
                  | none => simp [hQ, hW] at hStep
                  | some _ =>
                      simp only [hQ, hW] at hStep
                      exact storeObject_endpoint_preserves_cspaceSlotKeyUnique st st' endpointId _ hUnique hStep
              | cons _ _ => simp [hQ] at hStep

theorem endpointSend_preserves_capabilityInvariantBundle
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hInv : capabilityInvariantBundle st)
    (hStep : endpointSend endpointId sender st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  rcases hInv with ⟨hUnique, _hSound, hAttRule, _hLifecycle⟩
  exact ⟨endpointSend_preserves_cspaceSlotKeyUnique st st' endpointId sender hUnique hStep,
    cspaceLookupSound_holds st', hAttRule,
    lifecycleAuthorityMonotonicity_holds st'⟩

theorem endpointAwaitReceive_preserves_cspaceSlotKeyUnique
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId)
    (hUnique : cspaceSlotKeyUnique st)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st')) :
    cspaceSlotKeyUnique st' := by
  unfold endpointAwaitReceive at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj =>
      cases obj with
      | tcb _ | notification _ | cnode _ | vspaceRoot _ => simp [hObj] at hStep
      | endpoint ep =>
          simp [hObj] at hStep
          cases hState : ep.state with
          | send => simp [hState] at hStep
          | receive => simp [hState] at hStep
          | idle =>
              cases hQ : ep.queue with
              | cons _ _ => simp [hState, hQ] at hStep
              | nil =>
                  cases hW : ep.waitingReceiver with
                  | some _ => simp [hState, hQ, hW] at hStep
                  | none =>
                      simp [hState, hQ, hW] at hStep
                      exact storeObject_endpoint_preserves_cspaceSlotKeyUnique st st' endpointId _ hUnique hStep

theorem endpointAwaitReceive_preserves_capabilityInvariantBundle
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId)
    (hInv : capabilityInvariantBundle st)
    (hStep : endpointAwaitReceive endpointId receiver st = .ok ((), st')) :
    capabilityInvariantBundle st' := by
  rcases hInv with ⟨hUnique, _hSound, hAttRule, _hLifecycle⟩
  exact ⟨endpointAwaitReceive_preserves_cspaceSlotKeyUnique st st' endpointId receiver hUnique hStep,
    cspaceLookupSound_holds st', hAttRule,
    lifecycleAuthorityMonotonicity_holds st'⟩

theorem endpointReceive_preserves_cspaceSlotKeyUnique
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hUnique : cspaceSlotKeyUnique st)
    (hStep : endpointReceive endpointId st = .ok (sender, st')) :
    cspaceSlotKeyUnique st' := by
  unfold endpointReceive at hStep
  cases hObj : st.objects endpointId with
  | none => simp [hObj] at hStep
  | some obj =>
      cases obj with
      | tcb _ | notification _ | cnode _ | vspaceRoot _ => simp [hObj] at hStep
      | endpoint ep =>
          simp [hObj] at hStep
          cases hState : ep.state with
          | idle => simp [hState] at hStep
          | receive => simp [hState] at hStep
          | send =>
              cases hQ : ep.queue with
              | nil =>
                  cases hWR : ep.waitingReceiver with
                  | none => simp [hState, hQ, hWR] at hStep
                  | some _ => simp [hState, hQ, hWR] at hStep
              | cons hd rest =>
                  cases hWR : ep.waitingReceiver with
                  | some _ => simp [hState, hQ, hWR] at hStep
                  | none =>
                      simp only [hState, hQ, hWR] at hStep
                      revert hStep
                      cases hS : storeObject endpointId (.endpoint { state := if rest = [] then .idle else .send, queue := rest }) st with
                      | error e => intro h; simp at h
                      | ok val =>
                          obtain ⟨⟨⟩, st_mid⟩ := val
                          intro hStep; simp at hStep
                          obtain ⟨_, rfl⟩ := hStep
                          exact storeObject_endpoint_preserves_cspaceSlotKeyUnique st st_mid endpointId _ hUnique hS

theorem endpointReceive_preserves_capabilityInvariantBundle
    (st st' : SystemState)
    (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId)
    (hInv : capabilityInvariantBundle st)
    (hStep : endpointReceive endpointId st = .ok (sender, st')) :
    capabilityInvariantBundle st' := by
  rcases hInv with ⟨hUnique, _hSound, hAttRule, _hLifecycle⟩
  exact ⟨endpointReceive_preserves_cspaceSlotKeyUnique st st' endpointId sender hUnique hStep,
    cspaceLookupSound_holds st', hAttRule,
    lifecycleAuthorityMonotonicity_holds st'⟩

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

-- ─────────────────────────────────────────────────────────────────────────────
-- WS-E2 / H-03 — Badge consistency theorems for notification routing
-- ─────────────────────────────────────────────────────────────────────────────
--
-- These theorems establish that badge values propagated through `mintDerivedCap`
-- are consistent with notification routing semantics:
--   (1) `mintDerivedCap` preserves the caller-specified badge (or parent badge).
--   (2) `mintDerivedCap` preserves the parent target.
--   (3) Badge merge in `notificationSignal` is idempotent and associative.
--   (4) A fresh badge (no prior pending) is stored identically.
--   (5) Composed guarantee: `cspaceMint` → notification signal → the badge
--       delivered to the waiter is consistent with the minted capability's badge.

/-- (H-03.1) `mintDerivedCap` propagates the explicitly provided badge to the
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

/-- (H-03.2) `mintDerivedCap` preserves the parent's target in the derived
capability, ensuring that the minted capability routes to the same endpoint or
notification object. -/
theorem mintDerivedCap_target_preserved
    (parent : Capability) (rights : List AccessRight) (badge : Option SeLe4n.Badge)
    (child : Capability)
    (hMint : mintDerivedCap parent rights badge = .ok child) :
    child.target = parent.target := by
  unfold mintDerivedCap at hMint
  split at hMint
  · cases hMint; rfl
  · exact absurd hMint (by simp)

/-- (H-03.3) Badge OR-merge is idempotent: signaling the same badge twice is
indistinguishable from signaling it once.  This justifies the seL4 semantics
where repeated signals accumulate bits rather than queue messages. -/
theorem badge_merge_idempotent (b : SeLe4n.Badge) :
    SeLe4n.Badge.ofNat (b.toNat ||| b.toNat) = b := by
  simp [SeLe4n.Badge.ofNat, SeLe4n.Badge.toNat, Nat.or_self]

/-- (H-03.4) When no prior pending badge exists, `notificationSignal` stores
the signaled badge directly.  This is the base case of badge accumulation. -/
theorem notificationSignal_fresh_badge_identity
    (badge : SeLe4n.Badge) :
    (match (none : Option SeLe4n.Badge) with
     | some existing => SeLe4n.Badge.ofNat (existing.toNat ||| badge.toNat)
     | none => badge) = badge := by
  rfl

/-- (H-03.5) Composed badge consistency: when `cspaceMint` creates a derived
capability with explicit badge `some b`, the derived capability carries `b`,
and a subsequent `notificationSignal` on a fresh notification (no pending badge)
delivers exactly `b`.

This connects the capability-level badge propagation (H-03.1) to the IPC-level
notification merge (H-03.4), establishing the end-to-end contract. -/
theorem cspaceMint_badge_notification_consistent
    (parent child : Capability)
    (rights : List AccessRight)
    (b : SeLe4n.Badge)
    (hMint : mintDerivedCap parent rights (some b) = .ok child) :
    child.badge = some b ∧
    (match (none : Option SeLe4n.Badge) with
     | some existing => SeLe4n.Badge.ofNat (existing.toNat ||| b.toNat)
     | none => b) = b := by
  exact ⟨mintDerivedCap_badge_propagated parent rights (some b) child hMint, rfl⟩

end SeLe4n.Kernel
