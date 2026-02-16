import SeLe4n.Kernel.Capability.Operations

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- Lifecycle authority required to retype an object identity in this slice.

The authority capability must target the object directly and include `write` rights. -/
def lifecycleRetypeAuthority (cap : Capability) (target : SeLe4n.ObjId) : Bool :=
  decide (cap.target = .object target) && Capability.hasRight cap .write

/-- Retype an existing object id to a new typed object value.

Deterministic branch contract for M4-A step 2:
1. target object must exist,
2. lifecycle metadata for the target id must agree with object-store type (`illegalState` otherwise),
3. authority slot lookup must succeed,
4. authority must satisfy `lifecycleRetypeAuthority` (`illegalAuthority` otherwise),
5. object store + lifecycle object-type metadata are updated atomically on success. -/
def lifecycleRetypeObject
    (authority : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj : KernelObject) : Kernel Unit :=
  fun st =>
    match st.objects target with
    | none => .error .objectNotFound
    | some currentObj =>
        if st.lifecycle.objectTypes target = some currentObj.objectType then
          match cspaceLookupSlot authority st with
          | .error e => .error e
          | .ok (authCap, st') =>
              if lifecycleRetypeAuthority authCap target then
                storeObject target newObj st'
              else
                .error .illegalAuthority
        else
          .error .illegalState

/-- Compose local revoke/delete cleanup with lifecycle retype.

Authority and state preconditions for deterministic success:
1. `authority ≠ cleanup` (delete-before-reuse ordering guard),
2. `cleanup` must resolve to a capability so revoke/delete can execute,
3. post-delete lookup of `cleanup` must return `invalidCapability`,
4. lifecycle retype preconditions from `lifecycleRetypeObject` must hold.

Failure branches remain explicit and ordered:
- aliasing `authority = cleanup` is rejected as `illegalState`,
- revoke/delete failures are propagated directly,
- unexpected post-delete lookup success is rejected as `illegalState`,
- final retype failures are propagated directly. -/
def lifecycleRevokeDeleteRetype
    (authority cleanup : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj : KernelObject) : Kernel Unit :=
  fun st =>
    if authority = cleanup then
      .error .illegalState
    else
      match cspaceRevoke cleanup st with
      | .error e => .error e
      | .ok (_, stRevoked) =>
          match cspaceDeleteSlot cleanup stRevoked with
          | .error e => .error e
          | .ok (_, stDeleted) =>
              match cspaceLookupSlot cleanup stDeleted with
              | .ok _ => .error .illegalState
              | .error .invalidCapability =>
                  lifecycleRetypeObject authority target newObj stDeleted
              | .error e => .error e

/- Local lifecycle transition helper lemmas (M4-A step 4).
These theorems keep preservation scripts focused on invariant obligations rather than
repeating transition case analysis. -/

theorem lifecycle_storeObject_objects_eq
    (st st' : SystemState)
    (id : SeLe4n.ObjId)
    (obj : KernelObject)
    (hStore : storeObject id obj st = .ok ((), st')) :
    st'.objects id = some obj := by
  unfold storeObject at hStore
  cases hStore
  simp

theorem lifecycle_storeObject_objects_ne
    (st st' : SystemState)
    (id oid : SeLe4n.ObjId)
    (obj : KernelObject)
    (hNe : oid ≠ id)
    (hStore : storeObject id obj st = .ok ((), st')) :
    st'.objects oid = st.objects oid := by
  unfold storeObject at hStore
  cases hStore
  simp [hNe]

theorem lifecycle_storeObject_scheduler_eq
    (st st' : SystemState)
    (id : SeLe4n.ObjId)
    (obj : KernelObject)
    (hStore : storeObject id obj st = .ok ((), st')) :
    st'.scheduler = st.scheduler := by
  unfold storeObject at hStore
  cases hStore
  rfl

theorem cspaceLookupSlot_ok_state_eq
    (st : SystemState)
    (addr : CSpaceAddr)
    (cap : Capability)
    (st' : SystemState)
    (hLookup : cspaceLookupSlot addr st = .ok (cap, st')) :
    st' = st := by
  unfold cspaceLookupSlot at hLookup
  cases hCap : SystemState.lookupSlotCap st addr with
  | none =>
      cases hObj : st.objects addr.cnode with
      | none => simp [hCap, hObj] at hLookup
      | some obj =>
          cases obj <;> simp [hCap, hObj] at hLookup
  | some cap' =>
      simp [hCap] at hLookup
      exact hLookup.2.symm

theorem lifecycleRetypeObject_ok_as_storeObject
    (st st' : SystemState)
    (authority : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj : KernelObject)
    (hStep : lifecycleRetypeObject authority target newObj st = .ok ((), st')) :
    ∃ currentObj cap,
      st.objects target = some currentObj ∧
      st.lifecycle.objectTypes target = some currentObj.objectType ∧
      cspaceLookupSlot authority st = .ok (cap, st) ∧
      lifecycleRetypeAuthority cap target = true ∧
      storeObject target newObj st = .ok ((), st') := by
  unfold lifecycleRetypeObject at hStep
  cases hObj : st.objects target with
  | none => simp [hObj] at hStep
  | some currentObj =>
      by_cases hMeta : st.lifecycle.objectTypes target = some currentObj.objectType
      · cases hLookup : cspaceLookupSlot authority st with
        | error e => simp [hObj, hMeta, hLookup] at hStep
        | ok pair =>
            rcases pair with ⟨cap, stLookup⟩
            cases hAuth : lifecycleRetypeAuthority cap target with
            | false => simp [hObj, hMeta, hLookup, hAuth] at hStep
            | true =>
                have hLookupSt : stLookup = st :=
                  cspaceLookupSlot_ok_state_eq st authority cap stLookup hLookup
                subst hLookupSt
                simp [hObj, hMeta, hLookup, hAuth] at hStep
                exact ⟨currentObj, cap, by simp, hMeta, by simp, hAuth, hStep⟩
      · simp [hObj, hMeta] at hStep

theorem lifecycleRetypeObject_ok_lookup_preserved_ne
    (st st' : SystemState)
    (authority : CSpaceAddr)
    (target oid : SeLe4n.ObjId)
    (newObj : KernelObject)
    (hNe : oid ≠ target)
    (hStep : lifecycleRetypeObject authority target newObj st = .ok ((), st')) :
    st'.objects oid = st.objects oid := by
  rcases lifecycleRetypeObject_ok_as_storeObject st st' authority target newObj hStep with
    ⟨_, _, _, _, _, _, hStore⟩
  exact lifecycle_storeObject_objects_ne st st' target oid newObj hNe hStore

theorem lifecycleRetypeObject_ok_runnable_membership
    (st st' : SystemState)
    (authority : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj : KernelObject)
    (tid : SeLe4n.ThreadId)
    (hStep : lifecycleRetypeObject authority target newObj st = .ok ((), st'))
    (hRun : tid ∈ st'.scheduler.runnable) :
    tid ∈ st.scheduler.runnable := by
  rcases lifecycleRetypeObject_ok_as_storeObject st st' authority target newObj hStep with
    ⟨_, _, _, _, _, _, hStore⟩
  have hSchedEq : st'.scheduler = st.scheduler :=
    lifecycle_storeObject_scheduler_eq st st' target newObj hStore
  simpa [hSchedEq] using hRun

theorem lifecycleRetypeObject_ok_not_runnable_membership
    (st st' : SystemState)
    (authority : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj : KernelObject)
    (tid : SeLe4n.ThreadId)
    (hStep : lifecycleRetypeObject authority target newObj st = .ok ((), st'))
    (hNotRun : tid ∉ st.scheduler.runnable) :
    tid ∉ st'.scheduler.runnable := by
  rcases lifecycleRetypeObject_ok_as_storeObject st st' authority target newObj hStep with
    ⟨_, _, _, _, _, _, hStore⟩
  have hSchedEq : st'.scheduler = st.scheduler :=
    lifecycle_storeObject_scheduler_eq st st' target newObj hStore
  simpa [hSchedEq] using hNotRun

theorem lifecycleRetypeObject_error_illegalState
    (st : SystemState)
    (authority : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj currentObj : KernelObject)
    (hObj : st.objects target = some currentObj)
    (hMetaMismatch : st.lifecycle.objectTypes target ≠ some currentObj.objectType) :
    lifecycleRetypeObject authority target newObj st = .error .illegalState := by
  unfold lifecycleRetypeObject
  simp [hObj, hMetaMismatch]

theorem lifecycleRetypeObject_error_illegalAuthority
    (st : SystemState)
    (authority : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj currentObj : KernelObject)
    (cap : Capability)
    (hObj : st.objects target = some currentObj)
    (hMeta : st.lifecycle.objectTypes target = some currentObj.objectType)
    (hLookup : cspaceLookupSlot authority st = .ok (cap, st))
    (hAuthFail : lifecycleRetypeAuthority cap target = false) :
    lifecycleRetypeObject authority target newObj st = .error .illegalAuthority := by
  unfold lifecycleRetypeObject
  simp [hObj, hMeta, hLookup, hAuthFail]

theorem lifecycleRetypeObject_success_updates_object
    (st st' : SystemState)
    (authority : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj currentObj : KernelObject)
    (cap : Capability)
    (hObj : st.objects target = some currentObj)
    (hMeta : st.lifecycle.objectTypes target = some currentObj.objectType)
    (hLookup : cspaceLookupSlot authority st = .ok (cap, st))
    (hAuth : lifecycleRetypeAuthority cap target = true)
    (hStep : lifecycleRetypeObject authority target newObj st = .ok ((), st')) :
    st'.objects target = some newObj := by
  have _ : st.lifecycle.objectTypes target = some currentObj.objectType := hMeta
  have _ : lifecycleRetypeAuthority cap target = true := hAuth
  rcases lifecycleRetypeObject_ok_as_storeObject st st' authority target newObj hStep with
    ⟨currentObj', cap', hObj', _, hLookup', _, hStore⟩
  have hCurrent : currentObj' = currentObj := by
    apply Option.some.inj
    rw [← hObj', hObj]
  subst hCurrent
  have hCapLookup' : SystemState.lookupSlotCap st authority = some cap' :=
    (cspaceLookupSlot_ok_iff_lookupSlotCap st authority cap').1 hLookup'
  have hCapLookup : SystemState.lookupSlotCap st authority = some cap :=
    (cspaceLookupSlot_ok_iff_lookupSlotCap st authority cap).1 hLookup
  rw [hCapLookup'] at hCapLookup
  injection hCapLookup with hCapEq
  subst hCapEq
  exact lifecycle_storeObject_objects_eq st st' target newObj hStore

theorem lifecycleRevokeDeleteRetype_error_authority_cleanup_alias
    (st : SystemState)
    (authority cleanup : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj : KernelObject)
    (hAlias : authority = cleanup) :
    lifecycleRevokeDeleteRetype authority cleanup target newObj st = .error .illegalState := by
  unfold lifecycleRevokeDeleteRetype
  simp [hAlias]

theorem lifecycleRevokeDeleteRetype_ok_implies_authority_ne_cleanup
    (st st' : SystemState)
    (authority cleanup : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj : KernelObject)
    (hStep : lifecycleRevokeDeleteRetype authority cleanup target newObj st = .ok ((), st')) :
    authority ≠ cleanup := by
  intro hAlias
  have hErr := lifecycleRevokeDeleteRetype_error_authority_cleanup_alias
    st authority cleanup target newObj hAlias
  rw [hErr] at hStep
  cases hStep

theorem lifecycleRevokeDeleteRetype_ok_implies_staged_steps
    (st st' : SystemState)
    (authority cleanup : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj : KernelObject)
    (hStep : lifecycleRevokeDeleteRetype authority cleanup target newObj st = .ok ((), st')) :
    ∃ stRevoked stDeleted,
      authority ≠ cleanup ∧
      cspaceRevoke cleanup st = .ok ((), stRevoked) ∧
      cspaceDeleteSlot cleanup stRevoked = .ok ((), stDeleted) ∧
      cspaceLookupSlot cleanup stDeleted = .error .invalidCapability ∧
      lifecycleRetypeObject authority target newObj stDeleted = .ok ((), st') := by
  by_cases hAlias : authority = cleanup
  · have hErr : lifecycleRevokeDeleteRetype authority cleanup target newObj st = .error .illegalState := by
      simp [lifecycleRevokeDeleteRetype, hAlias]
    rw [hErr] at hStep
    cases hStep
  · cases hRevoke : cspaceRevoke cleanup st with
    | error e =>
        simp [lifecycleRevokeDeleteRetype, hAlias, hRevoke] at hStep
    | ok revPair =>
        cases revPair with
        | mk revUnit stRevoked =>
            cases revUnit
            cases hDelete : cspaceDeleteSlot cleanup stRevoked with
            | error e =>
                simp [lifecycleRevokeDeleteRetype, hAlias, hRevoke, hDelete] at hStep
            | ok delPair =>
                cases delPair with
                | mk delUnit stDeleted =>
                    cases delUnit
                    cases hLookup : cspaceLookupSlot cleanup stDeleted with
                    | ok pair =>
                        simp [lifecycleRevokeDeleteRetype, hAlias, hRevoke, hDelete, hLookup] at hStep
                    | error err =>
                        have hErr : err = .invalidCapability := by
                          cases err <;> simp [lifecycleRevokeDeleteRetype, hAlias, hRevoke, hDelete, hLookup] at hStep
                          rfl
                        subst hErr
                        refine ⟨stRevoked, stDeleted, hAlias, ?_, ?_, ?_, ?_⟩
                        · rfl
                        · simpa using hDelete
                        · exact hLookup
                        · simpa [lifecycleRevokeDeleteRetype, hAlias, hRevoke, hDelete, hLookup] using hStep


end SeLe4n.Kernel
