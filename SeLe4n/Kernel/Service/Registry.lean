-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Model.State

/-! # Service Registry Operations — seLe4n Extension

Capability-indexed service registry replacing the lifecycle-focused
orchestration model. Five deterministic operations with explicit error
returns and machine-checked post-conditions.

## Operations

| Operation | Mutates | Error conditions |
|-----------|---------|-----------------|
| `registerInterface` | `interfaceRegistry` | `illegalState` (duplicate) |
| `registerService` | `serviceRegistry`, its endpoint's `serviceRegistered` | `illegalState`, `objectNotFound`, `invalidCapability` |
| `lookupServiceByCap` | — (read-only; the specification) | `objectNotFound` |
| `lookupServiceByRecordedRegistration` | — (read-only; the O(1) form the kernel runs) | `objectNotFound` |
| `revokeService` | `serviceRegistry`, its endpoint's `serviceRegistered` | `objectNotFound` |
| `revokeServiceByRecordedRegistration` | as `revokeService` (the form the kernel runs) | `objectNotFound` |
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.RobinHood

-- ============================================================================
-- Registry operations
-- ============================================================================

/-- Register a concrete interface specification.
Returns `illegalState` if an interface with the same `ifaceId` is already
registered (duplicate prevention). -/
def registerInterface (spec : InterfaceSpec) : Kernel Unit :=
  fun st =>
    if st.interfaceRegistry[spec.ifaceId]? != none then
      .error .illegalState
    else
      .ok ((), { st with
        interfaceRegistry := st.interfaceRegistry.insert spec.ifaceId spec })

/-- Register a service with capability-mediated binding.
Checks (ordered for defense-in-depth — validate target before authority):
1. Service not already registered (`illegalState`)
2. Interface exists in registry (`objectNotFound`)
3. Endpoint capability target resolves to an existing object (`invalidCapability`)
4. R4-C.2 (L-09): Target object must be an endpoint (`invalidCapability`)
5. R4-C.1 (M-14): Endpoint capability must have Write right (`illegalAuthority`)
6. AE5-B (U-20): No existing service already targets this endpoint (`illegalState`),
   read off the endpoint's own record of its registration (`Endpoint.serviceRegistered`,
   WS-ZA ZA5.4 part 30), which `SystemState.tableReferencesRecorded` holds equal
   to the registry's — one field, where the check walked the registry.
-/
def registerService (reg : ServiceRegistration) : Kernel Unit :=
  fun st =>
    if st.serviceRegistry[reg.sid]? != none then
      .error .illegalState
    else if st.interfaceRegistry[reg.iface.ifaceId]? = none then
      .error .objectNotFound
    else
      match reg.endpointCap.target with
      | .object epId =>
        match hObj : st.getObject? epId with
        | none => .error .invalidCapability
        -- R4-C.2 (L-09): Target must be an endpoint object
        | some (.endpoint ep) =>
          -- R4-C.1 (M-14): Capability authority check — require Write right
          -- Checked after target validation to prevent authority probing on invalid targets
          if !Capability.hasRight reg.endpointCap .write then
            .error .illegalAuthority
          -- AE5-B (U-20): Reject duplicate endpoint registration
          else if ep.serviceRegistered then
            .error .illegalState
          else
            -- WS-ZA ZA5.4 part 30: the registration is recorded on its
            -- endpoint (`Endpoint.serviceRegistered`), the back-link a final delete
            -- reads instead of walking the registry.
            .ok ((), { st.rewriteObject epId (.endpoint { ep with serviceRegistered := true })
                ⟨_, hObj, rfl, rfl⟩ with
              serviceRegistry := st.serviceRegistry.insert reg.sid reg })
        | some _ => .error .invalidCapability
      | _ => .error .invalidCapability

/-- **WS-ZA ZA5.5**: `registerService`'s checks, read from the state before
anything is written, in its order (seL4's decode half). -/
@[inline] def registerServiceAdmitted (st : SystemState) (reg : ServiceRegistration) : Bool :=
  (st.serviceRegistry[reg.sid]?).isNone && (st.interfaceRegistry[reg.iface.ifaceId]?).isSome &&
    match reg.endpointCap.target with
    | .object epId =>
      match st.getObject? epId with
      | some (.endpoint ep) => Capability.hasRight reg.endpointCap .write && !ep.serviceRegistered
      | _ => false
    | _ => false

/-- **WS-ZA ZA5.5**: `registerService`'s writes, total: the endpoint records the
registration and the registry holds it (seL4's perform half).  A state whose
target is no endpoint is returned unchanged; `registerServiceAdmitted` rules
that state out. -/
@[inline] def registerServicePerform (st : SystemState) (reg : ServiceRegistration) :
    SystemState :=
  match reg.endpointCap.target with
  | .object epId =>
    match hObj : st.getObject? epId with
    | some (.endpoint ep) =>
      { st.rewriteObject epId (.endpoint { ep with serviceRegistered := true })
          ⟨_, hObj, rfl, rfl⟩ with
        serviceRegistry := st.serviceRegistry.insert reg.sid reg }
    | _ => st
  | _ => st

/-- **WS-ZA ZA5.5**: the object update that records `b` on an endpoint
(`Endpoint.serviceRegistered`): the registration's back-link set, or cleared. -/
@[inline] def setServiceRegisteredObject (b : Bool) : KernelObject → KernelObject
  | .endpoint ep => .endpoint { ep with serviceRegistered := b }
  | o => o

/-- **WS-ZA ZA5.5**: the registration inserted into the registry.  A call, not
inlined, so the state arrives exclusive and its record is written in place. -/
@[noinline] def insertServiceRegistration (st : SystemState) (reg : ServiceRegistration) :
    SystemState :=
  { st with serviceRegistry := st.serviceRegistry.insert reg.sid reg }

/-- **WS-ZA ZA5.5**: the compiled `registerServicePerform` — the endpoint's
record written in its slot (`SystemState.modifyObject`), so neither the
endpoint nor its `KernelObject` cell is rebuilt, and the registration inserted
by its own call; the cells left are the registration's own. -/
def registerServicePerformImpl (st : SystemState) (reg : ServiceRegistration) : SystemState :=
  match reg.endpointCap.target with
  | .object epId =>
    match st.getEndpoint? epId with
    | some _ =>
      insertServiceRegistration
        (st.modifyObject epId (setServiceRegisteredObject true)) reg
    | none => st
  | _ => st

@[csimp] theorem registerServicePerform_eq_impl :
    @registerServicePerform = @registerServicePerformImpl := by
  funext st reg
  unfold registerServicePerform registerServicePerformImpl
  split
  · next epId _ =>
    split
    · next ep h =>
      have h' : st.objects[epId]? = some (.endpoint ep) := h
      rw [(SystemState.getEndpoint?_eq_some_iff st epId ep).mpr h']
      dsimp only
      unfold insertServiceRegistration SystemState.rewriteObject SystemState.modifyObject
      rw [RHTable.modify_of_get? h']
      rfl
    · next hN =>
      have hN' : ∀ ep, st.objects[epId]? ≠ some (.endpoint ep) := hN
      split
      · next ep h => exact absurd ((SystemState.getEndpoint?_eq_some_iff st epId ep).mp h) (hN' ep)
      · rfl
  all_goals rfl

/-- An admitted registration succeeds as its perform. -/
theorem registerService_of_admitted (st : SystemState) (reg : ServiceRegistration)
    (h : registerServiceAdmitted st reg = true) :
    registerService reg st = .ok ((), registerServicePerform st reg) := by
  unfold registerServiceAdmitted at h
  unfold registerService registerServicePerform
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hFree, hIface⟩, hRest⟩ := h
  have hFree' : (st.serviceRegistry[reg.sid]? != none) = false := by
    cases hS : st.serviceRegistry[reg.sid]? with
    | none => rfl
    | some _ => rw [hS] at hFree; cases hFree
  have hIface' : ¬ st.interfaceRegistry[reg.iface.ifaceId]? = none := by
    intro hN; rw [hN] at hIface; cases hIface
  rw [hFree']
  simp only [Bool.false_eq_true, ↓reduceIte, hIface']
  revert hRest
  cases reg.endpointCap.target with
  | object epId =>
    dsimp only
    intro hRest
    split
    · next hN => rw [hN] at hRest; cases hRest
    · next ep hObj =>
      rw [hObj] at hRest
      simp only [Bool.and_eq_true] at hRest
      obtain ⟨hW, hC⟩ := hRest
      have hC' : ep.serviceRegistered = false := by simpa using hC
      simp only [hW, hC', Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      split
      · next ep' hObj' =>
        rw [hObj] at hObj'
        cases hObj'
        rfl
      · next hNe => exact absurd hObj (hNe ep)
    · next o hNe hObj =>
      rw [hObj] at hRest
      cases o <;> first | cases hRest | exact absurd rfl (hNe _)
  | _ => intro h; cases h

/-- Read-only lookup of a service registration by matching endpoint capability
target. Returns the first registration whose endpoint targets the given ObjId,
or `objectNotFound` if none matches.

T5-K (M-LCS-2): The `fold` iteration order is deterministic for `RHTable`:
entries are visited in probe-chain order (hash → linear probing). Within a
given probe chain, entries appear in insertion order. The first-match
convention is what makes the fold's answer independent of that order here,
since at most one registration can name a given endpoint
(`registryEndpointUnique`, derived from `SystemState.tableReferencesRecorded`):
the fold returns the one registration, or none.

This fold is the specification.  The kernel runs `lookupServiceByRecordedRegistration`,
which reads the code the endpoint records instead (WS-ZA ZA5.4 part 31); the two
agree wherever the table references are recorded
(`lookupServiceByRecordedRegistration_eq_lookupServiceByCap`). -/
def lookupServiceByCap (epId : SeLe4n.ObjId) : Kernel ServiceRegistration :=
  fun st =>
    let result := st.serviceRegistry.fold (init := none) fun acc _ reg =>
      match acc with
      | some _ => acc
      | none =>
        match reg.endpointCap.target with
        | .object id => if id == epId then some reg else none
        | _ => none
    match result with
    | some reg => .ok (reg, st)
    | none => .error .objectNotFound

/-- **The service lookup the kernel runs: O(1), through the endpoint's record.**
An endpoint records whether a registration names it
(`Endpoint.serviceRegistered`), and a service's identity is its endpoint's, so
the lookup reads that one object and that one registry key instead of folding
over the registry.  It returns what the
specification `lookupServiceByCap` returns wherever the table references are
recorded (`lookupServiceByRecordedRegistration_eq_lookupServiceByCap`), which every
reachable state satisfies (WS-ZA ZA5.4 part 31). -/
def lookupServiceByRecordedRegistration (epId : SeLe4n.ObjId) : Kernel ServiceRegistration :=
  fun st =>
    match st.getObject? epId with
    | some (.endpoint ep) =>
      match ep.serviceRegistered with
      | false => .error .objectNotFound
      | true =>
        match st.serviceRegistry[ServiceId.ofNat epId.toNat]? with
        | some reg => .ok (reg, st)
        | none => .error .objectNotFound
    | _ => .error .objectNotFound

/-- **WS-ZA ZA5.4 part 30: clear the registration's record on its endpoint**:
the endpoint the registration's capability names forgets the service, if it
records one and the service is its own (`Endpoint.serviceRegistered`; a
service's identity is its endpoint's).  Every other state is returned as it
is. -/
@[inline] def clearEndpointRegistration (st : SystemState) (cap : Capability) (sid : ServiceId) :
    SystemState :=
  match cap.target with
  | .object e =>
    match h : st.getObject? e with
    | some (.endpoint ep) =>
      if ep.serviceRegistered = true ∧ sid = ServiceId.ofNat e.toNat then
        st.rewriteObject e (.endpoint { ep with serviceRegistered := false }) ⟨_, h, rfl, rfl⟩
      else st
    | _ => st
  | _ => st


/-- **WS-ZA ZA5.5**: the compiled `clearEndpointRegistration` — the endpoint's
record cleared in its slot (`SystemState.modifyObject`), so on an exclusively
owned state neither the endpoint nor its `KernelObject` cell is rebuilt.  A
call, so the caller's state arrives exclusive. -/
def clearEndpointRegistrationImpl (st : SystemState) (cap : Capability) (sid : ServiceId) :
    SystemState :=
  match cap.target with
  | .object e =>
    match st.getEndpoint? e with
    | some ep =>
      if ep.serviceRegistered = true ∧ sid = ServiceId.ofNat e.toNat then
        st.modifyObject e (setServiceRegisteredObject false)
      else st
    | none => st
  | _ => st

@[csimp] theorem clearEndpointRegistration_eq_impl :
    @clearEndpointRegistration = @clearEndpointRegistrationImpl := by
  funext st cap sid
  unfold clearEndpointRegistration clearEndpointRegistrationImpl
  split
  · next e _ =>
    split
    · next ep h =>
      have h' : st.objects[e]? = some (.endpoint ep) := h
      rw [(SystemState.getEndpoint?_eq_some_iff st e ep).mpr h']
      dsimp only
      split
      · unfold SystemState.rewriteObject SystemState.modifyObject
        rw [RHTable.modify_of_get? h']
        rfl
      · rfl
    · next hN =>
      have hN' : ∀ ep, st.objects[e]? ≠ some (.endpoint ep) := hN
      split
      · next ep h => exact absurd ((SystemState.getEndpoint?_eq_some_iff st e ep).mp h) (hN' ep)
      · rfl
  all_goals rfl

/-- Remove a service registration by ServiceId.
Returns `objectNotFound` if no such registration exists.
WS-ZA ZA5.4 part 30: after erasing the registration, clears its record on its
endpoint (`clearEndpointRegistration`).  (Until part 32 it also cleaned the
kernel's service dependency graph, which the kernel no longer keeps.) -/
def revokeService (sid : ServiceId) : Kernel Unit :=
  fun st =>
    match st.serviceRegistry[sid]? with
    | none => .error .objectNotFound
    | some reg =>
      let st' := { st with
        serviceRegistry := st.serviceRegistry.erase sid }
      .ok ((), clearEndpointRegistration st' reg.endpointCap sid)


/-- **The revoke the kernel runs: the registration recorded on the invoked
endpoint.**  The caller names no service: the authority to remove a
registration is a capability to the endpoint it names, the same capability the
query reads it back through (`lookupServiceByRecordedRegistration`), and the
registration is the one that endpoint records (`Endpoint.serviceRegistered`,
under the endpoint's own id).  An endpoint recording none is `objectNotFound`,
as is any other object.

`revokeService` stays the primitive this runs: where the table references are
recorded the registration it erases names `epId`
(`SystemState.tableReferencesRecorded.serviceFlags`). -/
def revokeServiceByRecordedRegistration (epId : SeLe4n.ObjId) : Kernel Unit :=
  fun st =>
    match st.getObject? epId with
    | some (.endpoint ep) =>
      match ep.serviceRegistered with
      | false => .error .objectNotFound
      | true => revokeService (ServiceId.ofNat epId.toNat) st
    | _ => .error .objectNotFound

/-- **WS-ZA ZA5.5**: the check the query and the revoke through an endpoint
share, read before any write: the endpoint records a registration and the
registry holds it. -/
@[inline] def recordedRegistrationPresent (st : SystemState) (epId : SeLe4n.ObjId) : Bool :=
  match st.getObject? epId with
  | some (.endpoint ep) =>
    match ep.serviceRegistered with
    | false => false
    | true => (st.serviceRegistry[ServiceId.ofNat epId.toNat]?).isSome
  | _ => false

/-- **WS-ZA ZA5.5**: the registry entry `sid` erased.  A call, not inlined, so
the state arrives exclusive and its record is written in place: inlined into
the dispatch, the state's fields were each taken out and the record rebuilt. -/
@[noinline] def eraseServiceRegistration (st : SystemState) (sid : ServiceId) : SystemState :=
  { st with serviceRegistry := st.serviceRegistry.erase sid }

/-- **WS-ZA ZA5.5**: `revokeServiceByRecordedRegistration`'s writes, total: the
registry entry erased and the endpoint's record cleared.  A state with no
recorded registration is returned unchanged; `recordedRegistrationPresent`
rules it out. -/
@[inline] def revokeServiceByRecordedRegistrationPerform (st : SystemState) (epId : SeLe4n.ObjId) :
    SystemState :=
  match st.getObject? epId with
  | some (.endpoint ep) =>
    match ep.serviceRegistered with
    | false => st
    | true =>
      match st.serviceRegistry[ServiceId.ofNat epId.toNat]? with
      | none => st
      | some reg =>
        clearEndpointRegistration (eraseServiceRegistration st (ServiceId.ofNat epId.toNat))
          reg.endpointCap (ServiceId.ofNat epId.toNat)
  | _ => st

/-- An admitted revoke through the endpoint succeeds as its perform. -/
theorem revokeServiceByRecordedRegistration_of_admitted (st : SystemState) (epId : SeLe4n.ObjId)
    (h : recordedRegistrationPresent st epId = true) :
    revokeServiceByRecordedRegistration epId st = .ok ((), revokeServiceByRecordedRegistrationPerform st epId) := by
  unfold recordedRegistrationPresent at h
  unfold revokeServiceByRecordedRegistration revokeServiceByRecordedRegistrationPerform
  split at h
  · next ep hObj =>
    split at h
    · cases h
    · next hC =>
      unfold revokeService
      cases hR : st.serviceRegistry[ServiceId.ofNat epId.toNat]? with
      | none => rw [hR] at h; cases h
      | some reg => rfl
  · cases h

/-- A successful revoke through the endpoint is `revokeService` of the
registration the endpoint records. -/
theorem revokeServiceByRecordedRegistration_ok {epId : SeLe4n.ObjId} {st : SystemState}
    {r : Unit × SystemState} (h : revokeServiceByRecordedRegistration epId st = .ok r) :
    ∃ ep, st.objects[epId]? = some (.endpoint ep) ∧ ep.serviceRegistered = true ∧
      revokeService (ServiceId.ofNat epId.toNat) st = .ok r := by
  unfold revokeServiceByRecordedRegistration SystemState.getObject? at h
  split at h
  · rename_i ep hEp
    split at h
    · cases h
    · rename_i hC
      exact ⟨ep, hEp, hC, h⟩
  · cases h

/-- ...so it is a successful `revokeService` of some registration. -/
theorem revokeServiceByRecordedRegistration_revokeService {epId : SeLe4n.ObjId} {st st' : SystemState}
    (h : revokeServiceByRecordedRegistration epId st = .ok ((), st')) :
    ∃ sid, revokeService sid st = .ok ((), st') := by
  obtain ⟨_, _, _, h⟩ := revokeServiceByRecordedRegistration_ok h
  exact ⟨_, h⟩

-- ============================================================================
-- Theorems: error conditions, success post-conditions, frame lemmas
-- ============================================================================

/-- Duplicate interface registration returns `illegalState`. -/
theorem registerInterface_error_duplicate
    (st : SystemState) (spec : InterfaceSpec)
    (hDup : st.interfaceRegistry[spec.ifaceId]? ≠ none) :
    registerInterface spec st = .error .illegalState := by
  unfold registerInterface
  simp [hDup]

/-- Successful interface registration stores the spec in the registry. -/
theorem registerInterface_success_stores
    (st st' : SystemState) (spec : InterfaceSpec)
    (hInvExt : st.interfaceRegistry.invExt)
    (hStep : registerInterface spec st = .ok ((), st')) :
    st'.interfaceRegistry[spec.ifaceId]? = some spec := by
  unfold registerInterface at hStep
  split at hStep
  · cases hStep
  · simp at hStep; cases hStep
    simp only [RHTable_getElem?_eq_get?]
    exact RHTable.getElem?_insert_self _ _ _ hInvExt

/-- Interface registration preserves objects. -/
theorem registerInterface_preserves_objects
    (st st' : SystemState) (spec : InterfaceSpec)
    (hStep : registerInterface spec st = .ok ((), st')) :
    st'.objects = st.objects := by
  unfold registerInterface at hStep
  split at hStep
  · cases hStep
  · simp at hStep; cases hStep; rfl

/-- Duplicate service registration returns `illegalState`. -/
theorem registerService_error_duplicate
    (st : SystemState) (reg : ServiceRegistration)
    (hDup : st.serviceRegistry[reg.sid]? ≠ none) :
    registerService reg st = .error .illegalState := by
  unfold registerService SystemState.getObject?
  simp [hDup]

/-- Service registration with unknown interface returns `objectNotFound`. -/
theorem registerService_error_unknown_interface
    (st : SystemState) (reg : ServiceRegistration)
    (hNoDup : st.serviceRegistry[reg.sid]? = none)
    (hNoIface : st.interfaceRegistry[reg.iface.ifaceId]? = none) :
    registerService reg st = .error .objectNotFound := by
  unfold registerService SystemState.getObject?
  simp [hNoDup, hNoIface]

/-- Revoking a non-existent service returns `objectNotFound`. -/
theorem revokeService_error_not_found
    (st : SystemState) (sid : ServiceId)
    (hMissing : st.serviceRegistry[sid]? = none) :
    revokeService sid st = .error .objectNotFound := by
  unfold revokeService
  simp [hMissing]

/-- R4-C.1 (M-14): Service registration without Write right returns `illegalAuthority`
    when targeting an existing endpoint. -/
theorem registerService_error_no_write_right
    (st : SystemState) (reg : ServiceRegistration)
    (hNoDup : st.serviceRegistry[reg.sid]? = none)
    (hHasIface : st.interfaceRegistry[reg.iface.ifaceId]? ≠ none)
    (epId : SeLe4n.ObjId) (ep : Endpoint)
    (hTarget : reg.endpointCap.target = .object epId)
    (hEp : st.objects[epId]? = some (.endpoint ep))
    (hNoWrite : Capability.hasRight reg.endpointCap .write = false) :
    registerService reg st = .error .illegalAuthority := by
  unfold registerService
  simp only [hNoDup, hHasIface, hTarget]
  repeat' split
  all_goals (simp_all; try (rename_i hne heq; exact hne _ heq.symm))

/-- WS-ZA ZA5.4 part 30: **a successful registration** passed every check, and
records itself in the registry and on its endpoint, and writes nothing else. -/
theorem registerService_ok {reg : ServiceRegistration} {st st' : SystemState}
    (hStep : registerService reg st = .ok ((), st')) :
    ∃ epId ep, reg.endpointCap.target = .object epId ∧
      st.objects[epId]? = some (.endpoint ep) ∧
      st.serviceRegistry[reg.sid]? = none ∧
      ep.serviceRegistered = false ∧
      st' = { st with
        objects := st.objects.insert epId (.endpoint { ep with serviceRegistered := true })
        serviceRegistry := st.serviceRegistry.insert reg.sid reg } := by
  unfold registerService at hStep
  split at hStep
  · cases hStep
  · split at hStep
    · cases hStep
    · rename_i hNoDup _
      split at hStep
      · rename_i epId hTarget
        split at hStep
        · cases hStep
        · rename_i ep hObj
          split at hStep
          · cases hStep
          · split at hStep
            · cases hStep
            · rename_i hReg
              cases hStep
              exact ⟨epId, ep, hTarget, hObj, by simpa using hNoDup,
                by simpa using hReg, rfl⟩
        · cases hStep
      · cases hStep

/-- Service registration preserves scheduler state. -/
theorem registerService_preserves_scheduler
    (st st' : SystemState) (reg : ServiceRegistration)
    (hStep : registerService reg st = .ok ((), st')) :
    st'.scheduler = st.scheduler := by
  obtain ⟨_, _, _, _, _, _, rfl⟩ := registerService_ok hStep; rfl

/-- The registration's endpoint write: its record of the service, nothing more. -/
theorem clearEndpointRegistration_cases (st : SystemState) (cap : Capability) (sid : ServiceId) :
    clearEndpointRegistration st cap sid = st ∨
    ∃ e ep, cap.target = .object e ∧ st.objects[e]? = some (.endpoint ep) ∧
      (ep.serviceRegistered = true ∧ sid = ServiceId.ofNat e.toNat) ∧
      clearEndpointRegistration st cap sid =
        { st with objects := st.objects.insert e (.endpoint { ep with serviceRegistered := false }) } := by
  unfold clearEndpointRegistration
  split
  · rename_i e hT
    split
    · rename_i ep h
      split
      · rename_i hc; exact .inr ⟨e, ep, hT, h, hc, rfl⟩
      · exact .inl rfl
    · exact .inl rfl
  · exact .inl rfl

theorem clearEndpointRegistration_scheduler (st : SystemState) (cap : Capability) (sid : ServiceId) :
    (clearEndpointRegistration st cap sid).scheduler = st.scheduler := by
  rcases clearEndpointRegistration_cases st cap sid with h | ⟨_, _, _, _, _, h⟩ <;> rw [h]

/-- WS-ZA ZA5.4 part 30: **a successful revocation** erases a present
registration and clears its record on its endpoint. -/
theorem revokeService_ok {sid : ServiceId} {st st' : SystemState}
    (hStep : revokeService sid st = .ok ((), st')) :
    ∃ reg, st.serviceRegistry[sid]? = some reg ∧
      st' = clearEndpointRegistration { st with serviceRegistry := st.serviceRegistry.erase sid }
          reg.endpointCap sid := by
  unfold revokeService at hStep
  split at hStep
  · cases hStep
  · rename_i reg hReg
    cases hStep
    exact ⟨reg, hReg, rfl⟩

/-- Successful revocation removes the entry from the registry. -/
theorem revokeService_success_removes
    (st st' : SystemState) (sid : ServiceId)
    (hInvExt : st.serviceRegistry.invExt)
    (hStep : revokeService sid st = .ok ((), st')) :
    st'.serviceRegistry[sid]? = none := by
  obtain ⟨reg, _, rfl⟩ := revokeService_ok hStep
  rcases clearEndpointRegistration_cases { st with serviceRegistry := st.serviceRegistry.erase sid }
    reg.endpointCap sid with h | ⟨_, _, _, _, _, h⟩ <;> rw [h] <;>
  · simp only [RHTable_getElem?_eq_get?]
    exact RHTable.getElem?_erase_self _ _ hInvExt

/-- Revocation preserves scheduler state. -/
theorem revokeService_preserves_scheduler
    (st st' : SystemState) (sid : ServiceId)
    (hStep : revokeService sid st = .ok ((), st')) :
    st'.scheduler = st.scheduler := by
  obtain ⟨reg, _, rfl⟩ := revokeService_ok hStep
  rw [clearEndpointRegistration_scheduler]

/-- The registration's endpoint write writes the object store alone. -/
theorem clearEndpointRegistration_eq_withObjects (st : SystemState) (cap : Capability)
    (sid : ServiceId) :
    clearEndpointRegistration st cap sid =
      { st with objects := (clearEndpointRegistration st cap sid).objects } := by
  rcases clearEndpointRegistration_cases st cap sid with h | ⟨_, _, _, _, _, h⟩ <;> rw [h]

/-- ...and keeps every key present or absent. -/
theorem clearEndpointRegistration_objects_none_iff (st : SystemState) (cap : Capability)
    (sid : ServiceId) (hInv : st.objects.invExt) (k : SeLe4n.ObjId) :
    (clearEndpointRegistration st cap sid).objects[k]? = none ↔ st.objects[k]? = none := by
  rcases clearEndpointRegistration_cases st cap sid with h | ⟨e, ep, _, hE, _, h⟩
  · rw [h]
  · rw [h]
    simp only [RHTable_getElem?_eq_get?]
    by_cases hk : e = k
    · subst hk
      rw [RHTable.getElem?_insert_self _ _ _ hInv]
      simp only [RHTable_getElem?_eq_get?] at hE
      rw [hE]; simp
    · rw [RHTable.getElem?_insert_ne _ _ _ _ (fun hb => hk (eq_of_beq hb)) hInv]

/-- A successful revocation's registry is the old one without the service. -/
theorem revokeService_serviceRegistry {sid : ServiceId} {st st' : SystemState}
    (hStep : revokeService sid st = .ok ((), st')) :
    st'.serviceRegistry = st.serviceRegistry.erase sid ∧
    st'.interfaceRegistry = st.interfaceRegistry := by
  obtain ⟨reg, _, rfl⟩ := revokeService_ok hStep
  rw [clearEndpointRegistration_eq_withObjects]
  exact ⟨rfl, rfl⟩

/-- A successful revocation keeps every key present or absent. -/
theorem revokeService_objects_none_iff {sid : ServiceId} {st st' : SystemState}
    (hStep : revokeService sid st = .ok ((), st')) (hInv : st.objects.invExt)
    (k : SeLe4n.ObjId) : st'.objects[k]? = none ↔ st.objects[k]? = none := by
  obtain ⟨reg, _, rfl⟩ := revokeService_ok hStep
  exact clearEndpointRegistration_objects_none_iff
    { st with serviceRegistry := st.serviceRegistry.erase sid } _ _ hInv k

/-- A successful registration keeps every key present or absent. -/
theorem registerService_objects_none_iff {reg : ServiceRegistration} {st st' : SystemState}
    (hStep : registerService reg st = .ok ((), st')) (hInv : st.objects.invExt)
    (k : SeLe4n.ObjId) : st'.objects[k]? = none ↔ st.objects[k]? = none := by
  obtain ⟨e, ep, _, hE, _, _, rfl⟩ := registerService_ok hStep
  simp only [RHTable_getElem?_eq_get?]
  by_cases hk : e = k
  · subst hk
    rw [RHTable.getElem?_insert_self _ _ _ hInv]
    simp only [RHTable_getElem?_eq_get?] at hE
    rw [hE]; simp
  · rw [RHTable.getElem?_insert_ne _ _ _ _ (fun hb => hk (eq_of_beq hb)) hInv]

/-- The one object write the registry makes: an endpoint's `serviceRegistered`, every
other field — its queues and its other words — kept.  What a reader of the
object store transports across a registration or a revocation. -/
def RegistrationFlagRewrite (o o' : SeLe4n.Kernel.RobinHood.RHTable SeLe4n.ObjId KernelObject) : Prop :=
  o' = o ∨ ∃ e ep c, o[e]? = some (.endpoint ep) ∧
    o' = o.insert e (.endpoint { ep with serviceRegistered := c })

theorem registerService_registrationFlagRewrite {reg : ServiceRegistration} {st st' : SystemState}
    (hStep : registerService reg st = .ok ((), st')) :
    RegistrationFlagRewrite st.objects st'.objects := by
  obtain ⟨e, ep, _, hE, _, _, rfl⟩ := registerService_ok hStep
  exact .inr ⟨e, ep, _, hE, rfl⟩

theorem revokeService_registrationFlagRewrite {sid : ServiceId} {st st' : SystemState}
    (hStep : revokeService sid st = .ok ((), st')) :
    RegistrationFlagRewrite st.objects st'.objects := by
  obtain ⟨reg, _, rfl⟩ := revokeService_ok hStep
  rcases clearEndpointRegistration_cases { st with serviceRegistry := st.serviceRegistry.erase sid }
    reg.endpointCap sid with h | ⟨e, ep, _, hE, _, h⟩ <;> rw [h]
  · exact .inl rfl
  · exact .inr ⟨e, ep, _, hE, rfl⟩

/-- Across the rewrite, every key keeps its kind, and every object but an
endpoint keeps its value. -/
theorem RegistrationFlagRewrite.lookup {o o'} (h : RegistrationFlagRewrite o o') (hInv : o.invExt)
    (k : SeLe4n.ObjId) :
    (o'[k]? = o[k]?) ∨ ∃ ep c, o[k]? = some (.endpoint ep) ∧
      o'[k]? = some (.endpoint { ep with serviceRegistered := c }) := by
  rcases h with rfl | ⟨e, ep, c, hE, rfl⟩
  · exact .inl rfl
  · simp only [RHTable_getElem?_eq_get?] at hE ⊢
    by_cases hk : e = k
    · subst hk
      rw [RHTable.getElem?_insert_self _ _ _ hInv]
      exact .inr ⟨ep, c, hE, rfl⟩
    · rw [RHTable.getElem?_insert_ne _ _ _ _ (fun hb => hk (eq_of_beq hb)) hInv]
      exact .inl rfl

theorem RegistrationFlagRewrite.invExt {o o'} (h : RegistrationFlagRewrite o o') (hInv : o.invExt) :
    o'.invExt := by
  rcases h with rfl | ⟨e, ep, c, _, rfl⟩
  · exact hInv
  · exact o.insert_preserves_invExt e _ hInv

theorem RegistrationFlagRewrite.size_le {o o'} (h : RegistrationFlagRewrite o o') (hInv : o.invExt) :
    o'.size ≤ o.size := by
  rcases h with rfl | ⟨e, ep, c, hE, rfl⟩
  · exact Nat.le_refl _
  · simp only [RHTable_getElem?_eq_get?] at hE
    exact RHTable.size_insert_le_of_get? o e _ _ hInv hE

end SeLe4n.Kernel
