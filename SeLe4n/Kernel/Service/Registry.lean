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
returns and machine-checked post-conditions.  Since WS-ZA ZA5.9 the registry is
no table: each registration lives on the endpoint it names, and the registry is
read off the endpoints (`SystemState.serviceRegistry`), one object read at the
service's id.

## Operations

| Operation | Mutates | Error conditions |
|-----------|---------|-----------------|
| `registerInterface` | `interfaceRegistry` | `illegalState` (duplicate) |
| `registerService` | its endpoint's service record (`Endpoint.withService`) | `illegalState`, `objectNotFound`, `invalidCapability` |
| `lookupServiceByCap` | — (read-only; the specification) | `objectNotFound` |
| `lookupServiceByRecordedRegistration` | — (read-only; the O(1) form the kernel runs) | `objectNotFound` |
| `revokeService` | its endpoint's service record (`clearServiceRecord`) | `objectNotFound` |
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

/-- **Whether the endpoint `epId` records a registration**: its flag
(`Endpoint.serviceRegistered`), read in place.  Any other object, and an empty
slot, records none.  The check the register, the query and the revoke share,
read before any write: since WS-ZA ZA5.9 the registry is read off the endpoints
(`SystemState.serviceRegistry`), so this one field is whether the registry
holds the service with the endpoint's id
(`recordedRegistrationPresent_eq_isSome`), answered without building the
registration. -/
@[inline] def recordedRegistrationPresent (st : SystemState) (epId : SeLe4n.ObjId) : Bool :=
  match st.getObject? epId with
  | some (.endpoint ep) => ep.serviceRegistered
  | _ => false

/-- **The flag is the registry's answer**: the endpoint with a service's id
records a registration exactly when the registry holds one under that id. -/
theorem recordedRegistrationPresent_eq_isSome (st : SystemState) (sid : ServiceId) :
    recordedRegistrationPresent st (SeLe4n.ObjId.ofNat sid.toNat) =
      (st.serviceRegistry[sid]?).isSome := by
  unfold recordedRegistrationPresent SystemState.getObject?
  rw [SystemState.serviceRegistry_getElem?]
  cases st.objects[SeLe4n.ObjId.ofNat sid.toNat]? with
  | none => rfl
  | some o =>
    cases o with
    | endpoint ep => cases h : ep.serviceRegistered <;> simp [h]
    | _ => rfl

/-- Register a service with capability-mediated binding.
Checks (ordered for defense-in-depth — validate target before authority):
1. Service not already registered (`illegalState`): the endpoint with the
   service's id records none (`recordedRegistrationPresent`, the registry's
   answer, `recordedRegistrationPresent_eq_isSome`)
2. Interface exists in registry (`objectNotFound`)
3. Endpoint capability target resolves to an existing object (`invalidCapability`)
4. R4-C.2 (L-09): Target object must be an endpoint (`invalidCapability`)
5. R4-C.1 (M-14): Endpoint capability must have Write right (`illegalAuthority`)
6. AE5-B (U-20): No existing service already targets this endpoint (`illegalState`),
   read off the endpoint's own record of its registration (`Endpoint.serviceRegistered`,
   WS-ZA ZA5.4 part 30).

The one write is the endpoint's: since WS-ZA ZA5.9 the registration lives on
it (`Endpoint.withService`), and no table holds a copy. -/
def registerService (reg : ServiceRegistration) : Kernel Unit :=
  fun st =>
    if recordedRegistrationPresent st (SeLe4n.ObjId.ofNat reg.sid.toNat) then
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
            .ok ((), st.rewriteObject epId
                (.endpoint (ep.withService (EndpointService.ofRegistration reg)))
                ⟨_, hObj, rfl, rfl⟩)
        | some _ => .error .invalidCapability
      | _ => .error .invalidCapability

/-- **WS-ZA ZA5.5**: `registerService`'s checks, read from the state before
anything is written, in its order (seL4's decode half). -/
@[inline] def registerServiceAdmitted (st : SystemState) (reg : ServiceRegistration) : Bool :=
  !recordedRegistrationPresent st (SeLe4n.ObjId.ofNat reg.sid.toNat) &&
    (st.interfaceRegistry[reg.iface.ifaceId]?).isSome &&
    match reg.endpointCap.target with
    | .object epId =>
      match st.getObject? epId with
      | some (.endpoint ep) => Capability.hasRight reg.endpointCap .write && !ep.serviceRegistered
      | _ => false
    | _ => false

/-- **WS-ZA ZA5.5**: `registerService`'s writes, total: the endpoint records the
registration, its flag and words (seL4's perform half).  A state whose target is
no endpoint is returned unchanged; `registerServiceAdmitted` rules that state
out. -/
@[inline] def registerServicePerform (st : SystemState) (reg : ServiceRegistration) :
    SystemState :=
  match reg.endpointCap.target with
  | .object epId =>
    match hObj : st.getObject? epId with
    | some (.endpoint ep) =>
      st.rewriteObject epId (.endpoint (ep.withService (EndpointService.ofRegistration reg)))
        ⟨_, hObj, rfl, rfl⟩
    | _ => st
  | _ => st

/-- **WS-ZA ZA5.5**: the object update that writes the service record `sv` on
an endpoint (`Endpoint.withService`): a registration's flag and words set, or
the clear record a revocation leaves. -/
@[inline] def setServiceObject (sv : EndpointService) : KernelObject → KernelObject
  | .endpoint ep => .endpoint (ep.withService sv)
  | o => o

/-- **WS-ZA ZA5.5**: the compiled `registerServicePerform` — the endpoint's
record written in its slot (`SystemState.modifyObject`), so neither the
endpoint nor its `KernelObject` cell is rebuilt.  Since WS-ZA ZA5.9 that is the
whole write. -/
def registerServicePerformImpl (st : SystemState) (reg : ServiceRegistration) : SystemState :=
  match reg.endpointCap.target with
  | .object epId =>
    match st.getEndpoint? epId with
    | some _ => st.modifyObject epId (setServiceObject (EndpointService.ofRegistration reg))
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
      unfold SystemState.rewriteObject SystemState.modifyObject
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
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨hFree, hIface⟩, hRest⟩ := h
  have hIface' : ¬ st.interfaceRegistry[reg.iface.ifaceId]? = none := by
    intro hN; rw [hN] at hIface; cases hIface
  rw [hFree]
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

/-- The specification's fold body: the first registration naming `epId` among
those the endpoints record, each read off its endpoint
(`EndpointService.registrationAt`). -/
@[inline] def lookupServiceStep (epId : SeLe4n.ObjId) :
    Option ServiceRegistration → SeLe4n.ObjId → KernelObject → Option ServiceRegistration :=
  fun acc k o =>
    match acc with
    | some _ => acc
    | none =>
      match o with
      | .endpoint ep =>
        if ep.serviceRegistered then
          match (ep.service.registrationAt k).endpointCap.target with
          | .object id => if id == epId then some (ep.service.registrationAt k) else none
          | _ => none
        else none
      | _ => none

/-- Read-only lookup of a service registration by matching endpoint capability
target. Returns the first registration whose endpoint targets the given ObjId,
or `objectNotFound` if none matches.

T5-K (M-LCS-2): The `fold` iteration order is deterministic for `RHTable`:
entries are visited in probe-chain order (hash → linear probing). The
first-match convention is what makes the fold's answer independent of that
order here, since at most one registration can name a given endpoint
(`registryEndpointUnique`, which holds of every state since WS-ZA ZA5.9):
the fold returns the one registration, or none.  Since ZA5.9 the registrations
are the ones the endpoints record, so the fold runs over the object store.

This fold is the specification.  The kernel runs `lookupServiceByRecordedRegistration`,
which reads the registration the endpoint records instead (WS-ZA ZA5.4 part 31, ZA5.8); the two
agree wherever the object store is well formed
(`lookupServiceByRecordedRegistration_eq_lookupServiceByCap`). -/
def lookupServiceByCap (epId : SeLe4n.ObjId) : Kernel ServiceRegistration :=
  fun st =>
    match st.objects.fold (init := none) (lookupServiceStep epId) with
    | some reg => .ok (reg, st)
    | none => .error .objectNotFound

/-- **The service lookup the kernel runs: O(1), through the endpoint's record.**
An endpoint records whether a registration names it
(`Endpoint.serviceRegistered`) and, since WS-ZA ZA5.8, the registration's words
(`Endpoint.service`), and a service's identity is its endpoint's, so the lookup
reads that one object and no table.  It returns what the
specification `lookupServiceByCap` returns wherever the object store is well
formed (`lookupServiceByRecordedRegistration_eq_lookupServiceByCap`), which every
reachable state satisfies. -/
def lookupServiceByRecordedRegistration (epId : SeLe4n.ObjId) : Kernel ServiceRegistration :=
  fun st =>
    match st.getObject? epId with
    | some (.endpoint ep) =>
      match ep.serviceRegistered with
      | false => .error .objectNotFound
      | true => .ok (ep.service.registrationAt epId, st)
    | _ => .error .objectNotFound

/-- **Clear the service record of the endpoint `e`**: the endpoint forgets the
registration it records — its flag and the registration's words
(`Endpoint.withService {}`).  Every other state — `e` no endpoint, or one
recording none — is returned as it is.  Since WS-ZA ZA5.9 this is the whole of
a revocation's write: the registration lived on the endpoint and nowhere
else. -/
@[inline] def clearServiceRecord (st : SystemState) (e : SeLe4n.ObjId) : SystemState :=
  match h : st.getObject? e with
  | some (.endpoint ep) =>
    if ep.serviceRegistered then
      st.rewriteObject e (.endpoint (ep.withService {})) ⟨_, h, rfl, rfl⟩
    else st
  | _ => st

/-- **WS-ZA ZA5.5**: the compiled `clearServiceRecord` — the endpoint's record
cleared in its slot (`SystemState.modifyObject`), so on an exclusively owned
state neither the endpoint nor its `KernelObject` cell is rebuilt.  A call, so
the caller's state arrives exclusive. -/
def clearServiceRecordImpl (st : SystemState) (e : SeLe4n.ObjId) : SystemState :=
  match st.getEndpoint? e with
  | some ep => if ep.serviceRegistered then st.modifyObject e (setServiceObject {}) else st
  | none => st

@[csimp] theorem clearServiceRecord_eq_impl : @clearServiceRecord = @clearServiceRecordImpl := by
  funext st e
  unfold clearServiceRecord clearServiceRecordImpl
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

/-- Remove a service registration by ServiceId.
Returns `objectNotFound` if no such registration exists: the endpoint with the
service's id records none (`recordedRegistrationPresent`, the registry's answer,
`recordedRegistrationPresent_eq_isSome`).  Since WS-ZA ZA5.9 the registration
lives on that endpoint alone, so clearing its record (`clearServiceRecord`) is
the revocation.  (Until WS-ZA ZA5.4 part 32 it also cleaned the kernel's
service dependency graph, which the kernel no longer keeps.) -/
def revokeService (sid : ServiceId) : Kernel Unit :=
  fun st =>
    if recordedRegistrationPresent st (SeLe4n.ObjId.ofNat sid.toNat) then
      .ok ((), clearServiceRecord st (SeLe4n.ObjId.ofNat sid.toNat))
    else .error .objectNotFound

/-- **The revoke the kernel runs: the registration recorded on the invoked
endpoint.**  The caller names no service: the authority to remove a
registration is a capability to the endpoint it names, the same capability the
query reads it back through (`lookupServiceByRecordedRegistration`), and the
registration is the one that endpoint records (`Endpoint.serviceRegistered`,
under the endpoint's own id).  An endpoint recording none is `objectNotFound`,
as is any other object.  `revokeService` of the endpoint's id is the
primitive this runs. -/
def revokeServiceByRecordedRegistration (epId : SeLe4n.ObjId) : Kernel Unit :=
  fun st =>
    match st.getObject? epId with
    | some (.endpoint ep) =>
      match ep.serviceRegistered with
      | false => .error .objectNotFound
      | true => revokeService (ServiceId.ofNat epId.toNat) st
    | _ => .error .objectNotFound

/-- **WS-ZA ZA5.5**: `revokeServiceByRecordedRegistration`'s writes, total: the
endpoint's record cleared.  A state with no recorded registration is returned
unchanged; `recordedRegistrationPresent` rules it out. -/
@[inline] def revokeServiceByRecordedRegistrationPerform (st : SystemState) (epId : SeLe4n.ObjId) :
    SystemState :=
  clearServiceRecord st epId

/-- An admitted revoke through the endpoint succeeds as its perform. -/
theorem revokeServiceByRecordedRegistration_of_admitted (st : SystemState) (epId : SeLe4n.ObjId)
    (h : recordedRegistrationPresent st epId = true) :
    revokeServiceByRecordedRegistration epId st = .ok ((), revokeServiceByRecordedRegistrationPerform st epId) := by
  have h' := h
  unfold recordedRegistrationPresent at h
  unfold revokeServiceByRecordedRegistration revokeServiceByRecordedRegistrationPerform
  split
  · next ep hObj =>
    rw [hObj] at h
    have hC : ep.serviceRegistered = true := h
    simp only [hC]
    unfold revokeService
    exact if_pos h'
  · next hN =>
    split at h
    · next ep hObj => exact absurd hObj (hN ep)
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
  have hP : recordedRegistrationPresent st (SeLe4n.ObjId.ofNat reg.sid.toNat) = true := by
    rw [recordedRegistrationPresent_eq_isSome]
    cases h : st.serviceRegistry[reg.sid]? with
    | none => exact absurd h hDup
    | some _ => rfl
  unfold registerService
  simp [hP]

/-- No registration under a service id: its endpoint records none. -/
theorem recordedRegistrationPresent_of_none {st : SystemState} {sid : ServiceId}
    (h : st.serviceRegistry[sid]? = none) :
    recordedRegistrationPresent st (SeLe4n.ObjId.ofNat sid.toNat) = false := by
  rw [recordedRegistrationPresent_eq_isSome, h]; rfl

/-- Service registration with unknown interface returns `objectNotFound`. -/
theorem registerService_error_unknown_interface
    (st : SystemState) (reg : ServiceRegistration)
    (hNoDup : st.serviceRegistry[reg.sid]? = none)
    (hNoIface : st.interfaceRegistry[reg.iface.ifaceId]? = none) :
    registerService reg st = .error .objectNotFound := by
  unfold registerService
  simp [recordedRegistrationPresent_of_none hNoDup, hNoIface]

/-- Revoking a non-existent service returns `objectNotFound`. -/
theorem revokeService_error_not_found
    (st : SystemState) (sid : ServiceId)
    (hMissing : st.serviceRegistry[sid]? = none) :
    revokeService sid st = .error .objectNotFound := by
  unfold revokeService
  simp [recordedRegistrationPresent_of_none hMissing]

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
  simp only [recordedRegistrationPresent_of_none hNoDup, hHasIface, hTarget]
  repeat' split
  all_goals (simp_all; try (rename_i hne heq; exact hne _ heq.symm))

/-- WS-ZA ZA5.4 part 30: **a successful registration** passed every check, and
records itself on its endpoint — since WS-ZA ZA5.9 the one place it lives —
and writes nothing else. -/
theorem registerService_ok {reg : ServiceRegistration} {st st' : SystemState}
    (hStep : registerService reg st = .ok ((), st')) :
    ∃ epId ep, reg.endpointCap.target = .object epId ∧
      st.objects[epId]? = some (.endpoint ep) ∧
      st.serviceRegistry[reg.sid]? = none ∧
      ep.serviceRegistered = false ∧
      st' = { st with
        objects := st.objects.insert epId
          (.endpoint (ep.withService (EndpointService.ofRegistration reg))) } := by
  unfold registerService at hStep
  split at hStep
  · cases hStep
  · split at hStep
    · cases hStep
    · rename_i hNoDup _
      have hNone : st.serviceRegistry[reg.sid]? = none := by
        have h := recordedRegistrationPresent_eq_isSome st reg.sid
        cases hs : st.serviceRegistry[reg.sid]? with
        | none => rfl
        | some _ => rw [hs] at h; exact absurd (h.trans rfl) hNoDup
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
              exact ⟨epId, ep, hTarget, hObj, hNone, by simpa using hReg, rfl⟩
        · cases hStep
      · cases hStep

/-- Service registration preserves scheduler state. -/
theorem registerService_preserves_scheduler
    (st st' : SystemState) (reg : ServiceRegistration)
    (hStep : registerService reg st = .ok ((), st')) :
    st'.scheduler = st.scheduler := by
  obtain ⟨_, _, _, _, _, _, rfl⟩ := registerService_ok hStep; rfl

/-- Service registration writes no machine state. -/
theorem registerService_preserves_machine
    (st st' : SystemState) (reg : ServiceRegistration)
    (hStep : registerService reg st = .ok ((), st')) :
    st'.machine = st.machine := by
  obtain ⟨_, _, _, _, _, _, rfl⟩ := registerService_ok hStep; rfl

/-- The clear's one write: the endpoint's record of the service, nothing more. -/
theorem clearServiceRecord_cases (st : SystemState) (e : SeLe4n.ObjId) :
    clearServiceRecord st e = st ∨
    ∃ ep, st.objects[e]? = some (.endpoint ep) ∧ ep.serviceRegistered = true ∧
      clearServiceRecord st e =
        { st with objects := st.objects.insert e (.endpoint (ep.withService {})) } := by
  unfold clearServiceRecord
  split
  · rename_i ep h
    split
    · rename_i hc; exact .inr ⟨ep, h, hc, rfl⟩
    · exact .inl rfl
  · exact .inl rfl

theorem clearServiceRecord_scheduler (st : SystemState) (e : SeLe4n.ObjId) :
    (clearServiceRecord st e).scheduler = st.scheduler := by
  rcases clearServiceRecord_cases st e with h | ⟨_, _, _, h⟩ <;> rw [h]

/-- WS-ZA ZA5.4 part 30: **a successful revocation** finds a registration
recorded on the endpoint with the service's id and clears that record — since
WS-ZA ZA5.9 the one place the registration lived. -/
theorem revokeService_ok {sid : ServiceId} {st st' : SystemState}
    (hStep : revokeService sid st = .ok ((), st')) :
    ∃ ep, st.objects[SeLe4n.ObjId.ofNat sid.toNat]? = some (.endpoint ep) ∧
      ep.serviceRegistered = true ∧
      st' = { st with
        objects := st.objects.insert (SeLe4n.ObjId.ofNat sid.toNat) (.endpoint (ep.withService {})) } := by
  unfold revokeService at hStep
  split at hStep
  · rename_i hP
    cases hStep
    unfold recordedRegistrationPresent at hP
    unfold clearServiceRecord
    split
    · next ep hE =>
      rw [hE] at hP
      have hP' : ep.serviceRegistered = true := hP
      rw [if_pos hP']
      exact ⟨ep, hE, hP', rfl⟩
    · next hN =>
      split at hP
      · next ep hE => exact absurd hE (hN ep)
      · cases hP
  · cases hStep

/-- The registry's entry under `sid` after a revocation of it: none. -/
theorem revokeService_success_removes
    (st st' : SystemState) (sid : ServiceId)
    (hInv : st.objects.invExt)
    (hStep : revokeService sid st = .ok ((), st')) :
    st'.serviceRegistry[sid]? = none := by
  obtain ⟨ep, _, _, rfl⟩ := revokeService_ok hStep
  rw [SystemState.serviceRegistry_getElem?]
  simp only [RHTable_getElem?_eq_get?]
  rw [RHTable.getElem?_insert_self _ _ _ hInv]
  simp

/-- Revocation preserves scheduler state. -/
theorem revokeService_preserves_scheduler
    (st st' : SystemState) (sid : ServiceId)
    (hStep : revokeService sid st = .ok ((), st')) :
    st'.scheduler = st.scheduler := by
  obtain ⟨_, _, _, rfl⟩ := revokeService_ok hStep; rfl

/-- Revocation writes no machine state. -/
theorem revokeService_preserves_machine
    (st st' : SystemState) (sid : ServiceId)
    (hStep : revokeService sid st = .ok ((), st')) :
    st'.machine = st.machine := by
  obtain ⟨_, _, _, rfl⟩ := revokeService_ok hStep; rfl

/-- The clear writes the object store alone. -/
theorem clearServiceRecord_eq_withObjects (st : SystemState) (e : SeLe4n.ObjId) :
    clearServiceRecord st e = { st with objects := (clearServiceRecord st e).objects } := by
  rcases clearServiceRecord_cases st e with h | ⟨_, _, _, h⟩ <;> rw [h]

/-- ...and keeps every key present or absent. -/
theorem clearServiceRecord_objects_none_iff (st : SystemState) (e : SeLe4n.ObjId)
    (hInv : st.objects.invExt) (k : SeLe4n.ObjId) :
    (clearServiceRecord st e).objects[k]? = none ↔ st.objects[k]? = none := by
  rcases clearServiceRecord_cases st e with h | ⟨ep, hE, _, h⟩
  · rw [h]
  · rw [h]
    simp only [RHTable_getElem?_eq_get?]
    by_cases hk : e = k
    · subst hk
      rw [RHTable.getElem?_insert_self _ _ _ hInv]
      simp only [RHTable_getElem?_eq_get?] at hE
      rw [hE]; simp
    · rw [RHTable.getElem?_insert_ne _ _ _ _ (fun hb => hk (eq_of_beq hb)) hInv]

/-- A successful revocation keeps every key present or absent. -/
theorem revokeService_objects_none_iff {sid : ServiceId} {st st' : SystemState}
    (hStep : revokeService sid st = .ok ((), st')) (hInv : st.objects.invExt)
    (k : SeLe4n.ObjId) : st'.objects[k]? = none ↔ st.objects[k]? = none := by
  obtain ⟨ep, hE, _, rfl⟩ := revokeService_ok hStep
  simp only [RHTable_getElem?_eq_get?]
  by_cases hk : SeLe4n.ObjId.ofNat sid.toNat = k
  · subst hk
    rw [RHTable.getElem?_insert_self _ _ _ hInv]
    simp only [RHTable_getElem?_eq_get?] at hE
    rw [hE]; simp
  · rw [RHTable.getElem?_insert_ne _ _ _ _ (fun hb => hk (eq_of_beq hb)) hInv]

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

/-- The one object write the registry makes: an endpoint's service record (its
flag and the registration's words, `Endpoint.withService`), every other field —
its queues — kept.  What a reader of the
object store transports across a registration or a revocation. -/
def ServiceRecordRewrite (o o' : SeLe4n.Kernel.RobinHood.RHTable SeLe4n.ObjId KernelObject) : Prop :=
  o' = o ∨ ∃ e ep sv, o[e]? = some (.endpoint ep) ∧
    o' = o.insert e (.endpoint (ep.withService sv))

theorem registerService_serviceRecordRewrite {reg : ServiceRegistration} {st st' : SystemState}
    (hStep : registerService reg st = .ok ((), st')) :
    ServiceRecordRewrite st.objects st'.objects := by
  obtain ⟨e, ep, _, hE, _, _, rfl⟩ := registerService_ok hStep
  exact .inr ⟨e, ep, _, hE, rfl⟩

theorem revokeService_serviceRecordRewrite {sid : ServiceId} {st st' : SystemState}
    (hStep : revokeService sid st = .ok ((), st')) :
    ServiceRecordRewrite st.objects st'.objects := by
  obtain ⟨ep, hE, _, rfl⟩ := revokeService_ok hStep
  exact .inr ⟨_, ep, _, hE, rfl⟩

/-- Across the rewrite, every key keeps its kind, and every object but an
endpoint keeps its value. -/
theorem ServiceRecordRewrite.lookup {o o'} (h : ServiceRecordRewrite o o') (hInv : o.invExt)
    (k : SeLe4n.ObjId) :
    (o'[k]? = o[k]?) ∨ ∃ ep sv, o[k]? = some (.endpoint ep) ∧
      o'[k]? = some (.endpoint (ep.withService sv)) := by
  rcases h with rfl | ⟨e, ep, c, hE, rfl⟩
  · exact .inl rfl
  · simp only [RHTable_getElem?_eq_get?] at hE ⊢
    by_cases hk : e = k
    · subst hk
      rw [RHTable.getElem?_insert_self _ _ _ hInv]
      exact .inr ⟨ep, c, hE, rfl⟩
    · rw [RHTable.getElem?_insert_ne _ _ _ _ (fun hb => hk (eq_of_beq hb)) hInv]
      exact .inl rfl

theorem ServiceRecordRewrite.invExt {o o'} (h : ServiceRecordRewrite o o') (hInv : o.invExt) :
    o'.invExt := by
  rcases h with rfl | ⟨e, ep, c, _, rfl⟩
  · exact hInv
  · exact o.insert_preserves_invExt e _ hInv

theorem ServiceRecordRewrite.size_le {o o'} (h : ServiceRecordRewrite o o') (hInv : o.invExt) :
    o'.size ≤ o.size := by
  rcases h with rfl | ⟨e, ep, c, hE, rfl⟩
  · exact Nat.le_refl _
  · simp only [RHTable_getElem?_eq_get?] at hE
    exact RHTable.size_insert_le_of_get? o e _ _ hInv hE

end SeLe4n.Kernel
