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
orchestration model. Four deterministic operations with explicit error
returns and machine-checked post-conditions.

## Operations

| Operation | Mutates | Error conditions |
|-----------|---------|-----------------|
| `registerInterface` | `interfaceRegistry` | `illegalState` (duplicate) |
| `registerService` | `serviceRegistry` | `illegalState`, `objectNotFound`, `invalidCapability` |
| `lookupServiceByCap` | — (read-only) | `objectNotFound` |
| `revokeService` | `serviceRegistry` | `objectNotFound` |
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
Checks:
1. Service not already registered (`illegalState`)
2. Interface exists in registry (`objectNotFound`)
3. Endpoint capability target resolves to an existing object (`invalidCapability`)
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
        if st.objects[epId]? = none then
          .error .invalidCapability
        else
          .ok ((), { st with
            serviceRegistry := st.serviceRegistry.insert reg.sid reg })
      | _ => .error .invalidCapability

/-- Read-only lookup of a service registration by matching endpoint capability
target. Returns the first registration whose endpoint targets the given ObjId,
or `objectNotFound` if none matches. -/
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

/-- Remove a service registration by ServiceId.
Returns `objectNotFound` if no such registration exists. -/
def revokeService (sid : ServiceId) : Kernel Unit :=
  fun st =>
    if st.serviceRegistry[sid]? = none then
      .error .objectNotFound
    else
      .ok ((), { st with
        serviceRegistry := st.serviceRegistry.erase sid })

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

/-- Interface registration preserves services. -/
theorem registerInterface_preserves_services
    (st st' : SystemState) (spec : InterfaceSpec)
    (hStep : registerInterface spec st = .ok ((), st')) :
    st'.services = st.services := by
  unfold registerInterface at hStep
  split at hStep
  · cases hStep
  · simp at hStep; cases hStep; rfl

/-- Duplicate service registration returns `illegalState`. -/
theorem registerService_error_duplicate
    (st : SystemState) (reg : ServiceRegistration)
    (hDup : st.serviceRegistry[reg.sid]? ≠ none) :
    registerService reg st = .error .illegalState := by
  unfold registerService
  simp [hDup]

/-- Service registration with unknown interface returns `objectNotFound`. -/
theorem registerService_error_unknown_interface
    (st : SystemState) (reg : ServiceRegistration)
    (hNoDup : st.serviceRegistry[reg.sid]? = none)
    (hNoIface : st.interfaceRegistry[reg.iface.ifaceId]? = none) :
    registerService reg st = .error .objectNotFound := by
  unfold registerService
  simp [hNoDup, hNoIface]

/-- Revoking a non-existent service returns `objectNotFound`. -/
theorem revokeService_error_not_found
    (st : SystemState) (sid : ServiceId)
    (hMissing : st.serviceRegistry[sid]? = none) :
    revokeService sid st = .error .objectNotFound := by
  unfold revokeService
  simp [hMissing]

/-- Successful revocation removes the entry from the registry. -/
theorem revokeService_success_removes
    (st st' : SystemState) (sid : ServiceId)
    (hInvExt : st.serviceRegistry.invExt)
    (hStep : revokeService sid st = .ok ((), st')) :
    st'.serviceRegistry[sid]? = none := by
  unfold revokeService at hStep
  split at hStep
  · cases hStep
  · simp at hStep; cases hStep
    simp only [RHTable_getElem?_eq_get?]
    exact RHTable.getElem?_erase_self _ _ hInvExt

/-- Service registration preserves objects. -/
theorem registerService_preserves_objects
    (st st' : SystemState) (reg : ServiceRegistration)
    (hStep : registerService reg st = .ok ((), st')) :
    st'.objects = st.objects := by
  unfold registerService at hStep
  split at hStep
  · cases hStep
  · split at hStep
    · cases hStep
    · cases hTarget : reg.endpointCap.target with
      | object epId =>
        simp only [hTarget] at hStep
        split at hStep
        · cases hStep
        · cases hStep; rfl
      | cnodeSlot => simp [hTarget] at hStep
      | replyCap => simp [hTarget] at hStep

/-- Revocation preserves objects. -/
theorem revokeService_preserves_objects
    (st st' : SystemState) (sid : ServiceId)
    (hStep : revokeService sid st = .ok ((), st')) :
    st'.objects = st.objects := by
  unfold revokeService at hStep
  split at hStep
  · cases hStep
  · simp at hStep; cases hStep; rfl

/-- Service registration preserves scheduler state. -/
theorem registerService_preserves_scheduler
    (st st' : SystemState) (reg : ServiceRegistration)
    (hStep : registerService reg st = .ok ((), st')) :
    st'.scheduler = st.scheduler := by
  unfold registerService at hStep
  split at hStep
  · cases hStep
  · split at hStep
    · cases hStep
    · cases hTarget : reg.endpointCap.target with
      | object epId =>
        simp only [hTarget] at hStep
        split at hStep
        · cases hStep
        · cases hStep; rfl
      | cnodeSlot => simp [hTarget] at hStep
      | replyCap => simp [hTarget] at hStep

/-- Revocation preserves scheduler state. -/
theorem revokeService_preserves_scheduler
    (st st' : SystemState) (sid : ServiceId)
    (hStep : revokeService sid st = .ok ((), st')) :
    st'.scheduler = st.scheduler := by
  unfold revokeService at hStep
  split at hStep
  · cases hStep
  · simp at hStep; cases hStep; rfl

end SeLe4n.Kernel
