-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Service.Registry
import SeLe4n.Model.TableReferences

/-! # Service Registry Invariants

Since WS-ZA ZA5.9 the registry is read off the endpoints
(`SystemState.serviceRegistry`): a registration lives on the endpoint it names,
under that endpoint's id.  So two of its properties hold of every state, by
construction, and are theorems here rather than invariants a step must keep —
every registration names a live endpoint (`registryEndpointValid_holds`) and no
two name one endpoint (`registryEndpointUnique_holds`).  The third,
`registryInterfaceValid`, relates the endpoints to the interface registry, a
separate table, and stays an invariant every step keeps. -/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.RobinHood

/-- Every registered service's endpoint targets an existing kernel object. -/
def registryEndpointValid (st : SystemState) : Prop :=
  ∀ (sid : ServiceId) (reg : ServiceRegistration),
    st.serviceRegistry[sid]? = some reg →
    ∃ (epId : SeLe4n.ObjId),
      reg.endpointCap.target = CapTarget.object epId ∧
      st.objects[epId]? ≠ none

/-- **Every registration names a live endpoint, in every state**: the
registration is read off that endpoint (`SystemState.serviceRegistry_names`). -/
theorem registryEndpointValid_holds (st : SystemState) : registryEndpointValid st :=
  fun _ _ h => by
    obtain ⟨e, he, -, hc⟩ := st.serviceRegistry_names h
    refine ⟨e, he, fun hn => ?_⟩
    rw [hn] at hc; cases hc

/-- Every registered service references a known interface specification. -/
def registryInterfaceValid (st : SystemState) : Prop :=
  ∀ (sid : ServiceId) (reg : ServiceRegistration),
    st.serviceRegistry[sid]? = some reg →
    ∃ (spec : InterfaceSpec), st.interfaceRegistry[reg.iface.ifaceId]? = some spec

/-- Combined service registry invariant. -/
def registryInvariant (st : SystemState) : Prop :=
  registryEndpointValid st ∧ registryInterfaceValid st

/-- The empty state registers nothing: its store is empty. -/
theorem default_serviceRegistry_none (sid : ServiceId) :
    (default : SystemState).serviceRegistry[sid]? = none := by
  rw [SystemState.serviceRegistry_getElem?]
  have : (default : SystemState).objects[SeLe4n.ObjId.ofNat sid.toNat]? = none :=
    RHTable_get?_empty 16 (by omega)
  rw [this]

theorem default_registryInvariant :
    registryInvariant (default : SystemState) :=
  ⟨registryEndpointValid_holds _, fun sid reg h => by
    rw [default_serviceRegistry_none] at h; cases h⟩

-- ============================================================================
-- registryInterfaceValid: the one registry invariant a step keeps
-- ============================================================================

private theorem registerInterface_st'_eq
    (st : SystemState) (spec : InterfaceSpec)
    (hNoDup : st.interfaceRegistry[spec.ifaceId]? = none) :
    registerInterface spec st = .ok ((), { st with
      interfaceRegistry := st.interfaceRegistry.insert spec.ifaceId spec }) := by
  unfold registerInterface; simp [hNoDup]

theorem registerInterface_preserves_registryInterfaceValid
    (st st' : SystemState) (spec : InterfaceSpec)
    (hStep : registerInterface spec st = .ok ((), st'))
    (hInv : registryInterfaceValid st)
    (hIfaceInv : st.interfaceRegistry.invExt) :
    registryInterfaceValid st' := by
  unfold registerInterface at hStep
  split at hStep
  · simp at hStep
  · simp at hStep; subst st'
    intro sid reg hReg
    -- the object store, so the registry, unchanged
    -- interfaceRegistry = st.interfaceRegistry.insert spec.ifaceId spec
    have ⟨specOld, hSpec⟩ := hInv sid reg hReg
    refine ⟨?_, ?_⟩
    · exact if h : spec.ifaceId == reg.iface.ifaceId then spec else specOld
    · simp only [RHTable_getElem?_eq_get?]
      rw [RHTable_getElem?_insert st.interfaceRegistry spec.ifaceId spec hIfaceInv]
      split
      · rfl
      · exact hSpec

/-- A registration names a known interface (its second check), and writes it
on the endpoint it names, under that endpoint's id; every other entry is as it
was. -/
theorem registerService_preserves_registryInterfaceValid
    (st st' : SystemState) (newReg : ServiceRegistration)
    (hStep : registerService newReg st = .ok ((), st'))
    (hInv : registryInterfaceValid st)
    (hObjInv : st.objects.invExt) :
    registryInterfaceValid st' := by
  have hHasIface : st.interfaceRegistry[newReg.iface.ifaceId]? ≠ none := by
    intro hNo
    have hNoDup := (registerService_ok hStep).choose_spec.choose_spec.2.2.1
    rw [registerService_error_unknown_interface st newReg hNoDup hNo] at hStep
    cases hStep
  obtain ⟨epId, ep, hTarget, hObj, _, _, rfl⟩ := registerService_ok hStep
  intro sid reg hReg
  by_cases hk : epId = SeLe4n.ObjId.ofNat sid.toNat
  · have hs : sid = ServiceId.ofNat epId.toNat := by rw [hk]; rfl
    subst hs
    rw [SystemState.serviceRegistry_getElem?_insert_endpoint hObjInv rfl] at hReg
    simp only [Endpoint.serviceRegistered_withService, EndpointService.ofRegistration_registered,
      ↓reduceIte, Endpoint.service_withService, Option.some.injEq] at hReg
    rw [EndpointService.registrationAt_ofRegistration hTarget] at hReg
    subst hReg
    cases hIface : st.interfaceRegistry[newReg.iface.ifaceId]? with
    | none => exact absurd hIface hHasIface
    | some s => exact ⟨s, rfl⟩
  · rw [SystemState.serviceRegistry_getElem?_insert_ne hObjInv rfl hk] at hReg
    exact hInv sid reg hReg

/-- A revocation clears one endpoint's record: the registry loses that entry
and keeps every other. -/
theorem revokeService_preserves_registryInterfaceValid
    (st st' : SystemState) (sid : ServiceId)
    (hStep : revokeService sid st = .ok ((), st'))
    (hInv : registryInterfaceValid st)
    (hObjInv : st.objects.invExt) :
    registryInterfaceValid st' := by
  obtain ⟨ep, _, _, rfl⟩ := revokeService_ok hStep
  intro sid' reg hReg
  by_cases hk : SeLe4n.ObjId.ofNat sid.toNat = SeLe4n.ObjId.ofNat sid'.toNat
  · have hs : sid = sid' := by
      have := congrArg SeLe4n.ObjId.toNat hk
      exact congrArg ServiceId.ofNat this
    subst hs
    rw [show sid = ServiceId.ofNat (SeLe4n.ObjId.ofNat sid.toNat).toNat from rfl] at hReg
    rw [SystemState.serviceRegistry_getElem?_insert_endpoint hObjInv rfl] at hReg
    simp at hReg
  · rw [SystemState.serviceRegistry_getElem?_insert_ne hObjInv rfl hk] at hReg
    exact hInv sid' reg hReg

-- ============================================================================
-- Composed preservation
-- ============================================================================

theorem registerInterface_preserves_registryInvariant
    (st st' : SystemState) (spec : InterfaceSpec)
    (hStep : registerInterface spec st = .ok ((), st'))
    (hInv : registryInvariant st)
    (hIfaceInv : st.interfaceRegistry.invExt) : registryInvariant st' :=
  ⟨registryEndpointValid_holds st',
   registerInterface_preserves_registryInterfaceValid st st' spec hStep hInv.2 hIfaceInv⟩

theorem registerService_preserves_registryInvariant
    (st st' : SystemState) (newReg : ServiceRegistration)
    (hStep : registerService newReg st = .ok ((), st'))
    (hInv : registryInvariant st) (hObjInv : st.objects.invExt) : registryInvariant st' :=
  ⟨registryEndpointValid_holds st',
   registerService_preserves_registryInterfaceValid st st' newReg hStep hInv.2 hObjInv⟩

theorem revokeService_preserves_registryInvariant
    (st st' : SystemState) (sid : ServiceId)
    (hStep : revokeService sid st = .ok ((), st'))
    (hInv : registryInvariant st) (hObjInv : st.objects.invExt) : registryInvariant st' :=
  ⟨registryEndpointValid_holds st',
   revokeService_preserves_registryInterfaceValid st st' sid hStep hInv.2 hObjInv⟩

-- ============================================================================
-- AE5-B (U-20): registryEndpointUnique
-- ============================================================================

/-- AE5-B (U-20): No two distinct service registrations target the same endpoint.
    This ensures `lookupServiceByCap` returns a deterministic result regardless of
    `RHTable` iteration order. -/
def registryEndpointUnique (st : SystemState) : Prop :=
  ∀ (sid₁ sid₂ : ServiceId) (reg₁ reg₂ : ServiceRegistration)
    (epId : SeLe4n.ObjId),
    st.serviceRegistry[sid₁]? = some reg₁ →
    st.serviceRegistry[sid₂]? = some reg₂ →
    reg₁.endpointCap.target = CapTarget.object epId →
    reg₂.endpointCap.target = CapTarget.object epId →
    sid₁ = sid₂

/-- **No two registrations share an endpoint, in every state**: a registration
is read off the endpoint it names, under that endpoint's own id
(`SystemState.serviceRegistry_names`). -/
theorem registryEndpointUnique_holds (st : SystemState) : registryEndpointUnique st := by
  intro sid₁ sid₂ reg₁ reg₂ epId h₁ h₂ ht₁ ht₂
  obtain ⟨e₁, he₁, hs₁, -⟩ := st.serviceRegistry_names h₁
  obtain ⟨e₂, he₂, hs₂, -⟩ := st.serviceRegistry_names h₂
  rw [ht₁] at he₁; cases he₁
  rw [ht₂] at he₂; cases he₂
  exact hs₁.trans hs₂.symm

-- ============================================================================
-- The interrupt references across a registration and a revocation
-- ============================================================================

/-- **A registration keeps the references recorded**: it writes one endpoint
over an endpoint, and an endpoint holds no interrupt back-link. -/
theorem registerService_preserves_tableReferencesRecorded {reg : ServiceRegistration}
    {st st' : SystemState} (hStep : registerService reg st = .ok ((), st'))
    (hObjInv : st.objects.invExt) (hR : st.tableReferencesRecorded) :
    st'.tableReferencesRecorded := by
  obtain ⟨_, _, _, hObj, _, _, rfl⟩ := registerService_ok hStep
  exact SystemState.tableReferencesRecorded.of_endpoint_over_endpoint hObjInv hObj rfl rfl hR

/-- **A revocation keeps the references recorded**: it writes one endpoint
over an endpoint, and an endpoint holds no interrupt back-link. -/
theorem revokeService_preserves_tableReferencesRecorded {sid : ServiceId}
    {st st' : SystemState} (hStep : revokeService sid st = .ok ((), st'))
    (hObjInv : st.objects.invExt) (hR : st.tableReferencesRecorded) :
    st'.tableReferencesRecorded := by
  obtain ⟨_, hObj, _, rfl⟩ := revokeService_ok hStep
  exact SystemState.tableReferencesRecorded.of_endpoint_over_endpoint hObjInv hObj rfl rfl hR

-- ============================================================================
-- The O(1) lookup is the specification
-- ============================================================================

/-- The specification's fold answers only with a registration an endpoint
records, of `epId` itself. -/
private theorem lookupServiceFold_sound (st : SystemState) (epId : SeLe4n.ObjId)
    (hExt : st.objects.invExt) :
    ∀ reg, st.objects.fold (init := none) (lookupServiceStep epId) = some reg →
      ∃ ep, st.objects[epId]? = some (.endpoint ep) ∧ ep.serviceRegistered = true ∧
        reg = ep.service.registrationAt epId := by
  refine RHTable.fold_preserves_of_lookup st.objects none (lookupServiceStep epId)
    (fun acc => ∀ reg, acc = some reg →
      ∃ ep, st.objects[epId]? = some (.endpoint ep) ∧ ep.serviceRegistered = true ∧
        reg = ep.service.registrationAt epId)
    hExt (fun _ h => by cases h) ?_
  intro acc k v hk hAcc reg hEq
  cases acc with
  | some r => exact hAcc reg hEq
  | none =>
    simp only [lookupServiceStep] at hEq
    split at hEq
    · rename_i ep
      split at hEq
      · rename_i hC
        simp only [EndpointService.registrationAt_target] at hEq
        by_cases hId : k = epId
        · subst hId
          simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hEq
          exact ⟨ep, hk, hC, hEq.symm⟩
        · simp [hId] at hEq
      · cases hEq
    · cases hEq

/-- The specification's fold answers whenever the endpoint `epId` records a
registration. -/
private theorem lookupServiceFold_complete (st : SystemState) (epId : SeLe4n.ObjId)
    (hExt : st.objects.invExt) (ep : Endpoint) (hObj : st.objects[epId]? = some (.endpoint ep))
    (hC : ep.serviceRegistered = true) :
    st.objects.fold (init := none) (lookupServiceStep epId) ≠ none := by
  have hQ := RHTable.fold_pointwise st.objects none (lookupServiceStep epId)
    (fun _ _ => True) (fun k acc => k = epId → acc ≠ none) hExt (fun _ => trivial)
    (fun _ _ _ _ _ _ => trivial) ?_ ?_ epId (.endpoint ep) hObj
  · exact hQ rfl
  · intro acc k v hk _ hKs
    subst hKs
    have hv : v = .endpoint ep := by
      have h1 : st.objects[k]? = some v := hk
      rw [hObj] at h1; exact (Option.some.inj h1).symm
    subst hv
    cases acc with
    | some r => simp [lookupServiceStep]
    | none => simp [lookupServiceStep, hC]
  · intro acc k _ _ _ hAcc hKs
    cases acc with
    | some r => simp [lookupServiceStep]
    | none => exact absurd rfl (hAcc hKs)

/-- **The O(1) service lookup is the specification wherever the object store
is well formed.**  The fold over the endpoints' records finds a registration
naming `epId` only on `epId` itself, a registration's capability naming the
endpoint that records it, so reading that one endpoint's record finds what the
fold finds — and finds nothing exactly when the fold finds nothing. -/
theorem lookupServiceByRecordedRegistration_eq_lookupServiceByCap {st : SystemState}
    (hExt : st.objects.invExt) (epId : SeLe4n.ObjId) :
    lookupServiceByRecordedRegistration epId st = lookupServiceByCap epId st := by
  have hSpec : lookupServiceByCap epId st =
      (match st.objects.fold (init := none) (lookupServiceStep epId) with
        | some reg => .ok (reg, st)
        | none => .error .objectNotFound) := rfl
  rw [hSpec]
  unfold lookupServiceByRecordedRegistration
  simp only [SystemState.getObject?]
  cases hF : st.objects.fold (init := none) (lookupServiceStep epId) with
  | some reg =>
    obtain ⟨ep, hObj, hC, rfl⟩ := lookupServiceFold_sound st epId hExt reg hF
    simp only [hObj, hC]
  | none =>
    cases hObj : st.objects[epId]? with
    | none => rfl
    | some o =>
      cases o with
      | endpoint ep =>
        simp only []
        cases hc : ep.serviceRegistered with
        | false => rfl
        | true => exact absurd hF (lookupServiceFold_complete st epId hExt ep hObj hc)
      | _ => rfl

end SeLe4n.Kernel
