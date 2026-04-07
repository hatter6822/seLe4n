/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Service.Registry

/-! # Service Registry Invariants -/

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

/-- Every registered service references a known interface specification. -/
def registryInterfaceValid (st : SystemState) : Prop :=
  ∀ (sid : ServiceId) (reg : ServiceRegistration),
    st.serviceRegistry[sid]? = some reg →
    ∃ (spec : InterfaceSpec), st.interfaceRegistry[reg.iface.ifaceId]? = some spec

/-- Combined service registry invariant. -/
def registryInvariant (st : SystemState) : Prop :=
  registryEndpointValid st ∧ registryInterfaceValid st

theorem default_registryInvariant :
    registryInvariant (default : SystemState) := by
  constructor
  · intro sid reg h
    simp only [RHTable_getElem?_eq_get?] at h
    have : (default : SystemState).serviceRegistry.get? sid = none :=
      RHTable.getElem?_empty 16 (by omega) sid
    simp [this] at h
  · intro sid reg h
    simp only [RHTable_getElem?_eq_get?] at h
    have : (default : SystemState).serviceRegistry.get? sid = none :=
      RHTable.getElem?_empty 16 (by omega) sid
    simp [this] at h

-- ============================================================================
-- registerInterface
-- ============================================================================

private theorem registerInterface_st'_eq
    (st : SystemState) (spec : InterfaceSpec)
    (hNoDup : st.interfaceRegistry[spec.ifaceId]? = none) :
    registerInterface spec st = .ok ((), { st with
      interfaceRegistry := st.interfaceRegistry.insert spec.ifaceId spec }) := by
  unfold registerInterface; simp [hNoDup]

theorem registerInterface_preserves_registryEndpointValid
    (st st' : SystemState) (spec : InterfaceSpec)
    (hStep : registerInterface spec st = .ok ((), st'))
    (hInv : registryEndpointValid st) :
    registryEndpointValid st' := by
  unfold registerInterface at hStep
  split at hStep
  · simp at hStep
  · simp at hStep; subst st'
    -- serviceRegistry and objects unchanged
    exact hInv

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
    -- serviceRegistry unchanged, so reg was in original
    -- interfaceRegistry = st.interfaceRegistry.insert spec.ifaceId spec
    have ⟨specOld, hSpec⟩ := hInv sid reg hReg
    refine ⟨?_, ?_⟩
    · exact if h : spec.ifaceId == reg.iface.ifaceId then spec else specOld
    · simp only [RHTable_getElem?_eq_get?]
      rw [RHTable_getElem?_insert st.interfaceRegistry spec.ifaceId spec hIfaceInv]
      split
      · rfl
      · exact hSpec

-- ============================================================================
-- registerService
-- ============================================================================

theorem registerService_preserves_registryEndpointValid
    (st st' : SystemState) (newReg : ServiceRegistration)
    (hStep : registerService newReg st = .ok ((), st'))
    (hInv : registryEndpointValid st)
    (hSvcInv : st.serviceRegistry.invExt) :
    registryEndpointValid st' := by
  have hObjEq := registerService_preserves_objects st st' newReg hStep
  unfold registerService at hStep
  split at hStep
  · simp at hStep
  · split at hStep
    · simp at hStep
    · cases hTarget : newReg.endpointCap.target with
      | object epId =>
        simp only [hTarget] at hStep
        cases hObj : st.objects[epId]? with
        | none => simp [hObj] at hStep
        | some obj =>
          cases obj <;> simp [hObj] at hStep
          case endpoint ep =>
            split at hStep
            · cases hStep
            · split at hStep
              · cases hStep
              · simp at hStep; subst st'
                intro sid reg hReg
                simp only [RHTable_getElem?_eq_get?] at hReg
                rw [RHTable_getElem?_insert st.serviceRegistry newReg.sid newReg hSvcInv] at hReg
                split at hReg
                · cases hReg
                  refine ⟨epId, hTarget, ?_⟩
                  rw [← hObjEq, hObj]; simp
                · exact hObjEq ▸ hInv sid reg (by simp only [RHTable_getElem?_eq_get?]; exact hReg)
      | cnodeSlot => simp [hTarget] at hStep
      | replyCap => simp [hTarget] at hStep

theorem registerService_preserves_registryInterfaceValid
    (st st' : SystemState) (newReg : ServiceRegistration)
    (hStep : registerService newReg st = .ok ((), st'))
    (hInv : registryInterfaceValid st)
    (hSvcInv : st.serviceRegistry.invExt) :
    registryInterfaceValid st' := by
  unfold registerService at hStep
  split at hStep
  · simp at hStep
  · split at hStep
    · simp at hStep
    · rename_i hHasIface
      cases hTarget : newReg.endpointCap.target with
      | object epId =>
        simp only [hTarget] at hStep
        cases hObj : st.objects[epId]? with
        | none => simp [hObj] at hStep
        | some obj =>
          cases obj <;> simp [hObj] at hStep
          case endpoint ep =>
            split at hStep
            · cases hStep
            · split at hStep
              · cases hStep
              · simp at hStep; subst st'
                intro sid reg hReg
                simp only [RHTable_getElem?_eq_get?] at hReg
                rw [RHTable_getElem?_insert st.serviceRegistry newReg.sid newReg hSvcInv] at hReg
                split at hReg
                · cases hReg
                  suffices h : ∃ spec, st.interfaceRegistry[newReg.iface.ifaceId]? = some spec from h
                  cases hIface : st.interfaceRegistry[newReg.iface.ifaceId]? with
                  | none => exact absurd hIface hHasIface
                  | some s => exact ⟨s, rfl⟩
                · exact hInv sid reg (by simp only [RHTable_getElem?_eq_get?]; exact hReg)
      | cnodeSlot => simp [hTarget] at hStep
      | replyCap => simp [hTarget] at hStep

-- ============================================================================
-- revokeService
-- ============================================================================

theorem revokeService_preserves_registryEndpointValid
    (st st' : SystemState) (sid : ServiceId)
    (hStep : revokeService sid st = .ok ((), st'))
    (hInv : registryEndpointValid st)
    (hSvcK : st.serviceRegistry.invExtK) :
    registryEndpointValid st' := by
  have hObjEq := revokeService_preserves_objects st st' sid hStep
  have hSvcRegEq := revokeService_success_removes st st' sid hSvcK.1 hStep
  intro sid' reg hReg
  -- The post-state serviceRegistry = (erased).serviceRegistry (removeDependenciesOf preserves it)
  -- Need to recover that reg was in st.serviceRegistry
  unfold revokeService at hStep
  split at hStep
  · simp at hStep
  · simp at hStep; cases hStep
    -- st' = removeDependenciesOf {st with serviceRegistry := ...erase...} sid
    -- st'.serviceRegistry = {st with serviceRegistry := ...erase...}.serviceRegistry (by removeDependenciesOf_serviceRegistry_eq)
    rw [removeDependenciesOf_serviceRegistry_eq] at hReg
    have hOrig : st.serviceRegistry[sid']? = some reg := by
      simp only [RHTable_getElem?_eq_get?] at hReg
      rw [RHTable_getElem?_erase_K st.serviceRegistry sid hSvcK] at hReg
      split at hReg
      · simp at hReg
      · simp only [RHTable_getElem?_eq_get?]; exact hReg
    exact hObjEq ▸ hInv sid' reg hOrig

theorem revokeService_preserves_registryInterfaceValid
    (st st' : SystemState) (sid : ServiceId)
    (hStep : revokeService sid st = .ok ((), st'))
    (hInv : registryInterfaceValid st)
    (hSvcK : st.serviceRegistry.invExtK) :
    registryInterfaceValid st' := by
  unfold revokeService at hStep
  split at hStep
  · simp at hStep
  · simp at hStep; cases hStep
    intro sid' reg hReg
    rw [removeDependenciesOf_serviceRegistry_eq] at hReg
    have hOrig : st.serviceRegistry[sid']? = some reg := by
      simp only [RHTable_getElem?_eq_get?] at hReg
      rw [RHTable_getElem?_erase_K st.serviceRegistry sid hSvcK] at hReg
      split at hReg
      · simp at hReg
      · simp only [RHTable_getElem?_eq_get?]; exact hReg
    exact hInv sid' reg hOrig

-- ============================================================================
-- Composed preservation
-- ============================================================================

theorem registerInterface_preserves_registryInvariant
    (st st' : SystemState) (spec : InterfaceSpec)
    (hStep : registerInterface spec st = .ok ((), st'))
    (hInv : registryInvariant st)
    (hIfaceInv : st.interfaceRegistry.invExt) : registryInvariant st' :=
  ⟨registerInterface_preserves_registryEndpointValid st st' spec hStep hInv.1,
   registerInterface_preserves_registryInterfaceValid st st' spec hStep hInv.2 hIfaceInv⟩

theorem registerService_preserves_registryInvariant
    (st st' : SystemState) (newReg : ServiceRegistration)
    (hStep : registerService newReg st = .ok ((), st'))
    (hInv : registryInvariant st)
    (hSvcInv : st.serviceRegistry.invExt) : registryInvariant st' :=
  ⟨registerService_preserves_registryEndpointValid st st' newReg hStep hInv.1 hSvcInv,
   registerService_preserves_registryInterfaceValid st st' newReg hStep hInv.2 hSvcInv⟩

theorem revokeService_preserves_registryInvariant
    (st st' : SystemState) (sid : ServiceId)
    (hStep : revokeService sid st = .ok ((), st'))
    (hInv : registryInvariant st)
    (hSvcK : st.serviceRegistry.invExtK) : registryInvariant st' :=
  ⟨revokeService_preserves_registryEndpointValid st st' sid hStep hInv.1 hSvcK,
   revokeService_preserves_registryInterfaceValid st st' sid hStep hInv.2 hSvcK⟩

-- ============================================================================
-- T5-G (L-NEW-2): cleanupEndpointServiceRegistrations preservation
-- ============================================================================

/-- T5-G (L-NEW-2): After filtering service registrations by endpoint ID,
    remaining registrations still have valid endpoint references.

    The proof uses `RHTable.filter_get_subset` to show that any registration
    surviving the filter was present in the original state, and then
    `cleanupEndpointServiceRegistrations_objects_eq` to show the backing
    object still exists. -/
theorem cleanupEndpointServiceRegistrations_preserves_registryEndpointValid
    (st : SystemState) (epId : SeLe4n.ObjId)
    (hInv : registryEndpointValid st)
    (hSvcRegInv : st.serviceRegistry.invExt) :
    registryEndpointValid (cleanupEndpointServiceRegistrations st epId) := by
  intro sid reg hLookup
  have hObjEq := cleanupEndpointServiceRegistrations_objects_eq st epId
  -- Step 1: The result's serviceRegistry is the filtered original
  -- (foldl removeDependenciesOf preserves serviceRegistry)
  have hSvcRegResult : (cleanupEndpointServiceRegistrations st epId).serviceRegistry =
      (st.serviceRegistry.filter fun _sid reg' =>
        match reg'.endpointCap.target with
        | .object id => !(id == epId)
        | _ => true) := by
    unfold cleanupEndpointServiceRegistrations
    exact foldl_removeDependenciesOf_serviceRegistry_eq _ _
  -- Step 2: Rewrite lookup using the serviceRegistry equality
  rw [RHTable_getElem?_eq_get?] at hLookup
  rw [hSvcRegResult] at hLookup
  -- Step 3: Any entry in the filtered table was in the original
  have hOrig := RHTable.filter_get_subset st.serviceRegistry _ sid reg hSvcRegInv hLookup
  rw [← RHTable_getElem?_eq_get?] at hOrig
  -- Step 4: Original invariant gives us a valid endpoint
  rcases hInv sid reg hOrig with ⟨epId', hTarget, hExists⟩
  exact ⟨epId', hTarget, hObjEq ▸ hExists⟩

/-- U4-I (U-M06): After filtering service registrations by endpoint ID,
    remaining registrations still reference known interface specifications.

    The proof follows the same structure as `_preserves_registryEndpointValid`:
    any registration surviving the filter was in the original state, and the
    `interfaceRegistry` is unchanged by `cleanupEndpointServiceRegistrations`,
    so the original invariant applies directly. -/
theorem cleanupEndpointServiceRegistrations_preserves_registryInterfaceValid
    (st : SystemState) (epId : SeLe4n.ObjId)
    (hInv : registryInterfaceValid st)
    (hSvcRegInv : st.serviceRegistry.invExt) :
    registryInterfaceValid (cleanupEndpointServiceRegistrations st epId) := by
  intro sid reg hLookup
  have hIfaceEq := cleanupEndpointServiceRegistrations_interfaceRegistry_eq st epId
  -- Step 1: The result's serviceRegistry is the filtered original
  have hSvcRegResult : (cleanupEndpointServiceRegistrations st epId).serviceRegistry =
      (st.serviceRegistry.filter fun _sid reg' =>
        match reg'.endpointCap.target with
        | .object id => !(id == epId)
        | _ => true) := by
    unfold cleanupEndpointServiceRegistrations
    exact foldl_removeDependenciesOf_serviceRegistry_eq _ _
  -- Step 2: Rewrite lookup using the serviceRegistry equality
  rw [RHTable_getElem?_eq_get?] at hLookup
  rw [hSvcRegResult] at hLookup
  -- Step 3: Any entry in the filtered table was in the original
  have hOrig := RHTable.filter_get_subset st.serviceRegistry _ sid reg hSvcRegInv hLookup
  rw [← RHTable_getElem?_eq_get?] at hOrig
  -- Step 4: Original invariant gives us a valid interface
  rcases hInv sid reg hOrig with ⟨spec, hSpec⟩
  exact ⟨spec, hIfaceEq ▸ hSpec⟩

/-- U4-I (U-M06): cleanupEndpointServiceRegistrations preserves the full registryInvariant. -/
theorem cleanupEndpointServiceRegistrations_preserves_registryInvariant
    (st : SystemState) (epId : SeLe4n.ObjId)
    (hInv : registryInvariant st)
    (hSvcRegInv : st.serviceRegistry.invExt) :
    registryInvariant (cleanupEndpointServiceRegistrations st epId) :=
  ⟨cleanupEndpointServiceRegistrations_preserves_registryEndpointValid st epId hInv.1 hSvcRegInv,
   cleanupEndpointServiceRegistrations_preserves_registryInterfaceValid st epId hInv.2 hSvcRegInv⟩

-- ============================================================================
-- AE5-B (U-20): registryEndpointUnique invariant
-- ============================================================================

/-- AE5-B (U-20): No two distinct service registrations target the same endpoint.
    This ensures `lookupServiceByCap` returns a deterministic result regardless of
    `RHTable` iteration order. The runtime check in `registerService` (via
    `hasEndpointRegistered`) enforces this at registration time. -/
def registryEndpointUnique (st : SystemState) : Prop :=
  ∀ (sid₁ sid₂ : ServiceId) (reg₁ reg₂ : ServiceRegistration)
    (epId : SeLe4n.ObjId),
    st.serviceRegistry[sid₁]? = some reg₁ →
    st.serviceRegistry[sid₂]? = some reg₂ →
    reg₁.endpointCap.target = CapTarget.object epId →
    reg₂.endpointCap.target = CapTarget.object epId →
    sid₁ = sid₂

/-- AE5-B: The default (empty) state satisfies `registryEndpointUnique` vacuously. -/
theorem default_registryEndpointUnique :
    registryEndpointUnique (default : SystemState) := by
  intro sid₁ sid₂ reg₁ reg₂ epId h₁
  simp only [RHTable_getElem?_eq_get?] at h₁
  have : (default : SystemState).serviceRegistry.get? sid₁ = none :=
    RHTable.getElem?_empty 16 (by omega) sid₁
  simp [this] at h₁

/-- AE5-B: `registerInterface` preserves `registryEndpointUnique` (serviceRegistry unchanged). -/
theorem registerInterface_preserves_registryEndpointUnique
    (st st' : SystemState) (spec : InterfaceSpec)
    (hStep : registerInterface spec st = .ok ((), st'))
    (hInv : registryEndpointUnique st) :
    registryEndpointUnique st' := by
  unfold registerInterface at hStep
  split at hStep
  · simp at hStep
  · simp at hStep; subst st'
    -- serviceRegistry unchanged
    exact hInv

/-- AE5-B: `revokeService` preserves `registryEndpointUnique`.
    Removing a registration from the registry preserves uniqueness — if
    any two remaining registrations share an endpoint, they shared it before
    revocation, contradicting the pre-condition. -/
theorem revokeService_preserves_registryEndpointUnique
    (st st' : SystemState) (sid : ServiceId)
    (hStep : revokeService sid st = .ok ((), st'))
    (hInv : registryEndpointUnique st)
    (hSvcK : st.serviceRegistry.invExtK) :
    registryEndpointUnique st' := by
  unfold revokeService at hStep
  split at hStep
  · simp at hStep
  · simp at hStep; cases hStep
    intro sid₁ sid₂ reg₁ reg₂ epId h₁ h₂ ht₁ ht₂
    rw [removeDependenciesOf_serviceRegistry_eq] at h₁ h₂
    simp only [RHTable_getElem?_eq_get?] at h₁ h₂
    rw [RHTable_getElem?_erase_K st.serviceRegistry sid hSvcK] at h₁ h₂
    split at h₁
    · simp at h₁
    · split at h₂
      · simp at h₂
      · exact hInv sid₁ sid₂ reg₁ reg₂ epId
          (by simp only [RHTable_getElem?_eq_get?]; exact h₁)
          (by simp only [RHTable_getElem?_eq_get?]; exact h₂) ht₁ ht₂

/-- AE5-B: `cleanupEndpointServiceRegistrations` preserves `registryEndpointUnique`.
    Filtering out registrations preserves the uniqueness property — surviving
    registrations were in the original state and satisfied uniqueness there. -/
theorem cleanupEndpointServiceRegistrations_preserves_registryEndpointUnique
    (st : SystemState) (epId : SeLe4n.ObjId)
    (hInv : registryEndpointUnique st)
    (hSvcRegInv : st.serviceRegistry.invExt) :
    registryEndpointUnique (cleanupEndpointServiceRegistrations st epId) := by
  intro sid₁ sid₂ reg₁ reg₂ epId' h₁ h₂ ht₁ ht₂
  have hSvcRegResult : (cleanupEndpointServiceRegistrations st epId).serviceRegistry =
      (st.serviceRegistry.filter fun _sid reg' =>
        match reg'.endpointCap.target with
        | .object id => !(id == epId)
        | _ => true) := by
    unfold cleanupEndpointServiceRegistrations
    exact foldl_removeDependenciesOf_serviceRegistry_eq _ _
  rw [RHTable_getElem?_eq_get?] at h₁; rw [hSvcRegResult] at h₁
  rw [RHTable_getElem?_eq_get?] at h₂; rw [hSvcRegResult] at h₂
  have hOrig₁ := RHTable.filter_get_subset st.serviceRegistry _ sid₁ reg₁ hSvcRegInv h₁
  have hOrig₂ := RHTable.filter_get_subset st.serviceRegistry _ sid₂ reg₂ hSvcRegInv h₂
  rw [← RHTable_getElem?_eq_get?] at hOrig₁
  rw [← RHTable_getElem?_eq_get?] at hOrig₂
  exact hInv sid₁ sid₂ reg₁ reg₂ epId' hOrig₁ hOrig₂ ht₁ ht₂

end SeLe4n.Kernel
