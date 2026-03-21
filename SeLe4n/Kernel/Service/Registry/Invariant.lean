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
              subst st'
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
      split at hStep
      · simp at hStep
      · cases hTarget : newReg.endpointCap.target with
        | object epId =>
          simp only [hTarget] at hStep
          cases hObj : st.objects[epId]? with
          | none => simp [hObj] at hStep
          | some obj =>
            cases obj <;> simp [hObj] at hStep
            case endpoint ep =>
              subst st'
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
    (hSvcInv : st.serviceRegistry.invExt)
    (hSize : st.serviceRegistry.size < st.serviceRegistry.capacity) :
    registryEndpointValid st' := by
  have hObjEq := revokeService_preserves_objects st st' sid hStep
  unfold revokeService at hStep
  split at hStep
  · simp at hStep
  · simp at hStep; subst st'
    intro sid' reg hReg
    -- serviceRegistry.erase sid, need sid' ≠ sid
    have hOrig : st.serviceRegistry[sid']? = some reg := by
      simp only [RHTable_getElem?_eq_get?] at hReg
      rw [RHTable_getElem?_erase st.serviceRegistry sid hSvcInv hSize] at hReg
      split at hReg
      · simp at hReg
      · simp only [RHTable_getElem?_eq_get?]; exact hReg
    exact hObjEq ▸ hInv sid' reg hOrig

theorem revokeService_preserves_registryInterfaceValid
    (st st' : SystemState) (sid : ServiceId)
    (hStep : revokeService sid st = .ok ((), st'))
    (hInv : registryInterfaceValid st)
    (hSvcInv : st.serviceRegistry.invExt)
    (hSize : st.serviceRegistry.size < st.serviceRegistry.capacity) :
    registryInterfaceValid st' := by
  unfold revokeService at hStep
  split at hStep
  · simp at hStep
  · simp at hStep; subst st'
    intro sid' reg hReg
    have hOrig : st.serviceRegistry[sid']? = some reg := by
      simp only [RHTable_getElem?_eq_get?] at hReg
      rw [RHTable_getElem?_erase st.serviceRegistry sid hSvcInv hSize] at hReg
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
    (hSvcInv : st.serviceRegistry.invExt)
    (hSize : st.serviceRegistry.size < st.serviceRegistry.capacity) : registryInvariant st' :=
  ⟨revokeService_preserves_registryEndpointValid st st' sid hStep hInv.1 hSvcInv hSize,
   revokeService_preserves_registryInterfaceValid st st' sid hStep hInv.2 hSvcInv hSize⟩

end SeLe4n.Kernel
