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
    have : (default : SystemState).serviceRegistry = {} := rfl
    rw [this] at h; simp at h
  · intro sid reg h
    have : (default : SystemState).serviceRegistry = {} := rfl
    rw [this] at h; simp at h

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
    (hInv : registryInterfaceValid st) :
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
    · simp only [Std.HashMap.getElem?_insert]
      split
      · rfl
      · exact hSpec

-- ============================================================================
-- registerService
-- ============================================================================

theorem registerService_preserves_registryEndpointValid
    (st st' : SystemState) (newReg : ServiceRegistration)
    (hStep : registerService newReg st = .ok ((), st'))
    (hInv : registryEndpointValid st) :
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
        split at hStep
        · simp at hStep
        · rename_i hEpExists
          simp at hStep; subst st'
          intro sid reg hReg
          simp only [Std.HashMap.getElem?_insert] at hReg
          split at hReg
          · cases hReg
            refine ⟨epId, hTarget, ?_⟩
            rwa [← hObjEq]
          · exact hObjEq ▸ hInv sid reg hReg
      | cnodeSlot => simp [hTarget] at hStep
      | replyCap => simp [hTarget] at hStep

theorem registerService_preserves_registryInterfaceValid
    (st st' : SystemState) (newReg : ServiceRegistration)
    (hStep : registerService newReg st = .ok ((), st'))
    (hInv : registryInterfaceValid st) :
    registryInterfaceValid st' := by
  unfold registerService at hStep
  split at hStep
  · simp at hStep
  · split at hStep
    · simp at hStep
    · rename_i hHasIface
      -- hHasIface : ¬st.interfaceRegistry[newReg.iface.ifaceId]? = none
      cases hTarget : newReg.endpointCap.target with
      | object epId =>
        simp only [hTarget] at hStep
        split at hStep
        · simp at hStep
        · simp at hStep; subst st'
          -- interfaceRegistry unchanged, serviceRegistry has insert
          intro sid reg hReg
          simp only [Std.HashMap.getElem?_insert] at hReg
          split at hReg
          · cases hReg
            -- reg = newReg, interfaceRegistry unchanged in st'
            -- The goal is about {st with serviceRegistry := ...}.interfaceRegistry
            -- which definitionally equals st.interfaceRegistry
            suffices h : ∃ spec, st.interfaceRegistry[newReg.iface.ifaceId]? = some spec from h
            cases hIface : st.interfaceRegistry[newReg.iface.ifaceId]? with
            | none => exact absurd hIface hHasIface
            | some s => exact ⟨s, rfl⟩
          · exact hInv sid reg hReg
      | cnodeSlot => simp [hTarget] at hStep
      | replyCap => simp [hTarget] at hStep

-- ============================================================================
-- revokeService
-- ============================================================================

theorem revokeService_preserves_registryEndpointValid
    (st st' : SystemState) (sid : ServiceId)
    (hStep : revokeService sid st = .ok ((), st'))
    (hInv : registryEndpointValid st) :
    registryEndpointValid st' := by
  have hObjEq := revokeService_preserves_objects st st' sid hStep
  unfold revokeService at hStep
  split at hStep
  · simp at hStep
  · simp at hStep; subst st'
    intro sid' reg hReg
    -- serviceRegistry.erase sid, need sid' ≠ sid
    have hOrig : st.serviceRegistry[sid']? = some reg := by
      simp only [Std.HashMap.getElem?_erase] at hReg
      split at hReg
      · simp at hReg
      · exact hReg
    exact hObjEq ▸ hInv sid' reg hOrig

theorem revokeService_preserves_registryInterfaceValid
    (st st' : SystemState) (sid : ServiceId)
    (hStep : revokeService sid st = .ok ((), st'))
    (hInv : registryInterfaceValid st) :
    registryInterfaceValid st' := by
  unfold revokeService at hStep
  split at hStep
  · simp at hStep
  · simp at hStep; subst st'
    intro sid' reg hReg
    have hOrig : st.serviceRegistry[sid']? = some reg := by
      simp only [Std.HashMap.getElem?_erase] at hReg
      split at hReg
      · simp at hReg
      · exact hReg
    exact hInv sid' reg hOrig

-- ============================================================================
-- Composed preservation
-- ============================================================================

theorem registerInterface_preserves_registryInvariant
    (st st' : SystemState) (spec : InterfaceSpec)
    (hStep : registerInterface spec st = .ok ((), st'))
    (hInv : registryInvariant st) : registryInvariant st' :=
  ⟨registerInterface_preserves_registryEndpointValid st st' spec hStep hInv.1,
   registerInterface_preserves_registryInterfaceValid st st' spec hStep hInv.2⟩

theorem registerService_preserves_registryInvariant
    (st st' : SystemState) (newReg : ServiceRegistration)
    (hStep : registerService newReg st = .ok ((), st'))
    (hInv : registryInvariant st) : registryInvariant st' :=
  ⟨registerService_preserves_registryEndpointValid st st' newReg hStep hInv.1,
   registerService_preserves_registryInterfaceValid st st' newReg hStep hInv.2⟩

theorem revokeService_preserves_registryInvariant
    (st st' : SystemState) (sid : ServiceId)
    (hStep : revokeService sid st = .ok ((), st'))
    (hInv : registryInvariant st) : registryInvariant st' :=
  ⟨revokeService_preserves_registryEndpointValid st st' sid hStep hInv.1,
   revokeService_preserves_registryInterfaceValid st st' sid hStep hInv.2⟩

end SeLe4n.Kernel
