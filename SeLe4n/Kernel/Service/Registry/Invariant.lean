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
    (hSvcInv : st.serviceRegistry.invExt)
    (hObjInv : st.objects.invExt) :
    registryEndpointValid st' := by
  have hPres := registerService_objects_none_iff hStep hObjInv
  obtain ⟨epId, ep, hTarget, hObj, _, _, hEq⟩ := registerService_ok hStep
  intro sid reg hReg
  have hReg' : (st.serviceRegistry.insert newReg.sid newReg).get? sid = some reg := by
    rw [hEq] at hReg; exact hReg
  rw [RHTable_getElem?_insert st.serviceRegistry newReg.sid newReg hSvcInv] at hReg'
  split at hReg'
  · cases hReg'
    exact ⟨epId, hTarget, fun h => by rw [(hPres epId).mp h] at hObj; cases hObj⟩
  · obtain ⟨e, he, hn⟩ := hInv sid reg (by simp only [RHTable_getElem?_eq_get?]; exact hReg')
    exact ⟨e, he, fun h => hn ((hPres e).mp h)⟩

theorem registerService_preserves_registryInterfaceValid
    (st st' : SystemState) (newReg : ServiceRegistration)
    (hStep : registerService newReg st = .ok ((), st'))
    (hInv : registryInterfaceValid st)
    (hSvcInv : st.serviceRegistry.invExt) :
    registryInterfaceValid st' := by
  have hHasIface : st.interfaceRegistry[newReg.iface.ifaceId]? ≠ none := by
    intro hNo
    have hNoDup := (registerService_ok hStep).choose_spec.choose_spec.2.2.1
    rw [registerService_error_unknown_interface st newReg hNoDup hNo] at hStep
    cases hStep
  obtain ⟨epId, ep, hTarget, hObj, _, _, hEq⟩ := registerService_ok hStep
  subst hEq
  intro sid reg hReg
  simp only [RHTable_getElem?_eq_get?] at hReg
  rw [RHTable_getElem?_insert st.serviceRegistry newReg.sid newReg hSvcInv] at hReg
  split at hReg
  · cases hReg
    cases hIface : st.interfaceRegistry[newReg.iface.ifaceId]? with
    | none => exact absurd hIface hHasIface
    | some s => exact ⟨s, rfl⟩
  · exact hInv sid reg (by simp only [RHTable_getElem?_eq_get?]; exact hReg)

-- ============================================================================
-- revokeService
-- ============================================================================

theorem revokeService_preserves_registryEndpointValid
    (st st' : SystemState) (sid : ServiceId)
    (hStep : revokeService sid st = .ok ((), st'))
    (hInv : registryEndpointValid st)
    (hSvcK : st.serviceRegistry.invExtK)
    (hObjInv : st.objects.invExt) :
    registryEndpointValid st' := by
  have hPres := revokeService_objects_none_iff hStep hObjInv
  intro sid' reg hReg
  rw [(revokeService_serviceRegistry hStep).1] at hReg
  have hOrig : st.serviceRegistry[sid']? = some reg := by
    simp only [RHTable_getElem?_eq_get?] at hReg
    rw [RHTable_getElem?_erase_K st.serviceRegistry sid hSvcK] at hReg
    split at hReg
    · simp at hReg
    · simp only [RHTable_getElem?_eq_get?]; exact hReg
  obtain ⟨e, he, hn⟩ := hInv sid' reg hOrig
  exact ⟨e, he, fun h => hn ((hPres e).mp h)⟩

theorem revokeService_preserves_registryInterfaceValid
    (st st' : SystemState) (sid : ServiceId)
    (hStep : revokeService sid st = .ok ((), st'))
    (hInv : registryInterfaceValid st)
    (hSvcK : st.serviceRegistry.invExtK) :
    registryInterfaceValid st' := by
  obtain ⟨hR, hI⟩ := revokeService_serviceRegistry hStep
  intro sid' reg hReg
  rw [hR] at hReg
  have hOrig : st.serviceRegistry[sid']? = some reg := by
    simp only [RHTable_getElem?_eq_get?] at hReg
    rw [RHTable_getElem?_erase_K st.serviceRegistry sid hSvcK] at hReg
    split at hReg
    · simp at hReg
    · simp only [RHTable_getElem?_eq_get?]; exact hReg
  rw [hI]
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
    (hSvcInv : st.serviceRegistry.invExt) (hObjInv : st.objects.invExt) : registryInvariant st' :=
  ⟨registerService_preserves_registryEndpointValid st st' newReg hStep hInv.1 hSvcInv hObjInv,
   registerService_preserves_registryInterfaceValid st st' newReg hStep hInv.2 hSvcInv⟩

theorem revokeService_preserves_registryInvariant
    (st st' : SystemState) (sid : ServiceId)
    (hStep : revokeService sid st = .ok ((), st'))
    (hInv : registryInvariant st)
    (hSvcK : st.serviceRegistry.invExtK) (hObjInv : st.objects.invExt) : registryInvariant st' :=
  ⟨revokeService_preserves_registryEndpointValid st st' sid hStep hInv.1 hSvcK hObjInv,
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
    `RHTable` iteration order. The runtime check in `registerService` (the
    endpoint's own registration code, `Endpoint.serviceCode`) enforces this at
    registration time, and `SystemState.tableReferencesRecorded` implies it
    (`registryEndpointUnique_of_tableReferencesRecorded`). -/
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

/-- AE5-B: `registerService` preserves `registryEndpointUnique`.
    The duplicate check reads the endpoint's own record of its registration
    (`Endpoint.serviceCode`), which `SystemState.tableReferencesRecorded` holds
    equal to the registry's: a clear record means no registration targets the
    endpoint, so the new entry is the only one that does. -/
theorem registerService_preserves_registryEndpointUnique
    (st st' : SystemState) (newReg : ServiceRegistration)
    (hStep : registerService newReg st = .ok ((), st'))
    (hInv : registryEndpointUnique st)
    (hSvcInv : st.serviceRegistry.invExt)
    (hR : st.tableReferencesRecorded) :
    registryEndpointUnique st' := by
  obtain ⟨regEpId, ep, hTarget, hObj, _, hClear, hEq⟩ := registerService_ok hStep
  have hNone := hR.notTargeted hObj hClear
  subst hEq
  intro sid₁ sid₂ reg₁ reg₂ epId h₁ h₂ ht₁ ht₂
  simp only [RHTable_getElem?_eq_get?] at h₁ h₂
  rw [RHTable_getElem?_insert st.serviceRegistry newReg.sid newReg hSvcInv] at h₁ h₂
  by_cases hSid₁ : (newReg.sid == sid₁) = true
  · simp only [hSid₁, ite_true, Option.some.injEq] at h₁; subst reg₁
    by_cases hSid₂ : (newReg.sid == sid₂) = true
    · exact (eq_of_beq hSid₁).symm.trans (eq_of_beq hSid₂)
    · rw [Bool.eq_false_iff.mpr hSid₂] at h₂; simp only [Bool.false_eq_true, ite_false] at h₂
      rw [hTarget] at ht₁
      have := CapTarget.object.inj ht₁; subst epId
      exact absurd ht₂ (hNone sid₂ reg₂ (by simp only [RHTable_getElem?_eq_get?]; exact h₂))
  · rw [Bool.eq_false_iff.mpr hSid₁] at h₁; simp only [Bool.false_eq_true, ite_false] at h₁
    by_cases hSid₂ : (newReg.sid == sid₂) = true
    · simp only [hSid₂, ite_true, Option.some.injEq] at h₂; subst reg₂
      rw [hTarget] at ht₂
      have := CapTarget.object.inj ht₂; subst epId
      exact absurd ht₁ (hNone sid₁ reg₁ (by simp only [RHTable_getElem?_eq_get?]; exact h₁))
    · rw [Bool.eq_false_iff.mpr hSid₂] at h₂; simp only [Bool.false_eq_true, ite_false] at h₂
      exact hInv sid₁ sid₂ reg₁ reg₂ epId
        (by simp only [RHTable_getElem?_eq_get?]; exact h₁)
        (by simp only [RHTable_getElem?_eq_get?]; exact h₂) ht₁ ht₂

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
  intro sid₁ sid₂ reg₁ reg₂ epId h₁ h₂ ht₁ ht₂
  rw [(revokeService_serviceRegistry hStep).1] at h₁ h₂
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

-- ============================================================================
-- WS-ZA ZA5.4 part 30: the registrations recorded on their endpoints
-- ============================================================================

private theorem getElem?_insert_ite {α β : Type} [BEq α] [Hashable α] [LawfulBEq α]
    [DecidableEq α] (t : RHTable α β) (k j : α) (v : β) (h : t.invExt) :
    (t.insert k v)[j]? = if k = j then some v else t[j]? := by
  by_cases hk : k = j
  · subst hk; simp only [RHTable_getElem?_eq_get?]; rw [if_pos trivial]
    exact RHTable.getElem?_insert_self t k v h
  · simp only [RHTable_getElem?_eq_get?, if_neg hk]
    exact RHTable.getElem?_insert_ne t k j v (fun hb => hk (eq_of_beq hb)) h

private theorem getElem?_erase_ite {α β : Type} [BEq α] [Hashable α] [LawfulBEq α]
    [DecidableEq α] (t : RHTable α β) (k j : α) (h : t.invExtK) :
    (t.erase k)[j]? = if k = j then none else t[j]? := by
  by_cases hk : k = j
  · subst hk; simp only [RHTable_getElem?_eq_get?]; rw [if_pos trivial]
    exact RHTable.getElem?_erase_self t k h.1
  · simp only [RHTable_getElem?_eq_get?, if_neg hk]
    exact RHTable.getElem?_erase_ne_K t k j (fun hb => hk (eq_of_beq hb)) h

private theorem serviceId_eq_of_val {a b : ServiceId} (h : a.val + 1 = b.val + 1) : a = b := by
  cases a; cases b; simp only [Nat.add_right_cancel_iff] at h; subst h; rfl

/-- The revocation's endpoint write, when the endpoint records the service. -/
theorem clearEndpointServiceCode_of_recorded (st : SystemState) (cap : Capability)
    (sid : ServiceId) {e : SeLe4n.ObjId} {ep : Endpoint} (ht : cap.target = .object e)
    (hE : st.objects[e]? = some (.endpoint ep)) (hc : ep.serviceCode = sid.val + 1) :
    clearEndpointServiceCode st cap sid =
      { st with objects := st.objects.insert e (.endpoint { ep with serviceCode := 0 }) } := by
  unfold clearEndpointServiceCode
  simp only [ht]
  split
  · rename_i ep' hg
    have hg' : st.objects[e]? = some (.endpoint ep') := hg
    rw [hE] at hg'; cases hg'
    rw [if_pos hc]; rfl
  · rename_i hne
    exact absurd hE (hne ep)

/-- An empty service graph has no dependency to remove. -/
theorem removeDependenciesOf_of_slotsEmpty (st : SystemState) (sid : ServiceId)
    (h : st.services.slotsEmpty) : removeDependenciesOf st sid = st := by
  unfold removeDependenciesOf
  simp only [RHTable.erase_of_slotsEmpty h, RHTable.fold_of_slotsEmpty h]

/-- **A registration keeps the references recorded**: it records itself on the
endpoint it names, which recorded none (the duplicate check). -/
theorem registerService_preserves_tableReferencesRecorded {reg : ServiceRegistration}
    {st st' : SystemState} (hStep : registerService reg st = .ok ((), st'))
    (hObjInv : st.objects.invExt) (hR : st.tableReferencesRecorded) :
    st'.tableReferencesRecorded := by
  obtain ⟨epId, ep, hTarget, hObj, hFree, hClear, rfl⟩ := registerService_ok hStep
  have hO := fun j => getElem?_insert_ite st.objects epId j
    (.endpoint { ep with serviceCode := reg.sid.val + 1 }) hObjInv
  have hS := fun j => getElem?_insert_ite st.serviceRegistry reg.sid j reg hR.registryInvExtK.1
  refine ⟨RHTable.insert_preserves_invExtK _ _ _ hR.registryInvExtK, ?_, ?_, ?_, ?_,
    hR.servicesEmpty⟩
  · intro sid r h
    simp only at h ⊢
    rw [hS] at h
    by_cases hs : reg.sid = sid
    · rw [if_pos hs] at h; cases h; subst hs
      exact ⟨epId, hTarget, by rw [hO, if_pos rfl]; rfl⟩
    · rw [if_neg hs] at h
      obtain ⟨e, he, hc⟩ := hR.registry sid r h
      refine ⟨e, he, ?_⟩
      rw [hO]
      by_cases hk : epId = e
      · subst hk; rw [hObj] at hc; simp [KernelObject.tableBackLinks, hClear] at hc
      · rw [if_neg hk]; exact hc
  · intro e n h
    simp only at h ⊢
    rw [hO] at h
    by_cases hk : epId = e
    · subst hk
      rw [if_pos rfl] at h
      simp only [objTableBackLinks_some, KernelObject.tableBackLinks] at h
      have hn : n = reg.sid.val := by omega
      subst hn
      exact ⟨reg, by rw [hS, if_pos rfl], hTarget⟩
    · rw [if_neg hk] at h
      obtain ⟨r, hr, ht⟩ := hR.serviceCodes e n h
      refine ⟨r, ?_, ht⟩
      rw [hS, if_neg]
      · exact hr
      · intro hs; rw [← hs, hFree] at hr; cases hr
  · intro irq n h
    simp only at h ⊢
    rw [hO]
    by_cases hk : epId = n
    · subst hk
      have := hR.irqHandlers irq _ h
      rw [hObj] at this; simp [KernelObject.tableBackLinks] at this
    · rw [if_neg hk]; exact hR.irqHandlers irq n h
  · intro n h
    simp only at h ⊢
    rw [hO] at h
    by_cases hk : epId = n
    · subst hk; rw [if_pos rfl] at h; simp [KernelObject.tableBackLinks] at h
    · rw [if_neg hk] at h; exact hR.irqBound n h

/-- **A revocation keeps the references recorded**: it erases the registration
and clears the record on the endpoint it names, which records it. -/
theorem revokeService_preserves_tableReferencesRecorded {sid : ServiceId}
    {st st' : SystemState} (hStep : revokeService sid st = .ok ((), st'))
    (hObjInv : st.objects.invExt) (hR : st.tableReferencesRecorded) :
    st'.tableReferencesRecorded := by
  obtain ⟨reg, hReg, rfl⟩ := revokeService_ok hStep
  obtain ⟨e1, he1, hc1⟩ := hR.registry sid reg hReg
  obtain ⟨ep1, hE1, hCode1⟩ := objTableBackLinks_code_succ hc1
  rw [clearEndpointServiceCode_of_recorded { st with serviceRegistry := st.serviceRegistry.erase sid }
    reg.endpointCap sid he1 hE1 hCode1,
    removeDependenciesOf_of_slotsEmpty _ _ (by exact hR.servicesEmpty)]
  have hO := fun j => getElem?_insert_ite st.objects e1 j
    (.endpoint { ep1 with serviceCode := 0 }) hObjInv
  have hS := fun j => getElem?_erase_ite st.serviceRegistry sid j hR.registryInvExtK
  refine ⟨RHTable.erase_preserves_invExtK _ _ hR.registryInvExtK, ?_, ?_, ?_, ?_,
    hR.servicesEmpty⟩
  · intro s r h
    simp only at h ⊢
    rw [hS] at h
    by_cases hs : sid = s
    · rw [if_pos hs] at h; cases h
    · rw [if_neg hs] at h
      obtain ⟨e, he, hc⟩ := hR.registry s r h
      refine ⟨e, he, ?_⟩
      rw [hO]
      by_cases hk : e1 = e
      · subst hk; rw [hc1] at hc; exact absurd (serviceId_eq_of_val hc) hs
      · rw [if_neg hk]; exact hc
  · intro e n h
    simp only at h ⊢
    rw [hO] at h
    by_cases hk : e1 = e
    · subst hk; rw [if_pos rfl] at h; simp [KernelObject.tableBackLinks] at h
    · rw [if_neg hk] at h
      obtain ⟨r, hr, ht⟩ := hR.serviceCodes e n h
      refine ⟨r, ?_, ht⟩
      rw [hS, if_neg]
      · exact hr
      · intro hs
        rw [← hs, hReg] at hr; cases hr
        rw [he1] at ht; cases ht; exact hk rfl
  · intro irq n h
    simp only at h ⊢
    rw [hO]
    by_cases hk : e1 = n
    · subst hk
      have := hR.irqHandlers irq _ h
      rw [hE1] at this; simp [KernelObject.tableBackLinks] at this
    · rw [if_neg hk]; exact hR.irqHandlers irq n h
  · intro n h
    simp only at h ⊢
    rw [hO] at h
    by_cases hk : e1 = n
    · subst hk; rw [if_pos rfl] at h; simp [KernelObject.tableBackLinks] at h
    · rw [if_neg hk] at h; exact hR.irqBound n h

/-- **Every registration names a live endpoint** — `registryEndpointValid`, read
off the records: a registration's endpoint records it, so it is there. -/
theorem registryEndpointValid_of_tableReferencesRecorded {st : SystemState}
    (hR : st.tableReferencesRecorded) : registryEndpointValid st := fun sid reg h => by
  obtain ⟨e, he, hc⟩ := hR.registry sid reg h
  refine ⟨e, he, fun hn => ?_⟩
  rw [hn] at hc; cases hc

/-- **No two registrations share an endpoint** — `registryEndpointUnique`, read
off the records: an endpoint records one service. -/
theorem registryEndpointUnique_of_tableReferencesRecorded {st : SystemState}
    (hR : st.tableReferencesRecorded) : registryEndpointUnique st := by
  intro sid₁ sid₂ reg₁ reg₂ epId h₁ h₂ ht₁ ht₂
  obtain ⟨e₁, he₁, hc₁⟩ := hR.registry sid₁ reg₁ h₁
  obtain ⟨e₂, he₂, hc₂⟩ := hR.registry sid₂ reg₂ h₂
  rw [ht₁] at he₁; cases he₁
  rw [ht₂] at he₂; cases he₂
  rw [hc₁] at hc₂
  exact serviceId_eq_of_val hc₂

end SeLe4n.Kernel
