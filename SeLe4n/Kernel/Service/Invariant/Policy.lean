-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Service.Operations
import SeLe4n.Kernel.Service.Registry.Invariant
import SeLe4n.Kernel.Capability.Invariant

/-! # Service Policy Invariants — seLe4n Extension

**This module is a seLe4n-specific extension with no analogue in real seL4.**

Defines the service policy surface: invariants over backing-object typing,
owner-authority references, and cross-subsystem bundle composition with the
capability and lifecycle invariant surfaces. These predicates enable
machine-checked verification that service operations preserve structural
properties across subsystem boundaries.

See `Service/Operations.lean` for the full seLe4n extension rationale. -/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- Reusable policy predicate surface over a single service entry. -/
abbrev ServicePolicyPredicate := SystemState → ServiceGraphEntry → Prop

/-- Policy component: backing object identity remains lifecycle-typed. -/
def policyBackingObjectTyped : ServicePolicyPredicate :=
  fun st svc => ∃ ty, SystemState.lookupObjectTypeMeta st svc.identity.backingObject = some ty

/-- Policy component: lifecycle metadata records an owner-slot reference to the backing object. -/
def policyOwnerAuthorityRefRecorded : ServicePolicyPredicate :=
  fun st svc =>
    ∃ slot,
      SystemState.lookupCapabilityRefMeta st { cnode := svc.identity.owner, slot := slot } =
        some (.object svc.identity.backingObject)

/-- Policy component: owner CNode contains concrete authority to the backing object. -/
def policyOwnerAuthoritySlotPresent : ServicePolicyPredicate :=
  fun st svc =>
    ∃ slot cap,
      SystemState.lookupSlotCap st { cnode := svc.identity.owner, slot := slot } = some cap ∧
      cap.target = .object svc.identity.backingObject

/-- M5 policy bundle entrypoint (WS-M5-C): reusable, mutation-free policy assumptions. -/
def servicePolicySurfaceInvariant (st : SystemState) : Prop :=
  ∀ sid svc,
    lookupService st sid = some svc →
      policyBackingObjectTyped st svc ∧
      (policyOwnerAuthorityRefRecorded st svc → policyOwnerAuthoritySlotPresent st svc)

/-- Cross-subsystem M5/Q1 proof-package bundle over service policy + lifecycle + capability
+ registry surfaces. WS-Q1-C: `registryInvariant` added for capability-indexed registry. -/
def serviceLifecycleCapabilityInvariantBundle (st : SystemState) : Prop :=
  servicePolicySurfaceInvariant st ∧ lifecycleInvariantBundle st ∧
  capabilityInvariantBundle st ∧ registryInvariant st

theorem serviceLifecycleCapabilityInvariantBundle_of_components
    (st : SystemState)
    (hPolicy : servicePolicySurfaceInvariant st)
    (hLifecycle : lifecycleInvariantBundle st)
    (hCap : capabilityInvariantBundle st)
    (hReg : registryInvariant st) :
    serviceLifecycleCapabilityInvariantBundle st := by
  exact ⟨hPolicy, hLifecycle, hCap, hReg⟩

/-- Bridge lemma: lifecycle typing assumptions imply policy backing-object typing. -/
theorem policyBackingObjectTyped_of_lifecycleInvariant
    (st : SystemState)
    (svc : ServiceGraphEntry)
    (obj : KernelObject)
    (hLifecycle : lifecycleInvariantBundle st)
    (hObj : st.objects[svc.identity.backingObject]? = some obj) :
    policyBackingObjectTyped st svc := by
  -- AN4-B (H-03): the identity/aliasing bundle collapsed to its single exact
  -- conjunct, so we project directly.
  rcases hLifecycle with ⟨hTypeExact, _⟩
  refine ⟨obj.objectType, ?_⟩
  simpa [lifecycleIdentityTypeExact, SystemState.objectTypeMetadataConsistent,
    SystemState.lookupObjectTypeMeta, hObj] using hTypeExact svc.identity.backingObject

/-- Bridge lemma: lifecycle capability-reference backing implies concrete slot authority. -/
theorem policyOwnerAuthoritySlotPresent_of_lifecycleInvariant
    (st : SystemState)
    (svc : ServiceGraphEntry)
    (hLifecycle : lifecycleInvariantBundle st)
    (hRef : policyOwnerAuthorityRefRecorded st svc) :
    policyOwnerAuthoritySlotPresent st svc := by
  rcases hLifecycle with ⟨_, hCapRefBundle⟩
  rcases hCapRefBundle with ⟨_hExact, hBacked⟩
  rcases hRef with ⟨slot, hMeta⟩
  rcases hBacked { cnode := svc.identity.owner, slot := slot } svc.identity.backingObject hMeta with
    ⟨cap, hLookup, hTarget⟩
  exact ⟨slot, cap, hLookup, hTarget⟩

/-- Bridge lemma: capability lookup-soundness assumptions imply owner-slot witness facts.
    W5-F: Removed unused `_hCap : capabilityInvariantBundle st` parameter — the proof
    only requires the lookup equivalence, not the full capability invariant bundle. -/
theorem policyOwnerAuthoritySlotPresent_of_capabilityLookup
    (st : SystemState)
    (svc : ServiceGraphEntry)
    (slot : SeLe4n.Slot)
    (cap : Capability)
    (hLookup : cspaceLookupSlot { cnode := svc.identity.owner, slot := slot } st = .ok (cap, st))
    (hTarget : cap.target = .object svc.identity.backingObject) :
    policyOwnerAuthoritySlotPresent st svc := by
  have hSlotCap : SystemState.lookupSlotCap st { cnode := svc.identity.owner, slot := slot } = some cap :=
    (cspaceLookupSlot_ok_iff_lookupSlotCap st { cnode := svc.identity.owner, slot := slot } cap).1 hLookup
  exact ⟨slot, cap, hSlotCap, hTarget⟩

/-- Composed bridge theorem from lifecycle contracts to the service policy surface.

The assumption `hBackingObjects` states that each registered service references an existing backing
object identity in the object store. Under this assumption, lifecycle metadata consistency provides
all policy-surface obligations. -/
theorem servicePolicySurfaceInvariant_of_lifecycleInvariant
    (st : SystemState)
    (hLifecycle : lifecycleInvariantBundle st)
    (hBackingObjects :
      ∀ sid svc, lookupService st sid = some svc →
        ∃ obj, st.objects[svc.identity.backingObject]? = some obj) :
    servicePolicySurfaceInvariant st := by
  intro sid svc hSvc
  rcases hBackingObjects sid svc hSvc with ⟨obj, hObj⟩
  refine ⟨policyBackingObjectTyped_of_lifecycleInvariant st svc obj hLifecycle hObj, ?_⟩
  intro hRef
  exact policyOwnerAuthoritySlotPresent_of_lifecycleInvariant st svc hLifecycle hRef

/-- `storeServiceState` preserves the service policy surface invariant.

`storeServiceState` only modifies the `services` field. Identity, backing object,
and owner references are preserved when updating a service entry. -/
theorem storeServiceState_preserves_servicePolicySurfaceInvariant
    (st : SystemState)
    (sid : ServiceId)
    (entry : ServiceGraphEntry)
    (hSvc : lookupService st sid ≠ none)
    (hIdentityEq : ∀ svc, lookupService st sid = some svc → entry.identity = svc.identity)
    (hPolicy : servicePolicySurfaceInvariant st)
    (hSvcInv : st.services.invExt) :
    servicePolicySurfaceInvariant (storeServiceState sid entry st) := by
  intro sid' svc' hLookup
  by_cases hSid : sid' = sid
  · subst sid'
    have hLookupEq := storeServiceState_lookup_eq st sid entry hSvcInv
    rw [hLookupEq] at hLookup; cases hLookup
    cases hOld : lookupService st sid with
    | none => exact absurd hOld hSvc
    | some svc =>
      have hIdEq := hIdentityEq svc hOld
      rcases hPolicy sid svc hOld with ⟨hTyped, hBridge⟩
      refine ⟨?_, ?_⟩
      · simpa [policyBackingObjectTyped, hIdEq] using hTyped
      · intro hRef
        have hRefOld : policyOwnerAuthorityRefRecorded st svc := by
          simpa [policyOwnerAuthorityRefRecorded, hIdEq] using hRef
        have hPresentOld : policyOwnerAuthoritySlotPresent st svc := hBridge hRefOld
        simpa [policyOwnerAuthoritySlotPresent, hIdEq] using hPresentOld
  · have hLookupNe := storeServiceState_lookup_ne st sid sid' entry hSid hSvcInv
    have hLookupOld : lookupService st sid' = some svc' := by simpa [hLookupNe] using hLookup
    exact hPolicy sid' svc' hLookupOld

/-- `storeServiceState` preserves the lifecycle invariant bundle.

`storeServiceState` only modifies the `services` field, leaving objects,
lifecycle metadata, and capabilities unchanged. -/
theorem storeServiceState_preserves_lifecycleInvariantBundle
    (st : SystemState)
    (sid : ServiceId)
    (entry : ServiceGraphEntry)
    (hLifecycle : lifecycleInvariantBundle st) :
    lifecycleInvariantBundle (storeServiceState sid entry st) := by
  -- AN4-B (H-03): `lifecycleIdentityNoTypeAliasConflict` was removed from the
  -- bundle (redundant with `lifecycleIdentityTypeExact`), so the simpa list no
  -- longer unfolds it.
  simpa [lifecycleInvariantBundle, lifecycleIdentityAliasingInvariant, lifecycleIdentityTypeExact,
    lifecycleCapabilityReferenceInvariant,
    lifecycleCapabilityRefExact, lifecycleCapabilityRefObjectTargetBacked, storeServiceState,
    SystemState.objectTypeMetadataConsistent, SystemState.capabilityRefMetadataConsistent,
    SystemState.lookupObjectTypeMeta, SystemState.lookupCapabilityRefMeta,
    SystemState.lookupSlotCap, SystemState.lookupCNode] using hLifecycle

/-- `storeServiceState` preserves the capability invariant bundle compositionally.

`storeServiceState` only modifies the `services` field, leaving the object store
unchanged. Therefore CNode slot-index uniqueness transfers directly from the pre-state. -/
theorem storeServiceState_preserves_capabilityInvariantBundle
    (st : SystemState)
    (sid : ServiceId)
    (entry : ServiceGraphEntry)
    (hInv : capabilityInvariantBundle st) :
    capabilityInvariantBundle (storeServiceState sid entry st) := by
  rcases hInv with ⟨hUnique, hSound, hBounded, hComp, hAcyclic, hDepth⟩
  refine ⟨?_, ?_, hBounded, hComp, hAcyclic, hDepth⟩
  · intro cnodeId cn hCn
    exact hUnique cnodeId cn hCn
  · intro cnodeId cn slot cap hCn hMem
    have hSlot := hSound cnodeId cn slot cap hCn hMem
    simp only [SystemState.lookupSlotCap, storeServiceState] at hSlot ⊢
    exact hSlot

-- ============================================================================
-- S3-I/U-M25: Compile-time bridge signature witness
-- ============================================================================

/-- S3-I: Bridge signature witness — asserts that `servicePolicySurfaceInvariant`
    follows from `lifecycleInvariantBundle` plus backing-object existence at
    compile time. If the signature of `servicePolicySurfaceInvariant` or
    `lifecycleInvariantBundle` changes, this definition will fail to type-check,
    alerting the developer to update all bridge theorems.

    This is a type-level witness, not a runtime check. -/
def bridgeSignatureWitness :
    (∀ (st : SystemState),
      lifecycleInvariantBundle st →
      (∀ sid svc, lookupService st sid = some svc →
        ∃ obj, st.objects[svc.identity.backingObject]? = some obj) →
      servicePolicySurfaceInvariant st) :=
  servicePolicySurfaceInvariant_of_lifecycleInvariant

/-- S3-I: Extended bridge witness including the full cross-subsystem bundle.
    Fails to compile if `serviceLifecycleCapabilityInvariantBundle` changes shape. -/
def fullBridgeSignatureWitness :
    (∀ (st : SystemState),
      servicePolicySurfaceInvariant st →
      lifecycleInvariantBundle st →
      capabilityInvariantBundle st →
      registryInvariant st →
      serviceLifecycleCapabilityInvariantBundle st) :=
  serviceLifecycleCapabilityInvariantBundle_of_components
