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

Defines the service policy surface: the invariant that every registered
service's backing object is lifecycle-typed, and the cross-subsystem bundle
composition with the capability and lifecycle invariant surfaces.  These
predicates enable machine-checked verification that service operations
preserve structural properties across subsystem boundaries.

`v0.35.78`: the surface used to carry a second component, an implication
from an *owner-authority reference recorded in lifecycle metadata* to the
owner CNode holding concrete authority.  Its antecedent was stated through
`SystemState.lookupCapabilityRefMeta`, which read `lookupSlotCap` — so the
implication was `∃ slot, lookupSlotCap … = some cap ∧ cap.target = … →
∃ slot cap, lookupSlotCap … = some cap ∧ cap.target = …`, a tautology with
no consumer in the tree.  It is retired with the reader (see
`Model/State.lean`), and the surface is the typing invariant alone.

See `Service/Operations.lean` for the full seLe4n extension rationale. -/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- Reusable policy predicate surface over a single service entry. -/
abbrev ServicePolicyPredicate := SystemState → ServiceGraphEntry → Prop

/-- Policy component: backing object identity remains lifecycle-typed. -/
def policyBackingObjectTyped : ServicePolicyPredicate :=
  fun st svc => ∃ ty, SystemState.lookupObjectTypeMeta st svc.identity.backingObject = some ty

/-- M5 policy bundle entrypoint (WS-M5-C): reusable, mutation-free policy assumptions.
Since `v0.35.78` it is the typing component alone (see the module docstring). -/
def servicePolicySurfaceInvariant (st : SystemState) : Prop :=
  ∀ sid svc,
    lookupService st sid = some svc →
      policyBackingObjectTyped st svc

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
  -- conjunct; since `v0.35.78` the lifecycle bundle *is* that conjunct.
  have hTypeExact : lifecycleIdentityTypeExact st := hLifecycle
  refine ⟨obj.objectType, ?_⟩
  simpa [lifecycleIdentityTypeExact, SystemState.objectTypeMetadataConsistent,
    SystemState.lookupObjectTypeMeta, hObj] using hTypeExact svc.identity.backingObject

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
  exact policyBackingObjectTyped_of_lifecycleInvariant st svc obj hLifecycle hObj

/-- `storeServiceState` preserves the service policy surface invariant.

`storeServiceState` only modifies the `services` field. The identity — and with
it the backing object — is preserved when updating a service entry. -/
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
      have hTyped := hPolicy sid svc hOld
      simpa [policyBackingObjectTyped, hIdEq] using hTyped
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
  -- AN4-B (H-03) removed `lifecycleIdentityNoTypeAliasConflict` from the bundle
  -- and `v0.35.78` the capability-reference layer, so the bundle is the typing
  -- invariant and the simpa list unfolds exactly that.
  simpa [lifecycleInvariantBundle, lifecycleIdentityAliasingInvariant, lifecycleIdentityTypeExact,
    storeServiceState, SystemState.objectTypeMetadataConsistent,
    SystemState.lookupObjectTypeMeta] using hLifecycle

/-- `storeServiceState` preserves the capability invariant bundle compositionally.

`storeServiceState` only modifies the `services` field, leaving the object store
unchanged. Therefore CNode slot-index uniqueness transfers directly from the pre-state. -/
theorem storeServiceState_preserves_capabilityInvariantBundle
    (st : SystemState)
    (sid : ServiceId)
    (entry : ServiceGraphEntry)
    (hInv : capabilityInvariantBundle st) :
    capabilityInvariantBundle (storeServiceState sid entry st) := by
  rcases hInv with ⟨hSound, hBounded, hComp, hAcyclic, hDepth⟩
  refine ⟨?_, hBounded, hComp, hAcyclic, hDepth⟩
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
