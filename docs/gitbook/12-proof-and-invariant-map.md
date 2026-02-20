# Proof and Invariant Map

This chapter summarizes how theorem surfaces are organized and how they compose across milestones.

## 1. Layered invariant philosophy

seLe4n invariants are intentionally layered:

1. **component invariants** describe one focused safety condition,
2. **subsystem bundles** combine related components,
3. **cross-subsystem bundles** compose milestone contracts.

This keeps proof scripts reviewable and reduces blast radius when adding new transitions.

## 2. Scheduler invariants (M1)

Component level:

- `runQueueUnique`
- `currentThreadValid`
- `queueCurrentConsistent`

Bundle level:

- `schedulerInvariantBundle` (alias over `kernelInvariant`)

Preservation shape:

- `chooseThread_preserves_*`
- `schedule_preserves_*`
- `handleYield_preserves_*`

## 3. Capability invariants (M2)

Component level:

- uniqueness of slots,
- lookup soundness,
- attenuation rule,
- lifecycle authority monotonicity.

Bundle level:

- `capabilityInvariantBundle`

Preservation shape:

- operation-level `*_preserves_capabilityInvariantBundle` for lookup/insert/mint/delete/revoke.

## 4. IPC invariants (M3)

Component level:

- endpoint queue/object validity,
- endpoint invariant,
- `ipcInvariant` across object store.

Preservation shape:

- transition-level `endpointSend_preserves_ipcInvariant`, etc.

## 5. IPC-scheduler coherence (M3.5)

Component level:

- runnable threads should be IPC-ready,
- blocked-on-send threads should not remain runnable,
- blocked-on-receive threads should not remain runnable.

Bundle level:

- `ipcSchedulerContractPredicates`
- `ipcSchedulerCoherenceComponent`
- `m35IpcSchedulerInvariantBundle`

Preservation shape:

- local component preservation theorem per transition,
- composed contract preservation theorem per transition,
- bundle preservation theorem per transition.

## 6. Naming conventions and why they matter

Preferred shape:

- `<transition>_preserves_<componentOrBundle>`

Why:

- searchable theorem entrypoints,
- stable doc/test anchors,
- predictable maintainability under milestone growth.

## 7. M4 lifecycle invariant layering (M4-A complete, M4-B WS-B complete)

Current M4-A lifecycle invariant structure now follows the existing layered style:

1. identity/aliasing components (`lifecycleIdentityTypeExact`, `lifecycleIdentityNoTypeAliasConflict`),
2. identity bundle (`lifecycleIdentityAliasingInvariant`),
3. capability-reference components (`lifecycleCapabilityRefExact`, `lifecycleCapabilityRefObjectTargetBacked`),
4. capability-reference bundle (`lifecycleCapabilityReferenceInvariant`),
5. composed lifecycle bundle (`lifecycleInvariantBundle`),
6. stale-reference hardening family (`lifecycleStaleReferenceExclusionInvariant`),
7. lifecycle+stale bridge (`lifecycleIdentityStaleReferenceInvariant`).

This explicit split now includes transition-local lifecycle helper lemmas in `Lifecycle/Operations`,
local and composed lifecycle preservation entrypoints (`lifecycleRetypeObject_preserves_lifecycleInvariantBundle`,
`lifecycleRetypeObject_preserves_lifecycleStaleReferenceExclusionInvariant`,
`lifecycleRetypeObject_preserves_lifecycleIdentityStaleReferenceInvariant`,
`lifecycleRetypeObject_preserves_m3IpcSeedInvariantBundle`, and
`lifecycleRetypeObject_preserves_m4aLifecycleInvariantBundle`), and fixture-backed executable trace evidence
for unauthorized/illegal-state/success lifecycle retype outcomes plus composed lifecycle+capability behavior.

## 8. M5 policy-surface layering (WS-M5-C complete)

Policy surface entrypoints now live in `SeLe4n/Kernel/Service/Invariant.lean` and are explicitly
kept mutation-free:

- reusable components: `policyBackingObjectTyped`, `policyOwnerAuthorityRefRecorded`,
  `policyOwnerAuthoritySlotPresent`,
- bundle entrypoint: `servicePolicySurfaceInvariant`,
- bridge lemmas: lifecycle/capability assumptions can discharge policy authority obligations,
- composed bridge: `servicePolicySurfaceInvariant_of_lifecycleInvariant` lifts lifecycle contracts
  (plus backing-object existence assumptions) into the service policy bundle,
- check-vs-mutation separation: policy-denial theorem surfaces remain explicit and deterministic.

## 9. M5 proof package layering (WS-M5-D complete)

Proof-package entrypoints now extend the M5 policy surface to full local + composed preservation:

- composed bundle entrypoint: `serviceLifecycleCapabilityInvariantBundle`,
- local preservation entrypoints:
  - `serviceStart_preserves_serviceLifecycleCapabilityInvariantBundle`,
  - `serviceStop_preserves_serviceLifecycleCapabilityInvariantBundle`,
  - `serviceRestart_preserves_serviceLifecycleCapabilityInvariantBundle`,
- failure-path preservation entrypoints:
  - `serviceStart_failure_preserves_serviceLifecycleCapabilityInvariantBundle`,
  - `serviceStop_failure_preserves_serviceLifecycleCapabilityInvariantBundle`,
  - `serviceRestart_stop_failure_preserves_serviceLifecycleCapabilityInvariantBundle`,
  - `serviceRestart_start_failure_preserves_serviceLifecycleCapabilityInvariantBundle`.

This keeps the M5 theorem surface aligned with the local-first composition rule:
prove per-transition preservation first, then expose cross-subsystem bundle preservation with
explicit failure-path statements.

## 10. Architecture/VSpace invariant layering (M6 + WS-D3 complete)

VSpace invariant components and preservation:

- `vspaceAsidRootsUnique` — at most one VSpaceRoot per ASID in the object store,
- `vspaceRootNonOverlap` — no virtual-address overlap within any VSpaceRoot mappings,
- `vspaceInvariantBundle` — conjunction of the above two components.

Preservation shape (error-case):

- `vspaceMapPage_error_preserves_vspaceInvariantBundle`
- `vspaceUnmapPage_error_preserves_vspaceInvariantBundle`

Preservation shape (success, WS-D3/F-08):

- `vspaceMapPage_success_preserves_vspaceInvariantBundle`
- `vspaceUnmapPage_success_preserves_vspaceInvariantBundle`

Round-trip theorems (WS-D3/F-08, TPI-D05/TPI-001):

- `vspaceLookup_after_map` — map then lookup same vaddr yields mapped paddr,
- `vspaceLookup_map_other` — map does not affect lookup of a different vaddr,
- `vspaceLookup_after_unmap` — unmap then lookup yields translationFault,
- `vspaceLookup_unmap_other` — unmap does not affect lookup of a different vaddr.

Supporting infrastructure:

- VSpaceRoot helper lemmas in `Model/Object.lean` (`mapPage_asid_eq`, `unmapPage_asid_eq`, `lookup_eq_none_not_mem`, `mapPage_noVirtualOverlap`, `unmapPage_noVirtualOverlap`, `lookup_mapPage_ne`, `lookup_unmapPage_ne`),
- resolveAsidRoot characterization in `Architecture/VSpace.lean` (`resolveAsidRoot_some_implies`, `resolveAsidRoot_of_unique_root`, `storeObject_objectIndex_eq_of_mem`).

## 11. Capability badge-safety proofs (WS-D3/F-06 complete)

Badge-override safety theorems in `Capability/Invariant.lean` (TPI-D04):

- `mintDerivedCap_target_preserved` — target preserved regardless of badge,
- `mintDerivedCap_rights_attenuated` — rights attenuated regardless of badge,
- `cspaceMint_badge_override_rights_attenuated` — end-to-end: mint cannot escalate rights,
- `cspaceMint_badge_override_target_preserved` — end-to-end: mint cannot change target.

These extend the existing `mintDerivedCap_attenuates` / `cspaceMint_child_attenuates` foundations.

## 12. IF-M1 information-flow baseline layering (WS-B7 complete)

Information-flow proof-track entrypoints now exist with explicit local decomposition:

- policy lattice/labels:
  - `Confidentiality`, `Integrity`, `SecurityLabel`,
  - `confidentialityFlowsTo`, `integrityFlowsTo`, `securityFlowsTo`,
  - algebraic lemmas: `securityFlowsTo_refl`, `securityFlowsTo_trans`.
- observer projection helpers:
  - `projectState`, `projectObjects`, `projectRunnable`, `projectCurrent`,
  - relation scaffold: `lowEquivalent` with `refl/symm/trans` lemmas.

This keeps IF-M1 aligned with the repository's local-first theorem discipline:
first provide reusable policy + projection primitives, then stage transition-level
noninterference claims in IF-M2/IF-M3.
