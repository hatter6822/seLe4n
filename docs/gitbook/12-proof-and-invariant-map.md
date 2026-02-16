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

## 7. M4-A lifecycle invariant layering (steps 3-6 completed)

Current M4-A lifecycle invariant structure now follows the existing layered style:

1. identity/aliasing components (`lifecycleIdentityTypeExact`, `lifecycleIdentityNoTypeAliasConflict`),
2. identity bundle (`lifecycleIdentityAliasingInvariant`),
3. capability-reference components (`lifecycleCapabilityRefExact`, `lifecycleCapabilityRefObjectTargetBacked`),
4. capability-reference bundle (`lifecycleCapabilityReferenceInvariant`),
5. composed lifecycle bundle (`lifecycleInvariantBundle`).

This explicit split now includes transition-local lifecycle helper lemmas in `Lifecycle/Operations`,
local and composed lifecycle preservation entrypoints (`lifecycleRetypeObject_preserves_lifecycleInvariantBundle`,
`lifecycleRetypeObject_preserves_m3IpcSeedInvariantBundle`, and
`lifecycleRetypeObject_preserves_m4aLifecycleInvariantBundle`), and fixture-backed executable trace evidence
for unauthorized/illegal-state/success lifecycle retype outcomes.
