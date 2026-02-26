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

- `cspaceSlotUnique` — structural CNode slot-index uniqueness (reformulated in WS-E2; non-tautological, requires `CNode.slotsUnique`),
- `cspaceLookupSound` — lookup completeness grounded in slot membership (reformulated in WS-E2; non-tautological),
- `cspaceAttenuationRule` — minted capabilities attenuate rights,
- `lifecycleAuthorityMonotonicity` — authority only decreases through lifecycle operations.

Bridge theorem: `cspaceLookupSound_of_cspaceSlotUnique` derives lookup soundness from slot uniqueness.

Bundle level:

- `capabilityInvariantBundle` (conjunction of the four components above)
- `capabilityInvariantBundle_of_slotUnique` (constructor; requires all CNodes satisfy `slotsUnique`)

Preservation shape:

- operation-level `*_preserves_capabilityInvariantBundle` for insert/delete/revoke (compositional: pre-state → post-state),
- IPC-level preservation for endpoint send/receive/await-receive (compositional),
- lifecycle preservation with `hNewObjCNodeUniq` hypothesis.

Badge routing chain (H-03):

- `mintDerivedCap_badge_propagated` → `cspaceMint_child_badge_preserved` → `notificationSignal_badge_stored_fresh` → `notificationWait_recovers_pending_badge`
- End-to-end: `badge_notification_routing_consistent`
- Merge property: `badge_merge_idempotent`

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
- `ipcSchedulerCouplingInvariantBundle`

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
`lifecycleRetypeObject_preserves_coreIpcInvariantBundle`, and
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

## 10. VSpace proof completion (WS-D3 / F-08 / TPI-001 complete)

VSpace invariant bundle preservation is now proven for both success and error paths:

- **Error-path preservation** (trivially true, error returns unchanged state):
  - `vspaceMapPage_error_asidNotBound_preserves_vspaceInvariantBundle`
  - `vspaceUnmapPage_error_translationFault_preserves_vspaceInvariantBundle`
- **Success-path preservation** (substantive — prove invariant preservation over changed state):
  - `vspaceMapPage_success_preserves_vspaceInvariantBundle`
  - `vspaceUnmapPage_success_preserves_vspaceInvariantBundle`
- **Round-trip / functional-correctness theorems** (TPI-001 closure):
  - `vspaceLookup_after_map`: map then lookup yields mapped address
  - `vspaceLookup_map_other`: map at vaddr doesn't affect lookup at different vaddr'
  - `vspaceLookup_after_unmap`: after unmap, lookup fails with translationFault
  - `vspaceLookup_unmap_other`: unmap at vaddr doesn't affect lookup at different vaddr'

Supporting infrastructure in `VSpace.lean`:
- `resolveAsidRoot_some_implies` — extracts object-store facts from successful ASID resolution
- `resolveAsidRoot_of_unique_root` — characterization lemma enabling round-trip proofs
- `storeObject_objectIndex_eq_of_mem` — objectIndex stability for in-place updates

## 11. Badge-override safety (WS-D3 / F-06 / TPI-D04 complete)

Badge-override safety in `cspaceMint` is now fully proven:

- `mintDerivedCap_rights_attenuated_with_badge_override` — rights attenuation holds regardless of badge
- `mintDerivedCap_target_preserved_with_badge_override` — target identity preserved regardless of badge
- `cspaceMint_badge_override_safe` — composed kernel-operation-level safety witness

The core insight: `mintDerivedCap` checks `rightsSubset` and sets `target := parent.target`
unconditionally — the `badge` parameter only affects the `.badge` field of the child capability,
which is notification-signaling metadata, not authority scope.

## 12. Proof classification docstrings (WS-D3 / F-16 complete)

All seven `Invariant.lean` files now contain module-level `/-! ... -/` docstrings that classify
every theorem into one of these categories:

| Category | Assurance level |
|---|---|
| **Substantive preservation** | High — proves invariant preservation over changed state |
| **Error-case preservation** | Low — trivially true (unchanged state) |
| **Non-interference** | Critical — proves high-domain operations don't leak to low observers |
| **Badge-safety** | High — proves badge override cannot escalate privilege |
| **Structural / bridge** | High — proves decomposition/composition relationships |
| **Round-trip / functional-correctness** | High — proves semantic contracts between operations |

## 13. Kernel design hardening (WS-D4 complete)

### F-07: Service dependency cycle detection

Service dependency registration now includes BFS-based cycle detection:

- `serviceBfsFuel` — fuel computation for bounded BFS (objectIndex.length + 256)
- `serviceHasPathTo` — bounded BFS reachability check in the dependency graph
- `serviceRegisterDependency` — deterministic registration with self-loop, idempotency, and cycle checks
- `serviceRegisterDependency_error_self_loop` — self-dependency rejection theorem (no `sorry`)
- `serviceDependencyAcyclic` — acyclicity invariant definition
- `serviceRegisterDependency_preserves_acyclicity` — preservation theorem (no `sorry`; BFS bridge `bfs_complete_for_nontrivialPath` formally proven — TPI-D07-BRIDGE resolved, see §14)

### F-11: serviceRestart partial-failure semantics

serviceRestart uses documented partial-failure semantics (stop succeeds, start fails = service remains stopped):

- `serviceRestart_error_of_stop_error` — stop failure propagated directly
- `serviceRestart_error_of_start_error` — start failure propagated with post-stop state
- `serviceRestart_ok_implies_staged_steps` — success implies both stages succeeded
- `serviceRestart_error_discards_state` — error monad discards intermediate state
- `serviceRestart_error_from_start_phase` — functional decomposition of start-phase errors

### F-12: Double-wait prevention and uniqueness invariant

Notification waiting lists now enforce uniqueness:

- `notificationWait` — checks `waiter ∈ ntfn.waitingThreads` before appending; returns `alreadyWaiting` on duplicate
- `notificationWait_error_alreadyWaiting` — rejection theorem (no `sorry`)
- `notificationWait_badge_path_notification` — decomposition: badge-consumed path post-state notification
- `notificationWait_wait_path_notification` — decomposition: wait path post-state notification
- `uniqueWaiters` — invariant: notification waiting list has no duplicates (`List.Nodup`)
- `notificationWait_preserves_uniqueWaiters` — preservation theorem (no `sorry`)

Supporting infrastructure:

- `storeTcbIpcState_preserves_objects_ne` — storeTcbIpcState preserves objects at other IDs
- `storeTcbIpcState_preserves_notification` — storeTcbIpcState preserves notification objects
- `removeRunnable_preserves_objects` — removeRunnable preserves all objects

## 14. TPI-D07 acyclicity proof infrastructure (Risk 0 resolved, TPI-D07 closed, TPI-D07-BRIDGE resolved)

The vacuous BFS-based acyclicity invariant (Risk 0) has been resolved via Strategy B:
the invariant definition was corrected and a genuine 4-layer proof infrastructure was
implemented in `SeLe4n/Kernel/Service/Invariant.lean`.

**Problem:** The original `serviceDependencyAcyclic` was defined as
`∀ sid, ¬ serviceHasPathTo st sid sid fuel = true`, but `serviceHasPathTo` returns `true`
immediately for self-queries (BFS starts with `[src]` in frontier, immediately finds
`src = target`), making the invariant equivalent to `False` — trivially unsatisfiable.

**Resolution:** Replaced with declarative acyclicity using `serviceNontrivialPath`
(an inductive `Prop`-valued path relation of length ≥ 1).

Implemented proof layers:

- **Layer 0 (Definitions):** `serviceEdge`, `serviceReachable`, `serviceNontrivialPath`,
  revised `serviceDependencyAcyclic` (declarative, non-vacuous)
- **Layer 1 (Structural lemmas):** `serviceReachable_trans`, `serviceReachable_of_edge`,
  `serviceReachable_of_nontrivialPath`, `serviceNontrivialPath_of_edge_reachable`,
  `serviceNontrivialPath_of_reachable_ne`, `serviceNontrivialPath_trans`,
  `serviceNontrivialPath_step_right`. Frame lemmas: `serviceEdge_storeServiceState_ne`,
  `serviceEdge_storeServiceState_updated`, `serviceEdge_post_insert`
- **Layer 2 (BFS bridge):** `bfs_complete_for_nontrivialPath` — BFS completeness
  bridge connecting declarative paths to the executable BFS check. Formally proven
  (TPI-D07-BRIDGE resolved); no `sorry` remains
- **Layer 3 (Path decomposition):** `nontrivialPath_post_insert_cases` — decomposes
  any post-insertion nontrivial path into either a pre-state path or a composition
  using the new edge with pre-state reachability
- **Layer 4 (Closure):** `serviceRegisterDependency_preserves_acyclicity` — genuine
  preservation proof via post-insertion path decomposition and contradiction with the
  BFS cycle-detection check. The main theorem is sorry-free

**Sub-obligation resolved (TPI-D07-BRIDGE):** The `bfs_complete_for_nontrivialPath`
lemma has been formally proven, establishing that the BFS with `serviceBfsFuel` fuel
is complete enough to detect all nontrivial paths between distinct services. No
`sorry` obligations remain in the TPI-D07 proof infrastructure.

### 14.1 BFS completeness proof (TPI-D07-BRIDGE completed)

The formal proof eliminating the `bfs_complete_for_nontrivialPath` sorry has been
completed following the M2 milestone roadmap
([`M2_BFS_SOUNDNESS.md`](../audits/execution_plans/milestones/M2_BFS_SOUNDNESS.md))
and four sub-documents (M2A–M2D).

**Proof decomposition:**

1. **Equational theory ([M2A](../audits/execution_plans/milestones/M2A_EQUATIONAL_THEORY.md)):**
   A `lookupDeps` helper bridges the executable BFS dependency lookup to the
   declarative `serviceEdge` relation (`serviceEdge_iff_lookupDeps`). Five BFS
   unfolding lemmas (EQ1-EQ5) provide rewrite rules for each branch of the `go`
   function.

2. **Completeness invariant ([M2B](../audits/execution_plans/milestones/M2B_COMPLETENESS_INVARIANT.md)):**
   A named `bfsClosed` definition captures the visited-set closure property. Four
   lemmas (CB1-CB4) establish the invariant initially, preserve it across skip and
   expansion steps, and prove the critical boundary lemma: if a visited node reaches
   target and target is not visited, some frontier node also reaches target.

3. **Fuel adequacy ([M2C](../audits/execution_plans/milestones/M2C_FUEL_ADEQUACY.md)):**
   A `serviceCountBounded` precondition bounds the BFS universe by `serviceBfsFuel st`
   (Approach A). `serviceCountBounded_preserved_by_registerDependency` proves the
   precondition is maintained across dependency registration.

4. **Core completeness ([M2D](../audits/execution_plans/milestones/M2D_COMPLETENESS_PROOF.md)):**
   `go_complete` (CP1) carries the four-part invariant (I1: target not visited,
   I2: closure, I3: frontier witness, I4: fuel adequate) through strong induction
   on fuel with structural induction on the frontier list. The sorry is eliminated.

**Implemented scope:** 17 private lemmas + 4 definitions + 3 public theorems.

Frozen operational files (M0 semantics freeze):

| File | SHA-256 |
|---|---|
| `Operations.lean` | `a61fa6c1...42ffff44` |
| `State.lean` | `6f6f87d8...d1cbc1e6` |
| `Object.lean` | `db228ed6...14594f32` |
| `Prelude.lean` | `bffc93fe...d47b30fe` |

Full execution plan: [`docs/audits/execution_plans/00_INDEX.md`](../audits/execution_plans/00_INDEX.md)

## 15. Information-flow layering (WS-B7 baseline + WS-D2 enforcement and non-interference)

### IF-M1 baseline (WS-B7 complete)

Policy and projection primitives:

- policy lattice/labels:
  - `Confidentiality`, `Integrity`, `SecurityLabel`,
  - `confidentialityFlowsTo`, `integrityFlowsTo`, `securityFlowsTo`,
  - algebraic lemmas: `securityFlowsTo_refl`, `securityFlowsTo_trans`.
- observer projection helpers:
  - `projectState`, `projectObjects`, `projectRunnable`, `projectCurrent`,
  - relation scaffold: `lowEquivalent` with `refl/symm/trans` lemmas.

### Enforcement layer (WS-D2 / F-02 complete)

Policy checks wired into kernel operations via `Enforcement.lean`:

- `endpointSendChecked` — enforces `securityFlowsTo` before IPC send,
- `cspaceMintChecked` — enforces `securityFlowsTo` before capability minting,
- `serviceRestartChecked` — enforces `securityFlowsTo` before service restart.

### Non-interference theorems (WS-D2 / F-05 complete)

Transition-level non-interference proofs in `InformationFlow/Invariant.lean`:

- `chooseThread_preserves_lowEquivalent` — scheduler non-interference (TPI-D01),
- `cspaceMint_preserves_lowEquivalent` — capability mint non-interference (TPI-D02),
- `cspaceRevoke_preserves_lowEquivalent` — capability revoke non-interference (TPI-D02),
- `lifecycleRetypeObject_preserves_lowEquivalent` — lifecycle non-interference (TPI-D03).

### IF-M4 bundle-level non-interference (WS-E5 complete)

**H-04 — Parameterized security labels (≥3 domains):**

- `SecurityDomain` (Nat-indexed), `DomainFlowPolicy` with `canFlow`/`isReflexive`/`isTransitive`/`wellFormed`,
- `domainFlowsTo` with `domainFlowsTo_refl`/`domainFlowsTo_trans` proofs,
- Built-in policies: `DomainFlowPolicy.allowAll`, `DomainFlowPolicy.linearOrder` with well-formedness proofs,
- `GenericLabelingContext` with embedded policy field,
- `EndpointFlowPolicy` for per-endpoint flow overrides,
- `embedLegacyLabel` mapping legacy 2x2 lattice to 4-domain system,
- `embedLegacyLabel_preserves_flow` correctness proof,
- `threeDomainExample` with 3 named validation theorems.

**H-05 — Composed bundle-level non-interference:**

- `NonInterferenceStep` inductive (5 constructors: `chooseThread`, `endpointSend`, `cspaceMint`, `cspaceRevoke`, `lifecycleRetype`),
- `step_preserves_projection` — single-step projection preservation,
- `composedNonInterference_step` — primary IF-M4 single-step theorem,
- `NonInterferenceTrace` inductive (`nil`/`cons`),
- `trace_preserves_projection`, `composedNonInterference_trace` — multi-step lift,
- `preservesLowEquivalence`, `compose_preservesLowEquivalence` — abstract composition,
- `errorAction_preserves_lowEquiv` — error path preservation.

**M-07 — Enforcement boundary specification:**

- `EnforcementClass` inductive (`policyGated`/`capabilityOnly`/`readOnly`),
- `enforcementBoundary` — exhaustive 17-entry classification table,
- `denied_preserves_state_*` — denial preservation for all 3 checked operations,
- `enforcement_sufficiency_*` — complete-disjunction coverage proofs.
