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
- `serviceRegisterDependency_preserves_acyclicity` — preservation theorem (no `sorry`; BFS bridge deferred to `bfs_complete_for_nontrivialPath` as TPI-D07-BRIDGE — see §14)

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

## 14. TPI-D07 acyclicity proof infrastructure (Risk 0 resolved, TPI-D07 closed)

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
  bridge connecting declarative paths to the executable BFS check. Uses focused `sorry`
  (annotated TPI-D07-BRIDGE); operationally validated by executable tests
- **Layer 3 (Path decomposition):** `nontrivialPath_post_insert_cases` — decomposes
  any post-insertion nontrivial path into either a pre-state path or a composition
  using the new edge with pre-state reachability
- **Layer 4 (Closure):** `serviceRegisterDependency_preserves_acyclicity` — genuine
  preservation proof via post-insertion path decomposition and contradiction with the
  BFS cycle-detection check. The main theorem is sorry-free

**Remaining sub-obligation (TPI-D07-BRIDGE):** The focused `sorry` on
`bfs_complete_for_nontrivialPath` defers a formal proof that the BFS with
`serviceBfsFuel` fuel is complete enough to detect all nontrivial paths between
distinct services. See Risk 1 and Risk 3 in the risk register for future closure path.

### 14.1 BFS completeness roadmap (TPI-D07-BRIDGE closure path)

A detailed proof roadmap for eliminating the `bfs_complete_for_nontrivialPath`
sorry is documented in the M2 milestone
([`M2_BFS_SOUNDNESS.md §6`](../audits/execution_plans/milestones/M2_BFS_SOUNDNESS.md#6-completeness-proof-roadmap--the-harder-path)).

**Proof decomposition:**

1. **BFS completeness under adequate fuel:** If `serviceReachable st a b` and
   fuel exceeds the number of registered services, then
   `serviceHasPathTo st a b fuel = true`. This is proved via a loop invariant
   on the BFS `go` function (§6.5).

2. **Fuel adequacy:** `serviceBfsFuel st` provides enough fuel. Two approaches
   are analyzed (§6.8): adding a `serviceIndex` field to `SystemState` (preferred)
   or carrying finiteness as a hypothesis (preconditioned, no model change).

**Key design decisions:**

- **Induction measure:** Lexicographic `(countUnvisitedRegistered, frontier.length)`
  — the visited-node (fuel-recycling) case decreases frontier length while the
  expansion case decreases unvisited count (§6.9)
- **Prerequisite lemma tiers:** 12 helper lemmas organized into 4 dependency
  tiers covering list membership, reachability transfer through visited sets,
  fuel counting arithmetic, and BFS closure maintenance (§6.7)
- **BFS loop invariant:** 4 preconditions — target not visited, some frontier
  node reaches target, visited-set closure, fuel adequacy — maintained across
  all three BFS branches (§6.4–6.5)

**Estimated scope:** ~18 lemmas/theorems, ~140–270 lines of proof. Critical
path runs through the fuel adequacy decision, counting lemmas, closure
maintenance, and the core completeness theorem.

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
