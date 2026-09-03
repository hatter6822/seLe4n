# Claim vs Evidence Index

Every substantive claim seLe4n makes in public — in the README, the
specification, the website — with the command that checks it and the artefact
that carries it. If a claim is not in this table, it is not a claim the project
stands behind.

**This is an index, not a record.** What each version changed is in
[`CHANGELOG.md`](../CHANGELOG.md); what is in flight is in
[`REGISTERED_DEBT.md`](REGISTERED_DEBT.md).

## 1. Proof surface

| Claim | Where it is made | Check it with | Artefact |
|-------|------------------|---------------|----------|
| Zero `sorry` and zero `axiom` in the production proof surface | README, `SELE4N_SPEC.md` | `./scripts/test_tier0_hygiene.sh`; `python3 scripts/check_module_axioms.py` | `SeLe4n/`, `Main.lean` |
| Proofs are not vacuous one-liners | `SELE4N_SPEC.md` | `python3 scripts/check_proof_depth.py` | proof bodies across `SeLe4n/` |
| Every kernel transition is an executable pure function returning explicit success or failure | README, `SELE4N_SPEC.md` | `./scripts/test_tier2_negative.sh` | `SeLe4n/Kernel/*/Operations*.lean` |
| The kernel model is deterministic — the same input trace yields the same output | `SELE4N_SPEC.md` | `./scripts/test_tier2_determinism.sh` | `tests/fixtures/main_trace_smoke.expected` |
| Named theorems and invariants still exist and still say what the docs claim | this file | `./scripts/test_full.sh` (Tier 3) | `scripts/test_tier3_invariant_surface.sh` |
| Production never imports staged modules | `SELE4N_SPEC.md` | `./scripts/check_production_staging_partition.sh` | `scripts/staged_module_allowlist.txt` (62 modules) |
| Every kernel entry the HAL links against is defined — by the built archive, a defined symbol in assembly `build.rs` assembles, or a reconciled expected-unresolved entry — and the boot entry, once exported, calls the checked platform boot | `SELE4N_SPEC.md`, `CLAUDE.md` | `./scripts/check_kernel_entry_exports.py` (Tier 1, after `lake build SeLe4n:static`; `--self-test`, 22 cases) | `nm --defined-only` over `.lake/build/lib/libseLe4n_SeLe4n.a`; every HAL `extern "C"` declaration is required (`classify_link_requirements`), so a rename on either side fails; `asm_definitions_in` (outside cpp conditionals) ∧ `assembled_sources_in` (the live builder chain) ∩ the assembled archive's `nm` definitions when present; `boot_entry_binding_failures` |
| A hardware boot without a verified deployment labeling context fails closed | `SELE4N_SPEC.md` §6.7, `CLAUDE.md` | `lake exe syscall_dispatch_suite` (SD-043/SD-044) | `Platform.FFI.bootAndInitialiseFromPlatform` (mandatory context; guard before commit), `insecureLabelingContextBootError` |
| The labeling a hardware boot installs is bound in the platform contract, admitted and `LabelingContextValid` by construction, its declared separation witnesses are installed threads of the boot state, and neither witness is the binding's boot VSpace root's id | `SELE4N_SPEC.md` §6.7, `CLAUDE.md` | `lake exe syscall_dispatch_suite` (SD-046, SD-055, SD-056); Tier 3 | `PlatformBinding.deploymentLabeling : DeploymentLabeling`, `PlatformBinding.labeling_admitted`, `PlatformBinding.labeling_valid`, `rpi5_deploymentLabeling` (`rfl`), `rpi5LowerWitnessIndex_ne_bootVSpaceRoot`, `PlatformBinding.witnessesOffBootVSpaceRoot` (class obligation), `witnesses_ne_bootVSpaceRoot`, `bootAndInitialisePlatform_eq_checked_boot`, `declaredWitnessesInstalled`, `uninstalledSeparationWitnessBootError` |
| The admitted separation witness names neither the sentinel nor an idle thread | `SELE4N_SPEC.md` §6.7 | `lake exe information_flow_suite` | `separationWitnessAdmissible`, `separationWitnessAdmissible_idleThreadId`, `isInsecureDefaultContext_false_implies_witness_not_idle`, `upperWitnessIndex` |
| The insecure-context guard decides non-triviality rather than sampling for it | `SELE4N_SPEC.md` §6.7 | `lake exe information_flow_suite` | `isInsecureDefaultContext_false_implies_labelNonTriviality`, `deploymentLabelingContext_valid` |
| Every core the binding declares boots with its idle thread enqueued on its own run queue, the RPi5 binding declares every model core, no binding declares more cores than the model has, and an undeclared core's idle slot is absent after the boot | `SELE4N_SPEC.md` §6.5.5, §6.7, `CLAUDE.md` | `lake exe smp_idle_suite`, `lake exe syscall_dispatch_suite` (SD-045, SD-055, SD-056), `lake exe smp_foundations_suite` | `bootFromPlatformCheckedWithIdleThreads_idle_available` (production), `…_idleThreadEnqueuedOnCore` (staged, discharges `schedulerNoStall_smp`'s `hIdle`); `PlatformBinding.declaredCores`, `PlatformBinding.coreCountLe` (class obligation), `declaredCores_length`, `mem_declaredCores_iff`, `bootCoreModelId_mem_declaredCores`, `bootFromPlatformCheckedWithIdleThreadsFor_allCores`, `…For_undeclared_idle_absent`, `rpi5_cores_eq_allCores`, `bootAndInitialisePlatform_rpi5_all_cores` |
| The boot run queue is exactly the idle singleton on every core, so per-core selection succeeds with no hypothesis beyond the boot and first selects idle | `SELE4N_SPEC.md` §6.5.5, `CLAUDE.md` | `lake exe smp_idle_suite`; Tier 3 | `bootFromPlatformCheckedWithIdleThreads_runQueueOnCore_eq`, `…_runQueueOnCore_wellFormed`, `…_runnable_resolve` (production); `…_chooseThreadOnCore_succeeds`, `…_chooseThreadOnCore_idle` (staged) |
| The production boot state is `threadStateConsistent` — a boot-state theorem; the inactive-flag relation the live decisions read is `threadInactiveFlagConsistent`, and its preservation is registered debt — and the checked boot reserves the idle slots and every reference to them — an untyped's allocation and ancestry records included — with its own diagnostic | `SELE4N_SPEC.md` §6.5.5, `CLAUDE.md`, `docs/REGISTERED_DEBT.md` | `lake exe smp_idle_suite`; Tier 3 | `queuedIdleThread`, `bootFromPlatformCheckedWithIdleThreads_threadStateConsistent`, `…_threadInactiveFlagConsistent`, `idleSlotsReserved`, `bootObjectReferencesReservedIdleSlot`, `bootFromPlatformChecked_ok_idleSlotsFreshAt` |
| No syscall can act on a per-core idle TCB: a capability naming one resolves like an empty slot at the single resolution every invoked capability passes through | `SELE4N_SPEC.md` §6.5.5, `CLAUDE.md` | `lake exe syscall_dispatch_suite` (SD-054); Tier 3 | `capTargetsReservedIdleObject`, `syscallResolveCap_ok_not_reserved` |
| The deployment source carries the policy fields a binding configures, with fail-closed defaults and no bearing on validity | `SELE4N_SPEC.md` §6.7 | `lake exe information_flow_suite`; Tier 3 | `DeploymentLabeling.{memoryOwnership,endpointPolicy,declassificationPolicy,auditMonitorClearance}`, `deploymentLabelingContext_policy_fields`, `deploymentLabelingContext_valid` |
| Every hardware seam consults the per-core Lean-runtime readiness gate, over an export inventory derived from the comment-free Lean view | `CLAUDE.md`, `rust/sele4n-hal/src/kernel_entry.rs` | `cargo build -p sele4n-hal` (build.rs derivation; `verify_lean_export_collector`, 6 token-preserving mutations) | `scan_lean_upcalls_readiness_gated`, `lean_code_view`, `lean_exports_in`; `LEAN_UPCALLS_OUTSIDE_THE_GATE` holds one entry, the boot install |
| On a not-ready core every `SVC` halts, before the prefilters and the `x7` narrowing | `CLAUDE.md` | `cargo build -p sele4n-hal` (`svc_arm_readiness_gate_status`), `cargo test` (`readiness_gate_before_mark`, `…_after_mark`) | the gate is a top-level statement of the SVC arm ahead of the `dispatched` binding, on the executing core, ending in the diverging halt |
| The lock-order tripwire halts the holder, never a waiter | `CLAUDE.md` | `cargo test -p sele4n-hal` (`tripwire_trips_on_own_round_lock_hold_only`, `round_lock_records_its_owner`) | `round_lock_held_by`, `assert_not_holding_round_lock(core_id)` |
| Each release-surviving tripwire halts on its declared failure predicate — the whole condition, not a token of it — in every profile, and dominates the operation it protects | `CLAUDE.md`, `docs/REGISTERED_DEBT.md` | `cargo build -p sele4n-hal` (build.rs self-check with polarity and dominance mutations) | `release_surviving_tripwire_status`, `tripwire_dominates_protected_operation`, `RELEASE_SURVIVING_TRIPWIRES`, `verify_release_surviving_tripwire_polarity` |
| A Lean symbol is linker-visible only under `feature = "hw_target"`, decided over the parsed `cfg` predicate | `CLAUDE.md` | `cargo build -p sele4n-hal` (build.rs self-check, 12 token-preserving mutations) | `lean_extern_gating_status`, `cfg_predicate_entailment`, `header_is_linker_visible` |

## 2. Kernel invariants

| Claim | Where it is made | Check it with | Artefact |
|-------|------------------|---------------|----------|
| `ipcInvariantFull` (20 conjuncts) is machine-checked end to end: no bundle in the family assumes a conjunct on its own post-state | `SELE4N_SPEC.md`, GitBook 12 | `python3 scripts/check_ipc_invariant_dethreading.py` | `SeLe4n/Kernel/IPC/Invariant/` |
| The bundle carries across a whole syscall dispatch | `SELE4N_SPEC.md`, GitBook 12 | `lake build SeLe4n.Kernel.API` | `dispatchCapabilityOnly_preserves_ipcInvariantFull` (production); `dispatchWithCap_…` / `dispatchSyscall_…` (staged, `IPC/Invariant/DispatchPayoff.lean`) |
| The dispatch payoff's quiescence packs are inhabited, not vacuous | GitBook 12 | `lake build SeLe4n.Kernel.IPC.Invariant.DispatchPayoff` | `…Quiescence_inhabited` family |
| Capability derivation is acyclic and complete, so revocation terminates and is total | `SELE4N_SPEC.md` | `lake build SeLe4n.Kernel.Capability.Invariant` | `capabilityInvariantBundle` |
| Twelve cross-subsystem predicates hold, including blocking-graph acyclicity | `SELE4N_SPEC.md` | `lake build SeLe4n.Kernel.CrossSubsystem` | `crossSubsystemInvariant` |
| Slot uniqueness and waiter uniqueness are structural, not state predicates | GitBook 12 | `lake build SeLe4n.Model.Object.Structures` | `UniqueSlotMap`, `NoDupList ThreadId` |

## 3. Fault handling

| Claim | Where it is made | Check it with | Artefact |
|-------|------------------|---------------|----------|
| A fault is **delivered**, never returned — no execution path returns a thread to its faulting instruction without handler action | `SELE4N_SPEC.md`, README | `lake exe fault_handling_suite` | `faultDeliverOnCore_not_dispatchable`, `faultDeliverOnCoreChecked_not_dispatchable` |
| Fault delivery is total: no handler, an unresolvable one, missing rights, a denied flow, or an unlinkable reply all converge on a fail-closed suspend | `SELE4N_SPEC.md` | `lake build SeLe4n.Kernel.IPC.CrossCore.Fault` | `IPC/CrossCore/Fault.lean` |
| The live fault entry is the **flow-checked** arm, so a deployment policy can refuse a fault delivery | `SELE4N_SPEC.md` | `./scripts/test_full.sh` (Tier 0/3 pair) | `faultDeliverOnCoreChecked` |
| A kernel-origin exception is never delivered to a user handler | `SELE4N_SPEC.md` | `lake build SeLe4n.Kernel.Architecture.ExceptionModel`; `./scripts/test_aarch64_cross_build.sh` | `.kernelAbort` classification; `halt_if_kernel_origin` in `trap.rs` |
| The fault wire format round-trips and fits the message-register budget | `SELE4N_SPEC.md` | `lake build SeLe4n.Kernel.Architecture.Fault` | `decodeFault_encodeFault`, the length theorem |

## 4. SMP

| Claim | Where it is made | Check it with | Artefact |
|-------|------------------|---------------|----------|
| Per-core scheduler state, selection, wake, timer tick, PIP, domains and CBS are verified per core, not boot-core pinned | `SELE4N_SPEC.md`, README | `./scripts/test_full.sh` | `Scheduler/Invariant/PerCore*.lean` |
| Cross-core IPC — call, reply, notification, cancellation — preserves the IPC bundle | `SELE4N_SPEC.md` | `lake exe smp_ipc_suite` | `IPC/CrossCore/` |
| Every cross-core SchedContext hand-off migrates the CBS replenish queue | `SELE4N_SPEC.md` | `lake exe smp_ipc_suite` | `migrateSchedContextReplenishment`, `replenishQueueAffinityConsistent_smp` |
| TLB shootdown is a verified protocol with bounded wait and generation-tagged descriptors | `SELE4N_SPEC.md` | `lake exe smp_tlb_shootdown_suite` | `Architecture/TlbShootdownProtocol.lean` |
| Non-interference holds per core, and accepted covert channels are enumerated rather than assumed away | `SELE4N_SPEC.md` | `lake exe smp_information_flow_suite` | `acceptedCovertChannel_perCoreCount` |
| Declassification is audited, with causal provenance and refusal recording | `SELE4N_SPEC.md` | `lake exe smp_information_flow_suite` | `InformationFlow/Declassification*.lean` |
| The WS-SM theorem total is measured, not hand-summed — **903 theorems** across 1113 registered entries (210 are `def`s) | `SELE4N_SPEC.md`, GitBook 12 | `python3 scripts/generate_smp_theorem_manifest.py --check`; `lake build SeLe4n.Kernel.Concurrency.PhaseTheoremManifest` | `docs/smp_theorem_manifest.json` |

## 5. Data structures and performance

| Claim | Where it is made | Check it with | Artefact |
|-------|------------------|---------------|----------|
| The object store is a verified Robin Hood hash table with proven O(1) lookup, not a benchmarked one | README, `SELE4N_SPEC.md` | `lake exe robin_hood_suite` | `RHTable.invExt`, `allTablesInvExtK` |
| The CNode radix tree is verified flat-array, with the same treatment | `SELE4N_SPEC.md` | `lake exe radix_tree_suite` | `Kernel/RadixTree/` |

## 6. Hardware and build

| Claim | Where it is made | Check it with | Artefact |
|-------|------------------|---------------|----------|
| The HAL compiles **and generates code** for `aarch64-unknown-none` in both profiles, with the three `.S` sources assembled and clippy denied | README, `CI_POLICY.md` | `./scripts/test_aarch64_cross_build.sh` | CI job `aarch64 Cross Build` |
| The cross target cannot be silently dropped or weakened to a `check` | `CI_POLICY.md` | `python3 scripts/check_aarch64_cross_target.py` | 14-case self-test |
| Broadcast TLB maintenance is confined and the non-IS variants are gated | `SELE4N_SPEC.md` | `python3 scripts/check_tlbi_broadcast_discipline.py` | `scripts/tlbi_local_allowlist.txt`, `rust/sele4n-hal/src/tlb.rs` |
| No third-party code is linked into the runtime kernel binary | README, `THIRD_PARTY_LICENSES.md` | `./scripts/test_rust.sh` | `rust/` is `#![no_std]`, `core::*` only |

## 7. Process

| Claim | Where it is made | Check it with | Artefact |
|-------|------------------|---------------|----------|
| Every version-bearing site agrees with `lakefile.toml` | `DEVELOPMENT.md` §8 | `./scripts/check_version_sync.sh` | 36 sites, `scripts/version_locations.sh` |
| Every deferred item has an owner and a closure target | `DEVELOPMENT.md` §6 | `python3 scripts/check_deferral_registration.py` | *Registered debt index*, `REGISTERED_DEBT.md` |
| Every plan's numbering, counts and cross-references are consistent | `DEVELOPMENT.md` §11 | `python3 scripts/check_workstream_plan.py` | `docs/planning/` |
| No identifier or path encodes a workstream code | `DEVELOPMENT.md` §6 | `python3 scripts/check_identifier_naming.py` | `scripts/identifier_naming_baseline.json` |
| A gate that cannot run is reported NOT RUN, never PASS | `CI_POLICY.md` | `SELE4N_REQUIRE_GATES=1 ./scripts/test_tier4_smp_bootcheck.sh` | `scripts/test_gate_skip_accounting.sh` |
| Website-linked paths still exist | `DEVELOPMENT.md` §9 | `./scripts/check_website_links.sh` | `scripts/website_link_manifest.txt` |

## 8. What is **not** claimed

Stating these is part of the point of this index. Each is registered debt with
an owner, not an oversight.

| Not claimed | Why | Owner |
|-------------|-----|-------|
| That the kernel boots on hardware | No bootable image exists: no `[[bin]]`, no aarch64 Lean object code, no bare-metal runtime hosting. Every runtime seam behind the readiness gate is wired and dormant | SM10.1 |
| That per-object fine locks are deployed | SM3.C.9 is deferred: the `@[export]` bodies are, with one exception, not yet wrapped in `withLockSet`, so fine locks are a model-level discipline | WS-RR RR7 |
| Unconditional SMP starvation-freedom | The WCRT capstones take `hBandProgress` as an externalized deployment hypothesis, and the liveness trace model is still boot-core pinned | WS-SL |
| That the deployed RwLock is the one the Lean FIFO spec describes | `lock_bridge.rs` builds its pool from the CAS-retry lock; the FIFO `QueuedRwLock` has no consumers outside its own module | WS-RR RR6 |
| That live WCRT matches the fine-lock bound | Kernel entry is serialised by one global ticket lock, so the live bound is weaker than `PerCoreWcrt.lean`'s | SM10.1 |
| That Tier 4 acceptance gates have passed | They need the bootable image, so they have never executed. They report NOT RUN rather than PASS | SM10.1 |
| That a fault message's `MR4` onward reaches a handler on hardware | No receive path writes past `MR3` into the IPC buffer yet | WS-RR |

## Proof claim qualification

Not every theorem carries the same assurance.  A claim about proof coverage
must say which of these it means, because "N theorems" hides the difference.

| Category | Description | Assurance level |
|---|---|---|
| **Substantive preservation** | Proves that a *successful* operation preserves an invariant over *changed* state. | High |
| **Error-case preservation** | Proves that a *failed* operation preserves an invariant by returning unchanged state. Trivially true. | Low (technically correct but not security evidence) |
| **Compositional preservation** | Derives post-state invariant from pre-state through operation-specific transfer lemmas (`cspaceSlotUnique_of_storeObject_*`, `CNode.insert_slotsUnique`, etc.). (WS-E2 H-01 resolved: all preservation proofs refactored to this pattern.) | High |
| **Structural invariant** | Proves a genuine structural property requiring a witness (e.g., `capabilityInvariantBundle_of_slotUnique` requires `CNode.slotsUnique` evidence). (WS-E2 C-01 resolved: former tautological proofs reformulated. WS-G5: `slotsUnique` now trivially true — HashMap key uniqueness is structural.) | High |
| **End-to-end chain** | Proves a multi-step semantic property across subsystem boundaries (e.g., `badge_notification_routing_consistent` — badge propagation from mint through notification signal/wait). (WS-E2 H-03 resolved.) | High |
| **Non-interference** | Proves that a high-domain operation preserves low-equivalence for unrelated observers. | Critical for security assurance |

## Update policy

When a claim changes:

1. update the canonical root source first;
2. update the GitBook mirror(s) in the same PR;
3. refresh the row here;
4. run at least `./scripts/test_smoke.sh` (`./scripts/test_full.sh` when Tier-3
   anchors or policies changed).

A claim that loses its evidence command loses its row. A claim the tree no
longer supports moves to §8 with an owner — it is not quietly deleted.
