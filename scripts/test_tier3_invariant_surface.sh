#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck disable=SC1091
source "${SCRIPT_DIR}/test_lib.sh"

parse_common_args "$@"
cd "${REPO_ROOT}"

# M6 WS-M6-A assumption inventory anchors.
# WS-B1 closure anchors: VSpace transitions, invariants, and ADR publication.
run_check "INVARIANT" rg -n '^structure VSpaceRoot' SeLe4n/Model/Object.lean
run_check "INVARIANT" rg -n '^def vspaceDiscoveryWindow' SeLe4n/Kernel/Architecture/VSpace.lean
run_check "INVARIANT" rg -n '^def vspaceMapPage' SeLe4n/Kernel/Architecture/VSpace.lean
run_check "INVARIANT" rg -n '^def vspaceUnmapPage' SeLe4n/Kernel/Architecture/VSpace.lean
run_check "INVARIANT" rg -n '^def vspaceLookup' SeLe4n/Kernel/Architecture/VSpace.lean
run_check "INVARIANT" rg -n '^theorem vspaceLookup_deterministic' SeLe4n/Kernel/Architecture/VSpace.lean
run_check "INVARIANT" rg -n '^def vspaceInvariantBundle' SeLe4n/Kernel/Architecture/VSpaceInvariant.lean
run_check "DOC" rg -n '^# ADR: WS-B1 VSpace \+ Bounded Memory Model Foundation' docs/VSPACE_MEMORY_MODEL_ADR.md
run_check "DOC" rg -n '^# WS-B1 ADR: VSpace \+ Bounded Memory Model Foundation' docs/gitbook/26-ws-b1-vspace-memory-adr.md
# WS-B4 closure anchors: wrapper structures must remain explicit.
run_check "INVARIANT" rg -n '^structure DomainId' SeLe4n/Prelude.lean
run_check "INVARIANT" rg -n '^structure Priority' SeLe4n/Prelude.lean
run_check "INVARIANT" rg -n '^structure Irq' SeLe4n/Prelude.lean
run_check "INVARIANT" rg -n '^structure Badge' SeLe4n/Prelude.lean
run_check "INVARIANT" rg -n '^structure ASID' SeLe4n/Prelude.lean
run_check "INVARIANT" rg -n '^structure VAddr' SeLe4n/Prelude.lean
run_check "INVARIANT" rg -n '^structure PAddr' SeLe4n/Prelude.lean
# WS-B5 closure anchors: CSpace guard/radix path resolution surface.
run_check "INVARIANT" rg -n '^inductive ResolveError' SeLe4n/Model/Object.lean
run_check "INVARIANT" rg -n '^def resolveSlot' SeLe4n/Model/Object.lean
run_check "INVARIANT" rg -n '^def cspaceResolvePath' SeLe4n/Kernel/Capability/Operations.lean
run_check "INVARIANT" rg -n '^def cspaceLookupPath' SeLe4n/Kernel/Capability/Operations.lean
run_check "DOC" rg -n '^### WS-B5 — CSpace semantics completion \(Completed\)' docs/audits/COMPREHENSIVE_AUDIT_2026_02_WORKSTREAM_PLAN.md

# WS-B6 closure anchors: notification IPC object model and transition surface.
run_check "INVARIANT" rg -n '^inductive NotificationState' SeLe4n/Model/Object.lean
run_check "INVARIANT" rg -n '^structure Notification' SeLe4n/Model/Object.lean
run_check "INVARIANT" rg -n '^def notificationSignal' SeLe4n/Kernel/IPC/Operations.lean
run_check "INVARIANT" rg -n '^def notificationWait' SeLe4n/Kernel/IPC/Operations.lean
run_check "INVARIANT" rg -n '^def notificationInvariant' SeLe4n/Kernel/IPC/Invariant.lean
run_check "DOC" rg -n '^### WS-B6 — IPC completeness with notifications \(Completed\)' docs/audits/COMPREHENSIVE_AUDIT_2026_02_WORKSTREAM_PLAN.md

# WS-B7 closure anchors: information-flow policy/projection baseline and milestone docs.
run_check "INVARIANT" rg -n '^inductive Confidentiality' SeLe4n/Kernel/InformationFlow/Policy.lean
run_check "INVARIANT" rg -n '^structure SecurityLabel' SeLe4n/Kernel/InformationFlow/Policy.lean
run_check "INVARIANT" rg -n '^def securityFlowsTo' SeLe4n/Kernel/InformationFlow/Policy.lean
run_check "INVARIANT" rg -n '^theorem securityFlowsTo_trans' SeLe4n/Kernel/InformationFlow/Policy.lean
run_check "INVARIANT" rg -n '^def projectState' SeLe4n/Kernel/InformationFlow/Projection.lean
run_check "INVARIANT" rg -n '^def lowEquivalent' SeLe4n/Kernel/InformationFlow/Projection.lean
run_check "INVARIANT" rg -n '^theorem lowEquivalent_trans' SeLe4n/Kernel/InformationFlow/Projection.lean
run_check "INVARIANT" rg -n '^private def runInformationFlowChecks' tests/InformationFlowSuite.lean
run_check "INVARIANT" rg -n '^run_check "TRACE" lake exe information_flow_suite' scripts/test_tier2_negative.sh
run_check "DOC" rg -n '^### WS-B7 — Information-flow proof track start \(Completed\)' docs/audits/COMPREHENSIVE_AUDIT_2026_02_WORKSTREAM_PLAN.md
run_check "DOC" rg -n '^## IF-M1 — Policy lattice and labeling primitives ✅ completed \(WS-B7\)' docs/INFORMATION_FLOW_ROADMAP.md
run_check "DOC" rg -n '^# IF-M1 Baseline Package \(WS-B7\)' docs/IF_M1_BASELINE_PACKAGE.md
run_check "DOC" rg -n '^- \*\*Current completed slice:\*\* Comprehensive Audit 2026-02 execution \(WS-B portfolio; WS-B1 through WS-B11 completed\)\.' README.md
run_check "DOC" rg -n '^- \*\*Current completed slice:\*\* post-M7 comprehensive-audit execution portfolio \(WS-B1 through WS-B11 complete\)\.' docs/SEL4_SPEC.md
run_check "DOC" rg -n '^- \*\*Comprehensive Audit 2026-02 execution \(WS-B portfolio\)\*\* with WS-B1 through WS-B11 completed\.' docs/gitbook/01-project-overview.md
run_check "DOC" rg -n '^- \*\*Phase P2:\*\* WS-B5, WS-B6, WS-B2 \(WS-B1/WS-B2/WS-B5/WS-B6 complete; WS-B7 completed\)' docs/gitbook/06-development-workflow.md
run_check "DOC" rg -n '^- \*\*Phase P2:\*\* WS-B5 \+ WS-B6 \+ WS-B2 \(WS-B1/WS-B2/WS-B5/WS-B6 complete; WS-B7 completed\)' docs/gitbook/24-comprehensive-audit-2026-workstream-planning.md
run_check "DOC" rg -n '^1\. Sync branch and choose one coherent WS-B slice \(prefer the next documented priority in the active plan \(all WS-B streams are complete\)\)\.' docs/DEVELOPMENT.md
run_check "DOC" rg -n '^### WS-B8 — Documentation automation \+ consolidation \(Completed\)' docs/audits/COMPREHENSIVE_AUDIT_2026_02_WORKSTREAM_PLAN.md
run_check "DOC" rg -n '^### WS-B9 — Threat model and security hardening \(Completed\)' docs/audits/COMPREHENSIVE_AUDIT_2026_02_WORKSTREAM_PLAN.md
run_check "DOC" rg -n '^# Threat Model and Security Hardening Baseline \(WS-B9\)' docs/THREAT_MODEL.md
run_check "DOC" rg -n '^# Threat Model and Security Hardening \(WS-B9\)' docs/gitbook/28-threat-model-and-security-hardening.md
run_check "INVARIANT" rg -n '^ELAN_INSTALLER_SHA256=' scripts/setup_lean_env.sh
run_check "INVARIANT" rg -n '^compute_sha256\(\)' scripts/setup_lean_env.sh
# shellcheck disable=SC2016
run_check "DOC" rg -n '^- Active planning baseline: `COMPREHENSIVE_AUDIT_2026_02_WORKSTREAM_PLAN.md` \(WS-B11 completed\)\.' docs/DOCUMENTATION_SYNC_AND_COVERAGE_MATRIX.md
run_check "DOC" rg -n '^# Documentation Deduplication Map \(WS-B8\)' docs/DOCS_DEDUPLICATION_MAP.md
run_check "DOC" rg -n '^# Documentation Deduplication Map' docs/gitbook/27-documentation-deduplication-map.md
run_check "INVARIANT" rg -n '^#!/usr/bin/env python3' scripts/generate_doc_navigation.py
run_check "INVARIANT" rg -n '^#!/usr/bin/env python3' scripts/check_markdown_links.py
run_check "INVARIANT" rg -n '^run_check "HYGIENE" "\$\{SCRIPT_DIR\}/test_docs_sync\.sh"' scripts/test_tier0_hygiene.sh
run_check "INVARIANT" rg -n '^[[:space:]]+name: Docs Automation / Navigation \+ Links \+ DocGen Probe' .github/workflows/lean_action_ci.yml

# WS-B2 closure anchors: bootstrap DSL, negative suite, and nightly replay artifacts.
run_check "INVARIANT" rg -n '^structure BootstrapBuilder' SeLe4n/Testing/StateBuilder.lean
run_check "INVARIANT" rg -n '^def build \(builder : BootstrapBuilder\)' SeLe4n/Testing/StateBuilder.lean
run_check "INVARIANT" rg -n '^private def runNegativeChecks' tests/NegativeStateSuite.lean
run_check "INVARIANT" rg -n '^run_check "TRACE" lake exe negative_state_suite' scripts/test_tier2_negative.sh
run_check "INVARIANT" rg -n 'trace_sequence_probe_manifest\.csv' scripts/test_tier4_nightly_candidates.sh
run_check "INVARIANT" rg -n '^def runMainTrace' SeLe4n/Testing/MainTraceHarness.lean
run_check "INVARIANT" rg -n '^def bootstrapState' SeLe4n/Testing/MainTraceHarness.lean
run_check "INVARIANT" rg -n "^private def runCapabilityAndArchitectureTrace" SeLe4n/Testing/MainTraceHarness.lean
run_check "INVARIANT" rg -n "^private def runServiceAndStressTrace" SeLe4n/Testing/MainTraceHarness.lean
run_check "INVARIANT" rg -n "^private def runLifecycleAndEndpointTrace" SeLe4n/Testing/MainTraceHarness.lean


# M6 WS-M6-B adapter API anchors.
run_check "INVARIANT" rg -n '^inductive AdapterErrorKind' SeLe4n/Kernel/Architecture/Adapter.lean
run_check "INVARIANT" rg -n '^def mapAdapterError' SeLe4n/Kernel/Architecture/Adapter.lean
run_check "INVARIANT" rg -n '^def adapterAdvanceTimer' SeLe4n/Kernel/Architecture/Adapter.lean
run_check "INVARIANT" rg -n '^def adapterWriteRegister' SeLe4n/Kernel/Architecture/Adapter.lean
run_check "INVARIANT" rg -n '^def adapterReadMemory' SeLe4n/Kernel/Architecture/Adapter.lean
run_check "INVARIANT" rg -n '^theorem adapterAdvanceTimer_deterministic' SeLe4n/Kernel/Architecture/Adapter.lean
run_check "INVARIANT" rg -n '^def proofLayerInvariantBundle' SeLe4n/Kernel/Architecture/Invariant.lean
run_check "INVARIANT" rg -n '^structure AdapterProofHooks' SeLe4n/Kernel/Architecture/Invariant.lean
run_check "INVARIANT" rg -n '^theorem adapterAdvanceTimer_ok_preserves_proofLayerInvariantBundle' SeLe4n/Kernel/Architecture/Invariant.lean
run_check "INVARIANT" rg -n '^theorem adapterWriteRegister_ok_preserves_proofLayerInvariantBundle' SeLe4n/Kernel/Architecture/Invariant.lean
run_check "INVARIANT" rg -n '^theorem adapterReadMemory_ok_preserves_proofLayerInvariantBundle' SeLe4n/Kernel/Architecture/Invariant.lean
run_check "INVARIANT" rg -n '^theorem adapterAdvanceTimer_error_invalidContext_preserves_proofLayerInvariantBundle' SeLe4n/Kernel/Architecture/Invariant.lean
run_check "INVARIANT" rg -n '^theorem adapterAdvanceTimer_error_unsupportedBinding_preserves_proofLayerInvariantBundle' SeLe4n/Kernel/Architecture/Invariant.lean
run_check "INVARIANT" rg -n '^theorem adapterWriteRegister_error_unsupportedBinding_preserves_proofLayerInvariantBundle' SeLe4n/Kernel/Architecture/Invariant.lean
run_check "INVARIANT" rg -n '^theorem adapterReadMemory_error_unsupportedBinding_preserves_proofLayerInvariantBundle' SeLe4n/Kernel/Architecture/Invariant.lean
run_check "INVARIANT" rg -n '^import SeLe4n\.Kernel\.Architecture\.Invariant$' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n '^import SeLe4n\.Kernel\.Architecture\.Invariant$' SeLe4n.lean

run_check "INVARIANT" rg -n '^inductive ArchAssumption' SeLe4n/Kernel/Architecture/Assumptions.lean
run_check "INVARIANT" rg -n '^structure BootBoundaryContract' SeLe4n/Kernel/Architecture/Assumptions.lean
run_check "INVARIANT" rg -n '^structure RuntimeBoundaryContract' SeLe4n/Kernel/Architecture/Assumptions.lean
run_check "INVARIANT" rg -n "^\s*timerMonotonicDecidable\s*:" SeLe4n/Kernel/Architecture/Assumptions.lean
run_check "INVARIANT" rg -n "^\s*registerContextStableDecidable\s*:" SeLe4n/Kernel/Architecture/Assumptions.lean
run_check "INVARIANT" rg -n "^\s*memoryAccessAllowedDecidable\s*:" SeLe4n/Kernel/Architecture/Assumptions.lean
run_check "INVARIANT" rg -n '^structure InterruptBoundaryContract' SeLe4n/Kernel/Architecture/Assumptions.lean
run_check "INVARIANT" rg -n '^inductive ContractRef' SeLe4n/Kernel/Architecture/Assumptions.lean
run_check "INVARIANT" rg -n '^def assumptionContractMap' SeLe4n/Kernel/Architecture/Assumptions.lean
run_check "INVARIANT" rg -n '^def assumptionTransitionMap' SeLe4n/Kernel/Architecture/Assumptions.lean
run_check "INVARIANT" rg -n '^def assumptionInvariantMap' SeLe4n/Kernel/Architecture/Assumptions.lean
run_check "INVARIANT" rg -n '^theorem assumptionContractMap_nonempty' SeLe4n/Kernel/Architecture/Assumptions.lean
run_check "INVARIANT" rg -n '^theorem assumptionTransitionMap_nonempty' SeLe4n/Kernel/Architecture/Assumptions.lean
run_check "INVARIANT" rg -n '^theorem assumptionInvariantMap_nonempty' SeLe4n/Kernel/Architecture/Assumptions.lean


# WS-A5 closure anchors: test-only contract fixture separation + policy visibility.
run_check "INVARIANT" rg -n '^import SeLe4n\.Testing\.MainTraceHarness$' Main.lean
run_check "INVARIANT" rg -n '^import SeLe4n\.Testing\.RuntimeContractFixtures$' SeLe4n/Testing/MainTraceHarness.lean
run_check "INVARIANT" rg -n '^def runtimeContractAcceptAll' SeLe4n/Testing/RuntimeContractFixtures.lean
run_check "INVARIANT" rg -n '^def runtimeContractDenyAll' SeLe4n/Testing/RuntimeContractFixtures.lean
run_check "DOC" rg -n '^# Hardware Boundary Contract Policy' docs/HARDWARE_BOUNDARY_CONTRACT_POLICY.md
run_check "DOC" rg -n 'SeLe4n/Kernel.*must not reference test-only runtime contract' docs/HARDWARE_BOUNDARY_CONTRACT_POLICY.md
run_check "DOC" rg -n 'scripts/test_tier0_hygiene\.sh' docs/HARDWARE_BOUNDARY_CONTRACT_POLICY.md

# WS-A3 boundary hardening anchors must remain explicit.
run_check "INVARIANT" rg -n '^@\[inline\] def toObjId' SeLe4n/Prelude.lean
run_check "INVARIANT" bash -lc "if rg -n '^instance : Coe ThreadId ObjId where' SeLe4n/Prelude.lean; then echo 'Implicit ThreadId -> ObjId coercion must remain absent.' >&2; exit 1; fi"

# Invariant bundle surface anchors (M1/M2/M3 composed entrypoints).
run_check "INVARIANT" rg -n '^(def|abbrev) schedulerInvariantBundle' SeLe4n/Kernel/Scheduler/Invariant.lean
run_check "INVARIANT" rg -n '^def capabilityInvariantBundle' SeLe4n/Kernel/Capability/Invariant.lean
run_check "INVARIANT" rg -n '^def m3IpcSeedInvariantBundle' SeLe4n/Kernel/Capability/Invariant.lean

# M1 closure anchors: scheduler transition APIs + preservation theorem entrypoints.
run_check "INVARIANT" rg -n '^def chooseThread' SeLe4n/Kernel/Scheduler/Operations.lean
run_check "INVARIANT" rg -n '^def schedule' SeLe4n/Kernel/Scheduler/Operations.lean
run_check "INVARIANT" rg -n '^def handleYield' SeLe4n/Kernel/Scheduler/Operations.lean
run_check "INVARIANT" rg -n '^theorem chooseThread_preserves_schedulerInvariantBundle' SeLe4n/Kernel/Scheduler/Operations.lean
run_check "INVARIANT" rg -n '^theorem schedule_preserves_schedulerInvariantBundle' SeLe4n/Kernel/Scheduler/Operations.lean
run_check "INVARIANT" rg -n '^theorem handleYield_preserves_schedulerInvariantBundle' SeLe4n/Kernel/Scheduler/Operations.lean

# M2 closure anchors: CSpace transition APIs + capability-bundle preservation theorem entrypoints.
run_check "INVARIANT" rg -n '^def cspaceLookupSlot' SeLe4n/Kernel/Capability/Operations.lean
run_check "INVARIANT" rg -n '^def cspaceInsertSlot' SeLe4n/Kernel/Capability/Operations.lean
run_check "INVARIANT" rg -n '^def cspaceMint' SeLe4n/Kernel/Capability/Operations.lean
run_check "INVARIANT" rg -n '^def cspaceDeleteSlot' SeLe4n/Kernel/Capability/Operations.lean
run_check "INVARIANT" rg -n '^def cspaceRevoke' SeLe4n/Kernel/Capability/Operations.lean
run_check "INVARIANT" rg -n '^theorem cspaceInsertSlot_preserves_capabilityInvariantBundle' SeLe4n/Kernel/Capability/Invariant.lean
run_check "INVARIANT" rg -n '^theorem cspaceMint_preserves_capabilityInvariantBundle' SeLe4n/Kernel/Capability/Invariant.lean
run_check "INVARIANT" rg -n '^theorem cspaceDeleteSlot_preserves_capabilityInvariantBundle' SeLe4n/Kernel/Capability/Invariant.lean
run_check "INVARIANT" rg -n '^theorem cspaceRevoke_preserves_capabilityInvariantBundle' SeLe4n/Kernel/Capability/Invariant.lean

# M3 seed IPC preservation theorem anchors.
run_check "INVARIANT" rg -n '^theorem endpointSend_preserves_m3IpcSeedInvariantBundle' SeLe4n/Kernel/Capability/Invariant.lean
run_check "INVARIANT" rg -n '^theorem endpointReceive_preserves_m3IpcSeedInvariantBundle' SeLe4n/Kernel/Capability/Invariant.lean

# M3.5 step-2 transition anchors must remain present.
run_check "INVARIANT" rg -n '^def endpointSend' SeLe4n/Kernel/IPC/Operations.lean
run_check "INVARIANT" rg -n '^def endpointAwaitReceive' SeLe4n/Kernel/IPC/Operations.lean
run_check "INVARIANT" rg -n '^def endpointReceive' SeLe4n/Kernel/IPC/Operations.lean
run_check "INVARIANT" rg -n '^theorem endpointAwaitReceive_preserves_m3IpcSeedInvariantBundle' SeLe4n/Kernel/Capability/Invariant.lean

# M3.5 step-3 scheduler-contract predicate anchors must remain present.
run_check "INVARIANT" rg -n '^def runnableThreadIpcReady' SeLe4n/Kernel/IPC/Invariant.lean
run_check "INVARIANT" rg -n '^def blockedOnSendNotRunnable' SeLe4n/Kernel/IPC/Invariant.lean
run_check "INVARIANT" rg -n '^def blockedOnReceiveNotRunnable' SeLe4n/Kernel/IPC/Invariant.lean
run_check "INVARIANT" rg -n '^def ipcSchedulerContractPredicates' SeLe4n/Kernel/IPC/Invariant.lean
run_check "INVARIANT" rg -n '^theorem endpointSend_preserves_ipcSchedulerContractPredicates' SeLe4n/Kernel/IPC/Invariant.lean
run_check "INVARIANT" rg -n '^theorem endpointAwaitReceive_preserves_ipcSchedulerContractPredicates' SeLe4n/Kernel/IPC/Invariant.lean
run_check "INVARIANT" rg -n '^theorem endpointReceive_preserves_ipcSchedulerContractPredicates' SeLe4n/Kernel/IPC/Invariant.lean

# M3.5 step-4 composed bundle anchors must remain present.
run_check "INVARIANT" rg -n '^def ipcSchedulerRunnableReadyComponent' SeLe4n/Kernel/Capability/Invariant.lean
run_check "INVARIANT" rg -n '^def ipcSchedulerBlockedSendComponent' SeLe4n/Kernel/Capability/Invariant.lean
run_check "INVARIANT" rg -n '^def ipcSchedulerBlockedReceiveComponent' SeLe4n/Kernel/Capability/Invariant.lean
run_check "INVARIANT" rg -n '^def ipcSchedulerCoherenceComponent' SeLe4n/Kernel/Capability/Invariant.lean
run_check "INVARIANT" rg -n '^theorem ipcSchedulerCoherenceComponent_iff_contractPredicates' SeLe4n/Kernel/Capability/Invariant.lean
run_check "INVARIANT" rg -n '^def m35IpcSchedulerInvariantBundle' SeLe4n/Kernel/Capability/Invariant.lean
run_check "INVARIANT" rg -n '^theorem endpointSend_preserves_m35IpcSchedulerInvariantBundle' SeLe4n/Kernel/Capability/Invariant.lean
run_check "INVARIANT" rg -n '^theorem endpointAwaitReceive_preserves_m35IpcSchedulerInvariantBundle' SeLe4n/Kernel/Capability/Invariant.lean
run_check "INVARIANT" rg -n '^theorem endpointReceive_preserves_m35IpcSchedulerInvariantBundle' SeLe4n/Kernel/Capability/Invariant.lean

# M3.5 step-6 local-first preservation-theorem anchors must remain present.
run_check "INVARIANT" rg -n '^theorem endpointSend_preserves_runnableThreadIpcReady' SeLe4n/Kernel/IPC/Invariant.lean
run_check "INVARIANT" rg -n '^theorem endpointSend_preserves_blockedOnSendNotRunnable' SeLe4n/Kernel/IPC/Invariant.lean
run_check "INVARIANT" rg -n '^theorem endpointSend_preserves_blockedOnReceiveNotRunnable' SeLe4n/Kernel/IPC/Invariant.lean
run_check "INVARIANT" rg -n '^theorem endpointAwaitReceive_preserves_runnableThreadIpcReady' SeLe4n/Kernel/IPC/Invariant.lean
run_check "INVARIANT" rg -n '^theorem endpointAwaitReceive_preserves_blockedOnSendNotRunnable' SeLe4n/Kernel/IPC/Invariant.lean
run_check "INVARIANT" rg -n '^theorem endpointAwaitReceive_preserves_blockedOnReceiveNotRunnable' SeLe4n/Kernel/IPC/Invariant.lean
run_check "INVARIANT" rg -n '^theorem endpointReceive_preserves_runnableThreadIpcReady' SeLe4n/Kernel/IPC/Invariant.lean
run_check "INVARIANT" rg -n '^theorem endpointReceive_preserves_blockedOnSendNotRunnable' SeLe4n/Kernel/IPC/Invariant.lean
run_check "INVARIANT" rg -n '^theorem endpointReceive_preserves_blockedOnReceiveNotRunnable' SeLe4n/Kernel/IPC/Invariant.lean

# M3.5 step-5 helper-lemma anchors must remain present.
run_check "INVARIANT" rg -n '^theorem tcb_lookup_of_endpoint_store' SeLe4n/Kernel/IPC/Invariant.lean
run_check "INVARIANT" rg -n '^theorem runnable_membership_of_endpoint_store' SeLe4n/Kernel/IPC/Invariant.lean
run_check "INVARIANT" rg -n '^theorem not_runnable_membership_of_endpoint_store' SeLe4n/Kernel/IPC/Invariant.lean

# Bundle composition guard: M3 seed bundle must still compose scheduler + capability + IPC invariants.
run_check "INVARIANT" rg -n '^\s*schedulerInvariantBundle st ∧ capabilityInvariantBundle st ∧ ipcInvariant st' SeLe4n/Kernel/Capability/Invariant.lean

# M3.5 step-1 state-model anchors must remain present.
run_check "INVARIANT" rg -n '^inductive ThreadIpcState' SeLe4n/Model/Object.lean
run_check "INVARIANT" rg -n '^\s*ipcState\s*:\s*ThreadIpcState' SeLe4n/Model/Object.lean
run_check "INVARIANT" rg -n '^\s*waitingReceiver\s*:\s*Option SeLe4n\.ThreadId' SeLe4n/Model/Object.lean
run_check "INVARIANT" rg -n '^def endpointQueueWellFormed' SeLe4n/Kernel/IPC/Invariant.lean
run_check "INVARIANT" rg -n '^def endpointObjectValid' SeLe4n/Kernel/IPC/Invariant.lean


# M4-A step-1 lifecycle metadata anchors must remain present.
run_check "INVARIANT" rg -n '^structure LifecycleMetadata' SeLe4n/Model/State.lean
run_check "INVARIANT" rg -n '^def lifecycleMetadataConsistent' SeLe4n/Model/State.lean
run_check "INVARIANT" rg -n '^def cspaceRevoke' SeLe4n/Kernel/Capability/Operations.lean
run_check "INVARIANT" rg -n '^theorem cspaceRevoke_local_target_reduction' SeLe4n/Kernel/Capability/Invariant.lean

# M4-A step-3 lifecycle invariant layering anchors must remain present.
run_check "INVARIANT" rg -n '^def lifecycleIdentityAliasingInvariant' SeLe4n/Kernel/Lifecycle/Invariant.lean
run_check "INVARIANT" rg -n '^def lifecycleCapabilityReferenceInvariant' SeLe4n/Kernel/Lifecycle/Invariant.lean
run_check "INVARIANT" rg -n '^def lifecycleCapabilityRefObjectTargetBacked' SeLe4n/Kernel/Lifecycle/Invariant.lean
run_check "INVARIANT" rg -n '^def lifecycleInvariantBundle' SeLe4n/Kernel/Lifecycle/Invariant.lean
run_check "INVARIANT" rg -n '^theorem lifecycleCapabilityRefObjectTargetBacked_of_exact' SeLe4n/Kernel/Lifecycle/Invariant.lean
run_check "INVARIANT" rg -n '^theorem lifecycleInvariantBundle_of_metadata_consistent' SeLe4n/Kernel/Lifecycle/Invariant.lean

# M4-B WS-B invariant hardening anchors must remain present.
run_check "INVARIANT" rg -n '^def lifecycleCapabilityRefObjectTargetTypeAligned' SeLe4n/Kernel/Lifecycle/Invariant.lean
run_check "INVARIANT" rg -n '^def lifecycleCapabilityRefNoTypeAliasConflict' SeLe4n/Kernel/Lifecycle/Invariant.lean
run_check "INVARIANT" rg -n '^def lifecycleStaleReferenceExclusionInvariant' SeLe4n/Kernel/Lifecycle/Invariant.lean
run_check "INVARIANT" rg -n '^def lifecycleIdentityStaleReferenceInvariant' SeLe4n/Kernel/Lifecycle/Invariant.lean
run_check "INVARIANT" rg -n '^theorem lifecycleCapabilityRefObjectTargetTypeAligned_of_exact' SeLe4n/Kernel/Lifecycle/Invariant.lean
run_check "INVARIANT" rg -n '^theorem lifecycleCapabilityRefNoTypeAliasConflict_of_identity' SeLe4n/Kernel/Lifecycle/Invariant.lean
run_check "INVARIANT" rg -n '^theorem lifecycleStaleReferenceExclusionInvariant_of_lifecycleInvariantBundle' SeLe4n/Kernel/Lifecycle/Invariant.lean
run_check "INVARIANT" rg -n '^theorem lifecycleRetypeObject_preserves_lifecycleStaleReferenceExclusionInvariant' SeLe4n/Kernel/Lifecycle/Invariant.lean
run_check "INVARIANT" rg -n '^theorem lifecycleRetypeObject_preserves_lifecycleIdentityStaleReferenceInvariant' SeLe4n/Kernel/Lifecycle/Invariant.lean
run_check "INVARIANT" rg -n '^def lifecycleCapabilityStaleAuthorityInvariant' SeLe4n/Kernel/Capability/Invariant.lean
run_check "INVARIANT" rg -n '^theorem lifecycleCapabilityStaleAuthorityInvariant_of_bundles' SeLe4n/Kernel/Capability/Invariant.lean

# M4-A step-5 lifecycle preservation entrypoint anchors must remain present.
run_check "INVARIANT" rg -n '^theorem lifecycleRetypeObject_preserves_lifecycleInvariantBundle' SeLe4n/Kernel/Lifecycle/Invariant.lean
run_check "INVARIANT" rg -n '^def m4aLifecycleInvariantBundle' SeLe4n/Kernel/Capability/Invariant.lean
run_check "INVARIANT" rg -n '^theorem lifecycleRetypeObject_preserves_schedulerInvariantBundle' SeLe4n/Kernel/Capability/Invariant.lean
run_check "INVARIANT" rg -n '^theorem lifecycleRetypeObject_preserves_capabilityInvariantBundle' SeLe4n/Kernel/Capability/Invariant.lean
run_check "INVARIANT" rg -n '^theorem lifecycleRetypeObject_preserves_ipcInvariant' SeLe4n/Kernel/Capability/Invariant.lean
run_check "INVARIANT" rg -n '^theorem lifecycleRetypeObject_preserves_m3IpcSeedInvariantBundle' SeLe4n/Kernel/Capability/Invariant.lean
run_check "INVARIANT" rg -n '^theorem lifecycleRetypeObject_preserves_m4aLifecycleInvariantBundle' SeLe4n/Kernel/Capability/Invariant.lean

# M4-B WS-C preservation theorem expansion anchors must remain present.
run_check "INVARIANT" rg -n '^theorem lifecycleRevokeDeleteRetype_ok_implies_staged_steps' SeLe4n/Kernel/Lifecycle/Operations.lean
run_check "INVARIANT" rg -n '^theorem lifecycleRevokeDeleteRetype_preserves_capabilityInvariantBundle' SeLe4n/Kernel/Capability/Invariant.lean
run_check "INVARIANT" rg -n '^theorem lifecycleRevokeDeleteRetype_preserves_lifecycleCapabilityStaleAuthorityInvariant' SeLe4n/Kernel/Capability/Invariant.lean
run_check "INVARIANT" rg -n '^theorem lifecycleRevokeDeleteRetype_error_preserves_m4aLifecycleInvariantBundle' SeLe4n/Kernel/Capability/Invariant.lean

# M4-B WS-A composition transition anchors must remain present.
run_check "INVARIANT" rg -n '^def lifecycleRevokeDeleteRetype' SeLe4n/Kernel/Lifecycle/Operations.lean
run_check "INVARIANT" rg -n '^theorem lifecycleRevokeDeleteRetype_error_authority_cleanup_alias' SeLe4n/Kernel/Lifecycle/Operations.lean
run_check "INVARIANT" rg -n '^theorem lifecycleRevokeDeleteRetype_ok_implies_authority_ne_cleanup' SeLe4n/Kernel/Lifecycle/Operations.lean

# M4-A step-4 lifecycle local-helper anchors must remain present.
run_check "INVARIANT" rg -n '^theorem lifecycle_storeObject_objects_eq' SeLe4n/Kernel/Lifecycle/Operations.lean
run_check "INVARIANT" rg -n '^theorem lifecycle_storeObject_objects_ne' SeLe4n/Kernel/Lifecycle/Operations.lean
run_check "INVARIANT" rg -n '^theorem lifecycle_storeObject_scheduler_eq' SeLe4n/Kernel/Lifecycle/Operations.lean
run_check "INVARIANT" rg -n '^theorem lifecycleRetypeObject_ok_as_storeObject' SeLe4n/Kernel/Lifecycle/Operations.lean
run_check "INVARIANT" rg -n '^theorem lifecycleRetypeObject_ok_lookup_preserved_ne' SeLe4n/Kernel/Lifecycle/Operations.lean
run_check "INVARIANT" rg -n '^theorem lifecycleRetypeObject_ok_runnable_membership' SeLe4n/Kernel/Lifecycle/Operations.lean
run_check "INVARIANT" rg -n '^theorem lifecycleRetypeObject_ok_not_runnable_membership' SeLe4n/Kernel/Lifecycle/Operations.lean

# M4-A step-2 lifecycle transition anchors must remain present.
run_check "INVARIANT" rg -n '^\s*\| illegalState' SeLe4n/Model/State.lean
run_check "INVARIANT" rg -n '^\s*\| illegalAuthority' SeLe4n/Model/State.lean
run_check "INVARIANT" rg -n '^def lifecycleRetypeObject' SeLe4n/Kernel/Lifecycle/Operations.lean
run_check "INVARIANT" rg -n '^theorem lifecycleRetypeObject_error_illegalState' SeLe4n/Kernel/Lifecycle/Operations.lean
run_check "INVARIANT" rg -n '^theorem lifecycleRetypeObject_error_illegalAuthority' SeLe4n/Kernel/Lifecycle/Operations.lean
run_check "INVARIANT" rg -n '^theorem lifecycleRetypeObject_success_updates_object' SeLe4n/Kernel/Lifecycle/Operations.lean

# M5-B orchestration transition anchors must remain present.
run_check "INVARIANT" rg -n '^def serviceStart' SeLe4n/Kernel/Service/Operations.lean
run_check "INVARIANT" rg -n '^def serviceStop' SeLe4n/Kernel/Service/Operations.lean
run_check "INVARIANT" rg -n '^def serviceRestart' SeLe4n/Kernel/Service/Operations.lean
run_check "INVARIANT" rg -n '^theorem serviceStart_error_policyDenied' SeLe4n/Kernel/Service/Operations.lean
run_check "INVARIANT" rg -n '^theorem serviceStart_error_dependencyViolation' SeLe4n/Kernel/Service/Operations.lean
run_check "INVARIANT" rg -n '^theorem serviceStop_error_policyDenied' SeLe4n/Kernel/Service/Operations.lean
run_check "INVARIANT" rg -n '^theorem serviceStop_error_illegalState' SeLe4n/Kernel/Service/Operations.lean
run_check "INVARIANT" rg -n '^theorem serviceRestart_error_of_stop_error' SeLe4n/Kernel/Service/Operations.lean
run_check "INVARIANT" rg -n '^theorem serviceRestart_error_of_start_error' SeLe4n/Kernel/Service/Operations.lean
run_check "INVARIANT" rg -n '^theorem serviceRestart_ok_implies_staged_steps' SeLe4n/Kernel/Service/Operations.lean
run_check "INVARIANT" rg -n '^\s*\| policyDenied' SeLe4n/Model/State.lean
run_check "INVARIANT" rg -n '^\s*\| dependencyViolation' SeLe4n/Model/State.lean

# M5-C policy-surface anchors must remain present.
run_check "INVARIANT" rg -n '^abbrev ServicePolicyPredicate' SeLe4n/Kernel/Service/Invariant.lean
run_check "INVARIANT" rg -n '^def policyBackingObjectTyped' SeLe4n/Kernel/Service/Invariant.lean
run_check "INVARIANT" rg -n '^def policyOwnerAuthorityRefRecorded' SeLe4n/Kernel/Service/Invariant.lean
run_check "INVARIANT" rg -n '^def policyOwnerAuthoritySlotPresent' SeLe4n/Kernel/Service/Invariant.lean
run_check "INVARIANT" rg -n '^def servicePolicySurfaceInvariant' SeLe4n/Kernel/Service/Invariant.lean
run_check "INVARIANT" rg -n '^theorem policyBackingObjectTyped_of_lifecycleInvariant' SeLe4n/Kernel/Service/Invariant.lean
run_check "INVARIANT" rg -n '^theorem policyOwnerAuthoritySlotPresent_of_lifecycleInvariant' SeLe4n/Kernel/Service/Invariant.lean
run_check "INVARIANT" rg -n '^theorem policyOwnerAuthoritySlotPresent_of_capabilityLookup' SeLe4n/Kernel/Service/Invariant.lean
run_check "INVARIANT" rg -n '^theorem servicePolicySurfaceInvariant_of_lifecycleInvariant' SeLe4n/Kernel/Service/Invariant.lean
run_check "INVARIANT" rg -n '^theorem serviceStart_policyDenied_separates_check_from_mutation' SeLe4n/Kernel/Service/Invariant.lean
run_check "INVARIANT" rg -n '^theorem serviceStop_policyDenied_separates_check_from_mutation' SeLe4n/Kernel/Service/Invariant.lean

# M5-D proof-package anchors must remain present.
run_check "INVARIANT" rg -n '^def serviceLifecycleCapabilityInvariantBundle' SeLe4n/Kernel/Service/Invariant.lean
run_check "INVARIANT" rg -n '^theorem serviceLifecycleCapabilityInvariantBundle_of_components' SeLe4n/Kernel/Service/Invariant.lean
run_check "INVARIANT" rg -n '^theorem serviceStart_preserves_serviceLifecycleCapabilityInvariantBundle' SeLe4n/Kernel/Service/Invariant.lean
run_check "INVARIANT" rg -n '^theorem serviceStop_preserves_serviceLifecycleCapabilityInvariantBundle' SeLe4n/Kernel/Service/Invariant.lean
run_check "INVARIANT" rg -n '^theorem serviceRestart_preserves_serviceLifecycleCapabilityInvariantBundle' SeLe4n/Kernel/Service/Invariant.lean
run_check "INVARIANT" rg -n '^theorem serviceStart_failure_preserves_serviceLifecycleCapabilityInvariantBundle' SeLe4n/Kernel/Service/Invariant.lean
run_check "INVARIANT" rg -n '^theorem serviceStop_failure_preserves_serviceLifecycleCapabilityInvariantBundle' SeLe4n/Kernel/Service/Invariant.lean
run_check "INVARIANT" rg -n '^theorem serviceRestart_stop_failure_preserves_serviceLifecycleCapabilityInvariantBundle' SeLe4n/Kernel/Service/Invariant.lean
run_check "INVARIANT" rg -n '^theorem serviceRestart_start_failure_preserves_serviceLifecycleCapabilityInvariantBundle' SeLe4n/Kernel/Service/Invariant.lean

# M3.5 step-7 executable demonstration closure anchors.
run_check "TRACE" rg -n 'adapter timer success path value' SeLe4n/Testing/MainTraceHarness.lean
run_check "TRACE" rg -n 'adapter timer invalid-context branch' SeLe4n/Testing/MainTraceHarness.lean
run_check "TRACE" rg -n 'adapter timer unsupported branch' SeLe4n/Testing/MainTraceHarness.lean
run_check "TRACE" rg -n 'adapter read denied branch' SeLe4n/Testing/MainTraceHarness.lean
run_check "TRACE" rg -n 'adapter read success path byte' SeLe4n/Testing/MainTraceHarness.lean
run_check "TRACE" rg -n 'adapter register write success path value' SeLe4n/Testing/MainTraceHarness.lean
run_check "TRACE" rg -n 'adapter register write unsupported branch' SeLe4n/Testing/MainTraceHarness.lean
run_check "TRACE" rg -n 'adapter timer invalid-context branch: SeLe4n.Model.KernelError.illegalState' tests/fixtures/main_trace_smoke.expected
run_check "TRACE" rg -n 'adapter timer unsupported branch: SeLe4n.Model.KernelError.notImplemented' tests/fixtures/main_trace_smoke.expected
run_check "TRACE" rg -n 'adapter read denied branch: SeLe4n.Model.KernelError.notImplemented' tests/fixtures/main_trace_smoke.expected
run_check "TRACE" rg -n 'adapter read success path byte: 0' tests/fixtures/main_trace_smoke.expected
run_check "TRACE" rg -n 'adapter register write success path value: 99' tests/fixtures/main_trace_smoke.expected
run_check "TRACE" rg -n 'adapter register write unsupported branch: SeLe4n.Model.KernelError.notImplemented' tests/fixtures/main_trace_smoke.expected
run_check "TRACE" rg -n 'endpointAwaitReceive demoEndpoint 2' SeLe4n/Testing/MainTraceHarness.lean
run_check "TRACE" rg -n 'handshake send matched waiting receiver' SeLe4n/Testing/MainTraceHarness.lean
run_check "TRACE" rg -n 'handshake send matched waiting receiver' tests/fixtures/main_trace_smoke.expected
run_check "TRACE" rg -n 'serviceStart svcApi allowAll' SeLe4n/Testing/MainTraceHarness.lean
run_check "TRACE" rg -n 'service start denied branch' SeLe4n/Testing/MainTraceHarness.lean
run_check "TRACE" rg -n 'service start dependency branch' SeLe4n/Testing/MainTraceHarness.lean
run_check "TRACE" rg -n 'service restart status' SeLe4n/Testing/MainTraceHarness.lean
run_check "TRACE" rg -n 'service stop denied branch' SeLe4n/Testing/MainTraceHarness.lean
run_check "TRACE" rg -n 'service stop illegal-state branch' SeLe4n/Testing/MainTraceHarness.lean
run_check "TRACE" rg -n 'service restart stop-stage failure' SeLe4n/Testing/MainTraceHarness.lean
run_check "TRACE" rg -n 'service restart start-stage failure' SeLe4n/Testing/MainTraceHarness.lean
run_check "TRACE" rg -n 'service isolation api↔denied' SeLe4n/Testing/MainTraceHarness.lean
run_check "TRACE" rg -n 'service isolation api↔db' SeLe4n/Testing/MainTraceHarness.lean
run_check "TRACE" rg -n 'service start denied branch: SeLe4n.Model.KernelError.policyDenied' tests/fixtures/main_trace_smoke.expected
run_check "TRACE" rg -n 'service start dependency branch: SeLe4n.Model.KernelError.dependencyViolation' tests/fixtures/main_trace_smoke.expected
run_check "TRACE" rg -n 'service restart status: some' tests/fixtures/main_trace_smoke.expected
run_check "TRACE" rg -n 'service stop denied branch: SeLe4n.Model.KernelError.policyDenied' tests/fixtures/main_trace_smoke.expected
run_check "TRACE" rg -n 'service stop illegal-state branch: SeLe4n.Model.KernelError.illegalState' tests/fixtures/main_trace_smoke.expected
run_check "TRACE" rg -n 'service restart stop-stage failure: SeLe4n.Model.KernelError.policyDenied' tests/fixtures/main_trace_smoke.expected
run_check "TRACE" rg -n 'service restart start-stage failure: SeLe4n.Model.KernelError.dependencyViolation' tests/fixtures/main_trace_smoke.expected
run_check "TRACE" rg -n 'service isolation api↔denied: true' tests/fixtures/main_trace_smoke.expected
run_check "TRACE" rg -n 'service isolation api↔db: false' tests/fixtures/main_trace_smoke.expected
run_check "TRACE" rg -n 'lifecycle retype unauthorized branch' SeLe4n/Testing/MainTraceHarness.lean
run_check "TRACE" rg -n 'lifecycle retype illegal-state branch' SeLe4n/Testing/MainTraceHarness.lean
run_check "TRACE" rg -n 'lifecycle retype success object kind' SeLe4n/Testing/MainTraceHarness.lean
run_check "TRACE" rg -n 'composed transition alias guard \(expected error\)' SeLe4n/Testing/MainTraceHarness.lean
run_check "TRACE" rg -n 'composed transition unauthorized branch' SeLe4n/Testing/MainTraceHarness.lean
run_check "TRACE" rg -n 'composed revoke/delete/retype success' SeLe4n/Testing/MainTraceHarness.lean
run_check "TRACE" rg -n 'post-revoke sibling lookup' SeLe4n/Testing/MainTraceHarness.lean
run_check "TRACE" rg -n 'post-delete lookup \(expected error\)' SeLe4n/Testing/MainTraceHarness.lean
run_check "TRACE" rg -n 'lifecycle retype unauthorized branch: SeLe4n.Model.KernelError.illegalAuthority' tests/fixtures/main_trace_smoke.expected
run_check "TRACE" rg -n 'lifecycle retype illegal-state branch: SeLe4n.Model.KernelError.illegalState' tests/fixtures/main_trace_smoke.expected
run_check "TRACE" rg -n 'lifecycle retype success object kind: some \(SeLe4n.Model.KernelObjectType.endpoint\)' tests/fixtures/main_trace_smoke.expected
run_check "TRACE" rg -n 'composed transition alias guard \(expected error\): SeLe4n.Model.KernelError.illegalState' tests/fixtures/main_trace_smoke.expected
run_check "TRACE" rg -n 'composed transition unauthorized branch: SeLe4n.Model.KernelError.illegalAuthority' tests/fixtures/main_trace_smoke.expected
run_check "TRACE" rg -n 'composed revoke/delete/retype success' tests/fixtures/main_trace_smoke.expected
run_check "TRACE" rg -n 'post-revoke sibling lookup: SeLe4n.Model.KernelError.invalidCapability' tests/fixtures/main_trace_smoke.expected
run_check "TRACE" rg -n 'post-delete lookup \(expected error\): SeLe4n.Model.KernelError.invalidCapability' tests/fixtures/main_trace_smoke.expected

# Active milestone docs should stay synchronized for both current and next slices.
run_check "DOC" rg -n 'M3\.5' README.md docs/SEL4_SPEC.md docs/DEVELOPMENT.md
run_check "DOC" rg -n 'M4-A|M4-B|M5|M6|M7' docs/SEL4_SPEC.md
run_check "DOC" rg -n 'WS-B1\.\.WS-B11|WS-B portfolio|Comprehensive Audit 2026-02' README.md docs/SEL4_SPEC.md docs/DEVELOPMENT.md docs/gitbook/README.md docs/gitbook/05-specification-and-roadmap.md docs/gitbook/24-comprehensive-audit-2026-workstream-planning.md
run_check "DOC" rg -n 'Most recently completed slice:.*M7|M7 remediation is complete|M7 is complete and archived' README.md docs/gitbook/README.md docs/gitbook/23-m7-remediation-closeout-packet.md docs/gitbook/21-m7-current-slice-outcomes-and-workstreams.md
run_check "DOC" rg -n 'Previous completed slice:.*M6|M6 architecture-boundary|WS-M6-A through WS-M6-E' README.md docs/gitbook/README.md docs/TESTING_FRAMEWORK_PLAN.md docs/gitbook/05-specification-and-roadmap.md
run_check "DOC" rg -n 'test_tier4_nightly_candidates\.sh' docs/TESTING_FRAMEWORK_PLAN.md docs/gitbook/07-testing-and-ci.md scripts/test_nightly.sh
# shellcheck disable=SC2016
run_check "DOC" rg -n 'Tier 3 fails \(`\./scripts/test_tier3_invariant_surface\.sh`\)' docs/gitbook/07-testing-and-ci.md
# shellcheck disable=SC2016
run_check "DOC" rg -n 'Tier 4 fails \(`\./scripts/test_nightly\.sh` / `\./scripts/test_tier4_nightly_candidates\.sh`\)' docs/gitbook/07-testing-and-ci.md

# Full-suite contract should continue to include Tier 3.
run_check "DOC" rg -n 'test_tier3_invariant_surface\.sh' scripts/test_full.sh

run_check "DOC" rg -n '^# M7 Remediation Closeout Packet' docs/M7_CLOSEOUT_PACKET.md docs/gitbook/23-m7-remediation-closeout-packet.md
run_check "DOC" rg -n 'Next-slice kickoff dependencies and owners|Exit-gate checklist' docs/M7_CLOSEOUT_PACKET.md
run_check "DOC" rg -n 'M7 Remediation Closeout Packet' docs/gitbook/SUMMARY.md docs/gitbook/23-m7-remediation-closeout-packet.md
run_check "DOC" rg -n 'Contribution guide|Change history' README.md
run_check "DOC" test -f CONTRIBUTING.md
run_check "DOC" test -f CHANGELOG.md
run_check "DOC" rg -n 'Required checks \(Tier 0–3\)|Deterministic replay evidence' docs/CI_POLICY.md
run_check "DOC" rg -n 'Docs Automation / Navigation \+ Links \+ DocGen Probe' .github/workflows/lean_action_ci.yml docs/CI_POLICY.md docs/gitbook/07-testing-and-ci.md
run_check "DOC" rg -n 'Tier 0.*docs-sync automation' docs/TESTING_FRAMEWORK_PLAN.md
run_check "DOC" rg -n 'Tiered Tests / Full \(Tier 0 \+ Tier 1 \+ Tier 2 \+ Tier 3\)' .github/workflows/lean_action_ci.yml docs/CI_POLICY.md
run_check "DOC" rg -n 'Nightly Determinism|NIGHTLY_ENABLE_EXPERIMENTAL' .github/workflows/nightly_determinism.yml docs/CI_POLICY.md
run_check "DOC" rg -n 'WS-B10 CodeQL policy decision|informational/non-blocking' docs/CI_POLICY.md
run_check "DOC" rg -n 'lean_toolchain_update_proposal\.yml|dependabot\.yml' docs/CI_POLICY.md docs/CI_TELEMETRY_BASELINE.md
run_check "DOC" rg -n 'ci_capture_timing\.sh|ci_flake_probe\.sh' docs/CI_TELEMETRY_BASELINE.md .github/workflows/lean_action_ci.yml .github/workflows/nightly_determinism.yml
run_check "DOC" rg -n '^# CI Maturity and Telemetry Baseline \(WS-B10\)' docs/gitbook/29-ci-maturity-and-telemetry-baseline.md
run_check "DOC" rg -n 'WS-B10 — CI maturity upgrades \(Completed\)|WS-B11 — Scenario framework finalization \(Completed\)' docs/audits/COMPREHENSIVE_AUDIT_2026_02_WORKSTREAM_PLAN.md

run_check "DOC" rg -n '^# Scenario framework \(WS-B11\)' tests/scenarios/README.md
run_check "DOC" rg -n '^## 16\) WS-B11 closure evidence' docs/gitbook/24-comprehensive-audit-2026-workstream-planning.md
run_check "INVARIANT" rg -n '^\s*"schema_version": "1\.0\.0"' tests/scenarios/scenario_catalog.json
run_check "INVARIANT" rg -n '^def validate_catalog' scripts/scenario_catalog.py
run_check "INVARIANT" rg -n '^def nightly_seeds' scripts/scenario_catalog.py
run_check "INVARIANT" rg -n '^run_check "META" python3 "\$\{SCRIPT_DIR\}/scenario_catalog.py" validate' scripts/test_smoke.sh

# WS-A8 closure anchors: platform/security baseline workflow + information-flow roadmap visibility.
run_check "DOC" rg -n '^name: Platform and Security Baseline' .github/workflows/platform_security_baseline.yml
run_check "DOC" rg -n '^\s*name: Platform Signal / ARM64 Fast Gate' .github/workflows/platform_security_baseline.yml
run_check "DOC" rg -n '^\s*name: Security Signal / Secret \+ Dependency \+ CodeQL' .github/workflows/platform_security_baseline.yml
run_check "DOC" rg -n "if: github\.event_name != 'pull_request' \|\| github\.event\.pull_request\.head\.repo\.full_name == github\.repository" .github/workflows/platform_security_baseline.yml
run_check "DOC" rg -n "^\s*pull-requests:\s*read" .github/workflows/platform_security_baseline.yml
run_check "DOC" rg -n "^\s*fetch-depth:\s*0" .github/workflows/platform_security_baseline.yml
run_check "DOC" rg -n "^\s*continue-on-error:\s*true" .github/workflows/platform_security_baseline.yml
run_check "DOC" rg -n '^# Information-Flow Proof Roadmap' docs/INFORMATION_FLOW_ROADMAP.md
run_check "DOC" rg -n '^## IF-M1' docs/INFORMATION_FLOW_ROADMAP.md
run_check "DOC" rg -n '^## IF-M5' docs/INFORMATION_FLOW_ROADMAP.md
run_check "DOC" rg -n 'INFORMATION_FLOW_ROADMAP\.md' README.md docs/CI_POLICY.md docs/audits/AUDIT_REMEDIATION_WORKSTREAMS.md docs/gitbook/21-m7-current-slice-outcomes-and-workstreams.md docs/gitbook/20-repository-audit-remediation-workstreams.md

finalize_report
