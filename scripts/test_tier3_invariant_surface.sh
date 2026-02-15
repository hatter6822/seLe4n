#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck disable=SC1091
source "${SCRIPT_DIR}/test_lib.sh"

parse_common_args "$@"
cd "${REPO_ROOT}"

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
run_check "INVARIANT" rg -n '^def endpointAwaitReceive' SeLe4n/Kernel/IPC/Invariant.lean
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

# M4-A step-2 lifecycle transition anchors must remain present.
run_check "INVARIANT" rg -n '^\s*\| illegalState' SeLe4n/Model/State.lean
run_check "INVARIANT" rg -n '^\s*\| illegalAuthority' SeLe4n/Model/State.lean
run_check "INVARIANT" rg -n '^def lifecycleRetypeObject' SeLe4n/Kernel/Lifecycle/Operations.lean
run_check "INVARIANT" rg -n '^theorem lifecycleRetypeObject_error_illegalState' SeLe4n/Kernel/Lifecycle/Operations.lean
run_check "INVARIANT" rg -n '^theorem lifecycleRetypeObject_error_illegalAuthority' SeLe4n/Kernel/Lifecycle/Operations.lean
run_check "INVARIANT" rg -n '^theorem lifecycleRetypeObject_success_updates_object' SeLe4n/Kernel/Lifecycle/Operations.lean

# M3.5 step-7 executable demonstration closure anchors.
run_check "TRACE" rg -n 'endpointAwaitReceive demoEndpoint 2' Main.lean
run_check "TRACE" rg -n 'handshake send matched waiting receiver' Main.lean
run_check "TRACE" rg -n 'handshake send matched waiting receiver' tests/fixtures/main_trace_smoke.expected
run_check "TRACE" rg -n 'lifecycle retype illegal-state branch' Main.lean
run_check "TRACE" rg -n 'lifecycle retype illegal-state branch' tests/fixtures/main_trace_smoke.expected

# Active milestone docs should stay synchronized for both current and next slices.
run_check "DOC" rg -n 'M3\.5' README.md docs/SEL4_SPEC.md docs/DEVELOPMENT.md
run_check "DOC" rg -n 'M4' README.md docs/SEL4_SPEC.md docs/DEVELOPMENT.md

# Full-suite contract should continue to include Tier 3.
run_check "DOC" rg -n 'test_tier3_invariant_surface\.sh' scripts/test_full.sh

finalize_report
