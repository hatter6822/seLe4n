#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck disable=SC1091
source "${SCRIPT_DIR}/test_lib.sh"

parse_common_args "$@"
cd "${REPO_ROOT}"

# M-20 guard: rg (ripgrep) availability check with grep -P fallback.
# Tier 3 has ~440 rg invocations.  Without this guard, a missing rg
# produces hundreds of command-not-found errors instead of one clear message.
if ! command -v rg >/dev/null 2>&1; then
  # shellcheck disable=SC2312
  if echo "test" | grep -P "test" >/dev/null 2>&1; then
    log_section "INVARIANT" "ripgrep (rg) not found; using grep -P fallback for Tier 3 checks."
    _RG_SHIM_DIR="$(mktemp -d)"
    cat > "${_RG_SHIM_DIR}/rg" <<'RGSHIM'
#!/usr/bin/env bash
# Minimal rg -> grep -P shim (WS-H3/M-20 fallback).
nflag=""
pattern=""
files=()
while [[ $# -gt 0 ]]; do
  case "$1" in
    -n) nflag="-n"; shift ;;
    -*) shift ;;
    *)
      if [[ -z "${pattern}" ]]; then
        pattern="$1"
      else
        files+=("$1")
      fi
      shift
      ;;
  esac
done
if [[ -n "${nflag}" ]]; then
  exec grep -Pn -- "${pattern}" "${files[@]}"
else
  exec grep -P -- "${pattern}" "${files[@]}"
fi
RGSHIM
    chmod +x "${_RG_SHIM_DIR}/rg"
    export PATH="${_RG_SHIM_DIR}:${PATH}"
    # shellcheck disable=SC2154
    _rg_shim_cleanup() { rm -rf "${_RG_SHIM_DIR}"; }
    trap '_rg_shim_cleanup' EXIT
  else
    record_failure "INVARIANT" "Tier 3 requires ripgrep (rg) or grep with PCRE support. Neither is available."
    finalize_report
  fi
fi

# WS-B1 closure anchors: VSpace transitions, invariants, and ADR publication.
run_check "INVARIANT" rg -n '^structure VSpaceRoot' SeLe4n/Model/Object.lean
run_check "INVARIANT" rg -n '^def resolveAsidRoot' SeLe4n/Kernel/Architecture/VSpace.lean
# WS-G3/F-P06: resolveAsidRoot now uses asidTable O(1) lookup, NOT objectIndex.findSome? O(n) scan.
run_check "INVARIANT" bash -lc "! rg -n '^\s*st.objectIndex.findSome\?' SeLe4n/Kernel/Architecture/VSpace.lean"
run_check "INVARIANT" rg -n 'st.asidTable' SeLe4n/Kernel/Architecture/VSpace.lean
run_check "INVARIANT" rg -n '^def vspaceMapPage' SeLe4n/Kernel/Architecture/VSpace.lean
run_check "INVARIANT" rg -n '^def vspaceUnmapPage' SeLe4n/Kernel/Architecture/VSpace.lean
run_check "INVARIANT" rg -n '^def vspaceLookup' SeLe4n/Kernel/Architecture/VSpace.lean
run_check "INVARIANT" bash -lc "! rg -n '^theorem vspaceLookup_deterministic' SeLe4n/Kernel/Architecture/VSpace.lean"
run_check "INVARIANT" rg -n 'WS-C3 proof-surface note:' SeLe4n/Kernel/Architecture/VSpace.lean
run_check "INVARIANT" bash -lc "! rg -n '^theorem projectState_deterministic' SeLe4n/Kernel/InformationFlow/Projection.lean"
run_check "INVARIANT" rg -n 'WS-C3 proof-surface note:' SeLe4n/Kernel/InformationFlow/Projection.lean
run_check "INVARIANT" rg -n '^def vspaceInvariantBundle' SeLe4n/Kernel/Architecture/VSpaceInvariant.lean
# WS-B4 closure anchors: wrapper structures must remain explicit.
run_check "INVARIANT" rg -n '^structure DomainId' SeLe4n/Prelude.lean
run_check "INVARIANT" rg -n '^structure Priority' SeLe4n/Prelude.lean
run_check "INVARIANT" rg -n '^structure Irq' SeLe4n/Prelude.lean
run_check "INVARIANT" rg -n '^structure Badge' SeLe4n/Prelude.lean
run_check "INVARIANT" rg -n '^structure ASID' SeLe4n/Prelude.lean
run_check "INVARIANT" rg -n '^structure VAddr' SeLe4n/Prelude.lean
run_check "INVARIANT" rg -n '^structure PAddr' SeLe4n/Prelude.lean
run_check "INVARIANT" rg -n '^structure ServiceId' SeLe4n/Prelude.lean
# WS-B5 closure anchors: CSpace guard/radix path resolution surface.
run_check "INVARIANT" rg -n '^inductive ResolveError' SeLe4n/Model/Object.lean
run_check "INVARIANT" rg -n '^def resolveSlot' SeLe4n/Model/Object.lean
run_check "INVARIANT" rg -n '^def cspaceResolvePath' SeLe4n/Kernel/Capability/Operations.lean
run_check "INVARIANT" rg -n '^def cspaceLookupPath' SeLe4n/Kernel/Capability/Operations.lean

# WS-B6 closure anchors: notification IPC object model and transition surface.
run_check "INVARIANT" rg -n '^inductive NotificationState' SeLe4n/Model/Object.lean
run_check "INVARIANT" rg -n '^structure Notification' SeLe4n/Model/Object.lean
run_check "INVARIANT" rg -n '^def notificationSignal' SeLe4n/Kernel/IPC/Operations.lean
run_check "INVARIANT" rg -n '^def notificationWait' SeLe4n/Kernel/IPC/Operations.lean
run_check "INVARIANT" rg -n '^def notificationInvariant' SeLe4n/Kernel/IPC/Invariant.lean

# WS-B7 closure anchors: information-flow policy/projection baseline and milestone docs.
run_check "INVARIANT" rg -n '^inductive Confidentiality' SeLe4n/Kernel/InformationFlow/Policy.lean
run_check "INVARIANT" rg -n '^structure SecurityLabel' SeLe4n/Kernel/InformationFlow/Policy.lean
run_check "INVARIANT" rg -n '^def securityFlowsTo' SeLe4n/Kernel/InformationFlow/Policy.lean
run_check "INVARIANT" rg -n '^theorem securityFlowsTo_trans' SeLe4n/Kernel/InformationFlow/Policy.lean
run_check "INVARIANT" rg -n '^def projectState' SeLe4n/Kernel/InformationFlow/Projection.lean
run_check "INVARIANT" rg -n '^def lowEquivalent' SeLe4n/Kernel/InformationFlow/Projection.lean
run_check "INVARIANT" rg -n '^theorem lowEquivalent_trans' SeLe4n/Kernel/InformationFlow/Projection.lean
run_check "INVARIANT" rg -n '^def runInformationFlowChecks' tests/InformationFlowSuite.lean
run_check "INVARIANT" rg -n '^run_check "TRACE" lake env lean --run tests/InformationFlowSuite\.lean' scripts/test_tier2_negative.sh
run_check "INVARIANT" rg -n '^ELAN_INSTALLER_SHA256=' scripts/setup_lean_env.sh
run_check "INVARIANT" rg -n '^compute_sha256\(\)' scripts/setup_lean_env.sh
# shellcheck disable=SC2016

# WS-B2 closure anchors: bootstrap DSL, negative suite, and nightly replay artifacts.
run_check "INVARIANT" rg -n '^structure BootstrapBuilder' SeLe4n/Testing/StateBuilder.lean
run_check "INVARIANT" rg -n '^def build \(builder : BootstrapBuilder\)' SeLe4n/Testing/StateBuilder.lean
run_check "INVARIANT" rg -n '^private def runNegativeChecks' tests/NegativeStateSuite.lean
run_check "INVARIANT" rg -n '^run_check "TRACE" lake env lean --run tests/NegativeStateSuite\.lean' scripts/test_tier2_negative.sh
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
run_check "INVARIANT" bash -lc "if rg -n '^import SeLe4n\\.Kernel\\.Architecture\\.Invariant$' SeLe4n.lean; then exit 1; fi"

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

# WS-A3 boundary hardening anchors must remain explicit.
run_check "INVARIANT" rg -n '^@\[inline\] def toObjId' SeLe4n/Prelude.lean
run_check "INVARIANT" bash -lc "if rg -n '^instance : Coe ThreadId ObjId where' SeLe4n/Prelude.lean; then echo 'Implicit ThreadId -> ObjId coercion must remain absent.' >&2; exit 1; fi"

# Invariant bundle surface anchors (M1/M2/M3 composed entrypoints).
run_check "INVARIANT" rg -n '^(def|abbrev) schedulerInvariantBundle' SeLe4n/Kernel/Scheduler/Invariant.lean
run_check "INVARIANT" rg -n '^def capabilityInvariantBundle' SeLe4n/Kernel/Capability/Invariant.lean
run_check "INVARIANT" rg -n '^def coreIpcInvariantBundle' SeLe4n/Kernel/Capability/Invariant.lean

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

# C-01 remediation: non-tautological slot-uniqueness infrastructure at CNode level.
run_check "INVARIANT" rg -n '^def slotsUnique' SeLe4n/Model/Object.lean
run_check "INVARIANT" rg -n '^theorem insert_slotsUnique' SeLe4n/Model/Object.lean
run_check "INVARIANT" rg -n '^theorem remove_slotsUnique' SeLe4n/Model/Object.lean
run_check "INVARIANT" rg -n '^theorem revokeTargetLocal_slotsUnique' SeLe4n/Model/Object.lean
run_check "INVARIANT" rg -n '^theorem lookup_mem_of_some' SeLe4n/Model/Object.lean
run_check "INVARIANT" rg -n '^theorem mem_lookup_of_slotsUnique' SeLe4n/Model/Object.lean
# C-01/H-01 remediation: reformulated invariant definitions (non-tautological).
run_check "INVARIANT" rg -n 'cn.slotsUnique' SeLe4n/Kernel/Capability/Invariant.lean
run_check "INVARIANT" rg -n '^theorem cspaceLookupSound_of_cspaceSlotUnique' SeLe4n/Kernel/Capability/Invariant.lean
run_check "INVARIANT" rg -n '^theorem capabilityInvariantBundle_of_slotUnique' SeLe4n/Kernel/Capability/Invariant.lean
# H-01 remediation: compositional storeObject transfer lemmas.
run_check "INVARIANT" rg -n '^theorem cspaceSlotUnique_of_storeObject_nonCNode' SeLe4n/Kernel/Capability/Invariant.lean
run_check "INVARIANT" rg -n '^theorem cspaceSlotUnique_of_storeObject_cnode' SeLe4n/Kernel/Capability/Invariant.lean
# H-03 remediation: badge/notification routing consistency chain.
run_check "INVARIANT" rg -n '^theorem mintDerivedCap_badge_propagated' SeLe4n/Kernel/Capability/Invariant.lean
run_check "INVARIANT" rg -n '^theorem notificationSignal_badge_stored_fresh' SeLe4n/Kernel/Capability/Invariant.lean
run_check "INVARIANT" rg -n '^theorem notificationWait_recovers_pending_badge' SeLe4n/Kernel/Capability/Invariant.lean
run_check "INVARIANT" rg -n '^theorem badge_notification_routing_consistent' SeLe4n/Kernel/Capability/Invariant.lean
run_check "INVARIANT" rg -n '^theorem badge_merge_idempotent' SeLe4n/Kernel/Capability/Invariant.lean

# WS-H12a: Legacy M3 seed/M3.5 step-2 anchors removed — replaced by dual-queue operations.
# Dual-queue transition definition anchors:
run_check "INVARIANT" rg -n '^def endpointSendDual' SeLe4n/Kernel/IPC/DualQueue.lean
run_check "INVARIANT" rg -n '^def endpointReceiveDual' SeLe4n/Kernel/IPC/DualQueue.lean

# M3.5 step-3 scheduler-contract predicate anchors must remain present.
run_check "INVARIANT" rg -n '^def runnableThreadIpcReady' SeLe4n/Kernel/IPC/Invariant.lean
run_check "INVARIANT" rg -n '^def blockedOnSendNotRunnable' SeLe4n/Kernel/IPC/Invariant.lean
run_check "INVARIANT" rg -n '^def blockedOnReceiveNotRunnable' SeLe4n/Kernel/IPC/Invariant.lean
run_check "INVARIANT" rg -n '^def ipcSchedulerContractPredicates' SeLe4n/Kernel/IPC/Invariant.lean
# WS-H12a: Legacy per-operation ipcSchedulerContractPredicates anchors removed.
# Dual-queue equivalents are in IPC/Invariant.lean (endpointSendDual/ReceiveDual/Call/Reply/ReplyRecv).

# M3.5 step-4 composed bundle anchors must remain present.
run_check "INVARIANT" rg -n '^def ipcSchedulerRunnableReadyComponent' SeLe4n/Kernel/Capability/Invariant.lean
run_check "INVARIANT" rg -n '^def ipcSchedulerBlockedSendComponent' SeLe4n/Kernel/Capability/Invariant.lean
run_check "INVARIANT" rg -n '^def ipcSchedulerBlockedReceiveComponent' SeLe4n/Kernel/Capability/Invariant.lean
run_check "INVARIANT" rg -n '^def ipcSchedulerCoherenceComponent' SeLe4n/Kernel/Capability/Invariant.lean
run_check "INVARIANT" rg -n '^theorem ipcSchedulerCoherenceComponent_iff_contractPredicates' SeLe4n/Kernel/Capability/Invariant.lean
run_check "INVARIANT" rg -n '^def ipcSchedulerCouplingInvariantBundle' SeLe4n/Kernel/Capability/Invariant.lean
# WS-H12a: Legacy coupling/local-first preservation anchors removed.
# Dual-queue preservation is verified via dualQueueSystemInvariant anchors below.

# M3.5 step-5 helper-lemma anchors must remain present.
run_check "INVARIANT" rg -n '^theorem tcb_lookup_of_endpoint_store' SeLe4n/Kernel/IPC/Invariant.lean
run_check "INVARIANT" rg -n '^theorem runnable_membership_of_endpoint_store' SeLe4n/Kernel/IPC/Invariant.lean
run_check "INVARIANT" rg -n '^theorem not_runnable_membership_of_endpoint_store' SeLe4n/Kernel/IPC/Invariant.lean

# Bundle composition guard: M3 seed bundle must still compose scheduler + capability + IPC invariants.
run_check "INVARIANT" rg -n '^\s*schedulerInvariantBundle st ∧ capabilityInvariantBundle st ∧ ipcInvariant st' SeLe4n/Kernel/Capability/Invariant.lean

# M3.5 step-1 state-model anchors must remain present.
# WS-H12a: waitingReceiver removed from Endpoint (dual-queue uses sendQ/receiveQ).
# WS-H12a: endpointQueueWellFormed/endpointObjectValid removed (subsumed by dualQueueSystemInvariant).
run_check "INVARIANT" rg -n '^inductive ThreadIpcState' SeLe4n/Model/Object.lean
run_check "INVARIANT" rg -n '^\s*ipcState\s*:\s*ThreadIpcState' SeLe4n/Model/Object.lean
run_check "INVARIANT" rg -n '^\s*sendQ\s*:\s*IntrusiveQueue' SeLe4n/Model/Object.lean
run_check "INVARIANT" rg -n '^\s*receiveQ\s*:\s*IntrusiveQueue' SeLe4n/Model/Object.lean


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
run_check "INVARIANT" rg -n '^def lifecycleCompositionInvariantBundle' SeLe4n/Kernel/Capability/Invariant.lean
run_check "INVARIANT" rg -n '^theorem lifecycleRetypeObject_preserves_schedulerInvariantBundle' SeLe4n/Kernel/Capability/Invariant.lean
run_check "INVARIANT" rg -n '^theorem lifecycleRetypeObject_preserves_capabilityInvariantBundle' SeLe4n/Kernel/Capability/Invariant.lean
run_check "INVARIANT" rg -n '^theorem lifecycleRetypeObject_preserves_ipcInvariant' SeLe4n/Kernel/Capability/Invariant.lean
run_check "INVARIANT" rg -n '^theorem lifecycleRetypeObject_preserves_coreIpcInvariantBundle' SeLe4n/Kernel/Capability/Invariant.lean
run_check "INVARIANT" rg -n '^theorem lifecycleRetypeObject_preserves_lifecycleCompositionInvariantBundle' SeLe4n/Kernel/Capability/Invariant.lean

# M4-B WS-C preservation theorem expansion anchors must remain present.
run_check "INVARIANT" rg -n '^theorem lifecycleRevokeDeleteRetype_ok_implies_staged_steps' SeLe4n/Kernel/Lifecycle/Operations.lean
run_check "INVARIANT" rg -n '^theorem lifecycleRevokeDeleteRetype_preserves_capabilityInvariantBundle' SeLe4n/Kernel/Capability/Invariant.lean
run_check "INVARIANT" rg -n '^theorem lifecycleRevokeDeleteRetype_preserves_lifecycleCapabilityStaleAuthorityInvariant' SeLe4n/Kernel/Capability/Invariant.lean
run_check "INVARIANT" rg -n '^theorem lifecycleRevokeDeleteRetype_error_preserves_lifecycleCompositionInvariantBundle' SeLe4n/Kernel/Capability/Invariant.lean

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

# WS-D3 F-06/TPI-D04 badge-override safety anchors must remain present.
run_check "INVARIANT" rg -n '^theorem mintDerivedCap_rights_attenuated_with_badge_override' SeLe4n/Kernel/Capability/Invariant.lean
run_check "INVARIANT" rg -n '^theorem mintDerivedCap_target_preserved_with_badge_override' SeLe4n/Kernel/Capability/Invariant.lean
run_check "INVARIANT" rg -n '^theorem cspaceMint_badge_override_safe' SeLe4n/Kernel/Capability/Invariant.lean

# WS-D3 F-08/TPI-D05 VSpace success preservation + TPI-001 round-trip anchors must remain present.
run_check "INVARIANT" rg -n '^theorem vspaceMapPage_success_preserves_vspaceInvariantBundle' SeLe4n/Kernel/Architecture/VSpaceInvariant.lean
run_check "INVARIANT" rg -n '^theorem vspaceUnmapPage_success_preserves_vspaceInvariantBundle' SeLe4n/Kernel/Architecture/VSpaceInvariant.lean
run_check "INVARIANT" rg -n '^theorem vspaceLookup_after_map' SeLe4n/Kernel/Architecture/VSpaceInvariant.lean
run_check "INVARIANT" rg -n '^theorem vspaceLookup_map_other' SeLe4n/Kernel/Architecture/VSpaceInvariant.lean
run_check "INVARIANT" rg -n '^theorem vspaceLookup_after_unmap' SeLe4n/Kernel/Architecture/VSpaceInvariant.lean
run_check "INVARIANT" rg -n '^theorem vspaceLookup_unmap_other' SeLe4n/Kernel/Architecture/VSpaceInvariant.lean

# WS-D3/WS-G3 F-08 VSpace resolveAsidRoot extraction/characterization lemmas.
# WS-G3: resolveAsidRoot_some_implies replaced by resolveAsidRoot_some_implies_obj (asidTable-based).
# WS-G3: resolveAsidRoot_of_unique_root replaced by resolveAsidRoot_of_asidTable_entry (no uniqueness needed).
run_check "INVARIANT" rg -n '^theorem resolveAsidRoot_some_implies_obj' SeLe4n/Kernel/Architecture/VSpace.lean
run_check "INVARIANT" rg -n '^theorem resolveAsidRoot_of_asidTable_entry' SeLe4n/Kernel/Architecture/VSpace.lean
run_check "INVARIANT" rg -n '^def vspaceAsidRootsUnique' SeLe4n/Kernel/Architecture/VSpace.lean
run_check "INVARIANT" rg -n '^def asidTableConsistent' SeLe4n/Kernel/Architecture/VSpaceInvariant.lean

# WS-D4 F-07 service dependency cycle detection anchors must remain present.
run_check "INVARIANT" rg -n '^def serviceBfsFuel' SeLe4n/Kernel/Service/Operations.lean
run_check "INVARIANT" rg -n '^def serviceHasPathTo' SeLe4n/Kernel/Service/Operations.lean
run_check "INVARIANT" rg -n '^def serviceRegisterDependency' SeLe4n/Kernel/Service/Operations.lean
run_check "INVARIANT" rg -n '^theorem serviceRegisterDependency_error_self_loop' SeLe4n/Kernel/Service/Operations.lean
run_check "INVARIANT" rg -n '^\s*\| cyclicDependency' SeLe4n/Model/State.lean
run_check "INVARIANT" rg -n '^def serviceDependencyAcyclic' SeLe4n/Kernel/Service/Invariant.lean
run_check "INVARIANT" rg -n '^theorem serviceRegisterDependency_preserves_acyclicity' SeLe4n/Kernel/Service/Invariant.lean

# WS-D4 F-11 serviceRestart failure-semantics anchors must remain present.
run_check "INVARIANT" rg -n '^theorem serviceRestart_error_discards_state' SeLe4n/Kernel/Service/Invariant.lean
run_check "INVARIANT" rg -n '^theorem serviceRestart_error_from_start_phase' SeLe4n/Kernel/Service/Invariant.lean

# WS-D4 F-12 double-wait prevention + uniqueness invariant anchors must remain present.
run_check "INVARIANT" rg -n '^\s*\| alreadyWaiting' SeLe4n/Model/State.lean
run_check "INVARIANT" rg -n '^theorem notificationWait_error_alreadyWaiting' SeLe4n/Kernel/IPC/Operations.lean
run_check "INVARIANT" rg -n '^theorem notificationWait_badge_path_notification' SeLe4n/Kernel/IPC/Operations.lean
run_check "INVARIANT" rg -n '^theorem notificationWait_wait_path_notification' SeLe4n/Kernel/IPC/Operations.lean
run_check "INVARIANT" rg -n '^def uniqueWaiters' SeLe4n/Kernel/IPC/Invariant.lean
run_check "INVARIANT" rg -n '^theorem notificationWait_preserves_uniqueWaiters' SeLe4n/Kernel/IPC/Invariant.lean

# WS-E4/WS-F1 dual-queue IPC definition and theorem anchors must remain present.
run_check "INVARIANT" rg -n '^def endpointSendDual' SeLe4n/Kernel/IPC/DualQueue.lean
run_check "INVARIANT" rg -n '^def endpointReceiveDual' SeLe4n/Kernel/IPC/DualQueue.lean
run_check "INVARIANT" rg -n '^def endpointCall' SeLe4n/Kernel/IPC/DualQueue.lean
run_check "INVARIANT" rg -n '^def endpointReply' SeLe4n/Kernel/IPC/DualQueue.lean
run_check "INVARIANT" rg -n '^def endpointReplyRecv' SeLe4n/Kernel/IPC/DualQueue.lean
run_check "INVARIANT" rg -n '^def endpointQueuePopHead' SeLe4n/Kernel/IPC/DualQueue.lean
run_check "INVARIANT" rg -n '^def endpointQueueEnqueue' SeLe4n/Kernel/IPC/DualQueue.lean
run_check "INVARIANT" rg -n '^def endpointQueueRemoveDual' SeLe4n/Kernel/IPC/DualQueue.lean
run_check "INVARIANT" rg -n '^theorem endpointQueuePopHead_scheduler_eq' SeLe4n/Kernel/IPC/DualQueue.lean
run_check "INVARIANT" rg -n '^theorem endpointQueueEnqueue_scheduler_eq' SeLe4n/Kernel/IPC/DualQueue.lean
run_check "INVARIANT" rg -n '^theorem endpointQueueRemoveDual_scheduler_eq' SeLe4n/Kernel/IPC/DualQueue.lean
run_check "INVARIANT" rg -n '^theorem endpointQueueRemoveDual_tcb_ipcState_backward' SeLe4n/Kernel/IPC/DualQueue.lean

# WS-F1 dual-queue preservation theorem anchors (all three invariant families).
run_check "INVARIANT" rg -n '^theorem endpointSendDual_preserves_ipcInvariant' SeLe4n/Kernel/IPC/Invariant.lean
run_check "INVARIANT" rg -n '^theorem endpointSendDual_preserves_schedulerInvariantBundle' SeLe4n/Kernel/IPC/Invariant.lean
run_check "INVARIANT" rg -n '^theorem endpointSendDual_preserves_ipcSchedulerContractPredicates' SeLe4n/Kernel/IPC/Invariant.lean
run_check "INVARIANT" rg -n '^theorem endpointReceiveDual_preserves_ipcInvariant' SeLe4n/Kernel/IPC/Invariant.lean
run_check "INVARIANT" rg -n '^theorem endpointReceiveDual_preserves_schedulerInvariantBundle' SeLe4n/Kernel/IPC/Invariant.lean
run_check "INVARIANT" rg -n '^theorem endpointReceiveDual_preserves_ipcSchedulerContractPredicates' SeLe4n/Kernel/IPC/Invariant.lean
run_check "INVARIANT" rg -n '^theorem endpointQueueRemoveDual_preserves_ipcInvariant' SeLe4n/Kernel/IPC/Invariant.lean
run_check "INVARIANT" rg -n '^theorem endpointQueueRemoveDual_preserves_schedulerInvariantBundle' SeLe4n/Kernel/IPC/Invariant.lean
run_check "INVARIANT" rg -n '^theorem endpointQueueRemoveDual_preserves_ipcSchedulerContractPredicates' SeLe4n/Kernel/IPC/Invariant.lean
run_check "INVARIANT" rg -n '^theorem endpointCall_preserves_ipcInvariant' SeLe4n/Kernel/IPC/Invariant.lean
run_check "INVARIANT" rg -n '^theorem endpointCall_preserves_schedulerInvariantBundle' SeLe4n/Kernel/IPC/Invariant.lean
run_check "INVARIANT" rg -n '^theorem endpointCall_preserves_ipcSchedulerContractPredicates' SeLe4n/Kernel/IPC/Invariant.lean
run_check "INVARIANT" rg -n '^theorem endpointReply_preserves_ipcInvariant' SeLe4n/Kernel/IPC/Invariant.lean
run_check "INVARIANT" rg -n '^theorem endpointReply_preserves_schedulerInvariantBundle' SeLe4n/Kernel/IPC/Invariant.lean
run_check "INVARIANT" rg -n '^theorem endpointReply_preserves_ipcSchedulerContractPredicates' SeLe4n/Kernel/IPC/Invariant.lean
run_check "INVARIANT" rg -n '^theorem endpointReplyRecv_preserves_ipcInvariant' SeLe4n/Kernel/IPC/Invariant.lean
run_check "INVARIANT" rg -n '^theorem endpointReplyRecv_preserves_schedulerInvariantBundle' SeLe4n/Kernel/IPC/Invariant.lean
run_check "INVARIANT" rg -n '^theorem endpointReplyRecv_preserves_ipcSchedulerContractPredicates' SeLe4n/Kernel/IPC/Invariant.lean

# WS-F2 untyped memory invariant preservation anchors.
run_check "INVARIANT" rg -n '^theorem retypeFromUntyped_preserves_untypedMemoryInvariant' SeLe4n/Kernel/Lifecycle/Invariant.lean
run_check "INVARIANT" rg -n '^theorem allocate_preserves_childrenWithinWatermark' SeLe4n/Model/Object.lean
run_check "INVARIANT" rg -n '^theorem allocate_preserves_childrenNonOverlap' SeLe4n/Model/Object.lean
run_check "INVARIANT" rg -n '^theorem allocate_preserves_childrenUniqueIds' SeLe4n/Model/Object.lean

# WS-D3 F-16 module docstring classification anchors must remain present.
run_check "INVARIANT" rg -n '^/-!' SeLe4n/Kernel/Scheduler/Invariant.lean
run_check "INVARIANT" rg -n '^/-!' SeLe4n/Kernel/IPC/Invariant.lean
run_check "INVARIANT" rg -n '^/-!' SeLe4n/Kernel/Capability/Invariant.lean
run_check "INVARIANT" rg -n '^/-!' SeLe4n/Kernel/Lifecycle/Invariant.lean
run_check "INVARIANT" rg -n '^/-!' SeLe4n/Kernel/InformationFlow/Invariant.lean
run_check "INVARIANT" rg -n '^/-!' SeLe4n/Kernel/Service/Invariant.lean
run_check "INVARIANT" rg -n '^/-!' SeLe4n/Kernel/Architecture/Invariant.lean

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
# WS-G7: migrated from endpointAwaitReceive to endpointReceiveDual
run_check "TRACE" rg -n 'endpointReceiveDual demoEndpoint 12' SeLe4n/Testing/MainTraceHarness.lean
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


# Full-suite contract should continue to include Tier 3.


run_check "INVARIANT" rg -n '^\s*"schema_version": "1\.0\.0"' tests/scenarios/scenario_catalog.json
run_check "INVARIANT" rg -n '^def validate_catalog' scripts/scenario_catalog.py
run_check "INVARIANT" rg -n '^def nightly_seeds' scripts/scenario_catalog.py
run_check "INVARIANT" rg -n '^run_check "META" python3 "\$\{SCRIPT_DIR\}/scenario_catalog.py" validate' scripts/test_smoke.sh


# WS-E1 F-14 SHA-pinning anchors: all workflow action refs must be SHA-pinned.
run_check "INVARIANT" rg -n '@[0-9a-f]{40}' .github/workflows/lean_action_ci.yml
run_check "INVARIANT" rg -n '@[0-9a-f]{40}' .github/workflows/nightly_determinism.yml
run_check "INVARIANT" rg -n '@[0-9a-f]{40}' .github/workflows/lean_toolchain_update_proposal.yml
run_check "INVARIANT" rg -n '@[0-9a-f]{40}' .github/workflows/platform_security_baseline.yml

# WS-E1 M-11 runtime invariant check anchors must remain present.
run_check "INVARIANT" rg -n 'cspaceSlotCoherencyChecks' SeLe4n/Testing/InvariantChecks.lean
run_check "INVARIANT" rg -n 'capabilityRightsStructuralChecks' SeLe4n/Testing/InvariantChecks.lean
run_check "INVARIANT" rg -n 'lifecycleMetadataChecks' SeLe4n/Testing/InvariantChecks.lean
run_check "INVARIANT" rg -n 'serviceGraphAcyclicityChecks' SeLe4n/Testing/InvariantChecks.lean
run_check "INVARIANT" rg -n 'vspaceAsidUniquenessChecks' SeLe4n/Testing/InvariantChecks.lean
# WS-G3/F-P06: ASID table consistency runtime checks must remain present.
run_check "INVARIANT" rg -n 'asidTableConsistencyChecks' SeLe4n/Testing/InvariantChecks.lean

# WS-G7/F-P11: notification waiter consistency runtime checks must remain present.
run_check "INVARIANT" rg -n 'notificationWaiterConsistentChecks' SeLe4n/Testing/InvariantChecks.lean
run_check "INVARIANT" rg -n 'default_notificationWaiterConsistent' SeLe4n/Kernel/IPC/Invariant.lean

# WS-E1 M-10 parameterized topology anchors must remain present.
run_check "INVARIANT" rg -n 'buildParameterizedTopology' SeLe4n/Testing/MainTraceHarness.lean
run_check "INVARIANT" rg -n 'runParameterizedTopologies' SeLe4n/Testing/MainTraceHarness.lean
run_check "TRACE" rg -n 'parameterized topology ok' tests/fixtures/main_trace_smoke.expected

# WS-H12a: L-07 structured trace format anchors removed (scenario_id format retired).

# WS-E1 L-08 theorem-body validation anchors.
run_check "HYGIENE" rg -n 'L-08.*theorem-body spot-check' scripts/test_tier0_hygiene.sh

# WS-F2 untyped memory model anchors must remain present.
run_check "INVARIANT" rg -n '^structure UntypedChild' SeLe4n/Model/Object.lean
run_check "INVARIANT" rg -n '^structure UntypedObject' SeLe4n/Model/Object.lean
run_check "INVARIANT" rg -n '^def retypeFromUntyped' SeLe4n/Kernel/Lifecycle/Operations.lean
run_check "INVARIANT" rg -n '^theorem retypeFromUntyped_ok_decompose' SeLe4n/Kernel/Lifecycle/Operations.lean
run_check "INVARIANT" rg -n '^theorem retypeFromUntyped_error_typeMismatch' SeLe4n/Kernel/Lifecycle/Operations.lean
run_check "INVARIANT" rg -n '^theorem retypeFromUntyped_error_allocSizeTooSmall' SeLe4n/Kernel/Lifecycle/Operations.lean
run_check "INVARIANT" rg -n '^theorem retypeFromUntyped_error_regionExhausted' SeLe4n/Kernel/Lifecycle/Operations.lean
run_check "INVARIANT" rg -n '^def untypedMemoryInvariant' SeLe4n/Kernel/Lifecycle/Invariant.lean
run_check "INVARIANT" rg -n '^theorem default_systemState_untypedMemoryInvariant' SeLe4n/Kernel/Lifecycle/Invariant.lean
run_check "INVARIANT" rg -n '^theorem retypeFromUntyped_preserves_lifecycleMetadataConsistent' SeLe4n/Kernel/Lifecycle/Invariant.lean
run_check "INVARIANT" rg -n '^theorem retypeFromUntyped_preserves_lifecycleInvariantBundle' SeLe4n/Kernel/Lifecycle/Invariant.lean
run_check "INVARIANT" rg -n '^\s*\| untypedRegionExhausted' SeLe4n/Model/State.lean
run_check "INVARIANT" rg -n '^\s*\| untypedTypeMismatch' SeLe4n/Model/State.lean
run_check "INVARIANT" rg -n '^\s*\| untypedDeviceRestriction' SeLe4n/Model/State.lean
run_check "INVARIANT" rg -n '^\s*\| untypedAllocSizeTooSmall' SeLe4n/Model/State.lean
run_check "TRACE" rg -n 'retype-from-untyped success object kind' SeLe4n/Testing/MainTraceHarness.lean
run_check "TRACE" rg -n 'retype-from-untyped type-mismatch branch' SeLe4n/Testing/MainTraceHarness.lean
run_check "TRACE" rg -n 'retype-from-untyped region-exhausted branch' SeLe4n/Testing/MainTraceHarness.lean
run_check "TRACE" rg -n 'retype-from-untyped device-restriction branch' SeLe4n/Testing/MainTraceHarness.lean
run_check "TRACE" rg -n 'retype-from-untyped alloc-size-too-small branch' SeLe4n/Testing/MainTraceHarness.lean
run_check "TRACE" rg -n 'F2-01.*retype-from-untyped success' tests/fixtures/main_trace_smoke.expected
run_check "TRACE" rg -n 'F2-03.*retype-from-untyped type-mismatch' tests/fixtures/main_trace_smoke.expected
run_check "TRACE" rg -n 'F2-04.*retype-from-untyped region-exhausted' tests/fixtures/main_trace_smoke.expected
run_check "TRACE" rg -n 'F2-06.*retype-from-untyped device-restriction' tests/fixtures/main_trace_smoke.expected
run_check "TRACE" rg -n 'F2-08.*retype-from-untyped alloc-size-too-small' tests/fixtures/main_trace_smoke.expected
run_check "INVARIANT" rg -n 'untypedWatermarkChecks' SeLe4n/Testing/InvariantChecks.lean
run_check "INVARIANT" rg -n 'F2.*retype' tests/NegativeStateSuite.lean

# WS-F3 information-flow completeness anchors must remain present.
# Projection extensions (CRIT-02):
run_check "INVARIANT" rg -n '^def projectKernelObject' SeLe4n/Kernel/InformationFlow/Projection.lean
run_check "INVARIANT" rg -n '^def capTargetObservable' SeLe4n/Kernel/InformationFlow/Projection.lean
run_check "INVARIANT" rg -n '^def projectActiveDomain' SeLe4n/Kernel/InformationFlow/Projection.lean
run_check "INVARIANT" rg -n '^def projectIrqHandlers' SeLe4n/Kernel/InformationFlow/Projection.lean
run_check "INVARIANT" rg -n '^def projectObjectIndex' SeLe4n/Kernel/InformationFlow/Projection.lean
run_check "INVARIANT" rg -n '^\s*activeDomain' SeLe4n/Kernel/InformationFlow/Projection.lean
# CNode slot filtering safety theorems (F-22):
run_check "INVARIANT" rg -n '^theorem projectKernelObject_idempotent' SeLe4n/Kernel/InformationFlow/Projection.lean
run_check "INVARIANT" rg -n '^theorem projectKernelObject_objectType' SeLe4n/Kernel/InformationFlow/Projection.lean
# NI theorems (CRIT-03/F-21):
run_check "INVARIANT" rg -n '^theorem notificationSignal_preserves_lowEquivalent' SeLe4n/Kernel/InformationFlow/Invariant.lean
run_check "INVARIANT" rg -n '^theorem notificationWait_preserves_lowEquivalent' SeLe4n/Kernel/InformationFlow/Invariant.lean
run_check "INVARIANT" rg -n '^theorem serviceRestart_preserves_lowEquivalent' SeLe4n/Kernel/InformationFlow/Invariant.lean
run_check "INVARIANT" rg -n '^theorem cspaceInsertSlot_preserves_lowEquivalent' SeLe4n/Kernel/InformationFlow/Invariant.lean
# Enforcement-NI bridge (F-20):
run_check "INVARIANT" rg -n '^theorem endpointSendDualChecked_NI' SeLe4n/Kernel/InformationFlow/Invariant.lean
run_check "INVARIANT" rg -n '^theorem cspaceMintChecked_NI' SeLe4n/Kernel/InformationFlow/Invariant.lean
run_check "INVARIANT" rg -n '^theorem serviceRestartChecked_NI' SeLe4n/Kernel/InformationFlow/Invariant.lean
# Composed NI framework (H-05):
run_check "INVARIANT" rg -n '^inductive NonInterferenceStep' SeLe4n/Kernel/InformationFlow/Invariant.lean
run_check "INVARIANT" rg -n '^theorem composedNonInterference_trace' SeLe4n/Kernel/InformationFlow/Invariant.lean
# WS-F3 test suite coverage:
run_check "TRACE" rg -n 'WS-F3.*activeDomain' tests/InformationFlowSuite.lean
run_check "TRACE" rg -n 'WS-F3.*IRQ handler' tests/InformationFlowSuite.lean
run_check "TRACE" rg -n 'WS-F3/F-22.*CNode' tests/InformationFlowSuite.lean
run_check "TRACE" rg -n 'WS-F3.*serviceRestartChecked' tests/InformationFlowSuite.lean
run_check "TRACE" rg -n 'WS-F3.*7-field low-equivalence' tests/InformationFlowSuite.lean

# WS-F4 proof gap closure anchors — timerTick, cspaceMutate, cspaceRevoke, notification preservation.
run_check "INVARIANT" rg -n '^theorem timerTick_preserves_schedulerInvariantBundle' SeLe4n/Kernel/Scheduler/Operations.lean
run_check "INVARIANT" rg -n '^theorem timerTick_preserves_kernelInvariant' SeLe4n/Kernel/Scheduler/Operations.lean
run_check "INVARIANT" rg -n '^theorem cspaceMutate_preserves_capabilityInvariantBundle' SeLe4n/Kernel/Capability/Invariant.lean
run_check "INVARIANT" rg -n '^theorem cspaceRevokeCdt_preserves_capabilityInvariantBundle' SeLe4n/Kernel/Capability/Invariant.lean
run_check "INVARIANT" rg -n '^theorem cspaceRevokeCdtStrict_preserves_capabilityInvariantBundle' SeLe4n/Kernel/Capability/Invariant.lean
run_check "INVARIANT" rg -n '^theorem notificationSignal_preserves_ipcInvariant' SeLe4n/Kernel/IPC/Invariant.lean
run_check "INVARIANT" rg -n '^theorem notificationSignal_preserves_schedulerInvariantBundle' SeLe4n/Kernel/IPC/Invariant.lean
run_check "INVARIANT" rg -n '^theorem notificationWait_preserves_ipcInvariant' SeLe4n/Kernel/IPC/Invariant.lean
run_check "INVARIANT" rg -n '^theorem notificationWait_preserves_schedulerInvariantBundle' SeLe4n/Kernel/IPC/Invariant.lean
run_check "INVARIANT" rg -n '^theorem notificationSignal_preserves_ipcSchedulerContractPredicates' SeLe4n/Kernel/IPC/Invariant.lean
run_check "INVARIANT" rg -n '^theorem notificationWait_preserves_ipcSchedulerContractPredicates' SeLe4n/Kernel/IPC/Invariant.lean

# WS-H5 dual-queue structural invariant anchors — predicate definitions + preservation theorems.
run_check "INVARIANT" rg -n '^def intrusiveQueueWellFormed' SeLe4n/Kernel/IPC/Invariant.lean
run_check "INVARIANT" rg -n '^def tcbQueueLinkIntegrity' SeLe4n/Kernel/IPC/Invariant.lean
run_check "INVARIANT" rg -n '^def dualQueueEndpointWellFormed' SeLe4n/Kernel/IPC/Invariant.lean
run_check "INVARIANT" rg -n '^def dualQueueSystemInvariant' SeLe4n/Kernel/IPC/Invariant.lean
run_check "INVARIANT" rg -n '^def ipcInvariantFull' SeLe4n/Kernel/IPC/Invariant.lean
run_check "INVARIANT" rg -n '^theorem intrusiveQueueWellFormed_empty' SeLe4n/Kernel/IPC/Invariant.lean
run_check "INVARIANT" rg -n '^theorem tcbQueueLink_forward_safe' SeLe4n/Kernel/IPC/Invariant.lean
run_check "INVARIANT" rg -n '^theorem tcbQueueLink_reverse_safe' SeLe4n/Kernel/IPC/Invariant.lean
run_check "INVARIANT" rg -n '^theorem endpointQueuePopHead_sender_exists' SeLe4n/Kernel/IPC/Invariant.lean
run_check "INVARIANT" rg -n '^theorem endpointQueuePopHead_link_safe' SeLe4n/Kernel/IPC/Invariant.lean
run_check "INVARIANT" rg -n '^theorem endpointReceiveDual_sender_exists' SeLe4n/Kernel/IPC/Invariant.lean
run_check "INVARIANT" rg -n '^theorem endpointQueuePopHead_preserves_dualQueueSystemInvariant' SeLe4n/Kernel/IPC/Invariant.lean
run_check "INVARIANT" rg -n '^theorem endpointQueueEnqueue_preserves_dualQueueSystemInvariant' SeLe4n/Kernel/IPC/Invariant.lean
run_check "INVARIANT" rg -n '^theorem endpointSendDual_preserves_dualQueueSystemInvariant' SeLe4n/Kernel/IPC/Invariant.lean
run_check "INVARIANT" rg -n '^theorem endpointReceiveDual_preserves_dualQueueSystemInvariant' SeLe4n/Kernel/IPC/Invariant.lean
run_check "INVARIANT" rg -n '^theorem endpointCall_preserves_dualQueueSystemInvariant' SeLe4n/Kernel/IPC/Invariant.lean
run_check "INVARIANT" rg -n '^theorem endpointReply_preserves_dualQueueSystemInvariant' SeLe4n/Kernel/IPC/Invariant.lean
run_check "INVARIANT" rg -n '^theorem endpointReplyRecv_preserves_dualQueueSystemInvariant' SeLe4n/Kernel/IPC/Invariant.lean

finalize_report
