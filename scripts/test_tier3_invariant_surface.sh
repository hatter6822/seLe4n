#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
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
run_check "INVARIANT" rg -n '^structure VSpaceRoot' SeLe4n/Model/Object/Structures.lean
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
run_check "INVARIANT" rg -n '^inductive ResolveError' SeLe4n/Model/Object/Structures.lean
run_check "INVARIANT" rg -n '^def resolveSlot' SeLe4n/Model/Object/Structures.lean
run_check "INVARIANT" rg -n '^def cspaceResolvePath' SeLe4n/Kernel/Capability/Operations.lean
run_check "INVARIANT" rg -n '^def cspaceLookupPath' SeLe4n/Kernel/Capability/Operations.lean

# WS-B6 closure anchors: notification IPC object model and transition surface.
run_check "INVARIANT" rg -n '^inductive NotificationState' SeLe4n/Model/Object/Types.lean
run_check "INVARIANT" rg -n '^structure Notification' SeLe4n/Model/Object/Types.lean
run_check "INVARIANT" rg -n '^def notificationSignal' SeLe4n/Kernel/IPC/Operations/Endpoint.lean
run_check "INVARIANT" rg -n '^def notificationWait' SeLe4n/Kernel/IPC/Operations/Endpoint.lean
run_check "INVARIANT" rg -n '^def notificationInvariant' SeLe4n/Kernel/IPC/Invariant/Defs.lean

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

# WS-H15a: InterruptBoundaryContract decidability fields
run_check "INVARIANT" rg -n '^\s*irqLineSupportedDecidable' SeLe4n/Kernel/Architecture/Assumptions.lean
run_check "INVARIANT" rg -n '^\s*irqHandlerMappedDecidable' SeLe4n/Kernel/Architecture/Assumptions.lean

# WS-H15a: Decidability consistency theorems
run_check "INVARIANT" rg -n '^theorem irqLineSupported_decidable_consistent' SeLe4n/Kernel/Architecture/Assumptions.lean
run_check "INVARIANT" rg -n '^theorem irqHandlerMapped_decidable_consistent' SeLe4n/Kernel/Architecture/Assumptions.lean

# WS-H15b: RPi5 platform hardening anchors
run_check "INVARIANT" rg -n '^def mmioRegions' SeLe4n/Platform/RPi5/Board.lean
run_check "INVARIANT" rg -n '^def mmioRegionDisjointCheck' SeLe4n/Platform/RPi5/Board.lean
run_check "INVARIANT" rg -n '^theorem mmioRegionDisjoint_holds' SeLe4n/Platform/RPi5/Board.lean
run_check "INVARIANT" rg -n '^theorem rpi5MachineConfig_wellFormed' SeLe4n/Platform/RPi5/Board.lean

# WS-H15c: Syscall capability-checking wrappers
run_check "INVARIANT" rg -n '^structure SyscallGate' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n '^def syscallLookupCap' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n '^def syscallInvoke' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n '^theorem syscallLookupCap_implies_capability_held' SeLe4n/Kernel/API.lean
# W3: syscallLookupCap_state_unchanged removed as dead code (trivially follows from
# syscallLookupCap_implies_capability_held which provides the same state-unchanged guarantee).
run_check "INVARIANT" rg -n '^theorem syscallInvoke_requires_right' SeLe4n/Kernel/API.lean
# S5-A: Deprecated api* wrappers removed in v0.19.4. Verify removal and
# presence of production syscall dispatch path.
run_check "INVARIANT" rg -n '^def dispatchSyscall' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n '^def syscallEntry' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n '^private def dispatchWithCap' SeLe4n/Kernel/API.lean
# S5-G: Page-alignment check in retypeFromUntyped
run_check "INVARIANT" rg -n '^def requiresPageAlignment' SeLe4n/Kernel/Lifecycle/Operations.lean
run_check "INVARIANT" rg -n '^def allocationBasePageAligned' SeLe4n/Kernel/Lifecycle/Operations.lean

# WS-H15d: AdapterProofHooks concrete instantiation (Sim + RPi5)
run_check "INVARIANT" rg -n '^theorem advanceTimerState_preserves_proofLayerInvariantBundle' SeLe4n/Kernel/Architecture/Invariant.lean
run_check "INVARIANT" rg -n '^def simRestrictiveAdapterProofHooks' SeLe4n/Platform/Sim/ProofHooks.lean
run_check "INVARIANT" rg -n '^theorem simRestrictive_adapterAdvanceTimer_preserves' SeLe4n/Platform/Sim/ProofHooks.lean
run_check "INVARIANT" rg -n '^theorem simRestrictive_adapterWriteRegister_preserves' SeLe4n/Platform/Sim/ProofHooks.lean
run_check "INVARIANT" rg -n '^theorem simRestrictive_adapterReadMemory_preserves' SeLe4n/Platform/Sim/ProofHooks.lean
# S5-D: Substantive simulation proof hooks
run_check "INVARIANT" rg -n '^def simSubstantiveAdapterProofHooks' SeLe4n/Platform/Sim/ProofHooks.lean
run_check "INVARIANT" rg -n '^theorem simSubstantive_adapterAdvanceTimer_preserves' SeLe4n/Platform/Sim/ProofHooks.lean
run_check "INVARIANT" rg -n '^def rpi5RestrictiveAdapterProofHooks' SeLe4n/Platform/RPi5/ProofHooks.lean
run_check "INVARIANT" rg -n '^theorem rpi5Restrictive_adapterAdvanceTimer_preserves' SeLe4n/Platform/RPi5/ProofHooks.lean
run_check "INVARIANT" rg -n '^theorem rpi5Restrictive_adapterWriteRegister_preserves' SeLe4n/Platform/RPi5/ProofHooks.lean
run_check "INVARIANT" rg -n '^theorem rpi5Restrictive_adapterReadMemory_preserves' SeLe4n/Platform/RPi5/ProofHooks.lean
run_check "INVARIANT" rg -n '^def rpi5RuntimeContractRestrictive' SeLe4n/Platform/RPi5/RuntimeContract.lean

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
run_check "INVARIANT" rg -n '^def capabilityInvariantBundle' SeLe4n/Kernel/Capability/Invariant/Defs.lean
run_check "INVARIANT" rg -n '^def coreIpcInvariantBundle' SeLe4n/Kernel/Capability/Invariant/Preservation.lean

# M1 closure anchors: scheduler transition APIs + preservation theorem entrypoints.
run_check "INVARIANT" rg -n '^def chooseThread' SeLe4n/Kernel/Scheduler/Operations/Core.lean
run_check "INVARIANT" rg -n '^def schedule' SeLe4n/Kernel/Scheduler/Operations/Core.lean
run_check "INVARIANT" rg -n '^def handleYield' SeLe4n/Kernel/Scheduler/Operations/Core.lean
run_check "INVARIANT" rg -n '^theorem chooseThread_preserves_schedulerInvariantBundle' SeLe4n/Kernel/Scheduler/Operations/Preservation.lean
run_check "INVARIANT" rg -n '^theorem schedule_preserves_schedulerInvariantBundle' SeLe4n/Kernel/Scheduler/Operations/Preservation.lean
run_check "INVARIANT" rg -n '^theorem handleYield_preserves_schedulerInvariantBundle' SeLe4n/Kernel/Scheduler/Operations/Preservation.lean

# M2 closure anchors: CSpace transition APIs + capability-bundle preservation theorem entrypoints.
run_check "INVARIANT" rg -n '^def cspaceLookupSlot' SeLe4n/Kernel/Capability/Operations.lean
run_check "INVARIANT" rg -n '^def cspaceInsertSlot' SeLe4n/Kernel/Capability/Operations.lean
run_check "INVARIANT" rg -n '^def cspaceMint' SeLe4n/Kernel/Capability/Operations.lean
run_check "INVARIANT" rg -n '^def cspaceDeleteSlot' SeLe4n/Kernel/Capability/Operations.lean
run_check "INVARIANT" rg -n '^def cspaceRevoke' SeLe4n/Kernel/Capability/Operations.lean
run_check "INVARIANT" rg -n '^theorem cspaceInsertSlot_preserves_capabilityInvariantBundle' SeLe4n/Kernel/Capability/Invariant/Preservation.lean
run_check "INVARIANT" rg -n '^theorem cspaceMint_preserves_capabilityInvariantBundle' SeLe4n/Kernel/Capability/Invariant/Preservation.lean
run_check "INVARIANT" rg -n '^theorem cspaceDeleteSlot_preserves_capabilityInvariantBundle' SeLe4n/Kernel/Capability/Invariant/Preservation.lean
run_check "INVARIANT" rg -n '^theorem cspaceRevoke_preserves_capabilityInvariantBundle' SeLe4n/Kernel/Capability/Invariant/Preservation.lean

# C-01 remediation: non-tautological slot-uniqueness infrastructure at CNode level.
run_check "INVARIANT" rg -n '^def slotsUnique' SeLe4n/Model/Object/Structures.lean
run_check "INVARIANT" rg -n '^theorem insert_slotsUnique' SeLe4n/Model/Object/Structures.lean
run_check "INVARIANT" rg -n '^theorem remove_slotsUnique' SeLe4n/Model/Object/Structures.lean
run_check "INVARIANT" rg -n '^theorem revokeTargetLocal_slotsUnique' SeLe4n/Model/Object/Structures.lean
run_check "INVARIANT" rg -n '^theorem lookup_mem_of_some' SeLe4n/Model/Object/Structures.lean
run_check "INVARIANT" rg -n '^theorem mem_lookup_of_slotsUnique' SeLe4n/Model/Object/Structures.lean
# C-01/H-01 remediation: reformulated invariant definitions (non-tautological).
run_check "INVARIANT" rg -n 'cn.slotsUnique' SeLe4n/Kernel/Capability/Invariant/Preservation.lean
run_check "INVARIANT" rg -n '^theorem cspaceLookupSound_of_cspaceSlotUnique' SeLe4n/Kernel/Capability/Invariant/Authority.lean
run_check "INVARIANT" rg -n '^theorem capabilityInvariantBundle_of_slotUnique' SeLe4n/Kernel/Capability/Invariant/Authority.lean
# H-01 remediation: compositional storeObject transfer lemmas.
run_check "INVARIANT" rg -n '^theorem cspaceSlotUnique_of_storeObject_nonCNode' SeLe4n/Kernel/Capability/Invariant/Authority.lean
run_check "INVARIANT" rg -n '^theorem cspaceSlotUnique_of_storeObject_cnode' SeLe4n/Kernel/Capability/Invariant/Authority.lean
# H-03 remediation: badge/notification routing consistency chain.
run_check "INVARIANT" rg -n '^theorem mintDerivedCap_badge_propagated' SeLe4n/Kernel/Capability/Invariant/Authority.lean
run_check "INVARIANT" rg -n '^theorem notificationSignal_badge_stored_fresh' SeLe4n/Kernel/Capability/Invariant/Authority.lean
run_check "INVARIANT" rg -n '^theorem notificationWait_recovers_pending_badge' SeLe4n/Kernel/Capability/Invariant/Authority.lean
run_check "INVARIANT" rg -n '^theorem badge_notification_routing_consistent' SeLe4n/Kernel/Capability/Invariant/Authority.lean
run_check "INVARIANT" rg -n '^theorem badge_merge_idempotent' SeLe4n/Kernel/Capability/Invariant/Authority.lean

# WS-H12a: Legacy M3 seed/M3.5 step-2 anchors removed — replaced by dual-queue operations.
# Dual-queue transition definition anchors:
run_check "INVARIANT" rg -n '^def endpointSendDual' SeLe4n/Kernel/IPC/DualQueue/Transport.lean
run_check "INVARIANT" rg -n '^def endpointReceiveDual' SeLe4n/Kernel/IPC/DualQueue/Transport.lean

# M3.5 step-3 scheduler-contract predicate anchors must remain present.
run_check "INVARIANT" rg -n '^def runnableThreadIpcReady' SeLe4n/Kernel/IPC/Invariant/Defs.lean
run_check "INVARIANT" rg -n '^def blockedOnSendNotRunnable' SeLe4n/Kernel/IPC/Invariant/Defs.lean
run_check "INVARIANT" rg -n '^def blockedOnReceiveNotRunnable' SeLe4n/Kernel/IPC/Invariant/Defs.lean
run_check "INVARIANT" rg -n '^def ipcSchedulerContractPredicates' SeLe4n/Kernel/IPC/Invariant/Defs.lean
# WS-H12a: Legacy per-operation ipcSchedulerContractPredicates anchors removed.
# Dual-queue equivalents are in IPC/Invariant.lean (endpointSendDual/ReceiveDual/Call/Reply/ReplyRecv).

# M3.5 step-4 composed bundle anchors must remain present.
run_check "INVARIANT" rg -n '^def ipcSchedulerRunnableReadyComponent' SeLe4n/Kernel/Capability/Invariant/Preservation.lean
run_check "INVARIANT" rg -n '^def ipcSchedulerBlockedSendComponent' SeLe4n/Kernel/Capability/Invariant/Preservation.lean
run_check "INVARIANT" rg -n '^def ipcSchedulerBlockedReceiveComponent' SeLe4n/Kernel/Capability/Invariant/Preservation.lean
run_check "INVARIANT" rg -n '^def ipcSchedulerCoherenceComponent' SeLe4n/Kernel/Capability/Invariant/Preservation.lean
run_check "INVARIANT" rg -n '^theorem ipcSchedulerCoherenceComponent_iff_contractPredicates' SeLe4n/Kernel/Capability/Invariant/Preservation.lean
run_check "INVARIANT" rg -n '^def ipcSchedulerCouplingInvariantBundle' SeLe4n/Kernel/Capability/Invariant/Preservation.lean
# WS-H12a: Legacy coupling/local-first preservation anchors removed.
# Dual-queue preservation is verified via dualQueueSystemInvariant anchors below.

# M3.5 step-5 helper-lemma anchors must remain present.
run_check "INVARIANT" rg -n '^theorem tcb_lookup_of_endpoint_store' SeLe4n/Kernel/IPC/Invariant/Defs.lean
run_check "INVARIANT" rg -n '^theorem runnable_membership_of_endpoint_store' SeLe4n/Kernel/IPC/Invariant/Defs.lean
run_check "INVARIANT" rg -n '^theorem not_runnable_membership_of_endpoint_store' SeLe4n/Kernel/IPC/Invariant/Defs.lean

# Bundle composition guard: M3 seed bundle must compose scheduler + capability + full IPC invariants.
# WS-H12e: Updated from ipcInvariant to ipcInvariantFull (includes dualQueueSystemInvariant + allPendingMessagesBounded).
run_check "INVARIANT" rg -n '^\s*schedulerInvariantBundle st ∧ capabilityInvariantBundle st ∧ ipcInvariantFull st' SeLe4n/Kernel/Capability/Invariant/Preservation.lean

# M3.5 step-1 state-model anchors must remain present.
# WS-H12a: waitingReceiver removed from Endpoint (dual-queue uses sendQ/receiveQ).
# WS-H12a: endpointQueueWellFormed/endpointObjectValid removed (subsumed by dualQueueSystemInvariant).
run_check "INVARIANT" rg -n '^inductive ThreadIpcState' SeLe4n/Model/Object/Types.lean
run_check "INVARIANT" rg -n '^\s*ipcState\s*:\s*ThreadIpcState' SeLe4n/Model/Object/Types.lean
run_check "INVARIANT" rg -n '^\s*sendQ\s*:\s*IntrusiveQueue' SeLe4n/Model/Object/Types.lean
run_check "INVARIANT" rg -n '^\s*receiveQ\s*:\s*IntrusiveQueue' SeLe4n/Model/Object/Types.lean


# M4-A step-1 lifecycle metadata anchors must remain present.
run_check "INVARIANT" rg -n '^structure LifecycleMetadata' SeLe4n/Model/State.lean
run_check "INVARIANT" rg -n '^def lifecycleMetadataConsistent' SeLe4n/Model/State.lean
run_check "INVARIANT" rg -n '^def cspaceRevoke' SeLe4n/Kernel/Capability/Operations.lean
run_check "INVARIANT" rg -n '^theorem cspaceRevoke_local_target_reduction' SeLe4n/Kernel/Capability/Invariant/Authority.lean

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
run_check "INVARIANT" rg -n '^def lifecycleCapabilityStaleAuthorityInvariant' SeLe4n/Kernel/Capability/Invariant/Defs.lean
run_check "INVARIANT" rg -n '^theorem lifecycleCapabilityStaleAuthorityInvariant_of_bundles' SeLe4n/Kernel/Capability/Invariant/Defs.lean

# M4-A step-5 lifecycle preservation entrypoint anchors must remain present.
run_check "INVARIANT" rg -n '^theorem lifecycleRetypeObject_preserves_lifecycleInvariantBundle' SeLe4n/Kernel/Lifecycle/Invariant.lean
run_check "INVARIANT" rg -n '^def lifecycleCompositionInvariantBundle' SeLe4n/Kernel/Capability/Invariant/Preservation.lean
run_check "INVARIANT" rg -n '^theorem lifecycleRetypeObject_preserves_schedulerInvariantBundle' SeLe4n/Kernel/Capability/Invariant/Preservation.lean
run_check "INVARIANT" rg -n '^theorem lifecycleRetypeObject_preserves_capabilityInvariantBundle' SeLe4n/Kernel/Capability/Invariant/Preservation.lean
run_check "INVARIANT" rg -n '^theorem lifecycleRetypeObject_preserves_ipcInvariant' SeLe4n/Kernel/Capability/Invariant/Preservation.lean
run_check "INVARIANT" rg -n '^theorem lifecycleRetypeObject_preserves_coreIpcInvariantBundle' SeLe4n/Kernel/Capability/Invariant/Preservation.lean
run_check "INVARIANT" rg -n '^theorem lifecycleRetypeObject_preserves_lifecycleCompositionInvariantBundle' SeLe4n/Kernel/Capability/Invariant/Preservation.lean

# M4-B WS-C preservation theorem expansion anchors must remain present.
run_check "INVARIANT" rg -n '^theorem lifecycleRevokeDeleteRetype_ok_implies_staged_steps' SeLe4n/Kernel/Lifecycle/Operations.lean
run_check "INVARIANT" rg -n '^theorem lifecycleRevokeDeleteRetype_preserves_capabilityInvariantBundle' SeLe4n/Kernel/Capability/Invariant/Preservation.lean
run_check "INVARIANT" rg -n '^theorem lifecycleRevokeDeleteRetype_preserves_lifecycleCapabilityStaleAuthorityInvariant' SeLe4n/Kernel/Capability/Invariant/Preservation.lean
run_check "INVARIANT" rg -n '^theorem lifecycleRevokeDeleteRetype_error_preserves_lifecycleCompositionInvariantBundle' SeLe4n/Kernel/Capability/Invariant/Preservation.lean

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
run_check "INVARIANT" rg -n '^\s*\| invalidTypeTag' SeLe4n/Model/State.lean
run_check "INVARIANT" rg -n '^def lifecycleRetypeObject' SeLe4n/Kernel/Lifecycle/Operations.lean
run_check "INVARIANT" rg -n '^theorem lifecycleRetypeObject_error_illegalState' SeLe4n/Kernel/Lifecycle/Operations.lean
run_check "INVARIANT" rg -n '^theorem lifecycleRetypeObject_error_illegalAuthority' SeLe4n/Kernel/Lifecycle/Operations.lean
run_check "INVARIANT" rg -n '^theorem lifecycleRetypeObject_success_updates_object' SeLe4n/Kernel/Lifecycle/Operations.lean

# M5-B/Q1: Service registry transition anchors (lifecycle ops removed in Q1).
run_check "INVARIANT" rg -n '^def storeServiceEntry' SeLe4n/Kernel/Service/Operations.lean
run_check "INVARIANT" rg -n '^def serviceHasPathTo' SeLe4n/Kernel/Service/Operations.lean
run_check "INVARIANT" rg -n '^def serviceRegisterDependency' SeLe4n/Kernel/Service/Operations.lean
run_check "INVARIANT" rg -n '^theorem serviceRegisterDependency_error_self_loop' SeLe4n/Kernel/Service/Operations.lean
run_check "INVARIANT" rg -n '^\s*\| policyDenied' SeLe4n/Model/State.lean
run_check "INVARIANT" rg -n '^\s*\| dependencyViolation' SeLe4n/Model/State.lean

# M5-C policy-surface anchors must remain present.
run_check "INVARIANT" rg -n '^abbrev ServicePolicyPredicate' SeLe4n/Kernel/Service/Invariant/Policy.lean
run_check "INVARIANT" rg -n '^def policyBackingObjectTyped' SeLe4n/Kernel/Service/Invariant/Policy.lean
run_check "INVARIANT" rg -n '^def policyOwnerAuthorityRefRecorded' SeLe4n/Kernel/Service/Invariant/Policy.lean
run_check "INVARIANT" rg -n '^def policyOwnerAuthoritySlotPresent' SeLe4n/Kernel/Service/Invariant/Policy.lean
run_check "INVARIANT" rg -n '^def servicePolicySurfaceInvariant' SeLe4n/Kernel/Service/Invariant/Policy.lean
run_check "INVARIANT" rg -n '^theorem policyBackingObjectTyped_of_lifecycleInvariant' SeLe4n/Kernel/Service/Invariant/Policy.lean
run_check "INVARIANT" rg -n '^theorem policyOwnerAuthoritySlotPresent_of_lifecycleInvariant' SeLe4n/Kernel/Service/Invariant/Policy.lean
run_check "INVARIANT" rg -n '^theorem policyOwnerAuthoritySlotPresent_of_capabilityLookup' SeLe4n/Kernel/Service/Invariant/Policy.lean
run_check "INVARIANT" rg -n '^theorem servicePolicySurfaceInvariant_of_lifecycleInvariant' SeLe4n/Kernel/Service/Invariant/Policy.lean
# M5-D/Q1: proof-package anchors (lifecycle preservation theorems removed in Q1).
run_check "INVARIANT" rg -n '^def serviceLifecycleCapabilityInvariantBundle' SeLe4n/Kernel/Service/Invariant/Policy.lean
run_check "INVARIANT" rg -n '^theorem serviceLifecycleCapabilityInvariantBundle_of_components' SeLe4n/Kernel/Service/Invariant/Policy.lean
run_check "INVARIANT" rg -n '^theorem storeServiceState_preserves_servicePolicySurfaceInvariant' SeLe4n/Kernel/Service/Invariant/Policy.lean
run_check "INVARIANT" rg -n '^theorem storeServiceState_preserves_lifecycleInvariantBundle' SeLe4n/Kernel/Service/Invariant/Policy.lean
run_check "INVARIANT" rg -n '^theorem storeServiceState_preserves_capabilityInvariantBundle' SeLe4n/Kernel/Service/Invariant/Policy.lean

# WS-D3 F-06/TPI-D04 badge-override safety anchors must remain present.
run_check "INVARIANT" rg -n '^theorem mintDerivedCap_rights_attenuated_with_badge_override' SeLe4n/Kernel/Capability/Invariant/Authority.lean
run_check "INVARIANT" rg -n '^theorem mintDerivedCap_target_preserved_with_badge_override' SeLe4n/Kernel/Capability/Invariant/Authority.lean
run_check "INVARIANT" rg -n '^theorem cspaceMint_badge_override_safe' SeLe4n/Kernel/Capability/Invariant/Authority.lean

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
run_check "INVARIANT" rg -n '^def serviceDependencyAcyclic' SeLe4n/Kernel/Service/Invariant/Acyclicity.lean
run_check "INVARIANT" rg -n '^theorem serviceRegisterDependency_preserves_acyclicity' SeLe4n/Kernel/Service/Invariant/Acyclicity.lean

# WS-D4 F-11/Q1: serviceRestart failure anchors removed in Q1; replaced with graph invariant anchors.
run_check "INVARIANT" rg -n 'theorem serviceGraphInvariant_of_storeServiceState_sameDeps' SeLe4n/Kernel/Service/Invariant/Acyclicity.lean
run_check "INVARIANT" rg -n '^theorem serviceRegisterDependency_preserves_serviceGraphInvariant' SeLe4n/Kernel/Service/Invariant/Acyclicity.lean

# WS-D4 F-12 double-wait prevention + uniqueness invariant anchors must remain present.
run_check "INVARIANT" rg -n '^\s*\| alreadyWaiting' SeLe4n/Model/State.lean
run_check "INVARIANT" rg -n '^theorem notificationWait_error_alreadyWaiting' SeLe4n/Kernel/IPC/Operations/Endpoint.lean
run_check "INVARIANT" rg -n '^theorem notificationWait_badge_path_notification' SeLe4n/Kernel/IPC/Operations/Endpoint.lean
run_check "INVARIANT" rg -n '^theorem notificationWait_wait_path_notification' SeLe4n/Kernel/IPC/Operations/Endpoint.lean
run_check "INVARIANT" rg -n '^def uniqueWaiters' SeLe4n/Kernel/IPC/Invariant/Defs.lean
run_check "INVARIANT" rg -n '^theorem notificationWait_preserves_uniqueWaiters' SeLe4n/Kernel/IPC/Invariant/Defs.lean

# WS-E4/WS-F1 dual-queue IPC definition and theorem anchors must remain present.
run_check "INVARIANT" rg -n '^def endpointSendDual' SeLe4n/Kernel/IPC/DualQueue/Transport.lean
run_check "INVARIANT" rg -n '^def endpointReceiveDual' SeLe4n/Kernel/IPC/DualQueue/Transport.lean
run_check "INVARIANT" rg -n '^def endpointCall' SeLe4n/Kernel/IPC/DualQueue/Transport.lean
run_check "INVARIANT" rg -n '^def endpointReply' SeLe4n/Kernel/IPC/DualQueue/Transport.lean
run_check "INVARIANT" rg -n '^def endpointReplyRecv' SeLe4n/Kernel/IPC/DualQueue/Transport.lean
run_check "INVARIANT" rg -n '^def endpointQueuePopHead' SeLe4n/Kernel/IPC/DualQueue/Core.lean
run_check "INVARIANT" rg -n '^def endpointQueueEnqueue' SeLe4n/Kernel/IPC/DualQueue/Core.lean
run_check "INVARIANT" rg -n '^def endpointQueueRemoveDual' SeLe4n/Kernel/IPC/DualQueue/Transport.lean
run_check "INVARIANT" rg -n '^theorem endpointQueuePopHead_scheduler_eq' SeLe4n/Kernel/IPC/DualQueue/Transport.lean
run_check "INVARIANT" rg -n '^theorem endpointQueueEnqueue_scheduler_eq' SeLe4n/Kernel/IPC/DualQueue/Transport.lean
run_check "INVARIANT" rg -n '^theorem endpointQueueRemoveDual_scheduler_eq' SeLe4n/Kernel/IPC/DualQueue/Transport.lean
run_check "INVARIANT" rg -n '^theorem endpointQueueRemoveDual_tcb_ipcState_backward' SeLe4n/Kernel/IPC/DualQueue/Transport.lean

# WS-F1 dual-queue preservation theorem anchors (all three invariant families).
run_check "INVARIANT" rg -n '^theorem endpointSendDual_preserves_ipcInvariant' SeLe4n/Kernel/IPC/Invariant/Structural.lean
run_check "INVARIANT" rg -n '^theorem endpointSendDual_preserves_schedulerInvariantBundle' SeLe4n/Kernel/IPC/Invariant/EndpointPreservation.lean
run_check "INVARIANT" rg -n '^theorem endpointSendDual_preserves_ipcSchedulerContractPredicates' SeLe4n/Kernel/IPC/Invariant/EndpointPreservation.lean
run_check "INVARIANT" rg -n '^theorem endpointReceiveDual_preserves_ipcInvariant' SeLe4n/Kernel/IPC/Invariant/Structural.lean
run_check "INVARIANT" rg -n '^theorem endpointReceiveDual_preserves_schedulerInvariantBundle' SeLe4n/Kernel/IPC/Invariant/EndpointPreservation.lean
run_check "INVARIANT" rg -n '^theorem endpointReceiveDual_preserves_ipcSchedulerContractPredicates' SeLe4n/Kernel/IPC/Invariant/EndpointPreservation.lean
run_check "INVARIANT" rg -n '^theorem endpointQueueRemoveDual_preserves_ipcInvariant' SeLe4n/Kernel/IPC/Invariant/EndpointPreservation.lean
run_check "INVARIANT" rg -n '^theorem endpointQueueRemoveDual_preserves_schedulerInvariantBundle' SeLe4n/Kernel/IPC/Invariant/EndpointPreservation.lean
run_check "INVARIANT" rg -n '^theorem endpointQueueRemoveDual_preserves_ipcSchedulerContractPredicates' SeLe4n/Kernel/IPC/Invariant/EndpointPreservation.lean
run_check "INVARIANT" rg -n '^theorem endpointCall_preserves_ipcInvariant' SeLe4n/Kernel/IPC/Invariant/CallReplyRecv.lean
run_check "INVARIANT" rg -n '^theorem endpointCall_preserves_schedulerInvariantBundle' SeLe4n/Kernel/IPC/Invariant/CallReplyRecv.lean
run_check "INVARIANT" rg -n '^theorem endpointCall_preserves_ipcSchedulerContractPredicates' SeLe4n/Kernel/IPC/Invariant/CallReplyRecv.lean
run_check "INVARIANT" rg -n '^theorem endpointReply_preserves_ipcInvariant' SeLe4n/Kernel/IPC/Invariant/Structural.lean
run_check "INVARIANT" rg -n '^theorem endpointReply_preserves_schedulerInvariantBundle' SeLe4n/Kernel/IPC/Invariant/EndpointPreservation.lean
run_check "INVARIANT" rg -n '^theorem endpointReply_preserves_ipcSchedulerContractPredicates' SeLe4n/Kernel/IPC/Invariant/CallReplyRecv.lean
run_check "INVARIANT" rg -n '^theorem endpointReplyRecv_preserves_ipcInvariant' SeLe4n/Kernel/IPC/Invariant/Structural.lean
run_check "INVARIANT" rg -n '^theorem endpointReplyRecv_preserves_schedulerInvariantBundle' SeLe4n/Kernel/IPC/Invariant/CallReplyRecv.lean
run_check "INVARIANT" rg -n '^theorem endpointReplyRecv_preserves_ipcSchedulerContractPredicates' SeLe4n/Kernel/IPC/Invariant/CallReplyRecv.lean

# WS-F2 untyped memory invariant preservation anchors.
run_check "INVARIANT" rg -n '^theorem retypeFromUntyped_preserves_untypedMemoryInvariant' SeLe4n/Kernel/Lifecycle/Invariant.lean
run_check "INVARIANT" rg -n '^theorem allocate_preserves_childrenWithinWatermark' SeLe4n/Model/Object/Types.lean
run_check "INVARIANT" rg -n '^theorem allocate_preserves_childrenNonOverlap' SeLe4n/Model/Object/Types.lean
run_check "INVARIANT" rg -n '^theorem allocate_preserves_childrenUniqueIds' SeLe4n/Model/Object/Types.lean

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
run_check "TRACE" rg -n 'endpointReceiveDual demoEndpoint ⟨12⟩' SeLe4n/Testing/MainTraceHarness.lean
run_check "TRACE" rg -n 'handshake send matched waiting receiver' SeLe4n/Testing/MainTraceHarness.lean
run_check "TRACE" rg -n 'handshake send matched waiting receiver' tests/fixtures/main_trace_smoke.expected
# Q1: Service lifecycle trace anchors replaced with registry trace anchors.
run_check "TRACE" rg -n 'service lookup svcApi' SeLe4n/Testing/MainTraceHarness.lean
run_check "TRACE" rg -n 'store service entry' SeLe4n/Testing/MainTraceHarness.lean
run_check "TRACE" rg -n 'register dependency' SeLe4n/Testing/MainTraceHarness.lean
run_check "TRACE" rg -n 'register self-loop dependency' SeLe4n/Testing/MainTraceHarness.lean
run_check "TRACE" rg -n 'service path svcApi' SeLe4n/Testing/MainTraceHarness.lean
run_check "TRACE" rg -n 'service isolation api↔denied' SeLe4n/Testing/MainTraceHarness.lean
run_check "TRACE" rg -n 'service isolation api↔db' SeLe4n/Testing/MainTraceHarness.lean
run_check "TRACE" rg -n 'service isolation api↔denied: true' tests/fixtures/main_trace_smoke.expected
run_check "TRACE" rg -n 'service isolation api↔db: false' tests/fixtures/main_trace_smoke.expected
run_check "TRACE" rg -n 'register self-loop dependency: SeLe4n.Model.KernelError.cyclicDependency' tests/fixtures/main_trace_smoke.expected
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
run_check "INVARIANT" rg -n 'default_notificationWaiterConsistent' SeLe4n/Kernel/IPC/Invariant/Defs.lean

# WS-E1 M-10 parameterized topology anchors must remain present.
run_check "INVARIANT" rg -n 'buildParameterizedTopology' SeLe4n/Testing/MainTraceHarness.lean
run_check "INVARIANT" rg -n 'runParameterizedTopologies' SeLe4n/Testing/MainTraceHarness.lean
run_check "TRACE" rg -n 'parameterized topology ok' tests/fixtures/main_trace_smoke.expected

# WS-H12a: L-07 structured trace format anchors removed (scenario_id format retired).

# WS-E1 L-08 theorem-body validation anchors.
run_check "HYGIENE" rg -n 'L-08.*theorem-body spot-check' scripts/test_tier0_hygiene.sh

# WS-F2 untyped memory model anchors must remain present.
run_check "INVARIANT" rg -n '^structure UntypedChild' SeLe4n/Model/Object/Types.lean
run_check "INVARIANT" rg -n '^structure UntypedObject' SeLe4n/Model/Object/Types.lean
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
run_check "TRACE" rg -n 'retype-from-untyped success' tests/fixtures/main_trace_smoke.expected
run_check "TRACE" rg -n 'retype-from-untyped type-mismatch' tests/fixtures/main_trace_smoke.expected
run_check "TRACE" rg -n 'retype-from-untyped region-exhausted' tests/fixtures/main_trace_smoke.expected
run_check "TRACE" rg -n 'retype-from-untyped device-restriction' tests/fixtures/main_trace_smoke.expected
run_check "TRACE" rg -n 'retype-from-untyped alloc-size-too-small' tests/fixtures/main_trace_smoke.expected
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
run_check "INVARIANT" rg -n '^theorem notificationSignal_preserves_lowEquivalent' SeLe4n/Kernel/InformationFlow/Invariant/Helpers.lean
run_check "INVARIANT" rg -n '^theorem notificationWait_preserves_lowEquivalent' SeLe4n/Kernel/InformationFlow/Invariant/Helpers.lean
run_check "INVARIANT" rg -n '^theorem cspaceInsertSlot_preserves_lowEquivalent' SeLe4n/Kernel/InformationFlow/Invariant/Helpers.lean
# Enforcement-NI bridge (F-20/Q1: serviceRestartChecked removed):
run_check "INVARIANT" rg -n '^theorem endpointSendDualChecked_NI' SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean
run_check "INVARIANT" rg -n '^theorem cspaceMintChecked_NI' SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean
# Composed NI framework (H-05):
run_check "INVARIANT" rg -n '^inductive NonInterferenceStep' SeLe4n/Kernel/InformationFlow/Invariant/Composition.lean
run_check "INVARIANT" rg -n '^theorem composedNonInterference_trace' SeLe4n/Kernel/InformationFlow/Invariant/Composition.lean
# WS-F3 test suite coverage:
run_check "TRACE" rg -n 'WS-F3.*activeDomain' tests/InformationFlowSuite.lean
run_check "TRACE" rg -n 'WS-F3.*IRQ handler' tests/InformationFlowSuite.lean
run_check "TRACE" rg -n 'WS-F3/F-22.*CNode' tests/InformationFlowSuite.lean
run_check "TRACE" rg -n 'Q1.*Service registry projection' tests/InformationFlowSuite.lean
run_check "TRACE" rg -n 'WS-F3.*7-field low-equivalence' tests/InformationFlowSuite.lean

# WS-F4 proof gap closure anchors — timerTick, cspaceMutate, cspaceRevoke, notification preservation.
run_check "INVARIANT" rg -n '^theorem timerTick_preserves_schedulerInvariantBundle' SeLe4n/Kernel/Scheduler/Operations/Preservation.lean
run_check "INVARIANT" rg -n '^theorem cspaceMutate_preserves_capabilityInvariantBundle' SeLe4n/Kernel/Capability/Invariant/Preservation.lean
run_check "INVARIANT" rg -n '^theorem cspaceRevokeCdt_preserves_capabilityInvariantBundle' SeLe4n/Kernel/Capability/Invariant/Preservation.lean
run_check "INVARIANT" rg -n '^theorem cspaceRevokeCdtStrict_preserves_capabilityInvariantBundle' SeLe4n/Kernel/Capability/Invariant/Preservation.lean
run_check "INVARIANT" rg -n '^theorem notificationSignal_preserves_ipcInvariant' SeLe4n/Kernel/IPC/Invariant/Structural.lean
run_check "INVARIANT" rg -n '^theorem notificationSignal_preserves_schedulerInvariantBundle' SeLe4n/Kernel/IPC/Invariant/NotificationPreservation.lean
run_check "INVARIANT" rg -n '^theorem notificationWait_preserves_ipcInvariant' SeLe4n/Kernel/IPC/Invariant/Structural.lean
run_check "INVARIANT" rg -n '^theorem notificationWait_preserves_schedulerInvariantBundle' SeLe4n/Kernel/IPC/Invariant/NotificationPreservation.lean
run_check "INVARIANT" rg -n '^theorem notificationSignal_preserves_ipcSchedulerContractPredicates' SeLe4n/Kernel/IPC/Invariant/NotificationPreservation.lean
run_check "INVARIANT" rg -n '^theorem notificationWait_preserves_ipcSchedulerContractPredicates' SeLe4n/Kernel/IPC/Invariant/NotificationPreservation.lean

# WS-H5 dual-queue structural invariant anchors — predicate definitions + preservation theorems.
run_check "INVARIANT" rg -n '^def intrusiveQueueWellFormed' SeLe4n/Kernel/IPC/Invariant/Defs.lean
run_check "INVARIANT" rg -n '^def tcbQueueLinkIntegrity' SeLe4n/Kernel/IPC/Invariant/Defs.lean
run_check "INVARIANT" rg -n '^def dualQueueEndpointWellFormed' SeLe4n/Kernel/IPC/Invariant/Defs.lean
run_check "INVARIANT" rg -n '^def dualQueueSystemInvariant' SeLe4n/Kernel/IPC/Invariant/Defs.lean
run_check "INVARIANT" rg -n '^def ipcInvariantFull' SeLe4n/Kernel/IPC/Invariant/Defs.lean
run_check "INVARIANT" rg -n '^theorem intrusiveQueueWellFormed_empty' SeLe4n/Kernel/IPC/Invariant/Structural.lean
run_check "INVARIANT" rg -n '^theorem tcbQueueLink_forward_safe' SeLe4n/Kernel/IPC/Invariant/Structural.lean
run_check "INVARIANT" rg -n '^theorem tcbQueueLink_reverse_safe' SeLe4n/Kernel/IPC/Invariant/Structural.lean
run_check "INVARIANT" rg -n '^theorem endpointQueuePopHead_sender_exists' SeLe4n/Kernel/IPC/Invariant/Structural.lean
run_check "INVARIANT" rg -n '^theorem endpointQueuePopHead_link_safe' SeLe4n/Kernel/IPC/Invariant/Structural.lean
run_check "INVARIANT" rg -n '^theorem endpointReceiveDual_sender_exists' SeLe4n/Kernel/IPC/Invariant/Structural.lean
run_check "INVARIANT" rg -n '^theorem endpointQueuePopHead_preserves_dualQueueSystemInvariant' SeLe4n/Kernel/IPC/Invariant/Structural.lean
run_check "INVARIANT" rg -n '^theorem endpointQueueEnqueue_preserves_dualQueueSystemInvariant' SeLe4n/Kernel/IPC/Invariant/Structural.lean
run_check "INVARIANT" rg -n '^theorem endpointSendDual_preserves_dualQueueSystemInvariant' SeLe4n/Kernel/IPC/Invariant/Structural.lean
run_check "INVARIANT" rg -n '^theorem endpointReceiveDual_preserves_dualQueueSystemInvariant' SeLe4n/Kernel/IPC/Invariant/Structural.lean
run_check "INVARIANT" rg -n '^theorem endpointCall_preserves_dualQueueSystemInvariant' SeLe4n/Kernel/IPC/Invariant/Structural.lean
run_check "INVARIANT" rg -n '^theorem endpointReply_preserves_dualQueueSystemInvariant' SeLe4n/Kernel/IPC/Invariant/Structural.lean
run_check "INVARIANT" rg -n '^theorem endpointReplyRecv_preserves_dualQueueSystemInvariant' SeLe4n/Kernel/IPC/Invariant/Structural.lean

# WS-H12d IPC message payload bounds anchors — predicate definitions + enforcement + theorems.
run_check "INVARIANT" rg -n '^def maxMessageRegisters' SeLe4n/Model/Object/Types.lean
run_check "INVARIANT" rg -n '^def maxExtraCaps' SeLe4n/Model/Object/Types.lean
run_check "INVARIANT" rg -n '^def bounded' SeLe4n/Model/Object/Types.lean
run_check "INVARIANT" rg -n '^def checkBounds' SeLe4n/Model/Object/Types.lean
run_check "INVARIANT" rg -n '^theorem empty_bounded' SeLe4n/Model/Object/Types.lean
run_check "INVARIANT" rg -n '^theorem checkBounds_iff_bounded' SeLe4n/Model/Object/Types.lean
run_check "INVARIANT" rg -n '^def allPendingMessagesBounded' SeLe4n/Kernel/IPC/Invariant/Defs.lean
run_check "INVARIANT" rg -n '^theorem endpointSendDual_message_bounded' SeLe4n/Kernel/IPC/Invariant/EndpointPreservation.lean
run_check "INVARIANT" rg -n '^theorem endpointCall_message_bounded' SeLe4n/Kernel/IPC/Invariant/EndpointPreservation.lean
run_check "INVARIANT" rg -n '^theorem endpointReply_message_bounded' SeLe4n/Kernel/IPC/Invariant/EndpointPreservation.lean
run_check "INVARIANT" rg -n '^theorem endpointReplyRecv_message_bounded' SeLe4n/Kernel/IPC/Invariant/EndpointPreservation.lean
# WS-H12d: KernelError variants for bounds enforcement.
run_check "INVARIANT" rg -n '^\s*\| ipcMessageTooLarge' SeLe4n/Model/State.lean
run_check "INVARIANT" rg -n '^\s*\| ipcMessageTooManyCaps' SeLe4n/Model/State.lean
# WS-H12d: Trace harness and fixture anchors.
run_check "INVARIANT" rg -n '^private def runIpcMessageBoundsTrace' SeLe4n/Testing/MainTraceHarness.lean
run_check "TRACE" rg -n 'H12d oversized registers rejected' tests/fixtures/main_trace_smoke.expected
run_check "TRACE" rg -n 'H12d oversized caps rejected' tests/fixtures/main_trace_smoke.expected
run_check "TRACE" rg -n 'H12d boundary message accepted' tests/fixtures/main_trace_smoke.expected

# WS-H12e: Cross-subsystem invariant reconciliation anchors.
# contextMatchesCurrent defined and included in schedulerInvariantBundleFull.
run_check "INVARIANT" rg -n '^def contextMatchesCurrent' SeLe4n/Kernel/Scheduler/Invariant.lean
run_check "INVARIANT" rg -n 'contextMatchesCurrent st' SeLe4n/Kernel/Scheduler/Invariant.lean
# schedulerInvariantBundleFull includes contextMatchesCurrent (5-conjunct).
run_check "INVARIANT" rg -n '^def schedulerInvariantBundleFull' SeLe4n/Kernel/Scheduler/Invariant.lean
# ipcSchedulerCouplingInvariantBundle includes contextMatchesCurrent + currentThreadDequeueCoherent.
run_check "INVARIANT" rg -n 'contextMatchesCurrent st ∧ currentThreadDequeueCoherent st' SeLe4n/Kernel/Capability/Invariant/Preservation.lean
# proofLayerInvariantBundle uses schedulerInvariantBundleFull.
run_check "INVARIANT" rg -n 'schedulerInvariantBundleFull st' SeLe4n/Kernel/Architecture/Invariant.lean
# Extraction theorems for new components.
run_check "INVARIANT" rg -n '^theorem schedulerInvariantBundleFull_to_contextMatchesCurrent' SeLe4n/Kernel/Scheduler/Invariant.lean
run_check "INVARIANT" rg -n '^theorem coreIpcInvariantBundle_to_ipcInvariant' SeLe4n/Kernel/Capability/Invariant/Preservation.lean
run_check "INVARIANT" rg -n '^theorem coreIpcInvariantBundle_to_dualQueueSystemInvariant' SeLe4n/Kernel/Capability/Invariant/Preservation.lean
run_check "INVARIANT" rg -n '^theorem coreIpcInvariantBundle_to_allPendingMessagesBounded' SeLe4n/Kernel/Capability/Invariant/Preservation.lean
# switchDomain preserves contextMatchesCurrent (new for WS-H12e).
run_check "INVARIANT" rg -n '^theorem switchDomain_preserves_contextMatchesCurrent' SeLe4n/Kernel/Scheduler/Operations/Preservation.lean
# WS-H12e: allPendingMessagesBounded frame lemmas for primitive ops.
run_check "INVARIANT" rg -n '^theorem ensureRunnable_preserves_allPendingMessagesBounded' SeLe4n/Kernel/IPC/Invariant/Structural.lean
run_check "INVARIANT" rg -n '^theorem removeRunnable_preserves_allPendingMessagesBounded' SeLe4n/Kernel/IPC/Invariant/Structural.lean
run_check "INVARIANT" rg -n '^theorem storeTcbIpcState_preserves_allPendingMessagesBounded' SeLe4n/Kernel/IPC/Invariant/Structural.lean
run_check "INVARIANT" rg -n '^theorem storeTcbIpcStateAndMessage_preserves_allPendingMessagesBounded' SeLe4n/Kernel/IPC/Invariant/Structural.lean
run_check "INVARIANT" rg -n '^theorem storeTcbPendingMessage_preserves_allPendingMessagesBounded' SeLe4n/Kernel/IPC/Invariant/Structural.lean
run_check "INVARIANT" rg -n '^theorem storeObject_endpoint_preserves_allPendingMessagesBounded' SeLe4n/Kernel/IPC/Invariant/Structural.lean
run_check "INVARIANT" rg -n '^theorem storeTcbQueueLinks_preserves_allPendingMessagesBounded' SeLe4n/Kernel/IPC/Invariant/Structural.lean
run_check "INVARIANT" rg -n '^theorem storeObject_notification_preserves_allPendingMessagesBounded' SeLe4n/Kernel/IPC/Invariant/Structural.lean
# WS-H12e: Compound allPendingMessagesBounded preservation theorems.
run_check "INVARIANT" rg -n '^theorem notificationSignal_preserves_allPendingMessagesBounded' SeLe4n/Kernel/IPC/Invariant/Structural.lean
run_check "INVARIANT" rg -n '^theorem notificationWait_preserves_allPendingMessagesBounded' SeLe4n/Kernel/IPC/Invariant/Structural.lean
run_check "INVARIANT" rg -n '^theorem endpointReply_preserves_allPendingMessagesBounded' SeLe4n/Kernel/IPC/Invariant/Structural.lean
# WS-H12e: Composed ipcInvariantFull preservation theorems.
run_check "INVARIANT" rg -n '^theorem notificationSignal_preserves_ipcInvariantFull' SeLe4n/Kernel/IPC/Invariant/Structural.lean
run_check "INVARIANT" rg -n '^theorem notificationWait_preserves_ipcInvariantFull' SeLe4n/Kernel/IPC/Invariant/Structural.lean
run_check "INVARIANT" rg -n '^theorem endpointReply_preserves_ipcInvariantFull' SeLe4n/Kernel/IPC/Invariant/Structural.lean
run_check "INVARIANT" rg -n '^theorem endpointSendDual_preserves_ipcInvariantFull' SeLe4n/Kernel/IPC/Invariant/Structural.lean
run_check "INVARIANT" rg -n '^theorem endpointReceiveDual_preserves_ipcInvariantFull' SeLe4n/Kernel/IPC/Invariant/Structural.lean
run_check "INVARIANT" rg -n '^theorem endpointCall_preserves_ipcInvariantFull' SeLe4n/Kernel/IPC/Invariant/Structural.lean
run_check "INVARIANT" rg -n '^theorem endpointReplyRecv_preserves_ipcInvariantFull' SeLe4n/Kernel/IPC/Invariant/Structural.lean

# WS-H12f: Test harness & documentation sync anchors.
# Trace function definitions in MainTraceHarness.
run_check "INVARIANT" rg -n '^private def runDequeueOnDispatchTrace' SeLe4n/Testing/MainTraceHarness.lean
run_check "INVARIANT" rg -n '^private def runInlineContextSwitchTrace' SeLe4n/Testing/MainTraceHarness.lean
run_check "INVARIANT" rg -n '^private def runBoundedMessageExtendedTrace' SeLe4n/Testing/MainTraceHarness.lean
# Fixture output anchors for WS-H12f trace scenarios.
run_check "TRACE" rg -n 'H12f dequeue-on-dispatch current' tests/fixtures/main_trace_smoke.expected
run_check "TRACE" rg -n 'H12f dispatched thread absent from runQueue' tests/fixtures/main_trace_smoke.expected
run_check "TRACE" rg -n 'H12f preempted thread back in runQueue' tests/fixtures/main_trace_smoke.expected
run_check "TRACE" rg -n 'H12f context switch regs match incoming' tests/fixtures/main_trace_smoke.expected
run_check "TRACE" rg -n 'H12f outgoing context saved' tests/fixtures/main_trace_smoke.expected
run_check "TRACE" rg -n 'H12f empty message accepted' tests/fixtures/main_trace_smoke.expected

# ============================================================================
# WS-H16: Testing, Documentation & Cleanup — Semantic Assertions (A-43)
# ============================================================================
# These assertions go beyond name-based anchoring to verify structural
# properties of invariant bundles, preventing regression to trivially-true
# predicates or incomplete coverage.

log_section "INVARIANT" "WS-H16: Semantic invariant surface assertions"

# WS-H16/A-43: capabilityInvariantBundle definition must have at least 5 conjuncts (∧).
# Counts ∧ only in the bundle definition body. Prevents regression to
# trivially-true C-03 scenario.
CIBUNDLE_CONJUNCTS=$(sed -n '/^def capabilityInvariantBundle/,/^$/p' SeLe4n/Kernel/Capability/Invariant/Defs.lean | grep -o '∧' | wc -l)
run_check "INVARIANT" test "${CIBUNDLE_CONJUNCTS}" -ge 5

# WS-H16/A-43: schedulerInvariantBundleFull includes timeSlicePositive.
run_check "INVARIANT" rg -n 'timeSlicePositive st' SeLe4n/Kernel/Scheduler/Invariant.lean

# WS-H16/A-43: schedulerInvariantBundleFull includes edfCurrentHasEarliestDeadline.
run_check "INVARIANT" rg -n 'edfCurrentHasEarliestDeadline st' SeLe4n/Kernel/Scheduler/Invariant.lean

# WS-H16/A-43: schedulerInvariantBundleFull includes contextMatchesCurrent.
run_check "INVARIANT" rg -n 'contextMatchesCurrent st' SeLe4n/Kernel/Scheduler/Invariant.lean

# WS-H16/A-43: NonInterferenceStep has at least 20 constructors (up from 12 pre-H9).
# Counts constructor lines within the inductive definition body.  Uses the next
# top-level declaration (^theorem, ^def, ^/-!) as the end marker instead of ^$,
# which breaks on blank lines inside docstring comments.
NI_CTORS=$(sed -n '/^inductive NonInterferenceStep/,/^\(theorem\|def\|\/\-!\)/p' SeLe4n/Kernel/InformationFlow/Invariant/Composition.lean | grep -c '^\s*| ')
run_check "INVARIANT" test "${NI_CTORS}" -ge 20

# WS-H16/A-13: objectIndexLive predicate exists in Model/State.lean.
run_check "INVARIANT" rg -n '^def objectIndexLive' SeLe4n/Model/State.lean

# WS-H16/A-13: objectIndexLive default theorem exists.
run_check "INVARIANT" rg -n '^theorem objectIndexLive_default' SeLe4n/Model/State.lean

# WS-H16/A-13: objectIndexLive preservation theorem for storeObject exists.
run_check "INVARIANT" rg -n '^theorem storeObject_preserves_objectIndexLive' SeLe4n/Model/State.lean

# W3: runQueueThreadPriorityConsistent removed as dead code (superseded by
# schedulerPriorityMatch in schedulerInvariantBundleFull with full preservation proofs).

# WS-H16/M-18: Lifecycle negative test function exists in NegativeStateSuite.
run_check "INVARIANT" rg -n '^def runWSH16LifecycleChecks' tests/NegativeStateSuite.lean

# WS-H16/A-18: schedule uses O(1) RunQueue membership (not O(n) list scan).
# Verify schedule references runQueue (O(1) HashSet) not runnable (O(n) list).
run_check "INVARIANT" rg -n 'scheduler\.runQueue' SeLe4n/Kernel/Scheduler/Operations/Core.lean

# WS-F6/D1: Reclassified operation-correctness lemmas (removed from capabilityInvariantBundle).
run_check "INVARIANT" rg -n '^theorem cspaceAttenuationRule_holds' SeLe4n/Kernel/Capability/Invariant/Authority.lean
run_check "INVARIANT" rg -n '^theorem lifecycleAuthorityMonotonicity_holds' SeLe4n/Kernel/Capability/Invariant/Authority.lean

# WS-F6/D2: blockedOnNotificationNotRunnable predicate in IPC invariant defs.
run_check "INVARIANT" rg -n '^def blockedOnNotificationNotRunnable' SeLe4n/Kernel/IPC/Invariant/Defs.lean

# WS-F6/D2: ipcSchedulerBlockedNotificationComponent in capability preservation.
run_check "INVARIANT" rg -n '^def ipcSchedulerBlockedNotificationComponent' SeLe4n/Kernel/Capability/Invariant/Preservation.lean

# WS-F6/D3: runnableThreadsAreTCBs predicate and preservation theorems.
run_check "INVARIANT" rg -n '^def runnableThreadsAreTCBs' SeLe4n/Kernel/Scheduler/Invariant.lean
run_check "INVARIANT" rg -n '^theorem default_runnableThreadsAreTCBs' SeLe4n/Kernel/Scheduler/Invariant.lean
# W3: runnableThreadsAreTCBs_of_scheduler_objects_eq removed (dead frame lemma).
run_check "INVARIANT" rg -n '^theorem switchDomain_preserves_runnableThreadsAreTCBs' SeLe4n/Kernel/Scheduler/Operations/Preservation.lean
run_check "INVARIANT" rg -n '^theorem schedule_preserves_runnableThreadsAreTCBs' SeLe4n/Kernel/Scheduler/Operations/Preservation.lean
run_check "INVARIANT" rg -n '^theorem handleYield_preserves_runnableThreadsAreTCBs' SeLe4n/Kernel/Scheduler/Operations/Preservation.lean
run_check "INVARIANT" rg -n '^theorem timerTick_preserves_runnableThreadsAreTCBs' SeLe4n/Kernel/Scheduler/Operations/Preservation.lean

# WS-F6/D4: serviceCountBounded and serviceGraphInvariant default-state proofs.
run_check "INVARIANT" rg -n '^theorem default_serviceCountBounded' SeLe4n/Kernel/Service/Invariant/Acyclicity.lean
run_check "INVARIANT" rg -n '^theorem default_serviceGraphInvariant' SeLe4n/Kernel/Service/Invariant/Acyclicity.lean

# WS-F6/D6: vspaceCrossAsidIsolation in VSpace invariant bundle.
run_check "INVARIANT" rg -n '^def vspaceCrossAsidIsolation' SeLe4n/Kernel/Architecture/VSpaceInvariant.lean


# WS-J1-D: Register decode consistency predicate and preservation anchors.
run_check "INVARIANT" rg -n '^def registerDecodeConsistent' SeLe4n/Kernel/Architecture/Invariant.lean
run_check "INVARIANT" rg -n '^theorem registerDecodeConsistent_of_proofLayerInvariantBundle' SeLe4n/Kernel/Architecture/Invariant.lean
run_check "INVARIANT" rg -n '^theorem default_registerDecodeConsistent' SeLe4n/Kernel/Architecture/Invariant.lean
run_check "INVARIANT" rg -n '^theorem advanceTimerState_preserves_registerDecodeConsistent' SeLe4n/Kernel/Architecture/Invariant.lean
run_check "INVARIANT" rg -n '^theorem writeRegisterState_preserves_registerDecodeConsistent' SeLe4n/Kernel/Architecture/Invariant.lean
# WS-J1-D: syscallEntry invariant preservation and NI theorems in API.lean.
run_check "INVARIANT" rg -n '^theorem syscallEntry_preserves_proofLayerInvariantBundle' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n '^theorem syscallEntry_error_preserves_proofLayerInvariantBundle' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n '^theorem decodeSyscallArgs_preserves_lowEquivalent' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n '^theorem lookupThreadRegisterContext_preserves_lowEquivalent' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n '^theorem syscallLookupCap_preserves_projection' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n '^theorem syscallEntry_preserves_projection' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n '^theorem syscallEntry_error_yields_NI_step' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n '^theorem syscallEntry_success_yields_NI_step' SeLe4n/Kernel/API.lean
# WS-J1-D: NonInterferenceStep constructors for decode path.
run_check "INVARIANT" rg -n 'syscallDecodeError' SeLe4n/Kernel/InformationFlow/Invariant/Composition.lean
run_check "INVARIANT" rg -n 'syscallDispatchHigh' SeLe4n/Kernel/InformationFlow/Invariant/Composition.lean
# WS-J1-E: RegisterDecode module definitions and round-trip lemmas.
run_check "INVARIANT" rg -n 'def decodeCapPtr' SeLe4n/Kernel/Architecture/RegisterDecode.lean
run_check "INVARIANT" rg -n 'def decodeMsgInfo' SeLe4n/Kernel/Architecture/RegisterDecode.lean
run_check "INVARIANT" rg -n 'def decodeSyscallId' SeLe4n/Kernel/Architecture/RegisterDecode.lean
run_check "INVARIANT" rg -n 'def validateRegBound' SeLe4n/Kernel/Architecture/RegisterDecode.lean
run_check "INVARIANT" rg -n 'def decodeSyscallArgs' SeLe4n/Kernel/Architecture/RegisterDecode.lean
run_check "INVARIANT" rg -n '^theorem decodeCapPtr_roundtrip' SeLe4n/Kernel/Architecture/RegisterDecode.lean
run_check "INVARIANT" rg -n '^theorem decodeSyscallId_roundtrip' SeLe4n/Kernel/Architecture/RegisterDecode.lean
run_check "INVARIANT" rg -n '^theorem decodeSyscallId_error_iff' SeLe4n/Kernel/Architecture/RegisterDecode.lean
run_check "INVARIANT" rg -n '^theorem decodeMsgInfo_error_iff' SeLe4n/Kernel/Architecture/RegisterDecode.lean
run_check "INVARIANT" rg -n '^theorem decodeCapPtr_ok_iff' SeLe4n/Kernel/Architecture/RegisterDecode.lean
run_check "INVARIANT" rg -n '^theorem validateRegBound_ok_iff' SeLe4n/Kernel/Architecture/RegisterDecode.lean
run_check "INVARIANT" rg -n '^theorem validateRegBound_error_iff' SeLe4n/Kernel/Architecture/RegisterDecode.lean
# Audit optimization: new round-trip and composition theorems.
run_check "INVARIANT" rg -n '^theorem decodeMsgInfo_roundtrip' SeLe4n/Kernel/Architecture/RegisterDecode.lean
run_check "INVARIANT" rg -n '^theorem decode_components_roundtrip' SeLe4n/Kernel/Architecture/RegisterDecode.lean

# WS-K-A: Message register extraction definitions and theorems.
# W3: encodeMsgRegs (identity function) and decodeMsgRegs_roundtrip removed as dead code.
# Message registers need no encode/decode round-trip — identity in the abstract model.
run_check "INVARIANT" rg -n '^theorem decodeMsgRegs_length' SeLe4n/Kernel/Architecture/RegisterDecode.lean
run_check "INVARIANT" rg -n 'msgRegs.*Array.*RegValue' SeLe4n/Model/Object/Types.lean
run_check "INVARIANT" rg -n '^theorem encode_decode_roundtrip' SeLe4n/Model/Object/Types.lean

# WS-K-B: Per-syscall argument decode layer definitions and theorems.
run_check "INVARIANT" rg -n 'def requireMsgReg' SeLe4n/Kernel/Architecture/SyscallArgDecode.lean
run_check "INVARIANT" rg -n '^structure CSpaceMintArgs' SeLe4n/Kernel/Architecture/SyscallArgDecode.lean
run_check "INVARIANT" rg -n '^structure VSpaceMapArgs' SeLe4n/Kernel/Architecture/SyscallArgDecode.lean
run_check "INVARIANT" rg -n '^structure VSpaceUnmapArgs' SeLe4n/Kernel/Architecture/SyscallArgDecode.lean
run_check "INVARIANT" rg -n '^def decodeCSpaceMintArgs' SeLe4n/Kernel/Architecture/SyscallArgDecode.lean
run_check "INVARIANT" rg -n '^def decodeVSpaceMapArgs' SeLe4n/Kernel/Architecture/SyscallArgDecode.lean
run_check "INVARIANT" rg -n '^theorem decodeCSpaceMintArgs_error_iff' SeLe4n/Kernel/Architecture/SyscallArgDecode.lean
run_check "INVARIANT" rg -n '^theorem decodeVSpaceMapArgs_error_iff' SeLe4n/Kernel/Architecture/SyscallArgDecode.lean
run_check "INVARIANT" rg -n '^theorem requireMsgReg_error_iff' SeLe4n/Kernel/Architecture/SyscallArgDecode.lean

# WS-Q1-D: Service syscall argument decode structures and roundtrip proofs.
run_check "INVARIANT" rg -n '^structure ServiceRegisterArgs' SeLe4n/Kernel/Architecture/SyscallArgDecode.lean
run_check "INVARIANT" rg -n '^structure ServiceRevokeArgs' SeLe4n/Kernel/Architecture/SyscallArgDecode.lean
run_check "INVARIANT" rg -n '^def decodeServiceRegisterArgs' SeLe4n/Kernel/Architecture/SyscallArgDecode.lean
run_check "INVARIANT" rg -n '^def decodeServiceRevokeArgs' SeLe4n/Kernel/Architecture/SyscallArgDecode.lean
run_check "INVARIANT" rg -n 'def encodeServiceRegisterArgs' SeLe4n/Kernel/Architecture/SyscallArgDecode.lean
run_check "INVARIANT" rg -n 'def encodeServiceRevokeArgs' SeLe4n/Kernel/Architecture/SyscallArgDecode.lean
run_check "INVARIANT" rg -n '^theorem decodeServiceRegisterArgs_roundtrip' SeLe4n/Kernel/Architecture/SyscallArgDecode.lean
run_check "INVARIANT" rg -n '^theorem decodeServiceRevokeArgs_roundtrip' SeLe4n/Kernel/Architecture/SyscallArgDecode.lean

# WS-Q1-D: Service registration enforcement wrapper.
run_check "INVARIANT" rg -n '^def registerServiceChecked' SeLe4n/Kernel/InformationFlow/Enforcement/Wrappers.lean
run_check "INVARIANT" rg -n '^theorem registerServiceChecked_eq_registerService_when_allowed' SeLe4n/Kernel/InformationFlow/Enforcement/Soundness.lean
run_check "INVARIANT" rg -n '^theorem registerServiceChecked_flowDenied' SeLe4n/Kernel/InformationFlow/Enforcement/Soundness.lean
run_check "INVARIANT" rg -n '^theorem enforcementSoundness_registerServiceChecked' SeLe4n/Kernel/InformationFlow/Enforcement/Soundness.lean

# WS-K-E/Q1: IPC message population anchors (ServiceConfig and serviceStart/Stop dispatch removed in Q1).
run_check "INVARIANT" rg -n 'def extractMessageRegisters' SeLe4n/Kernel/Architecture/RegisterDecode.lean
run_check "INVARIANT" rg -n '^theorem extractMessageRegisters_length' SeLe4n/Kernel/Architecture/RegisterDecode.lean
run_check "INVARIANT" rg -n '^theorem extractMessageRegisters_ipc_bounded' SeLe4n/Kernel/Architecture/RegisterDecode.lean
run_check "INVARIANT" rg -n '^theorem dispatchWithCap_send_uses_withCaps' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n '^theorem dispatchWithCap_call_uses_withCaps' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n '^theorem dispatchWithCap_reply_populates_msg' SeLe4n/Kernel/API.lean

# WS-K-F1: Per-syscall encode functions (layer 2).
run_check "INVARIANT" rg -n 'def encodeCSpaceMintArgs' SeLe4n/Kernel/Architecture/SyscallArgDecode.lean
run_check "INVARIANT" rg -n 'def encodeVSpaceMapArgs' SeLe4n/Kernel/Architecture/SyscallArgDecode.lean

# WS-K-F2: Layer 2 round-trip proofs.
run_check "INVARIANT" rg -n '^theorem decodeCSpaceMintArgs_roundtrip' SeLe4n/Kernel/Architecture/SyscallArgDecode.lean
run_check "INVARIANT" rg -n '^theorem decode_layer2_roundtrip_all' SeLe4n/Kernel/Architecture/SyscallArgDecode.lean

# WS-K-F3: Layer 1 extraction round-trip.
run_check "INVARIANT" rg -n '^theorem extractMessageRegisters_roundtrip' SeLe4n/Kernel/Architecture/RegisterDecode.lean

# WS-K-F4: Dispatch preservation and decode purity.
run_check "INVARIANT" rg -n '^theorem dispatchWithCap_layer2_decode_pure' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n '^theorem dispatchWithCap_preservation_composition_witness' SeLe4n/Kernel/API.lean

# WS-K-F5: Lifecycle NI proofs.
run_check "INVARIANT" rg -n 'retypeFromUntyped_preserves_lowEquivalent' SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean

# WS-K-F6: NI coverage verification.
run_check "INVARIANT" rg -n 'syscallNI_coverage_witness' SeLe4n/Kernel/InformationFlow/Invariant/Composition.lean

# WS-K-G (v0.16.7): Lifecycle NI composition.
run_check "INVARIANT" rg -n 'lifecycleRevokeDeleteRetype_preserves_lowEquivalent' SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean
run_check "INVARIANT" rg -n 'cspaceRevoke_preserves_projection' SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean

# WS-I2/R-05: Lean #check correctness anchors (type-level validation).
# Build SchedContext.Invariant first (not in default build target).
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake build SeLe4n.Kernel.SchedContext.Invariant.Defs >/dev/null 2>&1 && lake env lean --stdin <<"EOF"
import SeLe4n.Kernel.Scheduler.Operations.Preservation
import SeLe4n.Kernel.Capability.Invariant.Preservation
import SeLe4n.Kernel.IPC.Invariant.EndpointPreservation
import SeLe4n.Kernel.Lifecycle.Invariant
import SeLe4n.Kernel.Service.Invariant.Acyclicity
import SeLe4n.Kernel.Architecture.VSpaceInvariant
import SeLe4n.Kernel.InformationFlow.Invariant.Composition
import SeLe4n.Kernel.API
import SeLe4n.Kernel.SchedContext.Invariant

#check @SeLe4n.Kernel.schedule_preserves_schedulerInvariantBundle
#check @SeLe4n.Kernel.timerTick_preserves_schedulerInvariantBundle
#check @SeLe4n.Kernel.cspaceMint_preserves_capabilityInvariantBundle
#check @SeLe4n.Kernel.cspaceRevoke_preserves_capabilityInvariantBundle
#check @SeLe4n.Kernel.endpointSendDual_preserves_ipcInvariant
#check @SeLe4n.Kernel.lifecycleRetypeObject_preserves_lifecycleInvariantBundle
#check @SeLe4n.Kernel.serviceRegisterDependency_preserves_serviceGraphInvariant
#check @SeLe4n.Kernel.Architecture.vspaceMapPage_success_preserves_vspaceInvariantBundle
#check @SeLe4n.Kernel.step_preserves_projection
#check @SeLe4n.Kernel.composedNonInterference_step
-- WS-J1-D: New decode/dispatch NI theorems
#check @SeLe4n.Kernel.Architecture.registerDecodeConsistent
#check @SeLe4n.Kernel.Architecture.registerDecodeConsistent_of_proofLayerInvariantBundle
#check @SeLe4n.Kernel.syscallEntry_preserves_proofLayerInvariantBundle
#check @SeLe4n.Kernel.decodeSyscallArgs_preserves_lowEquivalent
#check @SeLe4n.Kernel.lookupThreadRegisterContext_preserves_lowEquivalent
#check @SeLe4n.Kernel.syscallLookupCap_preserves_projection
#check @SeLe4n.Kernel.syscallEntry_preserves_projection
#check @SeLe4n.Kernel.syscallEntry_error_yields_NI_step
#check @SeLe4n.Kernel.syscallEntry_success_yields_NI_step
-- WS-K-A: Message register extraction theorems
-- W3: encodeMsgRegs and decodeMsgRegs_roundtrip removed (dead code — identity function)
#check @SeLe4n.Kernel.Architecture.RegisterDecode.decodeMsgRegs_length
#check @SeLe4n.Kernel.Architecture.RegisterDecode.decode_components_roundtrip
-- WS-K-B: Per-syscall argument decode structures, functions, and theorems
#check @SeLe4n.Kernel.Architecture.SyscallArgDecode.requireMsgReg
#check @SeLe4n.Kernel.Architecture.SyscallArgDecode.requireMsgReg_error_iff
#check @SeLe4n.Kernel.Architecture.SyscallArgDecode.requireMsgReg_ok_iff
#check @SeLe4n.Kernel.Architecture.SyscallArgDecode.CSpaceMintArgs
#check @SeLe4n.Kernel.Architecture.SyscallArgDecode.CSpaceCopyArgs
#check @SeLe4n.Kernel.Architecture.SyscallArgDecode.CSpaceMoveArgs
#check @SeLe4n.Kernel.Architecture.SyscallArgDecode.CSpaceDeleteArgs
#check @SeLe4n.Kernel.Architecture.SyscallArgDecode.LifecycleRetypeArgs
#check @SeLe4n.Kernel.Architecture.SyscallArgDecode.VSpaceMapArgs
#check @SeLe4n.Kernel.Architecture.SyscallArgDecode.VSpaceUnmapArgs
#check @SeLe4n.Kernel.Architecture.SyscallArgDecode.decodeCSpaceMintArgs
#check @SeLe4n.Kernel.Architecture.SyscallArgDecode.decodeCSpaceCopyArgs
#check @SeLe4n.Kernel.Architecture.SyscallArgDecode.decodeCSpaceMoveArgs
#check @SeLe4n.Kernel.Architecture.SyscallArgDecode.decodeCSpaceDeleteArgs
#check @SeLe4n.Kernel.Architecture.SyscallArgDecode.decodeLifecycleRetypeArgs
#check @SeLe4n.Kernel.Architecture.SyscallArgDecode.decodeVSpaceMapArgs
#check @SeLe4n.Kernel.Architecture.SyscallArgDecode.decodeVSpaceUnmapArgs
#check @SeLe4n.Kernel.Architecture.SyscallArgDecode.decodeCSpaceMintArgs_error_iff
#check @SeLe4n.Kernel.Architecture.SyscallArgDecode.decodeCSpaceCopyArgs_error_iff
#check @SeLe4n.Kernel.Architecture.SyscallArgDecode.decodeCSpaceMoveArgs_error_iff
#check @SeLe4n.Kernel.Architecture.SyscallArgDecode.decodeCSpaceDeleteArgs_error_iff
#check @SeLe4n.Kernel.Architecture.SyscallArgDecode.decodeLifecycleRetypeArgs_error_of_insufficient_regs
#check @SeLe4n.Kernel.Architecture.SyscallArgDecode.decodeLifecycleRetypeArgs_error_of_invalid_type
#check @SeLe4n.Kernel.Architecture.SyscallArgDecode.decodeVSpaceMapArgs_error_iff
#check @SeLe4n.Kernel.Architecture.SyscallArgDecode.decodeVSpaceUnmapArgs_error_iff

-- WS-K-D: Lifecycle and VSpace dispatch helpers
#check @SeLe4n.Kernel.objectOfTypeTag
-- W3: objectOfTypeTag_type and objectOfTypeTag_error_iff removed (dead code)
#check @SeLe4n.Model.PagePermissions.ofNat
#check @SeLe4n.Model.PagePermissions.toNat
#check @SeLe4n.Model.PagePermissions.ofNat_toNat_roundtrip
#check @SeLe4n.Kernel.lifecycleRetypeDirect
#check @SeLe4n.Kernel.dispatchWithCap_lifecycleRetype_delegates
#check @SeLe4n.Kernel.dispatchWithCap_vspaceMap_delegates
#check @SeLe4n.Kernel.dispatchWithCap_vspaceUnmap_delegates
-- WS-K-E/Q1: IPC message population (ServiceConfig, serviceStart/Stop dispatch removed in Q1)
#check @SeLe4n.Kernel.Architecture.RegisterDecode.extractMessageRegisters
#check @SeLe4n.Kernel.Architecture.RegisterDecode.extractMessageRegisters_length
#check @SeLe4n.Kernel.Architecture.RegisterDecode.extractMessageRegisters_ipc_bounded
#check @SeLe4n.Kernel.dispatchWithCap_send_uses_withCaps
#check @SeLe4n.Kernel.dispatchWithCap_call_uses_withCaps
#check @SeLe4n.Kernel.dispatchWithCap_reply_populates_msg
-- WS-K-F1: Per-syscall encode functions
#check @SeLe4n.Kernel.Architecture.SyscallArgDecode.encodeCSpaceMintArgs
#check @SeLe4n.Kernel.Architecture.SyscallArgDecode.encodeCSpaceCopyArgs
#check @SeLe4n.Kernel.Architecture.SyscallArgDecode.encodeCSpaceMoveArgs
#check @SeLe4n.Kernel.Architecture.SyscallArgDecode.encodeCSpaceDeleteArgs
#check @SeLe4n.Kernel.Architecture.SyscallArgDecode.encodeLifecycleRetypeArgs
#check @SeLe4n.Kernel.Architecture.SyscallArgDecode.encodeVSpaceMapArgs
#check @SeLe4n.Kernel.Architecture.SyscallArgDecode.encodeVSpaceUnmapArgs
-- WS-K-F2: Layer 2 round-trip proofs
#check @SeLe4n.Kernel.Architecture.SyscallArgDecode.decodeCSpaceMintArgs_roundtrip
#check @SeLe4n.Kernel.Architecture.SyscallArgDecode.decodeCSpaceCopyArgs_roundtrip
#check @SeLe4n.Kernel.Architecture.SyscallArgDecode.decodeCSpaceMoveArgs_roundtrip
#check @SeLe4n.Kernel.Architecture.SyscallArgDecode.decodeCSpaceDeleteArgs_roundtrip
#check @SeLe4n.Kernel.Architecture.SyscallArgDecode.decodeLifecycleRetypeArgs_roundtrip
#check @SeLe4n.Kernel.Architecture.SyscallArgDecode.decodeVSpaceMapArgs_roundtrip
#check @SeLe4n.Kernel.Architecture.SyscallArgDecode.decodeVSpaceUnmapArgs_roundtrip
#check @SeLe4n.Kernel.Architecture.SyscallArgDecode.decode_layer2_roundtrip_all
-- WS-K-F3: Layer 1 extraction round-trip
#check @SeLe4n.Kernel.Architecture.RegisterDecode.extractMessageRegisters_roundtrip
-- WS-K-F4: Dispatch preservation and decode purity
#check @SeLe4n.Kernel.dispatchWithCap_layer2_decode_pure
#check @SeLe4n.Kernel.dispatchWithCap_preservation_composition_witness
-- WS-K-F5: Lifecycle NI proofs
#check @SeLe4n.Kernel.retypeFromUntyped_preserves_lowEquivalent
-- WS-K-F6: NI coverage verification
#check @SeLe4n.Kernel.syscallNI_coverage_witness
-- WS-K-G (v0.16.7): Lifecycle NI composition
#check @SeLe4n.Kernel.cspaceRevoke_preserves_projection
#check @SeLe4n.Kernel.lifecycleRevokeDeleteRetype_preserves_projection
#check @SeLe4n.Kernel.lifecycleRevokeDeleteRetype_preserves_lowEquivalent
-- WS-Z Phase Z2: CBS Budget Engine invariants and preservation
#check @SeLe4n.Kernel.budgetWithinBounds
#check @SeLe4n.Kernel.replenishmentListWellFormed
#check @SeLe4n.Kernel.replenishmentAmountsBounded
#check @SeLe4n.Kernel.schedContextWellFormed
#check @SeLe4n.Kernel.cbsBudgetCheck_preserves_schedContextWellFormed
#check @SeLe4n.Kernel.cbsBudgetCheck_preserves_replenishmentAmountsBounded
#check @SeLe4n.Kernel.cbs_single_period_bound
#check @SeLe4n.Kernel.cbs_bandwidth_bounded
#check @SeLe4n.Kernel.consumeBudget_preserves_budgetWithinBounds
#check @SeLe4n.Kernel.consumeBudget_preserves_replenishmentAmountsBounded
#check @SeLe4n.Kernel.processReplenishments_preserves_budgetWithinBounds
#check @SeLe4n.Kernel.scheduleReplenishment_preserves_replenishmentListWellFormed
#check @SeLe4n.Kernel.cbsUpdateDeadline_preserves_budgetWithinBounds
EOF'

finalize_report
