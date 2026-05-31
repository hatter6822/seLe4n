#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
#
# AN11-E.6 (TST-M06) — Tier 3 "invariant-surface anchor" validator.
#
# This script verifies that every theorem named in the kernel's
# **invariant-surface anchor** index (via `rg`-driven name searches across
# `SeLe4n/Kernel/**`) is still present at its expected location.  An
# "invariant-surface anchor" is a theorem name that proof consumers cite
# explicitly — renaming or deleting an anchor would silently break those
# consumers, so this gate enforces name stability.
#
# This is **not** a behavioural-coverage test: a Tier 3 PASS means every
# anchor name resolves, NOT that the corresponding kernel transition was
# exercised on a populated state.  Behavioural validation lives in Tier 2
# (`test_tier2_negative.sh`, `test_tier2_trace.sh`).
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
# AN3-G post-delivery audit: `-r` added so GNU grep accepts directory
# arguments the way `rg` does.  Without `-r`, `grep -P pattern dir/`
# fails with `Is a directory` (exit code 2), which CI hit after AN3-C/D
# split monolithic files into Structural/, NotificationPreservation/,
# CallReplyRecv/ subdirectories whose Tier 3 surface checks now point
# at directories.  `-r` is harmless for individual file arguments and
# preserves rg's default `file:line:match` output format.
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
  exec grep -rPn -- "${pattern}" "${files[@]}"
else
  exec grep -rP -- "${pattern}" "${files[@]}"
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
run_check "INVARIANT" rg -n '^run_check(_with_timeout)? "TRACE" lake env lean --run tests/InformationFlowSuite\.lean' scripts/test_tier2_negative.sh
run_check "INVARIANT" rg -n '^ELAN_INSTALLER_SHA256=' scripts/setup_lean_env.sh
run_check "INVARIANT" rg -n '^compute_sha256\(\)' scripts/setup_lean_env.sh
# shellcheck disable=SC2016

# WS-B2 closure anchors: bootstrap DSL, negative suite, and nightly replay artifacts.
run_check "INVARIANT" rg -n '^structure BootstrapBuilder' SeLe4n/Testing/StateBuilder.lean
run_check "INVARIANT" rg -n '^def build \(builder : BootstrapBuilder\)' SeLe4n/Testing/StateBuilder.lean
run_check "INVARIANT" rg -n '^private def runNegativeChecks' tests/NegativeStateSuite.lean
run_check "INVARIANT" rg -n '^run_check(_with_timeout)? "TRACE" lake env lean --run tests/NegativeStateSuite\.lean' scripts/test_tier2_negative.sh
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
run_check "INVARIANT" rg -n '^def requiresPageAlignment' SeLe4n/Kernel/Lifecycle/Operations/ScrubAndUntyped.lean
run_check "INVARIANT" rg -n '^def allocationBasePageAligned' SeLe4n/Kernel/Lifecycle/Operations/ScrubAndUntyped.lean

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
run_check "INVARIANT" rg -n '^def coreIpcInvariantBundle' SeLe4n/Kernel/Capability/Invariant/Preservation/EndpointReplyAndLifecycle.lean

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
run_check "INVARIANT" rg -n '^theorem cspaceInsertSlot_preserves_capabilityInvariantBundle' SeLe4n/Kernel/Capability/Invariant/Preservation/Insert.lean
run_check "INVARIANT" rg -n '^theorem cspaceMint_preserves_capabilityInvariantBundle' SeLe4n/Kernel/Capability/Invariant/Preservation/Insert.lean
run_check "INVARIANT" rg -n '^theorem cspaceDeleteSlot_preserves_capabilityInvariantBundle' SeLe4n/Kernel/Capability/Invariant/Preservation/Delete.lean
run_check "INVARIANT" rg -n '^theorem cspaceRevoke_preserves_capabilityInvariantBundle' SeLe4n/Kernel/Capability/Invariant/Preservation/Delete.lean

# C-01 remediation: non-tautological slot-uniqueness infrastructure at CNode level.
run_check "INVARIANT" rg -n '^def slotsUnique' SeLe4n/Model/Object/Structures.lean
run_check "INVARIANT" rg -n '^theorem insert_slotsUnique' SeLe4n/Model/Object/Structures.lean
run_check "INVARIANT" rg -n '^theorem remove_slotsUnique' SeLe4n/Model/Object/Structures.lean
run_check "INVARIANT" rg -n '^theorem revokeTargetLocal_slotsUnique' SeLe4n/Model/Object/Structures.lean
run_check "INVARIANT" rg -n '^theorem lookup_mem_of_some' SeLe4n/Model/Object/Structures.lean
run_check "INVARIANT" rg -n '^theorem mem_lookup_of_slotsUnique' SeLe4n/Model/Object/Structures.lean
# C-01/H-01 remediation: reformulated invariant definitions (non-tautological).
run_check "INVARIANT" rg -n 'cn.slotsUnique' SeLe4n/Kernel/Capability/Invariant/Preservation/EndpointReplyAndLifecycle.lean
# WS-RC R4.A close-out: `cspaceLookupSound_of_cspaceSlotUnique` was renamed
# to `cspaceLookupSound_holds` (no preconditions; the historical
# `cspaceSlotUnique` precondition was deleted as a vestigial alias).
run_check "INVARIANT" rg -n '^theorem cspaceLookupSound_holds' SeLe4n/Kernel/Capability/Invariant/Authority.lean
# WS-RC R4.A close-out: `capabilityInvariantBundle_of_slotUnique` was renamed
# to `capabilityInvariantBundle_of_components` after the vestigial
# `cspaceSlotUnique` parameter was deleted.
run_check "INVARIANT" rg -n '^theorem capabilityInvariantBundle_of_components' SeLe4n/Kernel/Capability/Invariant/Authority.lean
# WS-RC R4.A close-out: the historical
# `cspaceSlotUnique_of_storeObject_{nonCNode,cnode}` transfer theorems were
# deleted along with the `cspaceSlotUnique` predicate.  Per-CNode discharge
# is direct via `slotsUnique_holds`.
run_check "INVARIANT" rg -n '^theorem slotsUnique_holds' SeLe4n/Model/Object/Structures.lean
run_check "INVARIANT" rg -n '^theorem cnode_slots_unique' SeLe4n/Model/Object/Structures.lean
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
run_check "INVARIANT" rg -n '^def ipcSchedulerRunnableReadyComponent' SeLe4n/Kernel/Capability/Invariant/Preservation/EndpointReplyAndLifecycle.lean
run_check "INVARIANT" rg -n '^def ipcSchedulerBlockedSendComponent' SeLe4n/Kernel/Capability/Invariant/Preservation/EndpointReplyAndLifecycle.lean
run_check "INVARIANT" rg -n '^def ipcSchedulerBlockedReceiveComponent' SeLe4n/Kernel/Capability/Invariant/Preservation/EndpointReplyAndLifecycle.lean
run_check "INVARIANT" rg -n '^def ipcSchedulerCoherenceComponent' SeLe4n/Kernel/Capability/Invariant/Preservation/EndpointReplyAndLifecycle.lean
run_check "INVARIANT" rg -n '^theorem ipcSchedulerCoherenceComponent_iff_contractPredicates' SeLe4n/Kernel/Capability/Invariant/Preservation/EndpointReplyAndLifecycle.lean
run_check "INVARIANT" rg -n '^def ipcSchedulerCouplingInvariantBundle' SeLe4n/Kernel/Capability/Invariant/Preservation/EndpointReplyAndLifecycle.lean
# WS-H12a: Legacy coupling/local-first preservation anchors removed.
# Dual-queue preservation is verified via dualQueueSystemInvariant anchors below.

# M3.5 step-5 helper-lemma anchors must remain present.
run_check "INVARIANT" rg -n '^theorem tcb_lookup_of_endpoint_store' SeLe4n/Kernel/IPC/Invariant/Defs.lean
run_check "INVARIANT" rg -n '^theorem runnable_membership_of_endpoint_store' SeLe4n/Kernel/IPC/Invariant/Defs.lean
run_check "INVARIANT" rg -n '^theorem not_runnable_membership_of_endpoint_store' SeLe4n/Kernel/IPC/Invariant/Defs.lean

# Bundle composition guard: M3 seed bundle must compose scheduler + capability + full IPC invariants.
# WS-H12e: Updated from ipcInvariant to ipcInvariantFull (includes dualQueueSystemInvariant + allPendingMessagesBounded).
run_check "INVARIANT" rg -n '^\s*schedulerInvariantBundle st ∧ capabilityInvariantBundle st ∧ ipcInvariantFull st' SeLe4n/Kernel/Capability/Invariant/Preservation/EndpointReplyAndLifecycle.lean

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
# AN4-B (H-03): `lifecycleIdentityAliasingInvariant` was collapsed to an
# `abbrev` aliasing `lifecycleIdentityTypeExact` (the redundant
# `lifecycleIdentityNoTypeAliasConflict` conjunct is derivable in one step
# from exactness and was removed).
run_check "INVARIANT" rg -n '^abbrev lifecycleIdentityAliasingInvariant' SeLe4n/Kernel/Lifecycle/Invariant.lean
run_check "INVARIANT" rg -n '^def lifecycleCapabilityReferenceInvariant' SeLe4n/Kernel/Lifecycle/Invariant.lean
run_check "INVARIANT" rg -n '^def lifecycleCapabilityRefObjectTargetBacked' SeLe4n/Kernel/Lifecycle/Invariant.lean
run_check "INVARIANT" rg -n '^def lifecycleInvariantBundle' SeLe4n/Kernel/Lifecycle/Invariant.lean
run_check "INVARIANT" rg -n '^theorem lifecycleCapabilityRefObjectTargetBacked_of_exact' SeLe4n/Kernel/Lifecycle/Invariant.lean
run_check "INVARIANT" rg -n '^theorem lifecycleInvariantBundle_of_metadata_consistent' SeLe4n/Kernel/Lifecycle/Invariant.lean

# M4-B WS-B invariant hardening anchors must remain present.
run_check "INVARIANT" rg -n '^def lifecycleCapabilityRefObjectTargetTypeAligned' SeLe4n/Kernel/Lifecycle/Invariant.lean
# AN4-B (H-03): `lifecycleCapabilityRefNoTypeAliasConflict` the standalone
# `def` is retained (it takes a reference+oid pair; the removed predicate was
# the identity-side `lifecycleIdentityNoTypeAliasConflict`). Match unchanged.
run_check "INVARIANT" rg -n '^def lifecycleCapabilityRefNoTypeAliasConflict' SeLe4n/Kernel/Lifecycle/Invariant.lean
run_check "INVARIANT" rg -n '^def lifecycleStaleReferenceExclusionInvariant' SeLe4n/Kernel/Lifecycle/Invariant.lean
run_check "INVARIANT" rg -n '^def lifecycleIdentityStaleReferenceInvariant' SeLe4n/Kernel/Lifecycle/Invariant.lean
run_check "INVARIANT" rg -n '^theorem lifecycleCapabilityRefObjectTargetTypeAligned_of_exact' SeLe4n/Kernel/Lifecycle/Invariant.lean
# AN4-B (H-03): the bridge theorem was renamed from `_of_identity` to
# `_of_exact` because the intermediate `lifecycleIdentityNoTypeAliasConflict`
# predicate was removed (derivable in one step from exactness).
run_check "INVARIANT" rg -n '^theorem lifecycleCapabilityRefNoTypeAliasConflict_of_exact' SeLe4n/Kernel/Lifecycle/Invariant.lean
run_check "INVARIANT" rg -n '^theorem lifecycleStaleReferenceExclusionInvariant_of_lifecycleInvariantBundle' SeLe4n/Kernel/Lifecycle/Invariant.lean
run_check "INVARIANT" rg -n '^theorem lifecycleRetypeObject_preserves_lifecycleStaleReferenceExclusionInvariant' SeLe4n/Kernel/Lifecycle/Invariant.lean
run_check "INVARIANT" rg -n '^theorem lifecycleRetypeObject_preserves_lifecycleIdentityStaleReferenceInvariant' SeLe4n/Kernel/Lifecycle/Invariant.lean
run_check "INVARIANT" rg -n '^def lifecycleCapabilityStaleAuthorityInvariant' SeLe4n/Kernel/Capability/Invariant/Defs.lean
run_check "INVARIANT" rg -n '^theorem lifecycleCapabilityStaleAuthorityInvariant_of_bundles' SeLe4n/Kernel/Capability/Invariant/Defs.lean

# M4-A step-5 lifecycle preservation entrypoint anchors must remain present.
run_check "INVARIANT" rg -n '^theorem lifecycleRetypeObject_preserves_lifecycleInvariantBundle' SeLe4n/Kernel/Lifecycle/Invariant.lean
run_check "INVARIANT" rg -n '^def lifecycleCompositionInvariantBundle' SeLe4n/Kernel/Capability/Invariant/Preservation/EndpointReplyAndLifecycle.lean
run_check "INVARIANT" rg -n '^theorem lifecycleRetypeObject_preserves_schedulerInvariantBundle' SeLe4n/Kernel/Capability/Invariant/Preservation/EndpointReplyAndLifecycle.lean
run_check "INVARIANT" rg -n '^theorem lifecycleRetypeObject_preserves_capabilityInvariantBundle' SeLe4n/Kernel/Capability/Invariant/Preservation/EndpointReplyAndLifecycle.lean
run_check "INVARIANT" rg -n '^theorem lifecycleRetypeObject_preserves_ipcInvariant' SeLe4n/Kernel/Capability/Invariant/Preservation/EndpointReplyAndLifecycle.lean
run_check "INVARIANT" rg -n '^theorem lifecycleRetypeObject_preserves_coreIpcInvariantBundle' SeLe4n/Kernel/Capability/Invariant/Preservation/EndpointReplyAndLifecycle.lean
run_check "INVARIANT" rg -n '^theorem lifecycleRetypeObject_preserves_lifecycleCompositionInvariantBundle' SeLe4n/Kernel/Capability/Invariant/Preservation/EndpointReplyAndLifecycle.lean

# M4-B WS-C preservation theorem expansion anchors must remain present.
run_check "INVARIANT" rg -n '^theorem lifecycleRevokeDeleteRetype_ok_implies_staged_steps' SeLe4n/Kernel/Lifecycle/Operations/ScrubAndUntyped.lean
run_check "INVARIANT" rg -n '^theorem lifecycleRevokeDeleteRetype_preserves_capabilityInvariantBundle' SeLe4n/Kernel/Capability/Invariant/Preservation/EndpointReplyAndLifecycle.lean
run_check "INVARIANT" rg -n '^theorem lifecycleRevokeDeleteRetype_preserves_lifecycleCapabilityStaleAuthorityInvariant' SeLe4n/Kernel/Capability/Invariant/Preservation/EndpointReplyAndLifecycle.lean
run_check "INVARIANT" rg -n '^theorem lifecycleRevokeDeleteRetype_error_preserves_lifecycleCompositionInvariantBundle' SeLe4n/Kernel/Capability/Invariant/Preservation/EndpointReplyAndLifecycle.lean

# M4-B WS-A composition transition anchors must remain present.
run_check "INVARIANT" rg -n '^def lifecycleRevokeDeleteRetype' SeLe4n/Kernel/Lifecycle/Operations/CleanupPreservation.lean
run_check "INVARIANT" rg -n '^theorem lifecycleRevokeDeleteRetype_error_authority_cleanup_alias' SeLe4n/Kernel/Lifecycle/Operations/ScrubAndUntyped.lean
run_check "INVARIANT" rg -n '^theorem lifecycleRevokeDeleteRetype_ok_implies_authority_ne_cleanup' SeLe4n/Kernel/Lifecycle/Operations/ScrubAndUntyped.lean

# M4-A step-4 lifecycle local-helper anchors must remain present.
run_check "INVARIANT" rg -n '^theorem lifecycle_storeObject_objects_eq' SeLe4n/Kernel/Lifecycle/Operations/ScrubAndUntyped.lean
run_check "INVARIANT" rg -n '^theorem lifecycle_storeObject_objects_ne' SeLe4n/Kernel/Lifecycle/Operations/ScrubAndUntyped.lean
run_check "INVARIANT" rg -n '^theorem lifecycle_storeObject_scheduler_eq' SeLe4n/Kernel/Lifecycle/Operations/ScrubAndUntyped.lean
run_check "INVARIANT" rg -n '^theorem lifecycleRetypeObject_ok_as_storeObject' SeLe4n/Kernel/Lifecycle/Operations/ScrubAndUntyped.lean
run_check "INVARIANT" rg -n '^theorem lifecycleRetypeObject_ok_lookup_preserved_ne' SeLe4n/Kernel/Lifecycle/Operations/ScrubAndUntyped.lean
run_check "INVARIANT" rg -n '^theorem lifecycleRetypeObject_ok_runnable_membership' SeLe4n/Kernel/Lifecycle/Operations/ScrubAndUntyped.lean
run_check "INVARIANT" rg -n '^theorem lifecycleRetypeObject_ok_not_runnable_membership' SeLe4n/Kernel/Lifecycle/Operations/ScrubAndUntyped.lean

# M4-A step-2 lifecycle transition anchors must remain present.
run_check "INVARIANT" rg -n '^\s*\| illegalState' SeLe4n/Model/State.lean
run_check "INVARIANT" rg -n '^\s*\| illegalAuthority' SeLe4n/Model/State.lean
run_check "INVARIANT" rg -n '^\s*\| invalidTypeTag' SeLe4n/Model/State.lean
run_check "INVARIANT" rg -n '^def lifecycleRetypeObject' SeLe4n/Kernel/Lifecycle/Operations/CleanupPreservation.lean
run_check "INVARIANT" rg -n '^theorem lifecycleRetypeObject_error_illegalState' SeLe4n/Kernel/Lifecycle/Operations/ScrubAndUntyped.lean
run_check "INVARIANT" rg -n '^theorem lifecycleRetypeObject_error_illegalAuthority' SeLe4n/Kernel/Lifecycle/Operations/ScrubAndUntyped.lean
run_check "INVARIANT" rg -n '^theorem lifecycleRetypeObject_success_updates_object' SeLe4n/Kernel/Lifecycle/Operations/ScrubAndUntyped.lean

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
# WS-RC R4.C close-out: the state-level `uniqueWaiters` predicate and its
# `notificationWait_preserves_uniqueWaiters` companion were deleted as part
# of the structural promotion to `NoDupList.hNodup`.  The plan-named
# canonical witness `notification_waiters_nodup` now discharges directly.
run_check "INVARIANT" rg -n '^theorem notification_waiters_nodup' SeLe4n/Kernel/IPC/Invariant/QueueNoDup.lean
run_check "INVARIANT" rg -n '^theorem notificationWait_runtime_check_implied_by_nodup' SeLe4n/Kernel/IPC/Invariant/QueueNoDup.lean

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
run_check "INVARIANT" rg -n '^theorem endpointSendDual_preserves_ipcInvariant' SeLe4n/Kernel/IPC/Invariant/Structural/
run_check "INVARIANT" rg -n '^theorem endpointSendDual_preserves_schedulerInvariantBundle' SeLe4n/Kernel/IPC/Invariant/EndpointPreservation.lean
run_check "INVARIANT" rg -n '^theorem endpointSendDual_preserves_ipcSchedulerContractPredicates' SeLe4n/Kernel/IPC/Invariant/EndpointPreservation.lean
run_check "INVARIANT" rg -n '^theorem endpointReceiveDual_preserves_ipcInvariant' SeLe4n/Kernel/IPC/Invariant/Structural/
run_check "INVARIANT" rg -n '^theorem endpointReceiveDual_preserves_schedulerInvariantBundle' SeLe4n/Kernel/IPC/Invariant/EndpointPreservation.lean
run_check "INVARIANT" rg -n '^theorem endpointReceiveDual_preserves_ipcSchedulerContractPredicates' SeLe4n/Kernel/IPC/Invariant/EndpointPreservation.lean
run_check "INVARIANT" rg -n '^theorem endpointQueueRemoveDual_preserves_ipcInvariant' SeLe4n/Kernel/IPC/Invariant/EndpointPreservation.lean
run_check "INVARIANT" rg -n '^theorem endpointQueueRemoveDual_preserves_schedulerInvariantBundle' SeLe4n/Kernel/IPC/Invariant/EndpointPreservation.lean
run_check "INVARIANT" rg -n '^theorem endpointQueueRemoveDual_preserves_ipcSchedulerContractPredicates' SeLe4n/Kernel/IPC/Invariant/EndpointPreservation.lean
run_check "INVARIANT" rg -n '^theorem endpointCall_preserves_ipcInvariant' SeLe4n/Kernel/IPC/Invariant/CallReplyRecv/
run_check "INVARIANT" rg -n '^theorem endpointCall_preserves_schedulerInvariantBundle' SeLe4n/Kernel/IPC/Invariant/CallReplyRecv/
run_check "INVARIANT" rg -n '^theorem endpointCall_preserves_ipcSchedulerContractPredicates' SeLe4n/Kernel/IPC/Invariant/CallReplyRecv/
run_check "INVARIANT" rg -n '^theorem endpointReply_preserves_ipcInvariant' SeLe4n/Kernel/IPC/Invariant/Structural/
run_check "INVARIANT" rg -n '^theorem endpointReply_preserves_schedulerInvariantBundle' SeLe4n/Kernel/IPC/Invariant/EndpointPreservation.lean
run_check "INVARIANT" rg -n '^theorem endpointReply_preserves_ipcSchedulerContractPredicates' SeLe4n/Kernel/IPC/Invariant/CallReplyRecv/
run_check "INVARIANT" rg -n '^theorem endpointReplyRecv_preserves_ipcInvariant' SeLe4n/Kernel/IPC/Invariant/Structural/
run_check "INVARIANT" rg -n '^theorem endpointReplyRecv_preserves_schedulerInvariantBundle' SeLe4n/Kernel/IPC/Invariant/CallReplyRecv/
run_check "INVARIANT" rg -n '^theorem endpointReplyRecv_preserves_ipcSchedulerContractPredicates' SeLe4n/Kernel/IPC/Invariant/CallReplyRecv/

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
run_check "INVARIANT" rg -n '^def retypeFromUntyped' SeLe4n/Kernel/Lifecycle/Operations/ScrubAndUntyped.lean
run_check "INVARIANT" rg -n '^theorem retypeFromUntyped_ok_decompose' SeLe4n/Kernel/Lifecycle/Operations/ScrubAndUntyped.lean
run_check "INVARIANT" rg -n '^theorem retypeFromUntyped_error_typeMismatch' SeLe4n/Kernel/Lifecycle/Operations/ScrubAndUntyped.lean
run_check "INVARIANT" rg -n '^theorem retypeFromUntyped_error_allocSizeTooSmall' SeLe4n/Kernel/Lifecycle/Operations/ScrubAndUntyped.lean
run_check "INVARIANT" rg -n '^theorem retypeFromUntyped_error_regionExhausted' SeLe4n/Kernel/Lifecycle/Operations/ScrubAndUntyped.lean
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
# WS-SM SM5.B (PR #805 review P2-4): cpuAffinity must be stripped by the NI projection.
run_check "INVARIANT" rg -n '^theorem projectKernelObject_erases_cpuAffinity' SeLe4n/Kernel/InformationFlow/Projection.lean
# WS-SM SM5.B (PR #805 review P2-4): cpuAffinity must be stripped by the NI projection.
run_check "INVARIANT" rg -n '^theorem projectKernelObject_erases_cpuAffinity' SeLe4n/Kernel/InformationFlow/Projection.lean
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
# Information-flow test suite coverage anchors.
run_check "TRACE" rg -n 'activeDomain visible' tests/InformationFlowSuite.lean
run_check "TRACE" rg -n 'IRQ handler' tests/InformationFlowSuite.lean
run_check "TRACE" rg -n 'CNode slot filtering' tests/InformationFlowSuite.lean
run_check "TRACE" rg -n 'Service registry projection' tests/InformationFlowSuite.lean
run_check "TRACE" rg -n '7-field low-equivalence' tests/InformationFlowSuite.lean

# WS-F4 proof gap closure anchors — timerTick, cspaceMutate, cspaceRevoke, notification preservation.
run_check "INVARIANT" rg -n '^theorem timerTick_preserves_schedulerInvariantBundle' SeLe4n/Kernel/Scheduler/Operations/Preservation.lean
run_check "INVARIANT" rg -n '^theorem cspaceMutate_preserves_capabilityInvariantBundle' SeLe4n/Kernel/Capability/Invariant/Preservation/CopyMoveMutate.lean
run_check "INVARIANT" rg -n '^theorem cspaceRevokeCdt_preserves_capabilityInvariantBundle' SeLe4n/Kernel/Capability/Invariant/Preservation/Revoke.lean
run_check "INVARIANT" rg -n '^theorem cspaceRevokeCdtStrict_preserves_capabilityInvariantBundle' SeLe4n/Kernel/Capability/Invariant/Preservation/Revoke.lean
run_check "INVARIANT" rg -n '^theorem notificationSignal_preserves_ipcInvariant' SeLe4n/Kernel/IPC/Invariant/Structural/
run_check "INVARIANT" rg -n '^theorem notificationSignal_preserves_schedulerInvariantBundle' SeLe4n/Kernel/IPC/Invariant/NotificationPreservation/
run_check "INVARIANT" rg -n '^theorem notificationWait_preserves_ipcInvariant' SeLe4n/Kernel/IPC/Invariant/Structural/
run_check "INVARIANT" rg -n '^theorem notificationWait_preserves_schedulerInvariantBundle' SeLe4n/Kernel/IPC/Invariant/NotificationPreservation/
run_check "INVARIANT" rg -n '^theorem notificationSignal_preserves_ipcSchedulerContractPredicates' SeLe4n/Kernel/IPC/Invariant/NotificationPreservation/
run_check "INVARIANT" rg -n '^theorem notificationWait_preserves_ipcSchedulerContractPredicates' SeLe4n/Kernel/IPC/Invariant/NotificationPreservation/

# WS-H5 dual-queue structural invariant anchors — predicate definitions + preservation theorems.
run_check "INVARIANT" rg -n '^def intrusiveQueueWellFormed' SeLe4n/Kernel/IPC/Invariant/Defs.lean
run_check "INVARIANT" rg -n '^def tcbQueueLinkIntegrity' SeLe4n/Kernel/IPC/Invariant/Defs.lean
run_check "INVARIANT" rg -n '^def dualQueueEndpointWellFormed' SeLe4n/Kernel/IPC/Invariant/Defs.lean
run_check "INVARIANT" rg -n '^def dualQueueSystemInvariant' SeLe4n/Kernel/IPC/Invariant/Defs.lean
run_check "INVARIANT" rg -n '^def ipcInvariantFull' SeLe4n/Kernel/IPC/Invariant/Defs.lean
run_check "INVARIANT" rg -n '^theorem intrusiveQueueWellFormed_empty' SeLe4n/Kernel/IPC/Invariant/Structural/
run_check "INVARIANT" rg -n '^theorem tcbQueueLink_forward_safe' SeLe4n/Kernel/IPC/Invariant/Structural/
run_check "INVARIANT" rg -n '^theorem tcbQueueLink_reverse_safe' SeLe4n/Kernel/IPC/Invariant/Structural/
run_check "INVARIANT" rg -n '^theorem endpointQueuePopHead_sender_exists' SeLe4n/Kernel/IPC/Invariant/Structural/
run_check "INVARIANT" rg -n '^theorem endpointQueuePopHead_link_safe' SeLe4n/Kernel/IPC/Invariant/Structural/
run_check "INVARIANT" rg -n '^theorem endpointReceiveDual_sender_exists' SeLe4n/Kernel/IPC/Invariant/Structural/
run_check "INVARIANT" rg -n '^theorem endpointQueuePopHead_preserves_dualQueueSystemInvariant' SeLe4n/Kernel/IPC/Invariant/Structural/
run_check "INVARIANT" rg -n '^theorem endpointQueueEnqueue_preserves_dualQueueSystemInvariant' SeLe4n/Kernel/IPC/Invariant/Structural/
run_check "INVARIANT" rg -n '^theorem endpointSendDual_preserves_dualQueueSystemInvariant' SeLe4n/Kernel/IPC/Invariant/Structural/
run_check "INVARIANT" rg -n '^theorem endpointReceiveDual_preserves_dualQueueSystemInvariant' SeLe4n/Kernel/IPC/Invariant/Structural/
run_check "INVARIANT" rg -n '^theorem endpointCall_preserves_dualQueueSystemInvariant' SeLe4n/Kernel/IPC/Invariant/Structural/
run_check "INVARIANT" rg -n '^theorem endpointReply_preserves_dualQueueSystemInvariant' SeLe4n/Kernel/IPC/Invariant/Structural/
run_check "INVARIANT" rg -n '^theorem endpointReplyRecv_preserves_dualQueueSystemInvariant' SeLe4n/Kernel/IPC/Invariant/Structural/

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
run_check "INVARIANT" rg -n 'contextMatchesCurrent st ∧ currentThreadDequeueCoherent st' SeLe4n/Kernel/Capability/Invariant/Preservation/EndpointReplyAndLifecycle.lean
# proofLayerInvariantBundle uses schedulerInvariantBundleFull.
run_check "INVARIANT" rg -n 'schedulerInvariantBundleFull st' SeLe4n/Kernel/Architecture/Invariant.lean
# Extraction theorems for new components.
run_check "INVARIANT" rg -n '^theorem schedulerInvariantBundleFull_to_contextMatchesCurrent' SeLe4n/Kernel/Scheduler/Invariant.lean
run_check "INVARIANT" rg -n '^theorem coreIpcInvariantBundle_to_ipcInvariant' SeLe4n/Kernel/Capability/Invariant/Preservation/EndpointReplyAndLifecycle.lean
run_check "INVARIANT" rg -n '^theorem coreIpcInvariantBundle_to_dualQueueSystemInvariant' SeLe4n/Kernel/Capability/Invariant/Preservation/EndpointReplyAndLifecycle.lean
run_check "INVARIANT" rg -n '^theorem coreIpcInvariantBundle_to_allPendingMessagesBounded' SeLe4n/Kernel/Capability/Invariant/Preservation/EndpointReplyAndLifecycle.lean
# switchDomain preserves contextMatchesCurrent (new for WS-H12e).
run_check "INVARIANT" rg -n '^theorem switchDomain_preserves_contextMatchesCurrent' SeLe4n/Kernel/Scheduler/Operations/Preservation.lean
# WS-H12e: allPendingMessagesBounded frame lemmas for primitive ops.
run_check "INVARIANT" rg -n '^theorem ensureRunnable_preserves_allPendingMessagesBounded' SeLe4n/Kernel/IPC/Invariant/Structural/
run_check "INVARIANT" rg -n '^theorem removeRunnable_preserves_allPendingMessagesBounded' SeLe4n/Kernel/IPC/Invariant/Structural/
run_check "INVARIANT" rg -n '^theorem storeTcbIpcState_preserves_allPendingMessagesBounded' SeLe4n/Kernel/IPC/Invariant/Structural/
run_check "INVARIANT" rg -n '^theorem storeTcbIpcStateAndMessage_preserves_allPendingMessagesBounded' SeLe4n/Kernel/IPC/Invariant/Structural/
run_check "INVARIANT" rg -n '^theorem storeTcbPendingMessage_preserves_allPendingMessagesBounded' SeLe4n/Kernel/IPC/Invariant/Structural/
run_check "INVARIANT" rg -n '^theorem storeObject_endpoint_preserves_allPendingMessagesBounded' SeLe4n/Kernel/IPC/Invariant/Structural/
run_check "INVARIANT" rg -n '^theorem storeTcbQueueLinks_preserves_allPendingMessagesBounded' SeLe4n/Kernel/IPC/Invariant/Structural/
run_check "INVARIANT" rg -n '^theorem storeObject_notification_preserves_allPendingMessagesBounded' SeLe4n/Kernel/IPC/Invariant/Structural/
# WS-H12e: Compound allPendingMessagesBounded preservation theorems.
run_check "INVARIANT" rg -n '^theorem notificationSignal_preserves_allPendingMessagesBounded' SeLe4n/Kernel/IPC/Invariant/Structural/
run_check "INVARIANT" rg -n '^theorem notificationWait_preserves_allPendingMessagesBounded' SeLe4n/Kernel/IPC/Invariant/Structural/
run_check "INVARIANT" rg -n '^theorem endpointReply_preserves_allPendingMessagesBounded' SeLe4n/Kernel/IPC/Invariant/Structural/
# WS-H12e: Composed ipcInvariantFull preservation theorems.
run_check "INVARIANT" rg -n '^theorem notificationSignal_preserves_ipcInvariantFull' SeLe4n/Kernel/IPC/Invariant/Structural/
run_check "INVARIANT" rg -n '^theorem notificationWait_preserves_ipcInvariantFull' SeLe4n/Kernel/IPC/Invariant/Structural/
run_check "INVARIANT" rg -n '^theorem endpointReply_preserves_ipcInvariantFull' SeLe4n/Kernel/IPC/Invariant/Structural/
run_check "INVARIANT" rg -n '^theorem endpointSendDual_preserves_ipcInvariantFull' SeLe4n/Kernel/IPC/Invariant/Structural/
run_check "INVARIANT" rg -n '^theorem endpointReceiveDual_preserves_ipcInvariantFull' SeLe4n/Kernel/IPC/Invariant/Structural/
run_check "INVARIANT" rg -n '^theorem endpointCall_preserves_ipcInvariantFull' SeLe4n/Kernel/IPC/Invariant/Structural/
run_check "INVARIANT" rg -n '^theorem endpointReplyRecv_preserves_ipcInvariantFull' SeLe4n/Kernel/IPC/Invariant/Structural/

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
run_check "INVARIANT" rg -n '^def ipcSchedulerBlockedNotificationComponent' SeLe4n/Kernel/Capability/Invariant/Preservation/EndpointReplyAndLifecycle.lean

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

# WS-RC R2 (DEEP-FFI-01/02/03): hardware syscall dispatch FFI bridge anchors.
# Pin the post-R2 surface so a regression that strips the substantive
# routing or renames the bridge symbols fails Tier 3 instead of silently
# downgrading to a stub return.
run_check "INVARIANT" rg -n '^def KernelError.toUInt32' SeLe4n/Platform/FFI.lean
run_check "INVARIANT" rg -n 'def encodeError' SeLe4n/Platform/FFI.lean
run_check "INVARIANT" rg -n 'def encodeOk' SeLe4n/Platform/FFI.lean
run_check "INVARIANT" rg -n '^initialize kernelStateRef' SeLe4n/Platform/FFI.lean
run_check "INVARIANT" rg -n '^initialize kernelLabelingContextRef' SeLe4n/Platform/FFI.lean
run_check "INVARIANT" rg -n '^def initialiseKernelState' SeLe4n/Platform/FFI.lean
run_check "INVARIANT" rg -n '^def getKernelState' SeLe4n/Platform/FFI.lean
run_check "INVARIANT" rg -n '^def updateKernelState' SeLe4n/Platform/FFI.lean
run_check "INVARIANT" rg -n '^def initialiseKernelLabelingContext' SeLe4n/Platform/FFI.lean
run_check "INVARIANT" rg -n '^def getKernelLabelingContext' SeLe4n/Platform/FFI.lean
run_check "INVARIANT" rg -n '^def bootAndInitialiseFromPlatform' SeLe4n/Platform/FFI.lean
run_check "INVARIANT" rg -n '^def writeFfiRegistersToTcb' SeLe4n/Platform/FFI.lean
run_check "INVARIANT" rg -n '^def readReturnValue' SeLe4n/Platform/FFI.lean
run_check "INVARIANT" rg -n '^def syscallDispatchFromAbi' SeLe4n/Platform/FFI.lean
run_check "INVARIANT" rg -n '^@\[export suspend_thread_inner\]' SeLe4n/Platform/FFI.lean
run_check "INVARIANT" rg -n '^@\[export syscall_dispatch_inner\]' SeLe4n/Platform/FFI.lean
run_check "INVARIANT" rg -n '^def suspendThreadInner' SeLe4n/Platform/FFI.lean
run_check "INVARIANT" rg -n '^def syscallDispatchInner' SeLe4n/Platform/FFI.lean
run_check "INVARIANT" rg -n '^theorem encodeError_high_bit_set' SeLe4n/Platform/FFI.lean
run_check "INVARIANT" rg -n '^theorem encodeOk_high_bit_clear' SeLe4n/Platform/FFI.lean
run_check "INVARIANT" rg -n '^theorem syscallDispatchFromAbi_total' SeLe4n/Platform/FFI.lean
run_check "INVARIANT" rg -n '^theorem syscallDispatchFromAbi_ok_of_syscallEntryChecked_ok' SeLe4n/Platform/FFI.lean
run_check "INVARIANT" rg -n '^theorem syscallDispatchFromAbi_error_of_syscallEntryChecked_error' SeLe4n/Platform/FFI.lean
run_check "INVARIANT" rg -n '^theorem syscallDispatchFromAbi_illegalState_when_no_current' SeLe4n/Platform/FFI.lean
run_check "INVARIANT" rg -n '^theorem syscallDispatchFromAbi_abiMismatch_rejected' SeLe4n/Platform/FFI.lean
run_check "INVARIANT" rg -n '^theorem writeFfiRegistersToTcb_id_when_not_tcb' SeLe4n/Platform/FFI.lean
run_check "INVARIANT" rg -n '^theorem readReturnValue_zero_when_not_tcb' SeLe4n/Platform/FFI.lean
# WS-RC R2.B.4: Rust comment alignment — the FFI inner symbol the
# Rust HAL extern-imports must match the Lean @[export] name.
run_check "INVARIANT" rg -n 'fn syscall_dispatch_inner' rust/sele4n-hal/src/svc_dispatch.rs
run_check "INVARIANT" rg -n 'fn suspend_thread_inner' rust/sele4n-hal/src/ffi.rs

# WS-I2/R-05: Lean #check correctness anchors (type-level validation).
# D5: The Liveness module is proof-only and not imported from Main.lean,
# so `lake build` (default target) does not produce its .olean files.
# Build it explicitly before the inline check to avoid CI cache misses.
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake build SeLe4n.Kernel.Scheduler.Liveness'
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake env lean --stdin <<"EOF"
import SeLe4n.Kernel.Scheduler.Operations.Preservation
import SeLe4n.Kernel.Capability.Invariant.Preservation
import SeLe4n.Kernel.IPC.Invariant.EndpointPreservation
import SeLe4n.Kernel.Lifecycle.Invariant
import SeLe4n.Kernel.Service.Invariant.Acyclicity
import SeLe4n.Kernel.Architecture.VSpaceInvariant
import SeLe4n.Kernel.InformationFlow.Invariant.Composition
import SeLe4n.Kernel.API
import SeLe4n.Kernel.SchedContext.Invariant
import SeLe4n.Kernel.Scheduler.Liveness
import SeLe4n.Kernel.SchedContext.ReplenishQueue

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
-- WS-Z Phase Z3: Replenishment Queue invariants and preservation
#check @SeLe4n.Kernel.replenishQueueSorted
#check @SeLe4n.Kernel.replenishQueueSizeConsistent
#check @SeLe4n.Kernel.replenishQueueConsistent
#check @SeLe4n.Kernel.insert_preserves_sorted
#check @SeLe4n.Kernel.popDue_preserves_sorted
#check @SeLe4n.Kernel.popDue_sizeConsistent
#check @SeLe4n.Kernel.remove_preserves_sorted
#check @SeLe4n.Kernel.filter_preserves_pairwiseSortedBy
#check @SeLe4n.Kernel.insertSorted_length
#check @SeLe4n.Kernel.insert_sizeConsistent
#check @SeLe4n.Kernel.remove_sizeConsistent
#check @SeLe4n.Kernel.empty_sorted
#check @SeLe4n.Kernel.empty_consistent
-- WS-Z Phase Z4: Scheduler Integration invariants, operations, and preservation
#check @SeLe4n.Kernel.budgetPositive
#check @SeLe4n.Kernel.currentBudgetPositive
#check @SeLe4n.Kernel.schedContextsWellFormed
#check @SeLe4n.Kernel.replenishQueueValid
#check @SeLe4n.Kernel.schedContextBindingConsistent
#check @SeLe4n.Kernel.effectiveParamsMatchRunQueue
#check @SeLe4n.Kernel.schedulerInvariantBundleExtended
-- WS-RC R5.C.1: effectivePriority retired (full deprecation); only
-- effectiveSchedParams remains as the canonical scheduling-param API.
#check @SeLe4n.Kernel.effectiveSchedParams
#check @SeLe4n.Kernel.hasSufficientBudget
#check @SeLe4n.Kernel.chooseThreadEffective
#check @SeLe4n.Kernel.timerTickBudget
#check @SeLe4n.Kernel.scheduleEffective
#check @SeLe4n.Kernel.timerTickWithBudget
#check @SeLe4n.Kernel.handleYieldWithBudget
#check @SeLe4n.Kernel.processReplenishmentsDue
#check @SeLe4n.Kernel.chooseThreadEffective_state_unchanged
#check @SeLe4n.Kernel.budgetPositive_subset
#check @SeLe4n.Kernel.effectiveSchedParams_unbound_legacy
#check @SeLe4n.Kernel.hasSufficientBudget_unbound_legacy
#check @SeLe4n.Kernel.consumeBudget_preserves_schedContextWellFormed_full
#check @SeLe4n.Kernel.scheduleReplenishment_preserves_schedContextWellFormed_full
#check @SeLe4n.Kernel.cbsUpdateDeadline_preserves_wf
-- D5: Bounded Latency Theorem surface anchors
#check @SeLe4n.Kernel.Liveness.WCRTHypotheses
#check @SeLe4n.Kernel.Liveness.wcrtBound
#check @SeLe4n.Kernel.Liveness.wcrtBound_unfold
#check @SeLe4n.Kernel.Liveness.countHigherOrEqual_mono_threshold
#check @SeLe4n.Kernel.Liveness.pip_enhanced_wcrt_le_base
#check @SeLe4n.Kernel.Liveness.domainRotationTotal_le_bound
#check @SeLe4n.Kernel.Liveness.fifoProgressBound
#check @SeLe4n.Kernel.Liveness.bandExhaustionBound
-- AF1: New theorems and renames
#check @SeLe4n.Kernel.PriorityInheritance.blockingChain_step
#check @SeLe4n.Kernel.PriorityInheritance.blockingChain_congr
#check @SeLe4n.Kernel.PriorityInheritance.blockingAcyclic_frame
#check @SeLe4n.Kernel.PriorityInheritance.pip_congruence
#check @SeLe4n.Kernel.PriorityInheritance.pip_revert_congruence
#check @SeLe4n.Kernel.crossSubsystemInvariant_to_blockingAcyclic
EOF'

# WS-SM SM0 — surface anchors for the Concurrency.* foundational types
# (CoreId, SharingDomain, SgiKind, LockKind, LockId, BklState) plus the
# AN12-B inventory hardening theorems (NoDup witnesses, 6-way ArchAssumption
# distinctness, Anchors module).  WS-SM SM1.B.5 adds the per-CPU FFI
# wrapper surface (Concurrency.Runtime + Platform.FFI.ffiCurrentCoreId).
# WS-SM SM1.C.6 adds the secondary-core kernel-entry placeholder
# (Kernel.SecondaryEntry.secondaryKernelMain + marker theorem).
# WS-SM SM1.E.4 adds the typed TLBI dispatcher wrapper
# (Architecture.TlbiForSharing + tag encoding theorems).
# WS-SM SM1.F.6 adds the SGI primitive FFI bindings
# (Platform.FFI.ffiSendSgi*).
# Build the foundational + Anchors + Runtime + SecondaryEntry +
# TlbiForSharing modules first so the .olean files exist.
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake build \
  SeLe4n.Kernel.Concurrency.Types \
  SeLe4n.Kernel.Concurrency.Locks \
  SeLe4n.Kernel.Concurrency.Locks.Kind \
  SeLe4n.Kernel.Concurrency.Sgi \
  SeLe4n.Kernel.Concurrency.Anchors \
  SeLe4n.Kernel.Concurrency.Runtime \
  SeLe4n.Kernel.SecondaryEntry \
  SeLe4n.Kernel.Architecture.TlbiForSharing'
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake env lean --stdin <<"EOF"
import SeLe4n.Kernel.Concurrency.Types
import SeLe4n.Kernel.Concurrency.Locks
import SeLe4n.Kernel.Concurrency.Locks.Kind
import SeLe4n.Kernel.Concurrency.Sgi
import SeLe4n.Kernel.Concurrency.Anchors
import SeLe4n.Kernel.Concurrency.Assumptions
import SeLe4n.Kernel.Concurrency.Runtime
import SeLe4n.Kernel.SecondaryEntry
import SeLe4n.Kernel.Architecture.Assumptions
import SeLe4n.Kernel.Architecture.TlbiForSharing
import SeLe4n.Platform.FFI
import SeLe4n.Platform.RPi5.Contract

-- SM0.E — CoreId enumeration
#check @SeLe4n.Kernel.Concurrency.numCores
#check @SeLe4n.Kernel.Concurrency.CoreId
#check @SeLe4n.Kernel.Concurrency.bootCoreId
#check @SeLe4n.Kernel.Concurrency.allCores
#check @SeLe4n.Kernel.Concurrency.numCores_pos
#check @SeLe4n.Kernel.Concurrency.allCores_length
#check @SeLe4n.Kernel.Concurrency.allCores_nodup
#check @SeLe4n.Kernel.Concurrency.bootCoreId_valid
-- SM0.F — SharingDomain
#check @SeLe4n.Kernel.Concurrency.SharingDomain
#check @SeLe4n.Kernel.Concurrency.dsbForSharing
#check @SeLe4n.Kernel.Concurrency.dsbStForSharing
#check @SeLe4n.Kernel.Concurrency.dsbForSharing_injective
#check @SeLe4n.Kernel.Concurrency.dsbStForSharing_injective
-- SM0.H — SgiKind
#check @SeLe4n.Kernel.Concurrency.SgiKind
#check @SeLe4n.Kernel.Concurrency.SgiKind.toIntid
#check @SeLe4n.Kernel.Concurrency.SgiKind.toIntid_injective
#check @SeLe4n.Kernel.Concurrency.SgiKind.toIntid_in_range
-- SM0.I — LockKind / LockId / BklState
#check @SeLe4n.Kernel.Concurrency.LockKind
#check @SeLe4n.Kernel.Concurrency.LockKind.level
#check @SeLe4n.Kernel.Concurrency.LockKind.level_strictMono
#check @SeLe4n.Kernel.Concurrency.LockKind.level_surjective
#check @SeLe4n.Kernel.Concurrency.LockKind.level_bounded
#check @SeLe4n.Kernel.Concurrency.LockId
#check @SeLe4n.Kernel.Concurrency.LockId.le_total
#check @SeLe4n.Kernel.Concurrency.LockId.le_refl
#check @SeLe4n.Kernel.Concurrency.LockId.le_trans
#check @SeLe4n.Kernel.Concurrency.LockId.le_antisymm
#check @SeLe4n.Kernel.Concurrency.LockId.lt_trichotomy
-- SM3.D.3 — LockId strict-order helpers (irreflexive / transitive / asymmetric).
#check @SeLe4n.Kernel.Concurrency.LockId.lt_irrefl
#check @SeLe4n.Kernel.Concurrency.LockId.lt_trans
#check @SeLe4n.Kernel.Concurrency.LockId.lt_asymm
#check @SeLe4n.Kernel.Concurrency.BklState
#check @SeLe4n.Kernel.Concurrency.bklHeldBy
#check @SeLe4n.Kernel.Concurrency.bklState_unique_owner
-- SM0.A/B — ArchAssumption 6-way machinery
#check @SeLe4n.Kernel.Architecture.ArchAssumption
#check @SeLe4n.Kernel.Architecture.assumptionInventory_count
#check @SeLe4n.Kernel.Architecture.archAssumptionConsumer_distinct_6
#check @SeLe4n.Kernel.Architecture.architecture_assumptions_index_total_6
-- SM0.C/D — AN12-B inventory hardening
#check @SeLe4n.Kernel.Concurrency.smpAnchorVerified
#check @SeLe4n.Kernel.Concurrency.smpLatentInventory_identifiers_nodup
#check @SeLe4n.Kernel.Concurrency.smpLatentInventory_sourceTheorems_nodup
-- SM4.E — single-core witness retirement + retirement ledger
#check @SeLe4n.Platform.Boot.bootFromPlatform_smp_witness
#check @SeLe4n.Platform.Boot.bootFromPlatform_smp_currentAllNone
#check @SeLe4n.Kernel.Concurrency.smpRetiredInventory_count
#check @SeLe4n.Kernel.Concurrency.smpRetiredInventory_covers_latent
#check @SeLe4n.Kernel.Concurrency.smpRetiredInventory_identifiers_nodup
#check @SeLe4n.Kernel.Concurrency.smpRetiredInventory_anchor_nodup
#check @SeLe4n.Kernel.Concurrency.smpRetiredInventory_pathARetired_count
#check @SeLe4n.Kernel.Concurrency.smpRetiredInventory_perCoreBracketGated_count
-- SM4.G — per-core idle-thread bootstrap
#check @SeLe4n.Platform.Boot.idleThreadId_injective
#check @SeLe4n.Platform.Boot.bootFromPlatformWithIdleThreads_all_cores_have_idle
#check @SeLe4n.Platform.Boot.bootFromPlatformWithIdleThreads_schedulerInvariantBundle
#check @SeLe4n.Platform.Boot.bootFromPlatformWithIdleThreads_schedulerInvariantBundleFull
#check @SeLe4n.Platform.Boot.bootFromPlatformWithIdleThreads_currentThreadInActiveDomain
#check @SeLe4n.Platform.Boot.bootFromPlatformWithIdleThreads_valid
#check @SeLe4n.Platform.Boot.idleSlotsFreshAt
#check @SeLe4n.Platform.Boot.bootFromPlatformWithIdleThreads_preserves_platform_objects
#check @SeLe4n.Platform.Boot.idleSlotsFreshAt_of_initialObjects_below_base
-- SM0.G — PlatformBinding extension
#check @SeLe4n.Platform.PlatformBinding.coreCount
#check @SeLe4n.Platform.PlatformBinding.bootCoreId
#check @SeLe4n.Platform.PlatformBinding.sharingDomain
#check @SeLe4n.Platform.RPi5.numCores_eq_rpi5_coreCount
#check @SeLe4n.Platform.RPi5.bootCoreId_val_eq_rpi5
#check @SeLe4n.Platform.RPi5.rpi5_sharingDomain
-- SM1.B.5 — Per-CPU core-id FFI wrapper (closes SMP-M4)
#check @SeLe4n.Platform.FFI.ffiCurrentCoreId
#check @SeLe4n.Kernel.Concurrency.currentCoreId
#check @SeLe4n.Kernel.Concurrency.currentCoreId_in_range_marker
#check @SeLe4n.Kernel.Concurrency.instInhabitedCoreId
-- SM1.C.6 — Secondary-core kernel-entry placeholder (closes SMP-C2 Lean side)
#check @SeLe4n.Kernel.secondaryKernelMain
#check @SeLe4n.Kernel.secondaryKernelMain_returns_unit_marker
-- SM1.E.4 — Typed TLBI dispatcher wrapper (post-SM7 cross-core call sites)
#check @SeLe4n.Kernel.Architecture.TlbInvalidation
#check @SeLe4n.Kernel.Architecture.TlbInvalidation.toOpTag
#check @SeLe4n.Kernel.Architecture.TlbInvalidation.toAsid
#check @SeLe4n.Kernel.Architecture.TlbInvalidation.toVaddr
#check @SeLe4n.Kernel.Concurrency.SharingDomain.toTag
#check @SeLe4n.Kernel.Architecture.tlbiForSharing
#check @SeLe4n.Kernel.Concurrency.SharingDomain.toTag_injective
#check @SeLe4n.Kernel.Concurrency.SharingDomain.toTag_in_range
#check @SeLe4n.Kernel.Architecture.TlbInvalidation.toOpTag_in_range
#check @SeLe4n.Kernel.Architecture.TlbInvalidation.toOpTag_distinct_constructors
#check @SeLe4n.Kernel.Architecture.tlbiForSharing_total
#check @SeLe4n.Kernel.Architecture.tlbiForSharing_ffi_args_in_range
#check @SeLe4n.Platform.FFI.ffiTlbiForSharing
-- SM1.F.6 — SGI primitive FFI bindings
#check @SeLe4n.Platform.FFI.ffiSendSgi
#check @SeLe4n.Platform.FFI.ffiSendSgiToSelf
#check @SeLe4n.Platform.FFI.ffiSendSgiToAllButSelf
-- SM1.I.3 — Per-core IDLE thread FFI bindings + typed wrappers
#check @SeLe4n.Platform.FFI.ffiIdleWait
#check @SeLe4n.Platform.FFI.ffiIdleWaitBounded
#check @SeLe4n.Kernel.Concurrency.idleWait
#check @SeLe4n.Kernel.Concurrency.idleWaitBounded
-- SM1.I.4 — Per-core stats FFI bindings + typed wrappers
#check @SeLe4n.Platform.FFI.ffiPerCoreIrqCount
#check @SeLe4n.Platform.FFI.ffiPerCoreTimerTickCount
#check @SeLe4n.Platform.FFI.ffiPerCoreSgiCount
#check @SeLe4n.Platform.FFI.ffiPerCoreSyscallCount
#check @SeLe4n.Kernel.Concurrency.perCoreIrqCount
#check @SeLe4n.Kernel.Concurrency.perCoreTimerTickCount
#check @SeLe4n.Kernel.Concurrency.perCoreSgiCount
#check @SeLe4n.Kernel.Concurrency.perCoreSyscallCount
#check @SeLe4n.Kernel.Concurrency.perCoreIrqCount_returns_baseio_uint64_marker
#check @SeLe4n.Kernel.Concurrency.perCoreTimerTickCount_returns_baseio_uint64_marker
#check @SeLe4n.Kernel.Concurrency.perCoreSgiCount_returns_baseio_uint64_marker
#check @SeLe4n.Kernel.Concurrency.perCoreSyscallCount_returns_baseio_uint64_marker
#check @SeLe4n.Kernel.Concurrency.idleWait_returns_baseio_unit_marker
#check @SeLe4n.Kernel.Concurrency.idleWaitBounded_returns_baseio_uint64_marker
EOF'

# WS-SM SM2.A — Abstract memory model surface anchors.  Covers every
# public symbol exported by `Kernel.Concurrency.MemoryModel` so SM2.B
# (TicketLock) and SM2.C (RwLock) consumers cannot break the upstream
# release-acquire pairing foundation without surfacing here first.
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake build SeLe4n.Kernel.Concurrency.MemoryModel'
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake env lean --stdin <<"EOF"
import SeLe4n.Kernel.Concurrency.MemoryModel

-- SM2.A.1 — MemoryOrder
#check @SeLe4n.Kernel.Concurrency.MemoryOrder
#check @SeLe4n.Kernel.Concurrency.MemoryOrder.isAcquire
#check @SeLe4n.Kernel.Concurrency.MemoryOrder.isRelease
#check @SeLe4n.Kernel.Concurrency.MemoryOrder.acqRel_both
#check @SeLe4n.Kernel.Concurrency.MemoryOrder.seqCst_both
#check @SeLe4n.Kernel.Concurrency.MemoryOrder.relaxed_neither
-- SM2.A.2 — AtomicLocation
#check @SeLe4n.Kernel.Concurrency.AtomicLocation
#check @SeLe4n.Kernel.Concurrency.AtomicLocation.nextTicketOf
#check @SeLe4n.Kernel.Concurrency.AtomicLocation.servingOf
#check @SeLe4n.Kernel.Concurrency.AtomicLocation.rwLockStateOf
#check @SeLe4n.Kernel.Concurrency.AtomicLocation.ticketLock_fields_distinct
-- SM2.A.3 — MemoryEvent
#check @SeLe4n.Kernel.Concurrency.MemoryEvent
-- SM2.A.4 — MemoryTrace
#check @SeLe4n.Kernel.Concurrency.MemoryTrace
#check @SeLe4n.Kernel.Concurrency.MemoryTrace.empty
#check @SeLe4n.Kernel.Concurrency.MemoryTrace.append
#check @SeLe4n.Kernel.Concurrency.MemoryTrace.empty_events
#check @SeLe4n.Kernel.Concurrency.MemoryTrace.append_events
#check @SeLe4n.Kernel.Concurrency.MemoryTrace.append_length
-- SM2.A.5 — wellFormed + eventPos
#check @SeLe4n.Kernel.Concurrency.MemoryTrace.wellFormed
#check @SeLe4n.Kernel.Concurrency.MemoryTrace.empty_wellFormed
#check @SeLe4n.Kernel.Concurrency.MemoryTrace.eventPos
#check @SeLe4n.Kernel.Concurrency.MemoryTrace.eventPos_lt_length
#check @SeLe4n.Kernel.Concurrency.MemoryTrace.eventPos_eq_length_of_not_mem
#check @SeLe4n.Kernel.Concurrency.MemoryTrace.eventPos_get_eq
#check @SeLe4n.Kernel.Concurrency.MemoryTrace.eventPos_inj
-- SM2.A.6 — synchronizesWith
#check @SeLe4n.Kernel.Concurrency.synchronizesWith
#check @SeLe4n.Kernel.Concurrency.synchronizesWith_relaxed_load_rejected
#check @SeLe4n.Kernel.Concurrency.synchronizesWith_relaxed_store_rejected
-- SM2.A.7 — sequencedBefore + happensBefore
#check @SeLe4n.Kernel.Concurrency.sequencedBefore
#check @SeLe4n.Kernel.Concurrency.happensBefore
#check @SeLe4n.Kernel.Concurrency.happensBefore.seq
#check @SeLe4n.Kernel.Concurrency.happensBefore.sync
#check @SeLe4n.Kernel.Concurrency.happensBefore.trans
#check @SeLe4n.Kernel.Concurrency.happensBefore_in_trace
#check @SeLe4n.Kernel.Concurrency.happensBefore_strict_positional
-- SM2.A.8/.9/.10/.11 — Partial-order theorems (the four canonical witnesses)
#check @SeLe4n.Kernel.Concurrency.happensBefore_irreflexive
#check @SeLe4n.Kernel.Concurrency.happensBefore_transitive
#check @SeLe4n.Kernel.Concurrency.happensBefore_antisymmetric
#check @SeLe4n.Kernel.Concurrency.happens_before_partial_order
#check @SeLe4n.Kernel.Concurrency.happens_before_strict_partial_order
#check @SeLe4n.Kernel.Concurrency.happensBefore_no_cycle
-- SM2.A helper lifters for SM2.B/SM2.C consumers
#check @SeLe4n.Kernel.Concurrency.sequencedBefore_implies_happensBefore
#check @SeLe4n.Kernel.Concurrency.synchronizesWith_implies_happensBefore
#check @SeLe4n.Kernel.Concurrency.MemoryTrace.wellFormed.nodup
#check @SeLe4n.Kernel.Concurrency.MemoryTrace.wellFormed.pairwise
#check @SeLe4n.Kernel.Concurrency.happensBefore_eventPos_lt
#check @SeLe4n.Kernel.Concurrency.happensBefore_endpoints_in_trace_with_pos
-- SM2.A operational-semantics base case + inductive step
#check @SeLe4n.Kernel.Concurrency.MemoryTrace.singleton_wellFormed
#check @SeLe4n.Kernel.Concurrency.MemoryTrace.wellFormed_append
EOF'

# WS-SM SM2.B — TicketLock surface anchors.  Covers every public symbol
# exported by `Kernel.Concurrency.Locks.TicketLock` so SM3 ladder-
# acquisition consumers cannot break the upstream wf-preservation /
# FIFO / bounded-wait / RA-pairing foundation without surfacing here
# first.
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake build SeLe4n.Kernel.Concurrency.Locks.TicketLock'
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake env lean --stdin <<"EOF"
import SeLe4n.Kernel.Concurrency.Locks.TicketLock

-- SM2.B.1 — TicketLockState
#check @SeLe4n.Kernel.Concurrency.TicketLockState
#check @SeLe4n.Kernel.Concurrency.TicketLockState.nextTicket
#check @SeLe4n.Kernel.Concurrency.TicketLockState.serving
#check @SeLe4n.Kernel.Concurrency.TicketLockState.pending
#check @SeLe4n.Kernel.Concurrency.TicketLockState.held
-- SM2.B.2 — unheld + witnesses
#check @SeLe4n.Kernel.Concurrency.TicketLockState.unheld
#check @SeLe4n.Kernel.Concurrency.TicketLockState.unheld_nextTicket
#check @SeLe4n.Kernel.Concurrency.TicketLockState.unheld_serving
#check @SeLe4n.Kernel.Concurrency.TicketLockState.unheld_pending
#check @SeLe4n.Kernel.Concurrency.TicketLockState.unheld_held
-- SM2.B.3 — wf predicate + Bool helpers
#check @SeLe4n.Kernel.Concurrency.TicketLockState.pendingInRange
#check @SeLe4n.Kernel.Concurrency.TicketLockState.heldCount
#check @SeLe4n.Kernel.Concurrency.TicketLockState.holderTicketIsServing
#check @SeLe4n.Kernel.Concurrency.TicketLockState.holderTicketDisjointFromPending
#check @SeLe4n.Kernel.Concurrency.TicketLockState.holderCoreDisjointFromPending
#check @SeLe4n.Kernel.Concurrency.TicketLockState.wf
#check @SeLe4n.Kernel.Concurrency.TicketLockState.pendingInRange_iff
#check @SeLe4n.Kernel.Concurrency.TicketLockState.holderTicketIsServing_iff
#check @SeLe4n.Kernel.Concurrency.TicketLockState.holderTicketDisjointFromPending_iff
#check @SeLe4n.Kernel.Concurrency.TicketLockState.holderCoreDisjointFromPending_iff
-- SM2.B.4 — unheld_wf
#check @SeLe4n.Kernel.Concurrency.TicketLockState.unheld_wf
-- SM2.B.5 — TicketLockOp
#check @SeLe4n.Kernel.Concurrency.TicketLockOp
#check @SeLe4n.Kernel.Concurrency.TicketLockOp.tryAcquire
#check @SeLe4n.Kernel.Concurrency.TicketLockOp.release
#check @SeLe4n.Kernel.Concurrency.TicketLockOp.observeServing
-- SM2.B.6 — Operational semantics
#check @SeLe4n.Kernel.Concurrency.TicketLockState.captureTicket
#check @SeLe4n.Kernel.Concurrency.TicketLockState.observeServing
#check @SeLe4n.Kernel.Concurrency.TicketLockState.observeServing_eq_serving
#check @SeLe4n.Kernel.Concurrency.TicketLockState.applyOp
-- SM2.B.7 — promotePending + releaseAndPromote
#check @SeLe4n.Kernel.Concurrency.TicketLockState.promotePending
#check @SeLe4n.Kernel.Concurrency.TicketLockState.releaseAndPromote
-- SM2.B.8 — mutex
#check @SeLe4n.Kernel.Concurrency.ticketLock_mutex
-- SM2.B.9 — wf preservation (per-op + aggregate)
#check @SeLe4n.Kernel.Concurrency.TicketLockState.applyOp_release_cases
#check @SeLe4n.Kernel.Concurrency.ticketLock_observeServing_preserves_wf
#check @SeLe4n.Kernel.Concurrency.ticketLock_release_preserves_partial_wf
#check @SeLe4n.Kernel.Concurrency.ticketLock_tryAcquire_preserves_wf
#check @SeLe4n.Kernel.Concurrency.ticketLock_releaseAndPromote_preserves_wf
#check @SeLe4n.Kernel.Concurrency.ticketLock_wf_invariant
-- SM2.B.10 — FIFO
#check @SeLe4n.Kernel.Concurrency.TicketLockState.applyOp_nextTicket_monotone
#check @SeLe4n.Kernel.Concurrency.TicketLockState.applyOp_release_nextTicket_eq
#check @SeLe4n.Kernel.Concurrency.TicketLockState.promotePending_nextTicket_eq
#check @SeLe4n.Kernel.Concurrency.TicketLockState.releaseAndPromote_nextTicket_eq
#check @SeLe4n.Kernel.Concurrency.TicketLockState.applyOp_tryAcquire_captures
#check @SeLe4n.Kernel.Concurrency.ticketLock_fifo
#check @SeLe4n.Kernel.Concurrency.ticketLock_fifo_trace
#check @SeLe4n.Kernel.Concurrency.ticketLock_fifo_strict
-- SM2.B.11 — bounded wait
#check @SeLe4n.Kernel.Concurrency.ticketLock_bounded_wait
-- SM2.B.12 — release-acquire pairing
#check @SeLe4n.Kernel.Concurrency.ticketLock_release_acquire_pairing
#check @SeLe4n.Kernel.Concurrency.ticketLock_release_acquire_happensBefore
-- SM2.B.13 — reachability
#check @SeLe4n.Kernel.Concurrency.KernelStep
#check @SeLe4n.Kernel.Concurrency.KernelStep.acquire
#check @SeLe4n.Kernel.Concurrency.KernelStep.release
#check @SeLe4n.Kernel.Concurrency.KernelStep.observe
#check @SeLe4n.Kernel.Concurrency.Reachable
#check @SeLe4n.Kernel.Concurrency.Reachable.base
#check @SeLe4n.Kernel.Concurrency.Reachable.step
#check @SeLe4n.Kernel.Concurrency.ticketLock_reachability
-- SM2.B.14 — determinism
#check @SeLe4n.Kernel.Concurrency.ticketLock_applyOp_deterministic
#check @SeLe4n.Kernel.Concurrency.ticketLock_promotePending_deterministic
-- SM2.B.15 — closure-form preservation aliases
#check @SeLe4n.Kernel.Concurrency.ticketLock_acquire_preserves_wf
#check @SeLe4n.Kernel.Concurrency.ticketLock_release_preserves_wf
EOF'

# WS-SM SM2.C — RwLock surface anchors.  Covers every public symbol
# exported by `Kernel.Concurrency.Locks.RwLock` so SM3 per-object lock
# consumers cannot break the upstream wf-preservation / FIFO admission /
# bounded-wait / RA-pairing / reader-batching foundation without
# surfacing here first.
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake build SeLe4n.Kernel.Concurrency.Locks.RwLock'
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake env lean --stdin <<"EOF"
import SeLe4n.Kernel.Concurrency.Locks.RwLock

-- SM2.C.1 — AccessMode + RwLockState
#check @SeLe4n.Kernel.Concurrency.AccessMode
#check @SeLe4n.Kernel.Concurrency.AccessMode.read
#check @SeLe4n.Kernel.Concurrency.AccessMode.write
#check @SeLe4n.Kernel.Concurrency.RwLockState
#check @SeLe4n.Kernel.Concurrency.RwLockState.writerHeld
#check @SeLe4n.Kernel.Concurrency.RwLockState.readers
#check @SeLe4n.Kernel.Concurrency.RwLockState.waiters
#check @SeLe4n.Kernel.Concurrency.RwLockState.unheld
#check @SeLe4n.Kernel.Concurrency.RwLockState.unheld_writerHeld
#check @SeLe4n.Kernel.Concurrency.RwLockState.unheld_readers
#check @SeLe4n.Kernel.Concurrency.RwLockState.unheld_waiters
-- SM2.C.2 — wf predicate + Bool helpers + iff bridges + decidability
#check @SeLe4n.Kernel.Concurrency.RwLockState.writerReadersExclusion
#check @SeLe4n.Kernel.Concurrency.RwLockState.waitersDisjointFromHolders
#check @SeLe4n.Kernel.Concurrency.RwLockState.fifoAdmissionDiscipline
#check @SeLe4n.Kernel.Concurrency.RwLockState.wf
#check @SeLe4n.Kernel.Concurrency.RwLockState.writerReadersExclusion_iff
#check @SeLe4n.Kernel.Concurrency.RwLockState.waitersDisjointFromHolders_iff
#check @SeLe4n.Kernel.Concurrency.RwLockState.fifoAdmissionDiscipline_iff
#check @SeLe4n.Kernel.Concurrency.RwLockState.unheld_wf
#check @SeLe4n.Kernel.Concurrency.RwLockState.wfPartial
#check @SeLe4n.Kernel.Concurrency.RwLockState.wf_implies_wfPartial
#check @SeLe4n.Kernel.Concurrency.RwLockState.wfPartial_to_wf
-- SM2.C.3 — RwLockOp
#check @SeLe4n.Kernel.Concurrency.RwLockOp
#check @SeLe4n.Kernel.Concurrency.RwLockOp.tryAcquireRead
#check @SeLe4n.Kernel.Concurrency.RwLockOp.releaseRead
#check @SeLe4n.Kernel.Concurrency.RwLockOp.tryAcquireWrite
#check @SeLe4n.Kernel.Concurrency.RwLockOp.releaseWrite
-- SM2.C.4 — Operational semantics
#check @SeLe4n.Kernel.Concurrency.RwLockState.coreInvolved
#check @SeLe4n.Kernel.Concurrency.RwLockState.applyOp
#check @SeLe4n.Kernel.Concurrency.RwLockState.promoteWaitersOnWriterRelease
#check @SeLe4n.Kernel.Concurrency.RwLockState.promoteWaitersIfReadersEmpty
-- SM2.C.5..6 — Exclusion + reader multiplicity
#check @SeLe4n.Kernel.Concurrency.rwLock_writer_readers_exclusion
#check @SeLe4n.Kernel.Concurrency.rwLock_reader_multiplicity
-- SM2.C.7 — FIFO admission (substantive drop-prefix claim)
#check @SeLe4n.Kernel.Concurrency.rwLock_fifo_admission
#check @SeLe4n.Kernel.Concurrency.rwLock_fifo_admission_readers_empty
#check @SeLe4n.Kernel.Concurrency.rwLock_promote_subset_of_waiters
#check @SeLe4n.Kernel.Concurrency.rwLock_promote_is_sublist_of_waiters
#check @SeLe4n.Kernel.Concurrency.rwLock_promote_preserves_order
-- SM2.C.8..9 — Bounded wait
#check @SeLe4n.Kernel.Concurrency.rwLock_bounded_wait_read
#check @SeLe4n.Kernel.Concurrency.rwLock_bounded_wait_write
-- SM2.C.10..11 — Release-acquire pairing
#check @SeLe4n.Kernel.Concurrency.rwLock_release_acquire_pairing_read
#check @SeLe4n.Kernel.Concurrency.rwLock_release_acquire_pairing_write
#check @SeLe4n.Kernel.Concurrency.rwLock_release_acquire_happensBefore_read
-- SM2.C.12 — wf preservation (per-op + aggregate)
#check @SeLe4n.Kernel.Concurrency.rwLock_tryAcquireRead_preserves_wf
#check @SeLe4n.Kernel.Concurrency.rwLock_releaseRead_preserves_wf
#check @SeLe4n.Kernel.Concurrency.rwLock_tryAcquireWrite_preserves_wf
#check @SeLe4n.Kernel.Concurrency.rwLock_releaseWrite_preserves_wf
#check @SeLe4n.Kernel.Concurrency.rwLock_wf_invariant
#check @SeLe4n.Kernel.Concurrency.rwLock_promoteWaitersOnWriterRelease_preserves_wf
#check @SeLe4n.Kernel.Concurrency.rwLock_promoteWaitersIfReadersEmpty_preserves_wf
#check @SeLe4n.Kernel.Concurrency.rwLock_promoteWaitersOnWriterRelease_preserves_wf_partial
#check @SeLe4n.Kernel.Concurrency.rwLock_promoteWaitersIfReadersEmpty_preserves_wf_partial
-- SM2.C.13 — Reader batching (structural + strengthened bounds)
#check @SeLe4n.Kernel.Concurrency.rwLock_reader_batching
#check @SeLe4n.Kernel.Concurrency.rwLock_reader_batching_admits_at_least_one
#check @SeLe4n.Kernel.Concurrency.rwLock_reader_batching_exact_count
-- SM2.C.14 — Writer safety + determinism
#check @SeLe4n.Kernel.Concurrency.rwLock_writer_safety_under_reader_acquire
#check @SeLe4n.Kernel.Concurrency.rwLock_no_writer_starvation
#check @SeLe4n.Kernel.Concurrency.rwLock_applyOp_deterministic
#check @SeLe4n.Kernel.Concurrency.rwLock_promoteWaitersOnWriterRelease_deterministic
#check @SeLe4n.Kernel.Concurrency.rwLock_promoteWaitersIfReadersEmpty_deterministic
-- SM2.C.15 — Closure-form preservation aliases
#check @SeLe4n.Kernel.Concurrency.rwLock_tryAcquireRead_preserves_wf_alias
#check @SeLe4n.Kernel.Concurrency.rwLock_releaseRead_preserves_wf_alias
#check @SeLe4n.Kernel.Concurrency.rwLock_tryAcquireWrite_preserves_wf_alias
#check @SeLe4n.Kernel.Concurrency.rwLock_releaseWrite_preserves_wf_alias
-- SM2.C.16..18 — Bit-packed encoding
#check @SeLe4n.Kernel.Concurrency.RwLockEncoded
#check @SeLe4n.Kernel.Concurrency.writerBitPos
#check @SeLe4n.Kernel.Concurrency.writerBit
#check @SeLe4n.Kernel.Concurrency.readerMask
#check @SeLe4n.Kernel.Concurrency.encodeRwLock
#check @SeLe4n.Kernel.Concurrency.decodeRwLock
#check @SeLe4n.Kernel.Concurrency.rwLock_encode_decode_roundtrip
#check @SeLe4n.Kernel.Concurrency.rwLock_decode_encode_roundtrip
#check @SeLe4n.Kernel.Concurrency.rwLock_encode_writer_bit_set
#check @SeLe4n.Kernel.Concurrency.rwLock_encode_writer_bit_clear
#check @SeLe4n.Kernel.Concurrency.rwLock_reader_count_no_overflow_under_numCores
EOF'

# WS-SM SM2.C.20 — RwLock refinement bridge surface anchors.
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake build SeLe4n.Kernel.Concurrency.Locks.RwLockRefinement'
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake env lean --stdin <<"EOF"
import SeLe4n.Kernel.Concurrency.Locks.RwLockRefinement

#check @SeLe4n.Kernel.Concurrency.rwLockSim
#check @SeLe4n.Kernel.Concurrency.rwLockSim_unheld
#check @SeLe4n.Kernel.Concurrency.rwLockSim_writer_only
#check @SeLe4n.Kernel.Concurrency.rwLockSim_readers_only
#check @SeLe4n.Kernel.Concurrency.rwLockSim_writer_bit_iff
#check @SeLe4n.Kernel.Concurrency.rwLockSim_reader_count_iff
#check @SeLe4n.Kernel.Concurrency.rwLock_refinement_preservation_noop

-- WS-SM SM2.C-defer D-1..D-4 deferred-completion surface anchors.
-- See docs/planning/SMP_RWLOCK_DEFERRED_COMPLETION_PLAN.md.
#check @SeLe4n.Kernel.Concurrency.RwLockKernelStep
#check @SeLe4n.Kernel.Concurrency.RwLockReachable
#check @SeLe4n.Kernel.Concurrency.RwLockReachable_implies_wf
#check @SeLe4n.Kernel.Concurrency.RwLockExecution
#check @SeLe4n.Kernel.Concurrency.RwLockExecution.stateAt
#check @SeLe4n.Kernel.Concurrency.RwLockExecution.stateAt_reachable
#check @SeLe4n.Kernel.Concurrency.RwLockExecution.stateAt_wf
#check @SeLe4n.Kernel.Concurrency.writerWaitDepth
#check @SeLe4n.Kernel.Concurrency.writerWaitDepth_bounded
#check @SeLe4n.Kernel.Concurrency.writerWaitDepth_componentBounded
#check @SeLe4n.Kernel.Concurrency.rwLock_bounded_wait_write_distinct_weak
#check @SeLe4n.Kernel.Concurrency.tryAcquireRead_waiters_append_or_noop
#check @SeLe4n.Kernel.Concurrency.tryAcquireWrite_waiters_append_or_noop
#check @SeLe4n.Kernel.Concurrency.releaseRead_waiters_sublist
#check @SeLe4n.Kernel.Concurrency.releaseWrite_waiters_sublist
#check @SeLe4n.Kernel.Concurrency.applyOp_preserves_waiter_order
#check @SeLe4n.Kernel.Concurrency.rwLock_fifo_admission_temporal_structural
#check @SeLe4n.Kernel.Concurrency.writerWaitDepth_monotone_under_effective_release
#check @SeLe4n.Kernel.Concurrency.leave_waiters_implies_holder
#check @SeLe4n.Kernel.Concurrency.promote_prefix_inclusion
#check @SeLe4n.Kernel.Concurrency.c_in_waiters_through_admission
#check @SeLe4n.Kernel.Concurrency.rwLock_fifo_admission_temporal
#check @SeLe4n.Kernel.Concurrency.FairTrace
#check @SeLe4n.Kernel.Concurrency.MAX_RELEASE_DELAY
#check @SeLe4n.Kernel.Concurrency.writer_at_head_promoted
#check @SeLe4n.Kernel.Concurrency.reader_at_head_promoted
#check @SeLe4n.Kernel.Concurrency.ConcreteRwLockOp
#check @SeLe4n.Kernel.Concurrency.concreteApplyOp
#check @SeLe4n.Kernel.Concurrency.opCorresponds
#check @SeLe4n.Kernel.Concurrency.encodeRwLock_at_least_one_when_reader
#check @SeLe4n.Kernel.Concurrency.ListCorresponds
#check @SeLe4n.Kernel.Concurrency.rustImplementsRwLock
#check @SeLe4n.Kernel.Concurrency.concreteApplyOp_fetch_sub_no_underflow
#check @SeLe4n.Kernel.Concurrency.rwLockSim_preserved_by_direct_acquire_read
#check @SeLe4n.Kernel.Concurrency.rwLockSim_preserved_by_direct_acquire_write
#check @SeLe4n.Kernel.Concurrency.rwLockSim_preserved_by_noop_chain
-- D-3.6 strict-FIFO foundations and bound (NEW)
#check @SeLe4n.Kernel.Concurrency.writerWaitDepth_non_increase_step_queued
#check @SeLe4n.Kernel.Concurrency.writerWaitDepth_strict_decrease_under_effective_release
#check @SeLe4n.Kernel.Concurrency.queued_writer_persists_or_admitted
#check @SeLe4n.Kernel.Concurrency.rwLock_writer_liveness_existence
#check @SeLe4n.Kernel.Concurrency.rwLock_writer_liveness_count_bound
#check @SeLe4n.Kernel.Concurrency.rwLock_writer_liveness_bound_under_fairness
#check @SeLe4n.Kernel.Concurrency.queued_implies_holder_at_step
#check @SeLe4n.Kernel.Concurrency.fair_writer_release_witness
#check @SeLe4n.Kernel.Concurrency.fair_reader_release_witness
#check @SeLe4n.Kernel.Concurrency.fair_release_witness_in_window
#check @SeLe4n.Kernel.Concurrency.writerHeld_transition_implies_releaseWrite
#check @SeLe4n.Kernel.Concurrency.reader_transition_implies_releaseRead
#check @SeLe4n.Kernel.Concurrency.release_transition_implies_effective_release_at_step
#check @SeLe4n.Kernel.Concurrency.fair_progress_one_step
#check @SeLe4n.Kernel.Concurrency.rwLock_writer_liveness
#check @SeLe4n.Kernel.Concurrency.rwLock_writer_admissionStep_bounded
#check @SeLe4n.Kernel.Concurrency.FairTrace.decidable
-- D-3.2 bounded form + bridge (computable decidability)
#check @SeLe4n.Kernel.Concurrency.fairTraceReaderBody
#check @SeLe4n.Kernel.Concurrency.fairTraceWriterBody
#check @SeLe4n.Kernel.Concurrency.fairTraceBoundedProp
#check @SeLe4n.Kernel.Concurrency.fairTrace_iff_bounded
#check @SeLe4n.Kernel.Concurrency.RwLockExecution.stateAt_of_ge_length
-- D-4.9 FULL bisim main theorem + per-block discharge lemmas (NEW)
#check @SeLe4n.Kernel.Concurrency.concreteFoldBlock
#check @SeLe4n.Kernel.Concurrency.blockBisim
#check @SeLe4n.Kernel.Concurrency.ListBlockBisim
#check @SeLe4n.Kernel.Concurrency.rust_rwLock_refines_lean
#check @SeLe4n.Kernel.Concurrency.rust_rwLock_refines_lean_via_rustImplementsRwLock
#check @SeLe4n.Kernel.Concurrency.blockBisim_of_noop
#check @SeLe4n.Kernel.Concurrency.blockBisim_tryRead_success
#check @SeLe4n.Kernel.Concurrency.blockBisim_tryRead_cas_fail_chain
#check @SeLe4n.Kernel.Concurrency.blockBisim_tryRead_park_retry_chain
#check @SeLe4n.Kernel.Concurrency.blockBisim_tryWrite_success
#check @SeLe4n.Kernel.Concurrency.blockBisim_releaseRead_no_promote
#check @SeLe4n.Kernel.Concurrency.blockBisim_releaseRead_no_promote_with_sev
#check @SeLe4n.Kernel.Concurrency.blockBisim_releaseWrite_no_sev_empty_queue
#check @SeLe4n.Kernel.Concurrency.blockBisim_releaseWrite_with_sev_empty_queue
EOF'

# WS-SM SM2.D — LockBridge typed FFI wrapper + RAII combinator surface
# anchors.  Covers every public symbol exported by
# `Kernel.Concurrency.LockBridge` so a regression on the typed handle
# carriers, FFI pass-through wrappers, RAII combinators, or marker
# theorems fails the surface check.
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake build SeLe4n.Kernel.Concurrency.LockBridge'
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake env lean --stdin <<"EOF"
import SeLe4n.Kernel.Concurrency.LockBridge

-- SM2.D pool dimensions
#check @SeLe4n.Kernel.Concurrency.staticTicketLockPoolSize
#check @SeLe4n.Kernel.Concurrency.staticRwLockPoolSize
#check @SeLe4n.Kernel.Concurrency.staticTicketLockPoolSize_pos
#check @SeLe4n.Kernel.Concurrency.staticRwLockPoolSize_pos
#check @SeLe4n.Kernel.Concurrency.staticTicketLockPoolSize_eq_numCores
#check @SeLe4n.Kernel.Concurrency.staticRwLockPoolSize_eq_numCores
-- SM2.D.1 — TicketLock typed handle + smart constructor
#check @SeLe4n.Kernel.Concurrency.TicketLockHandle
#check @SeLe4n.Kernel.Concurrency.TicketLockHandle.raw
#check @SeLe4n.Kernel.Concurrency.TicketLockHandle.isValid
#check @SeLe4n.Kernel.Concurrency.mkTicketLockHandle
#check @SeLe4n.Kernel.Concurrency.mkTicketLockHandle_raw_toNat
-- SM2.D.2 — RwLock typed handle + smart constructor
#check @SeLe4n.Kernel.Concurrency.RwLockHandle
#check @SeLe4n.Kernel.Concurrency.RwLockHandle.raw
#check @SeLe4n.Kernel.Concurrency.RwLockHandle.isValid
#check @SeLe4n.Kernel.Concurrency.mkRwLockHandle
#check @SeLe4n.Kernel.Concurrency.mkRwLockHandle_raw_toNat
-- SM2.D.1 — TicketLock typed FFI wrappers
#check @SeLe4n.Kernel.Concurrency.acquireTicketLock
#check @SeLe4n.Kernel.Concurrency.releaseTicketLock
#check @SeLe4n.Kernel.Concurrency.peekTicketLockHolder
#check @SeLe4n.Kernel.Concurrency.peekTicketLockNextTicket
#check @SeLe4n.Kernel.Concurrency.peekTicketLockServing
#check @SeLe4n.Kernel.Concurrency.ticketLockAcquireCount
#check @SeLe4n.Kernel.Concurrency.ticketLockReleaseCount
-- SM2.D.2 — RwLock typed FFI wrappers
#check @SeLe4n.Kernel.Concurrency.acquireReadLock
#check @SeLe4n.Kernel.Concurrency.releaseReadLock
#check @SeLe4n.Kernel.Concurrency.acquireWriteLock
#check @SeLe4n.Kernel.Concurrency.releaseWriteLock
#check @SeLe4n.Kernel.Concurrency.snapshotRwLock
#check @SeLe4n.Kernel.Concurrency.rwLockAcquireReadCount
#check @SeLe4n.Kernel.Concurrency.rwLockReleaseReadCount
#check @SeLe4n.Kernel.Concurrency.rwLockAcquireWriteCount
#check @SeLe4n.Kernel.Concurrency.rwLockReleaseWriteCount
-- SM2.D.3 — RAII combinators
#check @SeLe4n.Kernel.Concurrency.withTicketLock
#check @SeLe4n.Kernel.Concurrency.withReadLock
#check @SeLe4n.Kernel.Concurrency.withWriteLock
-- Marker theorems
#check @SeLe4n.Kernel.Concurrency.acquireTicketLock_eq_ffi
#check @SeLe4n.Kernel.Concurrency.releaseTicketLock_eq_ffi
#check @SeLe4n.Kernel.Concurrency.peekTicketLockHolder_eq_ffi
#check @SeLe4n.Kernel.Concurrency.acquireReadLock_eq_ffi
#check @SeLe4n.Kernel.Concurrency.releaseReadLock_eq_ffi
#check @SeLe4n.Kernel.Concurrency.acquireWriteLock_eq_ffi
#check @SeLe4n.Kernel.Concurrency.releaseWriteLock_eq_ffi
#check @SeLe4n.Kernel.Concurrency.snapshotRwLock_eq_ffi
#check @SeLe4n.Kernel.Concurrency.ticketLockAcquireCount_eq_ffi
#check @SeLe4n.Kernel.Concurrency.ticketLockReleaseCount_eq_ffi
#check @SeLe4n.Kernel.Concurrency.rwLockAcquireReadCount_eq_ffi
#check @SeLe4n.Kernel.Concurrency.rwLockReleaseReadCount_eq_ffi
#check @SeLe4n.Kernel.Concurrency.rwLockAcquireWriteCount_eq_ffi
#check @SeLe4n.Kernel.Concurrency.rwLockReleaseWriteCount_eq_ffi
#check @SeLe4n.Kernel.Concurrency.withTicketLock_unfold
#check @SeLe4n.Kernel.Concurrency.withReadLock_unfold
#check @SeLe4n.Kernel.Concurrency.withWriteLock_unfold
#check @SeLe4n.Kernel.Concurrency.peekTicketLockEncoding_roundtrip_u32_masked
#check @SeLe4n.Kernel.Concurrency.peekTicketLockNextTicket_is_high32
#check @SeLe4n.Kernel.Concurrency.peekTicketLockServing_is_low32
EOF'

# WS-SM SM2.D.7 — Lock-primitive theorem aggregator surface anchors.
# Covers the 22-theorem inventory + per-category counts + Nodup
# witnesses.
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake build SeLe4n.Kernel.Concurrency.LockPrimitives'
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake env lean --stdin <<"EOF"
import SeLe4n.Kernel.Concurrency.LockPrimitives

#check @SeLe4n.Kernel.Concurrency.LockPrimitiveCategory
#check @SeLe4n.Kernel.Concurrency.LockPrimitiveCategory.memoryModel
#check @SeLe4n.Kernel.Concurrency.LockPrimitiveCategory.ticketLock
#check @SeLe4n.Kernel.Concurrency.LockPrimitiveCategory.rwLock
#check @SeLe4n.Kernel.Concurrency.LockPrimitiveCategory.refinement
#check @SeLe4n.Kernel.Concurrency.LockPrimitiveTheorem
#check @SeLe4n.Kernel.Concurrency.LockPrimitiveTheorem.description
#check @SeLe4n.Kernel.Concurrency.LockPrimitiveTheorem.identifier
#check @SeLe4n.Kernel.Concurrency.LockPrimitiveTheorem.category
#check @SeLe4n.Kernel.Concurrency.lockPrimitives
#check @SeLe4n.Kernel.Concurrency.lockPrimitives_count
#check @SeLe4n.Kernel.Concurrency.lockPrimitives_memoryModel_count
#check @SeLe4n.Kernel.Concurrency.lockPrimitives_ticketLock_count
#check @SeLe4n.Kernel.Concurrency.lockPrimitives_rwLock_count
#check @SeLe4n.Kernel.Concurrency.lockPrimitives_refinement_count
#check @SeLe4n.Kernel.Concurrency.lockPrimitives_partition_sum
#check @SeLe4n.Kernel.Concurrency.lockPrimitives_identifiers_nodup
#check @SeLe4n.Kernel.Concurrency.lockPrimitives_descriptions_nodup
EOF'

# WS-SM SM2.D TicketLockRefinement (F-01 refinement bridge anchor).
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake build SeLe4n.Kernel.Concurrency.Locks.TicketLockRefinement'
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake env lean --stdin <<"EOF"
import SeLe4n.Kernel.Concurrency.Locks.TicketLockRefinement

#check @SeLe4n.Kernel.Concurrency.TicketLockConcrete
#check @SeLe4n.Kernel.Concurrency.TicketLockConcrete.nextTicket
#check @SeLe4n.Kernel.Concurrency.TicketLockConcrete.serving
#check @SeLe4n.Kernel.Concurrency.TicketLockConcrete.unheld
#check @SeLe4n.Kernel.Concurrency.ticketLockSim
#check @SeLe4n.Kernel.Concurrency.ticketLockSim_unheld
#check @SeLe4n.Kernel.Concurrency.ticketLockSim_preserved_by_tryAcquire
#check @SeLe4n.Kernel.Concurrency.ticketLockSim_preserved_by_release
#check @SeLe4n.Kernel.Concurrency.ticketLockSim_preserved_by_observeServing
#check @SeLe4n.Kernel.Concurrency.rust_ticketLock_refines_lean
EOF'

# WS-SM SM2.D — Lean-side FFI declarations.  Covers every SM2.D
# @[extern] declaration in Platform/FFI.lean so a regression that
# removed a declaration without updating the cross-language
# symmetry script fails here first.
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake build SeLe4n.Platform.FFI'
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake env lean --stdin <<"EOF"
import SeLe4n.Platform.FFI

#check @SeLe4n.Platform.FFI.ffiTicketLockStaticHandle
#check @SeLe4n.Platform.FFI.ffiTicketLockAcquire
#check @SeLe4n.Platform.FFI.ffiTicketLockRelease
#check @SeLe4n.Platform.FFI.ffiTicketLockPeekHolder
#check @SeLe4n.Platform.FFI.ffiTicketLockAcquireCount
#check @SeLe4n.Platform.FFI.ffiTicketLockReleaseCount
#check @SeLe4n.Platform.FFI.ffiRwLockStaticHandle
#check @SeLe4n.Platform.FFI.ffiRwLockAcquireRead
#check @SeLe4n.Platform.FFI.ffiRwLockReleaseRead
#check @SeLe4n.Platform.FFI.ffiRwLockAcquireWrite
#check @SeLe4n.Platform.FFI.ffiRwLockReleaseWrite
#check @SeLe4n.Platform.FFI.ffiRwLockSnapshot
#check @SeLe4n.Platform.FFI.ffiRwLockAcquireReadCount
#check @SeLe4n.Platform.FFI.ffiRwLockReleaseReadCount
#check @SeLe4n.Platform.FFI.ffiRwLockAcquireWriteCount
#check @SeLe4n.Platform.FFI.ffiRwLockReleaseWriteCount
EOF'

# WS-SM SM3.A — Per-object lock field surface anchors.  Every per-object
# `lock : RwLockState` field plus the SM3.A.10 `objectLockOf` projection
# and its per-variant unfold lemmas plus the SM3.A.11 default-state
# theorems.  A regression that renames the field (e.g., `lock` →
# `rwLock`) fails this surface check at the lean-build step.
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake build SeLe4n.Model.Object SeLe4n.Model.State SeLe4n.Model.FrozenState SeLe4n.Kernel.SchedContext.Types'
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake env lean --stdin <<"EOF"
import SeLe4n.Model.State
import SeLe4n.Model.FrozenState

-- SM3.A.1..A.9 — per-object lock fields on every kernel-object struct.
#check @SeLe4n.Model.TCB.lock
#check @SeLe4n.Model.Endpoint.lock
#check @SeLe4n.Model.CNode.lock
#check @SeLe4n.Model.Notification.lock
#check @SeLe4n.Model.UntypedObject.lock
#check @SeLe4n.Kernel.SchedContext.lock
#check @SeLe4n.Model.VSpaceRoot.lock
-- SM3.A.1 — TCB.ext extended with hLock conjunct (per-field witness form).
#check @SeLe4n.Model.TCB.ext
-- SM3.A.10 — KernelObject.objectLockOf projection + per-variant simp lemmas.
#check @SeLe4n.Model.KernelObject.objectLockOf
#check @SeLe4n.Model.KernelObject.objectLockOf_tcb
#check @SeLe4n.Model.KernelObject.objectLockOf_endpoint
#check @SeLe4n.Model.KernelObject.objectLockOf_notification
#check @SeLe4n.Model.KernelObject.objectLockOf_cnode
#check @SeLe4n.Model.KernelObject.objectLockOf_vspaceRoot
#check @SeLe4n.Model.KernelObject.objectLockOf_untyped
#check @SeLe4n.Model.KernelObject.objectLockOf_schedContext
-- SM3.A.10 — SystemState ObjStore table-level lock.
#check @SeLe4n.Model.SystemState.objStoreLock
-- SM3.A.10 — FrozenState lock-field forwarding (frozen mirror of SM3.A.3/A.7/A.10).
#check @SeLe4n.Model.FrozenCNode.lock
#check @SeLe4n.Model.FrozenVSpaceRoot.lock
#check @SeLe4n.Model.FrozenSystemState.objStoreLock
-- SM3.A.10 audit-pass-2 — FrozenKernelObject.objectLockOf symmetry projection.
#check @SeLe4n.Model.FrozenKernelObject.objectLockOf
#check @SeLe4n.Model.FrozenKernelObject.objectLockOf_tcb
#check @SeLe4n.Model.FrozenKernelObject.objectLockOf_endpoint
#check @SeLe4n.Model.FrozenKernelObject.objectLockOf_notification
#check @SeLe4n.Model.FrozenKernelObject.objectLockOf_cnode
#check @SeLe4n.Model.FrozenKernelObject.objectLockOf_vspaceRoot
#check @SeLe4n.Model.FrozenKernelObject.objectLockOf_untyped
#check @SeLe4n.Model.FrozenKernelObject.objectLockOf_schedContext
-- SM3.A.10 audit-pass-2 — freeze*_preserves_lock witness theorems.
#check @SeLe4n.Model.freeze_preserves_objStoreLock
#check @SeLe4n.Model.freezeCNode_preserves_lock
#check @SeLe4n.Model.freezeVSpaceRoot_preserves_lock
#check @SeLe4n.Model.freezeObject_preserves_objectLockOf
-- SM3.A.11 — default-state lock theorems.
#check @SeLe4n.Model.default_objStoreLock_unheld
#check @SeLe4n.Model.default_objects_locks_unheld
#check @SeLe4n.Model.default_objects_toList_empty
#check @SeLe4n.Model.default_objects_locks_unheld_via_toList
EOF'

# WS-SM SM3.A audit-pass-5 — non-vacuous SM3.A.11 + preservation
# theorems + consistency theorems + inventory aggregator surface.
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake build SeLe4n.Model.Object.PerObjectLockInventory'
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake env lean --stdin <<"EOF"
import SeLe4n.Model.State
import SeLe4n.Model.FrozenState
import SeLe4n.Model.Object.PerObjectLockInventory

-- Non-vacuous SM3.A.11 + preservation theorems.
#check @SeLe4n.Model.SystemState.allObjectLocksUnheld
#check @SeLe4n.Model.SystemState.allObjectLocksUnheldB
#check @SeLe4n.Model.default_allObjectLocksUnheld
#check @SeLe4n.Model.allObjectLocksUnheld_of_pointwise
#check @SeLe4n.Model.storeObject_preserves_objStoreLock
#check @SeLe4n.Model.storeObject_preserves_objectLockOf_off_target
#check @SeLe4n.Model.storeObject_inserted_object_lookup
#check @SeLe4n.Model.storeObject_preserves_allObjectLocksUnheld
-- Consistency theorems.
#check @SeLe4n.Model.KernelObject.objectLockOf_exists
#check @SeLe4n.Model.KernelObject.objectType_and_lockOf_total
#check @SeLe4n.Model.KernelObject.objectLockOf_consistent_with_type
#check @SeLe4n.Model.KernelObjectType.variants_count_exactly_seven
#check @SeLe4n.Model.KernelObjectType.variants_total
-- Inventory aggregator.
#check @SeLe4n.Model.PerObjectLockCategory
#check @SeLe4n.Model.PerObjectLockTheorem
#check @SeLe4n.Model.perObjectLockTheorems
#check @SeLe4n.Model.perObjectLockTheorems_count
#check @SeLe4n.Model.perObjectLockTheorems_fieldDefault_count
#check @SeLe4n.Model.perObjectLockTheorems_projection_count
#check @SeLe4n.Model.perObjectLockTheorems_defaultState_count
#check @SeLe4n.Model.perObjectLockTheorems_preservation_count
#check @SeLe4n.Model.perObjectLockTheorems_consistency_count
#check @SeLe4n.Model.perObjectLockTheorems_partition_sum
#check @SeLe4n.Model.perObjectLockTheorems_identifiers_nodup
#check @SeLe4n.Model.perObjectLockTheorems_descriptions_nodup
-- RwLockState.default equivalence.
#check @SeLe4n.Kernel.Concurrency.RwLockState.default_eq_unheld
EOF'

# WS-SM SM3.A audit-pass-6 — toList ↔ get? bridge theorems +
# allObjectLocksUnheld Prop↔Bool equivalence under invExt.  These
# close the audit-pass-5 dead-link docstring reference.
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake build SeLe4n.Model.FreezeProofs'
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake env lean --stdin <<"EOF"
import SeLe4n.Model.FreezeProofs

#check @SeLe4n.Model.get_some_of_toList_contains
#check @SeLe4n.Model.toList_all_iff_forall_get_some
#check @SeLe4n.Model.allObjectLocksUnheld_iff_via_toList
EOF'

# WS-SM SM3.B — LockSet + LockIdProjection + LockSetTransitions +
# LockSetInventory.  Surface anchors for every public SM3.B symbol:
#   * LockSet structure + canonical sort + ordered/complete/canonical
#     theorems (SM3.B.5/B.6/B.7/B.8)
#   * KernelObject.lockKind, LockId.fromObject, LockId.lookup +
#     round-trip theorems (SM3.B.1/B.2)
#   * Per-transition lockSet_<τ> declarations (SM3.B.3, 25 transitions)
#   * permittedKinds + per-transition lockSet_consistent_<τ> theorems
#     (SM3.B.4, 25 transitions)
#   * 72-theorem inventory aggregator + per-category count witnesses
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake build SeLe4n.Kernel.Concurrency.LockSet'
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake env lean --stdin <<"EOF"
import SeLe4n.Kernel.Concurrency.LockSet

-- SM3.B.1: KernelObject.lockKind + per-variant simp lemmas.
#check @SeLe4n.Model.KernelObject.lockKind
#check @SeLe4n.Model.KernelObject.lockKind_tcb
#check @SeLe4n.Model.KernelObject.lockKind_endpoint
#check @SeLe4n.Model.KernelObject.lockKind_notification
#check @SeLe4n.Model.KernelObject.lockKind_cnode
#check @SeLe4n.Model.KernelObject.lockKind_vspaceRoot
#check @SeLe4n.Model.KernelObject.lockKind_untyped
#check @SeLe4n.Model.KernelObject.lockKind_schedContext
#check @SeLe4n.Model.KernelObject.lockKind_exists
#check @SeLe4n.Model.KernelObject.lockKind_eq_of_objectType
-- SM3.B.1: LockId.fromObject + per-variant simp lemmas.
#check @SeLe4n.Model.LockId.fromObject
#check @SeLe4n.Model.LockId.fromObject_kind
#check @SeLe4n.Model.LockId.fromObject_objId
#check @SeLe4n.Model.LockId.fromObject_tcb
#check @SeLe4n.Model.LockId.fromObject_endpoint
#check @SeLe4n.Model.LockId.fromObject_notification
#check @SeLe4n.Model.LockId.fromObject_cnode
#check @SeLe4n.Model.LockId.fromObject_vspaceRoot
#check @SeLe4n.Model.LockId.fromObject_untyped
#check @SeLe4n.Model.LockId.fromObject_schedContext
-- SM3.B.2: LockId.lookup + structural theorems.
#check @SeLe4n.Model.LockId.lookup
#check @SeLe4n.Model.LockId.lookup_some_of_kindMatch
#check @SeLe4n.Model.LockId.lookup_fromObject_of_present
#check @SeLe4n.Model.LockId.lookup_objStore
#check @SeLe4n.Model.LockId.lookup_reply
#check @SeLe4n.Model.LockId.lookup_page
#check @SeLe4n.Model.LockId.lookup_kindMatch
#check @SeLe4n.Model.LockId.lookup_lockState_eq
-- SM3.B.5..B.8: LockSet structure + canonical sort + theorems.
#check @SeLe4n.Kernel.Concurrency.LockSet
#check @SeLe4n.Kernel.Concurrency.LockSet.empty
#check @SeLe4n.Kernel.Concurrency.LockSet.singleton
#check @SeLe4n.Kernel.Concurrency.LockSet.insert?
#check @SeLe4n.Kernel.Concurrency.LockSet.insertOrMerge
#check @SeLe4n.Kernel.Concurrency.LockSet.union
#check @SeLe4n.Kernel.Concurrency.LockSet.containsKey
#check @SeLe4n.Kernel.Concurrency.LockSet.size
#check @SeLe4n.Kernel.Concurrency.LockSet.lockAcquireSequence
#check @SeLe4n.Kernel.Concurrency.LockSet.lockAcquireSequence_ordered
#check @SeLe4n.Kernel.Concurrency.LockSet.lockAcquireSequence_complete
#check @SeLe4n.Kernel.Concurrency.LockSet.lockAcquireSequence_canonical
#check @SeLe4n.Kernel.Concurrency.LockSet.lockAcquireSequence_length
#check @SeLe4n.Kernel.Concurrency.LockSet.lockAcquireSequence_perm
#check @SeLe4n.Kernel.Concurrency.LockSet.fst_inj_at_pairs
#check @SeLe4n.Kernel.Concurrency.LockSet.insertOrMerge_mem
-- SM3.B AccessMode algebra.
#check @SeLe4n.Kernel.Concurrency.AccessMode.lub
#check @SeLe4n.Kernel.Concurrency.AccessMode.lub_idem
#check @SeLe4n.Kernel.Concurrency.AccessMode.lub_comm
#check @SeLe4n.Kernel.Concurrency.AccessMode.lub_assoc
#check @SeLe4n.Kernel.Concurrency.AccessMode.conflicts
#check @SeLe4n.Kernel.Concurrency.AccessMode.conflicts_symm
-- SM3.B LockSet structural helpers (audit-pass-1 additions).
#check @SeLe4n.Kernel.Concurrency.LockSet.union_mem_inv
#check @SeLe4n.Kernel.Concurrency.LockSet.union_empty
#check @SeLe4n.Kernel.Concurrency.LockSet.containsKey_iff
#check @SeLe4n.Kernel.Concurrency.LockSet.empty_pairs
#check @SeLe4n.Kernel.Concurrency.LockSet.singleton_pairs
-- SM3.B.3: Per-transition lockSet declarations.
#check @SeLe4n.Kernel.Concurrency.lockSet_endpointSend
#check @SeLe4n.Kernel.Concurrency.lockSet_endpointReceive
#check @SeLe4n.Kernel.Concurrency.lockSet_endpointCall
#check @SeLe4n.Kernel.Concurrency.lockSet_endpointReply
#check @SeLe4n.Kernel.Concurrency.lockSet_replyRecv
#check @SeLe4n.Kernel.Concurrency.lockSet_notificationSignal
#check @SeLe4n.Kernel.Concurrency.lockSet_notificationWait
#check @SeLe4n.Kernel.Concurrency.lockSet_cspaceMint
#check @SeLe4n.Kernel.Concurrency.lockSet_cspaceCopy
#check @SeLe4n.Kernel.Concurrency.lockSet_cspaceMove
#check @SeLe4n.Kernel.Concurrency.lockSet_cspaceDelete
#check @SeLe4n.Kernel.Concurrency.lockSet_lifecycleRetype
#check @SeLe4n.Kernel.Concurrency.lockSet_vspaceMap
#check @SeLe4n.Kernel.Concurrency.lockSet_vspaceUnmap
#check @SeLe4n.Kernel.Concurrency.lockSet_serviceRegister
#check @SeLe4n.Kernel.Concurrency.lockSet_serviceRevoke
#check @SeLe4n.Kernel.Concurrency.lockSet_serviceQuery
#check @SeLe4n.Kernel.Concurrency.lockSet_schedContextConfigure
#check @SeLe4n.Kernel.Concurrency.lockSet_schedContextBind
#check @SeLe4n.Kernel.Concurrency.lockSet_schedContextUnbind
#check @SeLe4n.Kernel.Concurrency.lockSet_tcbSuspend
#check @SeLe4n.Kernel.Concurrency.lockSet_tcbResume
#check @SeLe4n.Kernel.Concurrency.lockSet_tcbSetPriority
#check @SeLe4n.Kernel.Concurrency.lockSet_tcbSetMCPriority
#check @SeLe4n.Kernel.Concurrency.lockSet_tcbSetIPCBuffer
-- SM3.B.4: permittedKinds + per-transition lockSet_consistent_*.
#check @SeLe4n.Kernel.Concurrency.permittedKinds
#check @SeLe4n.Kernel.Concurrency.lockSet_consistent_send
#check @SeLe4n.Kernel.Concurrency.lockSet_consistent_receive
#check @SeLe4n.Kernel.Concurrency.lockSet_consistent_call
#check @SeLe4n.Kernel.Concurrency.lockSet_consistent_reply
#check @SeLe4n.Kernel.Concurrency.lockSet_consistent_replyRecv
#check @SeLe4n.Kernel.Concurrency.lockSet_consistent_notificationSignal
#check @SeLe4n.Kernel.Concurrency.lockSet_consistent_notificationWait
#check @SeLe4n.Kernel.Concurrency.lockSet_consistent_cspaceMint
#check @SeLe4n.Kernel.Concurrency.lockSet_consistent_cspaceCopy
#check @SeLe4n.Kernel.Concurrency.lockSet_consistent_cspaceMove
#check @SeLe4n.Kernel.Concurrency.lockSet_consistent_cspaceDelete
#check @SeLe4n.Kernel.Concurrency.lockSet_consistent_lifecycleRetype
#check @SeLe4n.Kernel.Concurrency.lockSet_consistent_vspaceMap
#check @SeLe4n.Kernel.Concurrency.lockSet_consistent_vspaceUnmap
#check @SeLe4n.Kernel.Concurrency.lockSet_consistent_serviceRegister
#check @SeLe4n.Kernel.Concurrency.lockSet_consistent_serviceRevoke
#check @SeLe4n.Kernel.Concurrency.lockSet_consistent_serviceQuery
#check @SeLe4n.Kernel.Concurrency.lockSet_consistent_schedContextConfigure
#check @SeLe4n.Kernel.Concurrency.lockSet_consistent_schedContextBind
#check @SeLe4n.Kernel.Concurrency.lockSet_consistent_schedContextUnbind
#check @SeLe4n.Kernel.Concurrency.lockSet_consistent_tcbSuspend
#check @SeLe4n.Kernel.Concurrency.lockSet_consistent_tcbResume
#check @SeLe4n.Kernel.Concurrency.lockSet_consistent_tcbSetPriority
#check @SeLe4n.Kernel.Concurrency.lockSet_consistent_tcbSetMCPriority
#check @SeLe4n.Kernel.Concurrency.lockSet_consistent_tcbSetIPCBuffer
-- SM3.B.3 audit-pass-5 — PIP-chain-walk start markers.
#check @SeLe4n.Kernel.Concurrency.pipChainStart_endpointCall
#check @SeLe4n.Kernel.Concurrency.pipChainStart_endpointReply
#check @SeLe4n.Kernel.Concurrency.pipChainStart_replyRecv
-- SM3.B Inventory aggregator.
#check @SeLe4n.Kernel.Concurrency.LockSetCategory
#check @SeLe4n.Kernel.Concurrency.LockSetTheorem
#check @SeLe4n.Kernel.Concurrency.lockSetTheorems
#check @SeLe4n.Kernel.Concurrency.lockSetTheorems_count
#check @SeLe4n.Kernel.Concurrency.lockSetTheorems_projection_count
#check @SeLe4n.Kernel.Concurrency.lockSetTheorems_lockSet_count
#check @SeLe4n.Kernel.Concurrency.lockSetTheorems_consistency_count
#check @SeLe4n.Kernel.Concurrency.lockSetTheorems_acquireSort_count
#check @SeLe4n.Kernel.Concurrency.lockSetTheorems_algebra_count
#check @SeLe4n.Kernel.Concurrency.lockSetTheorems_chainStart_count
#check @SeLe4n.Kernel.Concurrency.lockSetTheorems_partition_sum
#check @SeLe4n.Kernel.Concurrency.lockSetTheorems_identifiers_nodup
#check @SeLe4n.Kernel.Concurrency.lockSetTheorems_descriptions_nodup
#check @SeLe4n.Kernel.Concurrency.lockSet_consistent_aggregate_covers_every_syscall
EOF'

# WS-SM SM3.C — withLockSet 2PL discipline + lockSetHeld + dynamic
# chain extension + 51-theorem inventory.  Surface anchors verify
# every SM3.C public symbol survives renames at elaboration time.
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake build SeLe4n.Kernel.Concurrency.Locks.Sm3CInventory'
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake env lean --stdin <<"EOF"
import SeLe4n.Kernel.Concurrency.LockSet
import SeLe4n.Kernel.Concurrency.Locks.WithLockSet
import SeLe4n.Kernel.Concurrency.Locks.LockSetHeld
import SeLe4n.Kernel.Concurrency.Locks.LockSet2PL
import SeLe4n.Kernel.Concurrency.Locks.DynamicChainExtension
import SeLe4n.Kernel.Concurrency.Locks.Sm3CInventory

-- SM3.C.1: withLockSet combinator + unfolding lemmas.
#check @SeLe4n.Kernel.Concurrency.withLockSet
#check @SeLe4n.Kernel.Concurrency.withLockSet_empty
#check @SeLe4n.Kernel.Concurrency.withLockSet_unfold
#check @SeLe4n.Kernel.Concurrency.withLockSet_eq_decomposition
#check @SeLe4n.Kernel.Concurrency.withLockSet_fst
#check @SeLe4n.Kernel.Concurrency.withLockSet_snd
-- SM3.C.2: acquireLockOnObject / releaseLockOnObject + N/A simp lemmas.
#check @SeLe4n.Kernel.Concurrency.acquireLockOnObject
#check @SeLe4n.Kernel.Concurrency.releaseLockOnObject
#check @SeLe4n.Kernel.Concurrency.acquireLockOnObject_reply
#check @SeLe4n.Kernel.Concurrency.acquireLockOnObject_page
#check @SeLe4n.Kernel.Concurrency.releaseLockOnObject_reply
#check @SeLe4n.Kernel.Concurrency.releaseLockOnObject_page
-- SM3.C.1 helpers: AccessMode → RwLockOp + acquireAll/releaseAll.
#check @SeLe4n.Kernel.Concurrency.AccessMode.toAcquireOp
#check @SeLe4n.Kernel.Concurrency.AccessMode.toReleaseOp
#check @SeLe4n.Kernel.Concurrency.acquireAll
#check @SeLe4n.Kernel.Concurrency.releaseAll
#check @SeLe4n.Kernel.Concurrency.acquireAll_nil
#check @SeLe4n.Kernel.Concurrency.releaseAll_nil
#check @SeLe4n.Kernel.Concurrency.acquireAll_cons
#check @SeLe4n.Kernel.Concurrency.releaseAll_cons
#check @SeLe4n.Kernel.Concurrency.updateObjectAt
-- SM3.C.2 audit-pass-1 (Comment 5): kind-checked lock update.
#check @SeLe4n.Kernel.Concurrency.updateObjectLockAt
#check @SeLe4n.Kernel.Concurrency.updateObjectLockAt_preserves_objStoreLock
-- SM3.C.2 KernelObject.updateLock helper.
#check @SeLe4n.Model.KernelObject.updateLock
#check @SeLe4n.Model.KernelObject.updateLock_tcb
#check @SeLe4n.Model.KernelObject.updateLock_endpoint
#check @SeLe4n.Model.KernelObject.updateLock_notification
#check @SeLe4n.Model.KernelObject.updateLock_cnode
#check @SeLe4n.Model.KernelObject.updateLock_vspaceRoot
#check @SeLe4n.Model.KernelObject.updateLock_untyped
#check @SeLe4n.Model.KernelObject.updateLock_schedContext
#check @SeLe4n.Model.KernelObject.updateLock_preserves_lockKind
#check @SeLe4n.Model.KernelObject.updateLock_preserves_objectType
#check @SeLe4n.Model.KernelObject.objectLockOf_updateLock
#check @SeLe4n.Kernel.Concurrency.updateObjectAt_preserves_objStoreLock
#check @SeLe4n.Kernel.Concurrency.acquireLockOnObject_preserves_objStoreLock_of_modeled
#check @SeLe4n.Kernel.Concurrency.releaseLockOnObject_preserves_objStoreLock_of_modeled
#check @SeLe4n.Kernel.Concurrency.updateObjectAt_preserves_objectType_at
-- SM3.C.4 lockHeld / lockSetHeld + decidability + default-state-empty.
#check @SeLe4n.Kernel.Concurrency.RwLockState.coreHolds
-- SM3.C.4 audit-pass-1 (Comments 3, 4): abstract acquire grants on available lock.
#check @SeLe4n.Kernel.Concurrency.RwLockState.unheld_acquire_grants
#check @SeLe4n.Kernel.Concurrency.RwLockState.unheld_acquire_release_roundtrip
#check @SeLe4n.Kernel.Concurrency.lockHeld
#check @SeLe4n.Kernel.Concurrency.lockSetHeld
#check @SeLe4n.Kernel.Concurrency.lockHeld_reply
#check @SeLe4n.Kernel.Concurrency.lockHeld_page
#check @SeLe4n.Kernel.Concurrency.lockSetHeld_empty
#check @SeLe4n.Kernel.Concurrency.lockSetHeld_singleton
#check @SeLe4n.Kernel.Concurrency.lockSetHeld_subset
#check @SeLe4n.Kernel.Concurrency.lockSetHeld_default_iff_empty
-- SM3.C.5/C.6 ordering theorems.
#check @SeLe4n.Kernel.Concurrency.acquireOrder
#check @SeLe4n.Kernel.Concurrency.releaseOrder
#check @SeLe4n.Kernel.Concurrency.releaseOrder_eq_acquireOrder_reverse
#check @SeLe4n.Kernel.Concurrency.lockSet_acquired_in_order
#check @SeLe4n.Kernel.Concurrency.lockSet_released_in_reverse
-- SM3.C.7/C.8 atomicity/invariant-preservation theorems.
#check @SeLe4n.Kernel.Concurrency.withLockSet_three_phase_decomposition
#check @SeLe4n.Kernel.Concurrency.lockSet_atomic_under_2pl
#check @SeLe4n.Kernel.Concurrency.lockSet_invariant_preserved
#check @SeLe4n.Kernel.Concurrency.withLockSet_invariant_preserved
#check @SeLe4n.Kernel.Concurrency.acquireAll_preserves_objStoreLock_wf
-- SM3.C.8 audit-pass-1 (Comment 7): substantive acquire-grants theorems.
#check @SeLe4n.Kernel.Concurrency.acquireLockOnObject_objStore_establishes_lockHeld
#check @SeLe4n.Kernel.Concurrency.acquireLockOnObject_objStore_release_roundtrip
#check @SeLe4n.Kernel.Concurrency.withLockSet_satisfies_strict_2PL
#check @SeLe4n.Kernel.Concurrency.withLockSet_computation
-- SM3.C.8 (Group-B): acquire ESTABLISHES lockHeld / lockSetHeld + frames.
#check @SeLe4n.Kernel.Concurrency.LockId.lookup_eq_of_objects_getElem?_eq
#check @SeLe4n.Kernel.Concurrency.updateObjectLockAt_lookup_self
#check @SeLe4n.Kernel.Concurrency.acquireLockOnObject_establishes_lockHeld_modeled
#check @SeLe4n.Kernel.Concurrency.acquireLockOnObject_preserves_lockHeld_of_ne_objId
#check @SeLe4n.Kernel.Concurrency.acquireAll_preserves_lockHeld_of_ne_all
#check @SeLe4n.Kernel.Concurrency.acquireAll_establishes_lockHeld_of_distinct_present_unheld
#check @SeLe4n.Kernel.Concurrency.acquireAll_establishes_lockSetHeld
#check @SeLe4n.Kernel.Concurrency.lockAcquireSequence_distinct_objId_of_resolves
-- SM3.C.7 (Group-B): observational atomicity (lock-insensitive observer).
#check @SeLe4n.Kernel.Concurrency.AcquireInsensitive
#check @SeLe4n.Kernel.Concurrency.ReleaseInsensitive
#check @SeLe4n.Kernel.Concurrency.acquireAll_lockInsensitive
#check @SeLe4n.Kernel.Concurrency.releaseAll_lockInsensitive
#check @SeLe4n.Kernel.Concurrency.withLockSet_release_invisible
#check @SeLe4n.Kernel.Concurrency.lockSet_observer_atomic
-- SM3.C.11 dynamic chain walker + deadlock-freedom witness.
#check @SeLe4n.Kernel.Concurrency.MAX_PIP_RETRIES
#check @SeLe4n.Kernel.Concurrency.MAX_PIP_RETRIES_pos
#check @SeLe4n.Kernel.Concurrency.PipChainPath
#check @SeLe4n.Kernel.Concurrency.PipChainPath.singleton
#check @SeLe4n.Kernel.Concurrency.PipChainPath.length
#check @SeLe4n.Kernel.Concurrency.WalkOutcome
#check @SeLe4n.Kernel.Concurrency.walkStep
#check @SeLe4n.Kernel.Concurrency.walkAndAcquire
#check @SeLe4n.Kernel.Concurrency.withDynamicChainExtension
#check @SeLe4n.Kernel.Concurrency.withDynamicChainExtension_unfold
#check @SeLe4n.Kernel.Concurrency.dynamicChainHeld
#check @SeLe4n.Kernel.Concurrency.chainFollowsBlockingServer
#check @SeLe4n.Kernel.Concurrency.walkStep_extended_increases_objId
#check @SeLe4n.Kernel.Concurrency.walkStep_extended_blockingServer
#check @SeLe4n.Kernel.Concurrency.walkAndAcquire_path_ascending_in_ObjId_if_terminated
#check @SeLe4n.Kernel.Concurrency.walkAndAcquire_terminated_followsChain
#check @SeLe4n.Kernel.Concurrency.walkAndAcquire_terminated_satisfies_path_structure
#check @SeLe4n.Kernel.Concurrency.walkAndAcquireAux_terminated_length_le
#check @SeLe4n.Kernel.Concurrency.walkAndAcquire_terminated_length_bounded
#check @SeLe4n.Kernel.Concurrency.walkAndAcquire_total
-- SM3.C.11.c (Group-B): conjunct-1 establishment + blockingServer transport + capstone.
#check @SeLe4n.Kernel.Concurrency.chainLockSeq
#check @SeLe4n.Kernel.Concurrency.chainLockSeq_acquire_establishes_pathHeld
#check @SeLe4n.Kernel.Concurrency.blockingServer_eq_bind
#check @SeLe4n.Kernel.Concurrency.tcbReplyServer_updateLock
#check @SeLe4n.Kernel.Concurrency.acquireLockOnObject_preserves_blockingServer
#check @SeLe4n.Kernel.Concurrency.acquireAll_preserves_blockingServer
#check @SeLe4n.Kernel.Concurrency.chainFollowsBlockingServer_of_blockingServer_eq
#check @SeLe4n.Kernel.Concurrency.withDynamicChainExtension_establishes_dynamicChainHeld
-- SM3.C.11.d (Group-B): two-core deadlock-freedom.
#check @SeLe4n.Kernel.Concurrency.coreWaitsForLock
#check @SeLe4n.Kernel.Concurrency.dynamic_chain_deadlock_free
#check @SeLe4n.Kernel.Concurrency.dynamic_chain_no_mutual_wait
-- SM3.C Inventory aggregator.
#check @SeLe4n.Kernel.Concurrency.WithLockSetCategory
#check @SeLe4n.Kernel.Concurrency.WithLockSetTheorem
#check @SeLe4n.Kernel.Concurrency.withLockSetTheorems
#check @SeLe4n.Kernel.Concurrency.withLockSetTheorems_count
#check @SeLe4n.Kernel.Concurrency.withLockSetTheorems_combinator_count
#check @SeLe4n.Kernel.Concurrency.withLockSetTheorems_held_count
#check @SeLe4n.Kernel.Concurrency.withLockSetTheorems_ordering_count
#check @SeLe4n.Kernel.Concurrency.withLockSetTheorems_atomicity_count
#check @SeLe4n.Kernel.Concurrency.withLockSetTheorems_dynamicChain_count
#check @SeLe4n.Kernel.Concurrency.withLockSetTheorems_partition_sum
#check @SeLe4n.Kernel.Concurrency.withLockSetTheorems_identifiers_nodup
#check @SeLe4n.Kernel.Concurrency.withLockSetTheorems_descriptions_nodup
EOF'

# WS-SM SM3.D — deadlock-freedom + wait-graph acyclicity + bounded-wait +
# 37-theorem inventory.  Surface anchors verify every SM3.D public symbol
# survives renames at elaboration time.
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake build SeLe4n.Kernel.Concurrency.Locks.Sm3DInventory'
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake env lean --stdin <<"EOF"
import SeLe4n.Kernel.Concurrency.LockSet
import SeLe4n.Kernel.Concurrency.Locks.Deadlock
import SeLe4n.Kernel.Concurrency.Locks.Sm3DInventory

-- SM3.D.1: KernelExecution model + blockedAt / heldBy.
#check @SeLe4n.Kernel.Concurrency.KernelExecution
#check @SeLe4n.Kernel.Concurrency.blockedAt
#check @SeLe4n.Kernel.Concurrency.heldBy
-- SM3.D.4: hypotheses (per-core + execution-level) + ladder invariant.
#check @SeLe4n.Kernel.Concurrency.coreFollows2PL
#check @SeLe4n.Kernel.Concurrency.coreAcquiresInOrder
#check @SeLe4n.Kernel.Concurrency.executionFollows2PL
#check @SeLe4n.Kernel.Concurrency.executionAcquiresInLockIdOrder
#check @SeLe4n.Kernel.Concurrency.ladder_of_2pl_and_order
-- SM3.D.3: lockOrder_strict.
#check @SeLe4n.Kernel.Concurrency.lockOrder_strict
-- SM3.D.1 / SM3.D.4: noDeadlock + decidability + Theorem 2.1.9.
#check @SeLe4n.Kernel.Concurrency.noDeadlock
#check @SeLe4n.Kernel.Concurrency.mutualBlocked
#check @SeLe4n.Kernel.Concurrency.noDeadlockDec
#check @SeLe4n.Kernel.Concurrency.noDeadlock_iff_dec
#check @SeLe4n.Kernel.Concurrency.noDeadlock_definition_decidable
#check @SeLe4n.Kernel.Concurrency.deadlockFreedom_under_2pl_and_ordering
-- SM3.D.5: wait-graph acyclicity.
#check @SeLe4n.Kernel.Concurrency.waitsForCore
#check @SeLe4n.Kernel.Concurrency.blockedWaitsFor
#check @SeLe4n.Kernel.Concurrency.ReachesPlus
#check @SeLe4n.Kernel.Concurrency.Acyclic
#check @SeLe4n.Kernel.Concurrency.waitGraph
#check @SeLe4n.Kernel.Concurrency.blockedWaitsFor_wanted_lt
#check @SeLe4n.Kernel.Concurrency.reachesPlus_wanted_lt
#check @SeLe4n.Kernel.Concurrency.waitGraph_acyclic_under_2pl
#check @SeLe4n.Kernel.Concurrency.noDeadlock_of_waitGraph_acyclic
-- SM3.D.3 audit-pass: Irreflexive / Transitive (plan form).
#check @SeLe4n.Kernel.Concurrency.Irreflexive
#check @SeLe4n.Kernel.Concurrency.Transitive
#check @SeLe4n.Kernel.Concurrency.lockOrder_strict_classes
-- SM3.D.5b audit-pass: mode-aware (conflict) wait graph.
#check @SeLe4n.Kernel.Concurrency.ReachesPlus_mono
#check @SeLe4n.Kernel.Concurrency.Acyclic_mono
#check @SeLe4n.Kernel.Concurrency.conflictWaitsFor
#check @SeLe4n.Kernel.Concurrency.conflictWaitsFor_sub_blockedWaitsFor
#check @SeLe4n.Kernel.Concurrency.conflictWaitGraph_acyclic_under_2pl
-- SM3.D.6b audit-pass: static lock-set size bounds.
#check @SeLe4n.Kernel.Concurrency.insertOrMerge_size_le
#check @SeLe4n.Kernel.Concurrency.lockSetOfList_size_le
#check @SeLe4n.Kernel.Concurrency.lockSetExtendOpt_size_le
#check @SeLe4n.Kernel.Concurrency.size_le_1
#check @SeLe4n.Kernel.Concurrency.size_le_2
#check @SeLe4n.Kernel.Concurrency.size_le_3
#check @SeLe4n.Kernel.Concurrency.size_le_4
#check @SeLe4n.Kernel.Concurrency.lockSetTransitions_within_bound
-- SM3.D.6: bounded wait + KernelOperation + contention-sensitive WCRT.
#check @SeLe4n.Kernel.Concurrency.maxLockSetSize
#check @SeLe4n.Kernel.Concurrency.perLockWaitCost
#check @SeLe4n.Kernel.Concurrency.totalWaitCost
#check @SeLe4n.Kernel.Concurrency.sum_const_map
#check @SeLe4n.Kernel.Concurrency.totalWaitCost_eq
#check @SeLe4n.Kernel.Concurrency.totalWaitCost_le_bound
#check @SeLe4n.Kernel.Concurrency.KernelOperation
#check @SeLe4n.Kernel.Concurrency.KernelOperation.ofEndpointCall
#check @SeLe4n.Kernel.Concurrency.KernelOperation.ofReplyRecv
#check @SeLe4n.Kernel.Concurrency.KernelOperation.ofTcbSuspend
#check @SeLe4n.Kernel.Concurrency.otherCores
#check @SeLe4n.Kernel.Concurrency.otherCores_length_eq
#check @SeLe4n.Kernel.Concurrency.contendersAhead
#check @SeLe4n.Kernel.Concurrency.contendersAhead_le
#check @SeLe4n.Kernel.Concurrency.sum_le_length_mul
#check @SeLe4n.Kernel.Concurrency.sum_map_le_sum_map
#check @SeLe4n.Kernel.Concurrency.WCRT
#check @SeLe4n.Kernel.Concurrency.boundedWait_under_2pl
#check @SeLe4n.Kernel.Concurrency.WCRT_le_totalWaitCost
-- SM3.D §7: grounding bridge.
#check @SeLe4n.Kernel.Concurrency.acquireOrder_nodup
#check @SeLe4n.Kernel.Concurrency.CorePrefixOf
#check @SeLe4n.Kernel.Concurrency.coreFollows2PL_of_prefix
#check @SeLe4n.Kernel.Concurrency.coreAcquiresInOrder_of_prefix
#check @SeLe4n.Kernel.Concurrency.execution_satisfies_hypotheses_of_all_prefix
-- SM3.D §7b/§7c: model↔kernel bridge + twoCorePathScenario.
#check @SeLe4n.Kernel.Concurrency.executionOfHeld
#check @SeLe4n.Kernel.Concurrency.executionOfHeld_heldBy
#check @SeLe4n.Kernel.Concurrency.lockSetHeld_realizes_heldBy
#check @SeLe4n.Kernel.Concurrency.twoCorePathScenario
-- SM3.D Inventory aggregator.
#check @SeLe4n.Kernel.Concurrency.DeadlockCategory
#check @SeLe4n.Kernel.Concurrency.DeadlockTheorem
#check @SeLe4n.Kernel.Concurrency.deadlockTheorems
#check @SeLe4n.Kernel.Concurrency.deadlockTheorems_count
#check @SeLe4n.Kernel.Concurrency.deadlockTheorems_model_count
#check @SeLe4n.Kernel.Concurrency.deadlockTheorems_hypotheses_count
#check @SeLe4n.Kernel.Concurrency.deadlockTheorems_order_count
#check @SeLe4n.Kernel.Concurrency.deadlockTheorems_deadlock_count
#check @SeLe4n.Kernel.Concurrency.deadlockTheorems_waitGraph_count
#check @SeLe4n.Kernel.Concurrency.deadlockTheorems_modeAware_count
#check @SeLe4n.Kernel.Concurrency.deadlockTheorems_sizeBound_count
#check @SeLe4n.Kernel.Concurrency.deadlockTheorems_boundedWait_count
#check @SeLe4n.Kernel.Concurrency.deadlockTheorems_grounding_count
#check @SeLe4n.Kernel.Concurrency.deadlockTheorems_partition_sum
#check @SeLe4n.Kernel.Concurrency.deadlockTheorems_identifiers_nodup
#check @SeLe4n.Kernel.Concurrency.deadlockTheorems_descriptions_nodup
EOF'

# WS-SM SM3.E — serializability + conflict-graph acyclicity + commit-sort
# serialization order + single-core proof preservation + 111-theorem inventory.
# Surface anchors verify every SM3.E public symbol survives renames at
# elaboration time.  SM3.E.8: `#check` of the major theorems.
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake build SeLe4n.Kernel.Concurrency.Locks.Sm3EInventory'
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake env lean --stdin <<"EOF"
import SeLe4n.Kernel.Concurrency.LockSet
import SeLe4n.Kernel.Concurrency.Locks.Serializability
import SeLe4n.Kernel.Concurrency.Locks.Sm3EInventory

-- SM3.E.2: KernelTransitionInstance model + applySequential.
#check @SeLe4n.Kernel.Concurrency.KernelTransitionInstance
#check @SeLe4n.Kernel.Concurrency.applySequential
#check @SeLe4n.Kernel.Concurrency.applySequential_cons
#check @SeLe4n.Kernel.Concurrency.applySequential_append
-- SM3.E.1: conflict relation + conflictOrder.
#check @SeLe4n.Kernel.Concurrency.ktiSharesConflictingLock
#check @SeLe4n.Kernel.Concurrency.ktiConflictsB
#check @SeLe4n.Kernel.Concurrency.ktiConflictsB_iff
#check @SeLe4n.Kernel.Concurrency.ktiSharesConflictingLock_symm
#check @SeLe4n.Kernel.Concurrency.conflictOrder
#check @SeLe4n.Kernel.Concurrency.conflictOrder_sharesConflictingLock
#check @SeLe4n.Kernel.Concurrency.conflictOrder_implies_conflictPrecedes
-- SM3.E.4: strict 2PL.
#check @SeLe4n.Kernel.Concurrency.KernelTransitionInstance.followsStrict2PL
#check @SeLe4n.Kernel.Concurrency.scheduleFollowsStrict2PL
#check @SeLe4n.Kernel.Concurrency.KernelTransitionInstance.ofWithLockSet
#check @SeLe4n.Kernel.Concurrency.strictly_2pl_preserved
#check @SeLe4n.Kernel.Concurrency.scheduleFollowsStrict2PL_of_ofWithLockSet
#check @SeLe4n.Kernel.Concurrency.conflictOrder_commit_le
-- SM3.E.5: commutativity lemmas.
#check @SeLe4n.Kernel.Concurrency.KernelTransitionInstance.actionsCommute
#check @SeLe4n.Kernel.Concurrency.KernelTransitionInstance.actionsCommute_symm
#check @SeLe4n.Kernel.Concurrency.KernelTransitionInstance.actionsCommute_of_action_id_left
#check @SeLe4n.Kernel.Concurrency.KernelTransitionInstance.actionsCommute_of_action_id_right
#check @SeLe4n.Kernel.Concurrency.applySequential_swap_adjacent
#check @SeLe4n.Kernel.Concurrency.CommutingReorder
#check @SeLe4n.Kernel.Concurrency.CommutingReorder.cons
#check @SeLe4n.Kernel.Concurrency.applySequential_eq_of_commutingReorder
#check @SeLe4n.Kernel.Concurrency.readOnlyInstance
#check @SeLe4n.Kernel.Concurrency.readOnlyInstance_action
#check @SeLe4n.Kernel.Concurrency.readOnlyInstance_actionsCommute
#check @SeLe4n.Kernel.Concurrency.readOnlyInstance_actionsCommute_readOnly
#check @SeLe4n.Kernel.Concurrency.setObjStoreLockAction
#check @SeLe4n.Kernel.Concurrency.setSchedulerAction
#check @SeLe4n.Kernel.Concurrency.setObjStoreLock_setScheduler_commute
#check @SeLe4n.Kernel.Concurrency.disjointField_actionsCommute
#check @SeLe4n.Kernel.Concurrency.objStoreEquiv
#check @SeLe4n.Kernel.Concurrency.objStoreEquiv_refl
#check @SeLe4n.Kernel.Concurrency.objStoreEquiv_symm
#check @SeLe4n.Kernel.Concurrency.objStoreEquiv_trans
#check @SeLe4n.Kernel.Concurrency.updateObjectAt_preserves_invExt
#check @SeLe4n.Kernel.Concurrency.updateObjectAt_get?
#check @SeLe4n.Kernel.Concurrency.updateObjectAt_objStoreEquiv_comm
-- SM3.E.3: conflict-graph acyclicity (the acyclic conflict graph).
#check @SeLe4n.Kernel.Concurrency.conflictPrecedes
#check @SeLe4n.Kernel.Concurrency.conflictPrecedes_irreflexive
#check @SeLe4n.Kernel.Concurrency.conflictPrecedes_asymm
#check @SeLe4n.Kernel.Concurrency.ConflictReaches
#check @SeLe4n.Kernel.Concurrency.conflictReaches_commitTime_lt
#check @SeLe4n.Kernel.Concurrency.ConflictAcyclic
#check @SeLe4n.Kernel.Concurrency.conflictGraph_acyclic
#check @SeLe4n.Kernel.Concurrency.conflictPrecedes_total_of_distinct_commit
#check @SeLe4n.Kernel.Concurrency.conflictPrecedes_strict_total_of_distinct_commit
-- SM3.E.2/E.3: commit-sort serialization order + main theorem.
#check @SeLe4n.Kernel.Concurrency.insertByCommitTime
#check @SeLe4n.Kernel.Concurrency.commitSort
#check @SeLe4n.Kernel.Concurrency.insertByCommitTime_perm
#check @SeLe4n.Kernel.Concurrency.commitSort_perm
#check @SeLe4n.Kernel.Concurrency.insertByCommitTime_sorted
#check @SeLe4n.Kernel.Concurrency.commitSort_sorted
#check @SeLe4n.Kernel.Concurrency.commutesWithSmaller
#check @SeLe4n.Kernel.Concurrency.commutesWithSmaller_of_perm
#check @SeLe4n.Kernel.Concurrency.insertByCommitTime_commutingReorder
#check @SeLe4n.Kernel.Concurrency.outOfOrderCommute
#check @SeLe4n.Kernel.Concurrency.commitSort_commutingReorder
#check @SeLe4n.Kernel.Concurrency.serialEquivalent
#check @SeLe4n.Kernel.Concurrency.serialEquivalent_refl
#check @SeLe4n.Kernel.Concurrency.serializability_under_2pl
#check @SeLe4n.Kernel.Concurrency.serializability_under_2pl_exists
#check @SeLe4n.Kernel.Concurrency.outOfOrderCommute_of_forall_action_id
#check @SeLe4n.Kernel.Concurrency.serializability_of_readOnly_schedule
#check @SeLe4n.Kernel.Concurrency.commitSorted_respects_conflictPrecedes
#check @SeLe4n.Kernel.Concurrency.commitSorted_respects_conflictOrder
#check @SeLe4n.Kernel.Concurrency.conflictsCommitOrdered
#check @SeLe4n.Kernel.Concurrency.outOfOrderCommute_of_conflictsCommitOrdered
#check @SeLe4n.Kernel.Concurrency.serializability_under_2pl_of_conflicts_ordered
-- SM3.E.6: single-core proof preservation (Corollary 2.1.11).
#check @SeLe4n.Kernel.Concurrency.singleCore_invariant_preservation
#check @SeLe4n.Kernel.Concurrency.singleCore_proof_preservation
#check @SeLe4n.Kernel.Concurrency.withLockSet_growing_phase_establishes_lockSetHeld
#check @SeLe4n.Kernel.Concurrency.acquireLockOnObject_preserves_objStoreLock_wf
#check @SeLe4n.Kernel.Concurrency.releaseLockOnObject_preserves_objStoreLock_wf
#check @SeLe4n.Kernel.Concurrency.withLockSet_preserves_objStoreLock_wf
#check @SeLe4n.Kernel.Concurrency.releaseLockOnObject_preserves_invExt
#check @SeLe4n.Kernel.Concurrency.updateObjectLockAt_preserves_objectType_at
#check @SeLe4n.Kernel.Concurrency.acquireLockOnObject_preserves_objectType_at
#check @SeLe4n.Kernel.Concurrency.releaseLockOnObject_preserves_objectType_at
#check @SeLe4n.Kernel.Concurrency.withLockSet_preserves_objectType_at
#check @SeLe4n.Kernel.Concurrency.ActionPiCongr
#check @SeLe4n.Kernel.Concurrency.applySequential_piCongr
#check @SeLe4n.Kernel.Concurrency.withLockSet_observation_eq_action
#check @SeLe4n.Kernel.Concurrency.applySequentialWithLockSet
#check @SeLe4n.Kernel.Concurrency.applySequentialWithLockSet_observation
#check @SeLe4n.Kernel.Concurrency.acquireLockOnObject_preserves_scheduler
#check @SeLe4n.Kernel.Concurrency.releaseLockOnObject_preserves_scheduler
#check @SeLe4n.Kernel.Concurrency.schedulerObserver_acquireInsensitive
#check @SeLe4n.Kernel.Concurrency.schedulerObserver_releaseInsensitive
#check @SeLe4n.Kernel.Concurrency.withLockSet_observation_scheduler_witness
#check @SeLe4n.Kernel.Concurrency.ActionObsCongr
#check @SeLe4n.Kernel.Concurrency.ActionPreservesInvExt
#check @SeLe4n.Kernel.Concurrency.KernelTransitionInstance.wellBehavedObs
#check @SeLe4n.Kernel.Concurrency.KernelTransitionInstance.actionsCommuteObs
#check @SeLe4n.Kernel.Concurrency.updateObjectAt_actionObsCongr
#check @SeLe4n.Kernel.Concurrency.updateObjectAt_actionPreservesInvExt
#check @SeLe4n.Kernel.Concurrency.updateObjectAt_wellBehavedObs
#check @SeLe4n.Kernel.Concurrency.applySequential_preservesInvExt
#check @SeLe4n.Kernel.Concurrency.applySequential_obsCongr
#check @SeLe4n.Kernel.Concurrency.applySequential_swap_front_obs
#check @SeLe4n.Kernel.Concurrency.applySequential_cons_obs
#check @SeLe4n.Kernel.Concurrency.outOfOrderCommuteObs
#check @SeLe4n.Kernel.Concurrency.insertByCommitTime_obs
#check @SeLe4n.Kernel.Concurrency.commitSort_obs
#check @SeLe4n.Kernel.Concurrency.serializability_under_2pl_obs
#check @SeLe4n.Kernel.Concurrency.objStoreWriteInstance
#check @SeLe4n.Kernel.Concurrency.objStoreWriteInstance_wellBehavedObs
#check @SeLe4n.Kernel.Concurrency.objStoreWriteInstance_actionsCommuteObs
-- SM3.E Inventory aggregator.
#check @SeLe4n.Kernel.Concurrency.SerializabilityCategory
#check @SeLe4n.Kernel.Concurrency.SerializabilityTheorem
#check @SeLe4n.Kernel.Concurrency.serializabilityTheorems
#check @SeLe4n.Kernel.Concurrency.serializabilityTheorems_count
#check @SeLe4n.Kernel.Concurrency.serializabilityTheorems_partition_sum
#check @SeLe4n.Kernel.Concurrency.serializabilityTheorems_identifiers_nodup
#check @SeLe4n.Kernel.Concurrency.serializabilityTheorems_descriptions_nodup
EOF'

# WS-SM SM4.A — per-core Vector bootstrap surface anchors.  Covers the
# SM4.A.1/A.2 `SeLe4n.PerCoreVector` helper surface (the get_eq_getElem bridge
# plus the six lemmas), the SM4.A.4 RPi5 coreCount pinning, the SM4.A.5
# single-core simulation binding, and the SM4.A.6/A.7/A.8 CoreId /
# bootCoreId / allCores recap.  A rename / removal of any SM4.A symbol
# fails here at elaboration time, before SM4.B can consume them.
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake build SeLe4n.Prelude SeLe4n.Platform.RPi5.Contract SeLe4n.Platform.Sim.Contract'
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake env lean --stdin <<"EOF"
import SeLe4n.Prelude
import SeLe4n.Kernel.Concurrency.Types
import SeLe4n.Platform.RPi5.Contract
import SeLe4n.Platform.Sim.Contract

-- SM4.A.1/A.2/A.3 — Per-core Vector helper surface.
#check @SeLe4n.PerCoreVector.get_eq_getElem
#check @SeLe4n.PerCoreVector.get_eq_toArray_getElem
#check @SeLe4n.PerCoreVector.get_set_eq
#check @SeLe4n.PerCoreVector.get_set_ne
#check @SeLe4n.PerCoreVector.toList_length
#check @SeLe4n.PerCoreVector.replicate_get
#check @SeLe4n.PerCoreVector.ext
#check @SeLe4n.PerCoreVector.nodup_of_finRange
-- SM4.A.4 — RPi5 coreCount pinning.
#check @SeLe4n.Platform.RPi5.numCores_eq_rpi5_coreCount
#check @SeLe4n.Platform.RPi5.bootCoreId_val_eq_rpi5
-- SM4.A.5 — Simulation bindings (single-core + 4-core SMP).
#check @SeLe4n.Platform.Sim.SimSingleCorePlatform
#check SeLe4n.Platform.Sim.simSingleCorePlatformBinding
#check SeLe4n.Platform.Sim.simPlatformBinding
#check SeLe4n.Platform.Sim.simRestrictivePlatformBinding
-- SM4.A.6/A.7/A.8 — CoreId / bootCoreId / allCores recap.
#check @SeLe4n.Kernel.Concurrency.CoreId
#check @SeLe4n.Kernel.Concurrency.bootCoreId
#check @SeLe4n.Kernel.Concurrency.allCores
#check @SeLe4n.Kernel.Concurrency.allCores_length
#check @SeLe4n.Kernel.Concurrency.allCores_nodup
EOF'

# WS-SM SM4.B — per-core SchedulerState foundation surface anchors.  Covers
# the SM4.B.8 seven per-core accessors, the SM4.B.9 default-state per-core
# initialisation theorem, and the SM4.B.10 per-core extensionality theorem.
# A rename / removal of any SM4.B foundation symbol fails here at
# elaboration time, before the SM4.C/SM4.D migrations can consume them.
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake build SeLe4n.Model.State'
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake env lean --stdin <<"EOF"
import SeLe4n.Model.State
import SeLe4n.Kernel.Concurrency.Types

-- SM4.B.8 — the seven per-core accessors.
#check @SeLe4n.Model.SchedulerState.currentOnCore
#check @SeLe4n.Model.SchedulerState.runQueueOnCore
#check @SeLe4n.Model.SchedulerState.replenishQueueOnCore
#check @SeLe4n.Model.SchedulerState.activeDomainOnCore
#check @SeLe4n.Model.SchedulerState.domainTimeRemainingOnCore
#check @SeLe4n.Model.SchedulerState.domainScheduleIndexOnCore
#check @SeLe4n.Model.SchedulerState.lastTimeoutErrorsOnCore
-- SM4.B.phase-2 — the seven per-core setters (path-a write API).
#check @SeLe4n.Model.SchedulerState.setCurrentOnCore
#check @SeLe4n.Model.SchedulerState.setRunQueueOnCore
#check @SeLe4n.Model.SchedulerState.setReplenishQueueOnCore
#check @SeLe4n.Model.SchedulerState.setActiveDomainOnCore
#check @SeLe4n.Model.SchedulerState.setDomainTimeRemainingOnCore
#check @SeLe4n.Model.SchedulerState.setDomainScheduleIndexOnCore
#check @SeLe4n.Model.SchedulerState.setLastTimeoutErrorsOnCore
-- SM4.B.phase-2 — store/load algebra: 7 read-after-write _self lemmas +
-- representative cross-field and system-wide frame lemmas.
#check @SeLe4n.Model.SchedulerState.setCurrentOnCore_currentOnCore_self
#check @SeLe4n.Model.SchedulerState.setRunQueueOnCore_runQueueOnCore_self
#check @SeLe4n.Model.SchedulerState.setReplenishQueueOnCore_replenishQueueOnCore_self
#check @SeLe4n.Model.SchedulerState.setActiveDomainOnCore_activeDomainOnCore_self
#check @SeLe4n.Model.SchedulerState.setDomainTimeRemainingOnCore_domainTimeRemainingOnCore_self
#check @SeLe4n.Model.SchedulerState.setDomainScheduleIndexOnCore_domainScheduleIndexOnCore_self
#check @SeLe4n.Model.SchedulerState.setLastTimeoutErrorsOnCore_lastTimeoutErrorsOnCore_self
#check @SeLe4n.Model.SchedulerState.setRunQueueOnCore_currentOnCore
#check @SeLe4n.Model.SchedulerState.setRunQueueOnCore_domainSchedule
-- SM4.B.phase-2 — per-core independence: the seven same-field cross-core (_ne) frames.
#check @SeLe4n.Model.SchedulerState.setCurrentOnCore_currentOnCore_ne
#check @SeLe4n.Model.SchedulerState.setRunQueueOnCore_runQueueOnCore_ne
#check @SeLe4n.Model.SchedulerState.setReplenishQueueOnCore_replenishQueueOnCore_ne
#check @SeLe4n.Model.SchedulerState.setActiveDomainOnCore_activeDomainOnCore_ne
#check @SeLe4n.Model.SchedulerState.setDomainTimeRemainingOnCore_domainTimeRemainingOnCore_ne
#check @SeLe4n.Model.SchedulerState.setDomainScheduleIndexOnCore_domainScheduleIndexOnCore_ne
#check @SeLe4n.Model.SchedulerState.setLastTimeoutErrorsOnCore_lastTimeoutErrorsOnCore_ne
-- SM4.B.9 — default-state per-core initialisation.
#check @SeLe4n.Model.default_state_perCoreInitialized
-- SM4.B.10 — per-core extensionality.
#check @SeLe4n.Model.SchedulerState.ext_perCore
EOF'

# WS-SM SM4.C — per-core scheduler invariant migration surface anchors.
# Covers the 16 per-core predicate forms (plan §3.4 Pattern 1), the 16
# boot-core bridges (defeq grounding the live `schedulerInvariantBundle*`
# surface), the SM4.C.29 aggregate `schedulerInvariant_perCore` +
# `schedulerInvariant_smp` + `aggregateForall` + projections, the bundle
# bridges to `schedulerInvariantBundleFull/Extended`, the default-state
# theorems on every core in `allCores`, the per-core / idle-core frame
# lemmas, the three cross-core independence corollaries, the SM4.C.30
# pairwise theorem, and the single-core-preservation-lifts-to-SMP
# skeleton.  A rename / removal of any SM4.C symbol fails here at
# elaboration time, before SM5's per-core scheduler can consume them.
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake build SeLe4n.Kernel.Scheduler.Invariant.PerCore'
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake env lean --stdin <<"EOF"
import SeLe4n.Kernel.Scheduler.Invariant.PerCore
open SeLe4n.Kernel

-- SM4.C §1 — 16 per-core predicate forms.
#check @queueCurrentConsistentOnCore
#check @runQueueUniqueOnCore
#check @currentThreadValidOnCore
#check @currentThreadInActiveDomainOnCore
#check @timeSlicePositiveOnCore
#check @currentTimeSlicePositiveOnCore
#check @edfCurrentHasEarliestDeadlineOnCore
#check @contextMatchesCurrentOnCore
#check @runnableThreadsAreTCBsOnCore
#check @schedulerPriorityMatchOnCore
#check @domainTimeRemainingPositiveOnCore
#check @currentBudgetPositiveOnCore
#check @budgetPositiveOnCore
#check @replenishmentPipelineOrderOnCore
#check @replenishQueueValidOnCore
#check @effectiveParamsMatchRunQueueOnCore
-- SM4.C §2 — 16 boot-core bridges.
#check @queueCurrentConsistentOnCore_bootCore_iff
#check @runQueueUniqueOnCore_bootCore_iff
#check @currentThreadValidOnCore_bootCore_iff
#check @currentThreadInActiveDomainOnCore_bootCore_iff
#check @timeSlicePositiveOnCore_bootCore_iff
#check @currentTimeSlicePositiveOnCore_bootCore_iff
#check @edfCurrentHasEarliestDeadlineOnCore_bootCore_iff
#check @contextMatchesCurrentOnCore_bootCore_iff
#check @runnableThreadsAreTCBsOnCore_bootCore_iff
#check @schedulerPriorityMatchOnCore_bootCore_iff
#check @domainTimeRemainingPositiveOnCore_bootCore_iff
#check @currentBudgetPositiveOnCore_bootCore_iff
#check @budgetPositiveOnCore_bootCore_iff
#check @replenishmentPipelineOrderOnCore_bootCore_iff
#check @replenishQueueValidOnCore_bootCore_iff
#check @effectiveParamsMatchRunQueueOnCore_bootCore_iff
-- SM4.C.29 — aggregate per-core + SMP forall + projections.
#check @schedulerInvariant_perCore
#check @schedulerInvariant_smp
#check @schedulerInvariant_perCore_aggregateForall
#check @schedulerInvariant_smp_at
#check @schedulerInvariant_perCore_to_queueCurrentConsistent
#check @schedulerInvariant_perCore_to_runQueueUnique
#check @schedulerInvariant_perCore_to_currentThreadValid
#check @schedulerInvariant_perCore_to_timeSlicePositive
#check @schedulerInvariant_perCore_to_currentTimeSlicePositive
#check @schedulerInvariant_perCore_to_edfCurrentHasEarliestDeadline
#check @schedulerInvariant_perCore_to_contextMatchesCurrent
#check @schedulerInvariant_perCore_to_runnableThreadsAreTCBs
#check @schedulerInvariant_perCore_to_schedulerPriorityMatch
#check @schedulerInvariant_perCore_to_domainTimeRemainingPositive
-- SM4.C §4 — bundle bridges to the live cross-subsystem surface.
#check @schedulerInvariantBundleFull_to_perCore_bootCore
#check @schedulerInvariant_perCore_bootCore_to_bundleFull
#check @schedulerInvariantBundleExtended_to_perCore_bootCore
-- SM4.C §5 — default-state.
#check @default_schedulerInvariant_perCore
#check @default_schedulerInvariant_smp
-- SM4.C.30 — frame + cross-core independence + SMP-preservation skeleton.
#check @schedulerInvariant_perCore_frame
#check @schedulerInvariant_perCore_frame_idle
#check @schedulerInvariant_perCore_independent_of_setCurrentOnCore
#check @schedulerInvariant_perCore_independent_of_setRunQueueOnCore
#check @schedulerInvariant_perCore_independent_of_setDomainTimeRemainingOnCore
#check @schedulerInvariant_perCore_independent_of_setReplenishQueueOnCore
#check @schedulerInvariant_perCore_independent_of_setActiveDomainOnCore
#check @schedulerInvariant_perCore_independent_of_setDomainScheduleIndexOnCore
#check @schedulerInvariant_perCore_independent_of_setLastTimeoutErrorsOnCore
#check @schedulerInvariant_perCore_pairwise
#check @schedulerInvariant_smp_of_bootCore_and_idle_frame
-- SM4.C plan §5.6 missing predicate.
#check @runQueueOnCoreWellFormed
-- SM4.C §5.5 per-conjunct frame lemmas (17 total).
#check @queueCurrentConsistentOnCore_frame
#check @runQueueUniqueOnCore_frame
#check @runQueueOnCoreWellFormed_frame
#check @currentThreadValidOnCore_frame
#check @currentThreadInActiveDomainOnCore_frame
#check @timeSlicePositiveOnCore_frame
#check @currentTimeSlicePositiveOnCore_frame
#check @edfCurrentHasEarliestDeadlineOnCore_frame
#check @contextMatchesCurrentOnCore_frame
#check @runnableThreadsAreTCBsOnCore_frame
#check @schedulerPriorityMatchOnCore_frame
#check @domainTimeRemainingPositiveOnCore_frame
#check @currentBudgetPositiveOnCore_frame
#check @budgetPositiveOnCore_frame
#check @replenishmentPipelineOrderOnCore_frame
#check @replenishQueueValidOnCore_frame
#check @effectiveParamsMatchRunQueueOnCore_frame
-- SM4.C §3.5 extended per-core aggregate (mirrors schedulerInvariantBundleExtended).
#check @schedulerInvariant_perCore_extended
#check @schedulerInvariant_smp_extended
#check @schedulerInvariant_perCore_extended_aggregateForall
#check @schedulerInvariant_smp_extended_at
#check @schedulerInvariant_perCore_extended_to_base
#check @schedulerInvariant_perCore_extended_to_currentBudgetPositive
#check @schedulerInvariant_perCore_extended_to_budgetPositive
#check @schedulerInvariant_perCore_extended_to_replenishQueueValid
#check @schedulerInvariant_perCore_extended_to_effectiveParamsMatchRunQueue
-- SM4.C extended bundle bridges.
#check @schedulerInvariantBundleExtended_to_perCore_extended_bootCore
#check @schedulerInvariant_perCore_extended_bootCore_to_bundleExtended
-- SM4.C extended default-state.
#check @default_schedulerInvariant_perCore_extended
#check @default_schedulerInvariant_smp_extended
-- SM4.C §8 extended-aggregate frame + pairwise + SMP-preservation skeleton.
#check @schedulerInvariant_perCore_extended_frame
#check @schedulerInvariant_perCore_extended_frame_idle
#check @schedulerInvariant_perCore_extended_pairwise
#check @schedulerInvariant_smp_extended_of_bootCore_and_idle_frame
-- SM4.C §9 cross-subsystem per-core predicates (plan §5.6).
#check @schedContextRunQueueConsistent_perCore
#check @priorityInheritance_perCore
#check @activeDomainOnCore_isInDomainSchedule
#check @schedContextRunQueueConsistent_perCore_bootCore_iff
#check @priorityInheritance_perCore_iff
#check @default_schedContextRunQueueConsistent_perCore
#check @default_priorityInheritance_perCore
#check @default_activeDomainOnCore_isInDomainSchedule
#check @schedContextRunQueueConsistent_perCore_frame
#check @priorityInheritance_perCore_frame
#check @activeDomainOnCore_isInDomainSchedule_frame
-- SM4.C §10 cross-subsystem per-core aggregate + projections + bridge.
#check @schedulerInvariant_perCore_crossSubsystem
#check @schedulerInvariant_smp_crossSubsystem
#check @schedulerInvariant_perCore_crossSubsystem_aggregateForall
#check @schedulerInvariant_smp_crossSubsystem_at
#check @schedulerInvariant_perCore_crossSubsystem_to_extended
#check @schedulerInvariant_perCore_crossSubsystem_to_schedContextRunQueueConsistent
#check @schedulerInvariant_perCore_crossSubsystem_to_priorityInheritance
#check @schedulerInvariant_perCore_crossSubsystem_to_activeDomainOnCore_isInDomainSchedule
#check @crossSubsystemInvariant_to_perCore_crossSubsystem_bootCore
#check @default_schedulerInvariant_perCore_crossSubsystem
#check @default_schedulerInvariant_smp_crossSubsystem
-- SM4.C §11 "sufficient idle" + SMP-preservation composition.
#check @schedulerInvariant_perCore_holds_if_idle
#check @schedulerInvariant_perCore_idle_on_post_state
#check @schedulerInvariant_smp_of_bootCore_preservation
#check @schedulerInvariant_smp_extended_of_bootCore_preservation
EOF'

# WS-SM SM4.C audit-pass-4 — per-operation per-core preservation theorems.
# The 5 boot-core scheduler operations with single-core Full preservation
# (`schedule`, `handleYield`, `timerTick`, `switchDomain`, `scheduleDomain`)
# each get a per-core SMP preservation theorem composing the existing
# single-core surface with the SM4.C SMP-preservation skeleton; plus a
# base-aggregate bridge for `chooseThread`.
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake build SeLe4n.Kernel.Scheduler.Invariant.PerCorePreservation'
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake env lean --stdin <<"EOF"
import SeLe4n.Kernel.Scheduler.Invariant.PerCorePreservation
open SeLe4n.Kernel

#check @schedule_preserves_schedulerInvariant_smp
#check @handleYield_preserves_schedulerInvariant_smp
#check @timerTick_preserves_schedulerInvariant_smp
#check @switchDomain_preserves_schedulerInvariant_smp
#check @scheduleDomain_preserves_schedulerInvariant_smp
-- audit-pass-9: chooseThread genuine per-core forms (single-core bundle
-- form lives in Scheduler/Operations/Preservation.lean and is already
-- surface-anchored).
#check @chooseThread_preserves_schedulerInvariantBase_perCore_bootCore
#check @chooseThread_preserves_schedulerInvariantBase_smp
#check @chooseThread_preserves_schedulerInvariant_smp
-- audit-pass-9: schedulerInvariantBase_perCore aggregate + projections + bridges
#check @schedulerInvariantBase_perCore
#check @schedulerInvariantBase_smp
#check @schedulerInvariantBase_perCore_aggregateForall
#check @schedulerInvariantBase_smp_at
#check @schedulerInvariantBase_perCore_to_queueCurrentConsistent
#check @schedulerInvariantBase_perCore_to_runQueueUnique
#check @schedulerInvariantBase_perCore_to_currentThreadValid
#check @schedulerInvariantBundle_to_perCoreBase_bootCore
#check @schedulerInvariantBase_perCore_bootCore_to_bundle
#check @schedulerInvariant_perCore_to_base
#check @schedulerInvariant_smp_to_base
#check @default_schedulerInvariantBase_perCore
#check @default_schedulerInvariantBase_smp
-- audit-pass-11: convenience wrapper taking runQueueOnCore = empty (stronger
-- structural hypothesis; derives toList-empty and wellFormed internally).
#check @schedulerInvariant_perCore_holds_if_idle_default
EOF'

# WS-SM SM4.D — cross-subsystem per-core invariant migration surface anchors.
# Covers the IPC↔scheduler coherence predicates (12 per-core forms + the
# `∀ c` SMP aggregates + boot-core bridges + frame lemmas + defaults), the
# capability no-stale-scheduler-ref retype precondition, the architecture
# register-decode consistency, the IF-M1 per-core projections + the
# `projectStateOnCore` aggregate + observability frame lemmas, and the
# CrossSubsystem capstone (`crossSubsystemInvariant_perCore` +
# `crossSubsystemSchedulerContract_perCore` + SMP forms).  A rename /
# removal of any SM4.D symbol fails here at elaboration time, before SM5's
# per-core scheduler can consume them.
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake build SeLe4n.Kernel.CrossSubsystemPerCorePreservation'
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake env lean --stdin <<"EOF"
import SeLe4n.Kernel.CrossSubsystemPerCorePreservation
open SeLe4n.Kernel
open SeLe4n.Kernel.Architecture

-- SM4.D.1/.2 — IPC per-core predicate forms (12) + aggregates.
#check @runnableThreadIpcReady_perCore
#check @blockedOnSendNotRunnable_perCore
#check @blockedOnReceiveNotRunnable_perCore
#check @blockedOnCallNotRunnable_perCore
#check @blockedOnReplyNotRunnable_perCore
#check @blockedOnNotificationNotRunnable_perCore
#check @currentThreadIpcReady_perCore
#check @currentNotEndpointQueueHead_perCore
#check @currentNotOnNotificationWaitList_perCore
#check @passiveServerIdle_perCore
#check @ipcSchedulerContractPredicates_perCore
#check @currentThreadDequeueCoherent_perCore
-- SM4.D.1/.2 — IPC boot-core bridges.
#check @runnableThreadIpcReady_perCore_bootCore_iff
#check @blockedOnSendNotRunnable_perCore_bootCore_iff
#check @currentThreadIpcReady_perCore_bootCore_iff
#check @passiveServerIdle_perCore_bootCore_iff
#check @ipcSchedulerContractPredicates_perCore_bootCore_iff
#check @currentThreadDequeueCoherent_perCore_bootCore_iff
-- SM4.D.1/.2 — IPC frame lemmas.
#check @runnableThreadIpcReady_perCore_frame
#check @currentThreadIpcReady_perCore_frame
#check @passiveServerIdle_perCore_frame
-- SM4.D.1/.2 — IPC defaults + SMP aggregates + extractors + projections.
#check @default_ipcSchedulerContractPredicates_perCore
#check @default_currentThreadDequeueCoherent_perCore
#check @default_passiveServerIdle_perCore
#check @ipcSchedulerContractPredicates_smp
#check @currentThreadDequeueCoherent_smp
#check @passiveServerIdle_smp
#check @ipcSchedulerContractPredicates_smp_aggregateForall
#check @ipcSchedulerContractPredicates_smp_at
#check @ipcSchedulerContractPredicates_smp_to_singleCore
#check @currentThreadDequeueCoherent_smp_to_singleCore
#check @passiveServerIdle_smp_to_singleCore
#check @default_ipcSchedulerContractPredicates_smp
#check @default_currentThreadDequeueCoherent_smp
#check @default_passiveServerIdle_smp
#check @ipcSchedulerContractPredicates_perCore_to_runnableThreadIpcReady
#check @ipcSchedulerContractPredicates_perCore_to_blockedOnNotificationNotRunnable
#check @currentThreadDequeueCoherent_perCore_to_currentThreadIpcReady
#check @currentThreadDequeueCoherent_perCore_to_currentNotOnNotificationWaitList
-- SM4.D.3/.4 — Capability per-core no-stale-scheduler-ref.
#check @cleanupNoStaleSchedRef_perCore
#check @cleanupHookDischarged_perCore
#check @cleanupNoStaleSchedRef_perCore_bootCore_iff
#check @cleanupHookDischarged_perCore_bootCore_iff
#check @cleanupNoStaleSchedRef_perCore_frame
#check @default_cleanupNoStaleSchedRef_perCore
#check @cleanupNoStaleSchedRef_smp
#check @cleanupNoStaleSchedRef_smp_aggregateForall
#check @cleanupNoStaleSchedRef_smp_at
#check @cleanupNoStaleSchedRef_smp_to_singleCore
#check @default_cleanupNoStaleSchedRef_smp
-- SM4.D.9 — Architecture per-core register-decode consistency.
#check @registerDecodeConsistent_perCore
#check @registerDecodeConsistent_perCore_bootCore_iff
#check @registerDecodeConsistent_perCore_frame
#check @default_registerDecodeConsistent_perCore
#check @registerDecodeConsistent_smp
#check @registerDecodeConsistent_smp_aggregateForall
#check @registerDecodeConsistent_smp_at
#check @registerDecodeConsistent_smp_to_singleCore
#check @default_registerDecodeConsistent_smp
-- SM4.D.12/.13/.14 — InformationFlow per-core projections.
#check @projectRunnableOnCore
#check @projectCurrentOnCore
#check @projectActiveDomainOnCore
#check @projectDomainTimeRemainingOnCore
#check @projectDomainScheduleIndexOnCore
#check @projectMachineRegsOnCore
#check @projectStateOnCore
#check @projectRunnableOnCore_bootCore
#check @projectCurrentOnCore_bootCore
#check @projectActiveDomainOnCore_bootCore
#check @projectDomainTimeRemainingOnCore_bootCore
#check @projectDomainScheduleIndexOnCore_bootCore
#check @projectMachineRegsOnCore_bootCore
#check @projectStateOnCore_bootCore
#check @projectRunnableOnCore_frame
#check @projectCurrentOnCore_frame
#check @projectActiveDomainOnCore_frame
#check @projectDomainTimeRemainingOnCore_frame
#check @projectDomainScheduleIndexOnCore_frame
#check @projectMachineRegsOnCore_frame
#check @projectStateOnCore_congr
-- SM4.D.19 — CrossSubsystem capstone aggregates.
#check @crossSubsystemInvariant_perCore
#check @crossSubsystemInvariant_perCore_bootCore_iff
#check @crossSubsystemInvariant_smp
#check @crossSubsystemInvariant_smp_aggregateForall
#check @crossSubsystemInvariant_smp_at
#check @crossSubsystemInvariant_smp_to_singleCore
#check @crossSubsystemInvariant_perCore_to_schedContextRunQueueConsistent
#check @default_crossSubsystemInvariant_perCore
#check @default_crossSubsystemInvariant_smp
#check @crossSubsystemSchedulerContract_perCore
#check @crossSubsystemSchedulerContract_perCore_bootCore_iff
#check @crossSubsystemSchedulerContract_smp
#check @crossSubsystemSchedulerContract_smp_aggregateForall
#check @crossSubsystemSchedulerContract_smp_at
#check @crossSubsystemSchedulerContract_perCore_to_ipcSchedulerContractPredicates
#check @crossSubsystemSchedulerContract_perCore_to_currentThreadDequeueCoherent
#check @crossSubsystemSchedulerContract_perCore_to_passiveServerIdle
#check @crossSubsystemSchedulerContract_perCore_to_registerDecodeConsistent
#check @crossSubsystemSchedulerContract_perCore_to_schedContextRunQueueConsistent
#check @default_crossSubsystemSchedulerContract_perCore
#check @default_crossSubsystemSchedulerContract_smp
-- SM4.D audit-pass-1 additions: passiveServerIdle natural-SMP theorem,
-- per-core low-equivalence (SM4.D.13 NI substrate), full SMP cleanup-hook.
#check @passiveServerIdle_smp_not_scheduled_anywhere
#check @lowEquivalentOnCore
#check @lowEquivalentOnCore_bootCore
#check @lowEquivalentOnCore_refl
#check @lowEquivalentOnCore_symm
#check @lowEquivalentOnCore_trans
#check @lowEquivalent_smp
#check @lowEquivalent_smp_aggregateForall
#check @lowEquivalent_smp_at
#check @lowEquivalent_smp_to_singleCore
#check @cleanupHookDischarged_smp
#check @cleanupHookDischarged_smp_to_singleCore
#check @cleanupHookDischarged_smp_to_noStaleSchedRef
-- SM4.D audit-pass-2: preservation layer + SMP retype-target consumer.
#check @ipcSchedulerContractPredicates_perCore_holds_if_idle
#check @currentThreadDequeueCoherent_perCore_holds_if_idle
#check @registerDecodeConsistent_perCore_holds_if_idle
#check @cleanupNoStaleSchedRef_perCore_holds_if_idle
#check @schedContextRunQueueConsistent_perCore_holds_if_idle
#check @ipcSchedulerContractPredicates_smp_of_singleCore_and_idle
#check @currentThreadDequeueCoherent_smp_of_singleCore_and_idle
#check @registerDecodeConsistent_smp_of_singleCore_and_idle
#check @schedContextRunQueueConsistent_smp_of_singleCore_and_idle
#check @cleanupNoStaleSchedRef_smp_of_singleCore_and_idle
#check @passiveServerIdle_scheduledNowhere
#check @passiveServerIdle_scheduledNowhere_of_singleCore
#check @passiveServerIdle_smp_to_scheduledNowhere
#check @passiveServerIdle_scheduledNowhere_of_ipcInvariantFull
#check @default_passiveServerIdle_scheduledNowhere
#check @endpointSendDual_preserves_ipcSchedulerContractPredicates_smp
#check @endpointReceiveDual_preserves_ipcSchedulerContractPredicates_smp
#check @endpointCall_preserves_ipcSchedulerContractPredicates_smp
#check @endpointReply_preserves_ipcSchedulerContractPredicates_smp
#check @endpointReplyRecv_preserves_ipcSchedulerContractPredicates_smp
#check @notificationSignal_preserves_ipcSchedulerContractPredicates_smp
#check @notificationWait_preserves_ipcSchedulerContractPredicates_smp
#check @endpointQueueRemoveDual_preserves_ipcSchedulerContractPredicates_smp
#check @advanceTimerState_preserves_registerDecodeConsistent_smp
#check @writeRegisterState_preserves_registerDecodeConsistent_smp
#check @timerTick_preserves_schedContextRunQueueConsistent_smp
#check @RetypeTargetSmp
#check @mkRetypeTargetSmp
#check @RetypeTargetSmp.toRetypeTarget
EOF'

# WS-SM SM4.D audit-pass-3: per-core RPi5 register-context runtime contract
# (the one Platform-layer scheduler-reader found by the exhaustive audit).
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake build SeLe4n.Platform.RPi5.RuntimeContractPerCore'
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake env lean --stdin <<"EOF"
import SeLe4n.Platform.RPi5.RuntimeContractPerCore
open SeLe4n.Platform.RPi5
#check @registerContextStableCheckOnCore
#check @registerContextStablePredOnCore
#check @registerContextStableCheckOnCore_bootCore
#check @registerContextStablePredOnCore_bootCore_iff
#check @registerContextStableCheckOnCore_true_of_currentNone
#check @default_registerContextStableCheckOnCore
EOF'

# WS-SM SM5.A — per-core chooseThread surface anchors.  Covers the SM5.A.2
# run-queue lock-set (`RunQueueLockId` + `chooseThreadOnCoreLockSet` + 4
# witnesses), the SM5.A.3 per-core-independence frame + corollaries, the
# SM5.A.4 idle-fallback completeness theorems + `schedulerInvariant_perCore`
# corollaries, the SM5.A.6 selection-soundness results, and the SM5.A.7
# decidable predicates.  `chooseThreadOnCore` (SM5.A.1) and the legacy
# `chooseThread` migration bridge (SM5.A.5) are checked against the
# production module.  A rename / removal of any SM5.A symbol fails here at
# elaboration time, before SM5.B's per-core `switchToThread` consumes them.
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake build SeLe4n.Kernel.Scheduler.Operations.PerCoreChooseThread'
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake env lean --stdin <<"EOF"
import SeLe4n.Kernel.Scheduler.Operations.PerCoreChooseThread
open SeLe4n.Kernel

-- SM5.A.1 + SM5.A.5 — per-core selection + legacy-chooseThread migration bridge.
#check @chooseThreadOnCore
#check @chooseThread_eq_chooseThreadOnCore_bootCore

-- SM5.A.2 — run-queue lock identifier + cross-domain SchedLockId + the
-- complete (object-store + run-queue) chooseThread lock-set.
#check @RunQueueLockId
#check @SchedLockId
#check @schedObjStoreLockId
#check @SchedLockId.le
#check @SchedLockId.lt
#check @SchedLockId.le_refl
#check @SchedLockId.le_trans
#check @SchedLockId.le_antisymm
#check @SchedLockId.le_total
#check @SchedLockId.lt_irrefl
#check @SchedLockId.lt_asymm
#check @SchedLockId.object_lt_runQueue
#check @chooseThreadOnCoreLockSet
#check @chooseThreadOnCoreLockSet_length
#check @chooseThreadOnCoreLockSet_read_only
#check @chooseThreadOnCoreLockSet_contains_objStore_read
#check @chooseThreadOnCoreLockSet_contains_runQueue_read
#check @chooseThreadOnCoreLockSet_object_before_runQueue
#check @chooseThreadOnCoreLockSet_keys_nodup

-- SM5.A.3 — per-core-independence frame + corollaries.
#check @chooseThreadOnCore_frame
#check @chooseThreadOnCore_perCore_independence
#check @chooseThreadOnCore_independent_of_setRunQueueOnCore
#check @chooseThreadOnCore_independent_of_setActiveDomainOnCore
#check @chooseThreadOnCore_independent_of_setCurrentOnCore
#check @chooseThreadOnCore_independent_of_write_off_lockSet

-- SM5.A.4 — idle-fallback completeness + schedulerInvariant_perCore corollary.
#check @chooseThreadOnCore_ok_of_runnableTCBs
#check @chooseThreadOnCore_none_no_eligible
#check @chooseThreadOnCore_some_of_eligible
#check @chooseThreadOnCore_ok_of_schedulerInvariant

-- SM5.A.6 — selection soundness + preservation form + invariant corollary.
#check @chooseThreadOnCore_some_mem_runQueueOnCore
#check @chooseThread_preserves_runQueueOnCore_wellFormed
#check @chooseThreadOnCore_some_mem_of_schedulerInvariant

-- SM5.A.7 — decidable selection predicates.
#check @chooseThreadOnCoreSelects
#check @chooseThreadOnCoreIdleFallback

-- SM5.A.3 — selection optimality (§3.1.1) + literal preserves-wellFormed anchor.
#check @chooseThreadOnCore_selects_highest
#check @chooseThreadOnCore_preserves_wellFormed

-- SM5.A.2 — run-queue-lock total order + §4.4 level.
#check @RunQueueLockId.le
#check @RunQueueLockId.lt
#check @RunQueueLockId.le_refl
#check @RunQueueLockId.le_trans
#check @RunQueueLockId.le_antisymm
#check @RunQueueLockId.le_total
#check @RunQueueLockId.lt_irrefl
#check @RunQueueLockId.lt_asymm
#check @RunQueueLockId.runQueueLockLevel
#check @RunQueueLockId.objectLockLevels_lt_runQueueLockLevel

-- SM5.A §6 — budget-aware companion chooseThreadEffectiveOnCore.
#check @chooseThreadEffectiveOnCore
#check @chooseThreadEffective_eq_chooseThreadEffectiveOnCore_bootCore
#check @chooseThreadEffectiveOnCore_frame
#check @chooseThreadEffectiveOnCore_independent_of_setRunQueueOnCore
#check @chooseThreadEffectiveOnCore_ok_of_runnableTCBs
#check @chooseThreadEffectiveOnCore_some_mem_runQueueOnCore
#check @chooseThreadEffectiveOnCore_selected_has_budget
#check @chooseThreadEffectiveOnCore_none_no_eligible
#check @chooseThreadEffectiveOnCoreSelects
#check @chooseThreadEffectiveOnCoreIdleFallback

-- SM5.A §6 — budget selector complete footprint: object-store + run-queue.
#check @chooseThreadEffectiveOnCoreLockSet
#check @chooseThreadEffectiveOnCoreLockSet_eq
#check @chooseThreadEffectiveOnCoreLockSet_contains_objStore_read
#check @chooseThreadEffectiveOnCoreLockSet_contains_runQueue_read
#check @chooseThreadEffectiveOnCoreLockSet_read_only

-- SM5.A support: RunQueue.ofList well-formedness (production helper).
#check @SeLe4n.Kernel.RunQueue.ofList_wellFormed
EOF'

# WS-SM SM5.B — per-core switchToThread surface anchors.  Covers the SM5.B.4
# foundation (the `TCB.cpuAffinity` field + `KernelError.threadOnDifferentCore`),
# the SM5.B.1/.3/.4 production operations (`switchToThreadOnCore` /
# `preemptCurrentOnCore` / `affinityAdmitsCore`), the SM5.B.2 cross-domain
# lock-set + acquisition-order completeness, the preempt frame + preservation +
# unreachability lemmas, the SM5.B.1/.3/.4/.5/.6 switch-semantics theorems, the
# §3b invariant-preservation foundations, the SM5.B.8 complete classification +
# decidability, and the SM5.B.7 FFI seam (extern decls + typed wrappers +
# markers).  A rename / removal of any SM5.B
# symbol fails here at elaboration time, before SM5.C's cross-core wake / SGI
# dispatch loop consumes them.
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake build SeLe4n.Kernel.Scheduler.Operations.PerCoreSwitchToThread'
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake env lean --stdin <<"EOF"
import SeLe4n.Kernel.Scheduler.Operations.PerCoreSwitchToThread
import SeLe4n.Kernel.Concurrency.Runtime
open SeLe4n.Model
open SeLe4n.Kernel
open SeLe4n.Kernel.Concurrency

-- SM5.B.4 foundation: the per-thread CPU-affinity field + reject-remote error.
#check @TCB.cpuAffinity
#check @SeLe4n.Model.KernelError.threadOnDifferentCore

-- SM5.B.1/.3/.4 production operations (Scheduler.Operations.Selection).
#check @affinityAdmitsCore
#check @affinityAdmitsCore_none
#check @affinityAdmitsCore_some
#check @preemptCurrentOnCore
#check @switchToThreadOnCore

-- SM5.B.2 cross-domain lock-set.
#check @switchToThreadOnCoreLockSet
#check @switchToThreadOnCoreLockSet_length
#check @switchToThreadOnCoreLockSet_write_only
#check @switchToThreadOnCoreLockSet_contains_objStore_write
#check @switchToThreadOnCoreLockSet_contains_runQueue_write
#check @switchToThreadOnCoreLockSet_object_before_runQueue
#check @switchToThreadOnCoreLockSet_keys_nodup

-- §2/§2b preempt frame + preservation + unreachability lemmas.
#check @preemptCurrentOnCore_currentOnCore
#check @preemptCurrentOnCore_runQueueOnCore_ne
#check @preemptCurrentOnCore_runQueueOnCore_self_active
#check @preemptCurrentOnCore_preserves_objects_invExt
#check @preemptCurrentOnCore_preserves_runQueueOnCore_wellFormed
#check @preemptCurrentOnCore_active_under_valid

-- SM5.B.1/.3/.4/.5/.6 switch-semantics theorems.
#check @switchToThreadOnCore_sets_current
#check @switchToThreadOnCore_preempts_previous
#check @switchToThreadOnCore_rejects_remote
#check @switchToThreadOnCore_ok_of_admits
#check @switchToThreadOnCore_runQueueOnCore_excludes_current
#check @switchToThreadOnCore_independent_of_other_core

-- §3b invariant preservation + object frame (structural foundations for SM5.I.8).
#check @switchToThreadOnCore_preserves_objects_invExt
#check @switchToThreadOnCore_preserves_runQueueOnCore_wellFormed
#check @switchToThreadOnCore_establishes_queueCurrentConsistentOnCore
#check @switchToThreadOnCore_establishes_currentThreadValidOnCore
#check @preemptCurrentOnCore_getTcb?_incoming
#check @switchToThreadOnCore_objects_eq_preempt

-- §3c acquisition-order completeness (SM5.B.2).
#check @switchToThreadOnCoreLockSet_pairwise_le

-- SM5.B.8 complete classification + decidability.
#check @switchToThreadOnCore_ok_iff
#check @switchToThreadOnCoreSucceeds
#check @switchToThreadOnCoreRejectsRemote

-- SM5.B.7 FFI seam: extern decls + typed wrappers + markers.
#check @SeLe4n.Platform.FFI.ffiSwitchToThread
#check @SeLe4n.Platform.FFI.ffiPerCoreCurrentThread
#check @switchToThreadHw
#check @perCoreCurrentThreadHw
#check @switchToThreadHw_returns_baseio_uint64_marker
#check @perCoreCurrentThreadHw_returns_baseio_uint64_marker
-- WS-SM SM5.B (PR #805 review P2-2): fail-closed ThreadId encodability guard.
#check @switchToThreadHwTidBound
#check @switchToThreadHwRejected
#check @switchToThreadHw_rejects_unencodable
EOF'

# WS-SM SM5.C — cross-core wake via SGI surface anchors.  Covers the SM5.C
# production transitions (`enqueueRunnableOnCore` / `determineTargetCore` /
# `wakeThread` / `handleRescheduleSgiOnCore` / `setThreadCpuAffinity`), the
# SM5.C.3 cross-domain lock-sets, the SM5.C.9 determine-target routing, the
# SM5.C.1 enqueue lemmas, the SM5.C.2/.4/.10 wake-semantics theorems, the
# SM5.C.6 losslessness (`SchedStep` / `SchedReachable` / `wakeThread_lossless`),
# the SM5.C.5 SGI-handler theorems, the SM5.C.11 latency bound, the SM5.C.8
# affinity-control op, the decidability witnesses, and the SM5.C.4 SGI-emission
# typed wrappers.  A rename / removal of any SM5.C symbol fails here at
# elaboration time, before SM5.D's per-core timer tick consumes them.
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake build SeLe4n.Kernel.Scheduler.Operations.PerCoreWake'
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake build SeLe4n.Kernel.Scheduler.Operations.Sm5CInventory'
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake env lean --stdin <<"EOF"
import SeLe4n.Kernel.Scheduler.Operations.PerCoreWake
import SeLe4n.Kernel.Scheduler.Operations.Sm5CInventory
import SeLe4n.Kernel.Concurrency.Runtime
open SeLe4n.Model
open SeLe4n.Kernel
open SeLe4n.Kernel.Concurrency

-- SM5.C.1/.2/.5/.8/.9 production transitions (Scheduler.Operations.Selection).
#check @enqueueRunnableOnCore
#check @determineTargetCore
#check @wakeThread
#check @handleRescheduleSgiOnCore
#check @setThreadCpuAffinity

-- SM5.C.3 cross-domain lock-sets.
#check @wakeThreadLockSet
#check @wakeThreadLockSet_length
#check @wakeThreadLockSet_write_only
#check @wakeThreadLockSet_contains_objStore_write
#check @wakeThreadLockSet_contains_runQueue_write
#check @wakeThreadLockSet_object_before_runQueue
#check @wakeThreadLockSet_keys_nodup
#check @wakeThreadLockSet_pairwise_le
#check @handleRescheduleSgiOnCoreLockSet
#check @handleRescheduleSgiOnCoreLockSet_eq

-- SM5.C.9 determine-target routing.
#check @determineTargetCore_bound_eq_affinity
#check @determineTargetCore_unbound_eq_bootCore
#check @determineTargetCore_no_tcb_eq_bootCore
#check @determineTargetCore_in_range

-- SM5.C.1 enqueueRunnableOnCore lemmas.
#check @enqueueRunnableOnCore_preserves_objects_invExt
#check @enqueueRunnableOnCore_preserves_runQueueOnCore_wellFormed
#check @enqueueRunnableOnCore_mem_runQueueOnCore
#check @enqueueRunnableOnCore_makes_ready
#check @enqueueRunnableOnCore_runQueueOnCore_ne
#check @enqueueRunnableOnCore_currentOnCore
#check @enqueueRunnableOnCore_getTcb?_ne
#check @enqueueRunnableOnCore_no_tcb_noop

-- SM5.C.2/.4/.10 wake-semantics theorems.
#check @wakeThread_state_eq_enqueue
#check @wakeThread_emits_sgi_if_remote
#check @wakeThread_no_sgi_if_local
#check @wakeThread_sgi_is_reschedule
#check @wakeThread_target_runQueue_contains
#check @wakeThread_preserves_objects_invExt
#check @wakeThread_preserves_target_runQueue_wellFormed
#check @wakeThread_independent_of_other_core

-- SM5.C.6 losslessness.
#check @SchedStep
#check @SchedReachable
#check @SchedReachable.of_enqueue
#check @SchedReachable.trans
#check @wakeThread_lossless

-- SM5.C.5 SGI-handler theorems.
#check @handleRescheduleSgiOnCore_idle_when_none
#check @handleRescheduleSgiOnCore_eq_switch_of_choose_some
#check @handleRescheduleSgiOnCore_switches_current
#check @handleRescheduleSgiOnCore_preserves_objects_invExt
#check @handleRescheduleSgiOnCore_preserves_runQueueOnCore_wellFormed
#check @handleRescheduleSgiOnCore_independent_of_other_core

-- SM5.C.11 SGI delivery latency bound.
#check @wakeSgiCount
#check @wakeThread_emits_at_most_one_sgi
#check @rescheduleSgi_intid_eq_zero
#check @rescheduleSgi_lowest_intid
#check @sgiDeliveryLatencyBound
#check @sgiDeliveryLatencyBound_eq_zero

-- SM5.C.8 affinity-control op.
#check @setThreadCpuAffinity_ok_of_tcb
#check @setThreadCpuAffinity_error_of_no_tcb
#check @setThreadCpuAffinity_sets_affinity
#check @setThreadCpuAffinity_preserves_objects_invExt
#check @setThreadCpuAffinity_preserves_scheduler
#check @setThreadCpuAffinity_getTcb?_ne
#check @setThreadCpuAffinity_affects_determineTargetCore

-- SM5.C decidability witnesses.
#check @handleRescheduleSgiOnCoreSucceeds
#check @setThreadCpuAffinitySucceeds

-- SM5.C.4 SGI-emission typed wrappers (Concurrency.Runtime).
#check @coreIdTargetMask
#check @sgiIntidU8
#check @sendSgiToCore
#check @sendRescheduleSgi
#check @emitWakeSgi
#check @sendSgiToCore_eq_ffi
#check @sendRescheduleSgi_eq
#check @emitWakeSgi_none
#check @emitWakeSgi_some
#check @sgiIntidU8_reschedule
#check @coreIdTargetMask_bootCore

-- WS-SM SM5.C audit-pass-1: ghost-wake SGI guard (SM5.C.4).
#check @wakeThread_no_sgi_if_no_tcb

-- WS-SM SM5.C audit-pass-1 §10: invariant preservation (SM5.B-parity coverage).
#check @enqueueRunnableOnCore_getTcb?_isSome
#check @enqueueRunnableOnCore_preserves_currentThreadValidOnCore
#check @enqueueRunnableOnCore_preserves_queueCurrentConsistentOnCore_ne
#check @enqueueRunnableOnCore_preserves_queueCurrentConsistentOnCore_self
#check @enqueueRunnableOnCore_preserves_runnableThreadIpcReady
#check @enqueueRunnableOnCore_preserves_blockedOnSendNotRunnable
#check @enqueueRunnableOnCore_preserves_blockedOnReceiveNotRunnable
#check @enqueueRunnableOnCore_preserves_blockedOnCallNotRunnable
#check @enqueueRunnableOnCore_preserves_blockedOnReplyNotRunnable
#check @enqueueRunnableOnCore_preserves_blockedOnNotificationNotRunnable
#check @enqueueRunnableOnCore_preserves_ipcSchedulerContract
#check @wakeThread_preserves_currentThreadValidOnCore
#check @wakeThread_preserves_ipcSchedulerContract
#check @wakeThread_preserves_queueCurrentConsistentOnCore

-- WS-SM SM5.C audit-pass-1 §6b: multi-step wake→dispatch liveness.
#check @wakeThread_then_handle_dispatches_current
#check @wakeThread_roundtrip_reachable_current

-- WS-SM SM5.C audit-pass-1 SM5.C.11: honest latency-bound scoping.
#check @sgiDeliveryLatencyBound_counts_higher_priority_kernel_sgis

-- WS-SM SM5.C audit-pass-1 §11: memory-model happens-before (BKL ordering).
#check @SeLe4n.Kernel.Concurrency.wakeReleaseEvent
#check @SeLe4n.Kernel.Concurrency.wakeAcquireEvent
#check @SeLe4n.Kernel.Concurrency.wakeOrderingTrace
#check @SeLe4n.Kernel.Concurrency.wakeOrderingTrace_wellFormed
#check @SeLe4n.Kernel.Concurrency.wakeOrdering_synchronizesWith
#check @SeLe4n.Kernel.Concurrency.wakeOrdering_happensBefore

-- WS-SM SM5.C audit-pass-1 (gap m): the SM5.C theorem inventory.
#check @sm5CTheorems
#check @sm5CTheorems_count
#check @sm5CTheorems_lockSet_count
#check @sm5CTheorems_target_count
#check @sm5CTheorems_enqueue_count
#check @sm5CTheorems_wake_count
#check @sm5CTheorems_handler_count
#check @sm5CTheorems_preservation_count
#check @sm5CTheorems_latencyAffinityEmit_count
#check @sm5CTheorems_partition_sum
#check @sm5CTheorems_identifiers_nodup
#check @sm5CTheorems_descriptions_nodup
EOF'

finalize_report
