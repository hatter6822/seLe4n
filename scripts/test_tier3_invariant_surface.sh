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

# --------------------------------------------------------------------------
# Build prerequisite: the staged-module closure.
#
# Most Tier 3 checks are `rg` name searches over the source tree, which need
# no build.  A minority elaborate a small probe file (`lake env lean`) whose
# `#check`s resolve the anchored symbols — and `lake env lean` only *reads*
# `.olean`s, it never builds them.  Those probes import staged modules
# (`scripts/staged_module_allowlist.txt`), which sit outside the default
# `lake build` target (`defaultTargets = ["sele4n"]`, root `Main`) and are
# materialised only by the separate `SeLe4n.Platform.Staged` anchor target.
#
# Tier 1 builds both, so the full `test_full.sh` chain happened to satisfy
# this — but a *standalone* Tier 3 run (which the script header invites) had
# no such guarantee, and failed with "object file ... does not exist" rather
# than a genuine anchor regression.  Building the anchor here makes the gate
# self-sufficient and order-independent; it is a fast no-op replay whenever
# Tier 1 has already run.
#
# `ensure_lake_available` first (as Tier 2 does): the gate has always needed a
# toolchain for its `#check` probes, and resolving that here reports a missing
# `lake` once, by name, instead of as an opaque command-not-found several
# hundred checks later.
# --------------------------------------------------------------------------
ensure_lake_available
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake build SeLe4n.Platform.Staged'

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
run_prose_check "INVARIANT" rg -n 'WS-C3 proof-surface note:' SeLe4n/Kernel/Architecture/VSpace.lean
run_check "INVARIANT" bash -lc "! rg -n '^theorem projectState_deterministic' SeLe4n/Kernel/InformationFlow/Projection.lean"
run_prose_check "INVARIANT" rg -n 'WS-C3 proof-surface note:' SeLe4n/Kernel/InformationFlow/Projection.lean
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
run_prose_check "INVARIANT" rg -n '^/-!' SeLe4n/Kernel/Scheduler/Invariant.lean
run_prose_check "INVARIANT" rg -n '^/-!' SeLe4n/Kernel/IPC/Invariant.lean
run_prose_check "INVARIANT" rg -n '^/-!' SeLe4n/Kernel/Capability/Invariant.lean
run_prose_check "INVARIANT" rg -n '^/-!' SeLe4n/Kernel/Lifecycle/Invariant.lean
run_prose_check "INVARIANT" rg -n '^/-!' SeLe4n/Kernel/InformationFlow/Invariant.lean
run_prose_check "INVARIANT" rg -n '^/-!' SeLe4n/Kernel/Service/Invariant.lean
run_prose_check "INVARIANT" rg -n '^/-!' SeLe4n/Kernel/Architecture/Invariant.lean

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
run_prose_check "TRACE" rg -n 'Service registry projection' tests/InformationFlowSuite.lean
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
# WS-SM SM6.D per-core IPC invariant bundle anchors — the four named per-core
# conjuncts (D.3-D.6), the twenty-field aggregate (D.1) + SMP form + exact
# decomposition, the home-core restriction, and the six per-operation
# preservation theorems (D.2) + the cross-core call flagship (staged).
run_check "INVARIANT" rg -n '^def threadHomeCore' SeLe4n/Kernel/IPC/Invariant/PerCoreBundle.lean
run_check "INVARIANT" rg -n '^def ipcStateQueueMembershipConsistent_perCore' SeLe4n/Kernel/IPC/Invariant/PerCoreBundle.lean
run_check "INVARIANT" rg -n '^def endpointQueueNoDup_perCore' SeLe4n/Kernel/IPC/Invariant/PerCoreBundle.lean
run_check "INVARIANT" rg -n '^def queueNextBlockingConsistent_perCore' SeLe4n/Kernel/IPC/Invariant/PerCoreBundle.lean
run_check "INVARIANT" rg -n '^def queueHeadBlockedConsistent_perCore' SeLe4n/Kernel/IPC/Invariant/PerCoreBundle.lean
run_check "INVARIANT" rg -n '^structure ipcInvariantFull_perCore' SeLe4n/Kernel/IPC/Invariant/PerCoreBundle.lean
run_check "INVARIANT" rg -n '^def ipcInvariantFull_smp' SeLe4n/Kernel/IPC/Invariant/PerCoreBundle.lean
run_check "INVARIANT" rg -n '^theorem ipcInvariantFull_smp_iff_full_and_passive_smp' SeLe4n/Kernel/IPC/Invariant/PerCoreBundle.lean
run_check "INVARIANT" rg -n '^theorem ipcStateQueueMembershipConsistent_smp_iff' SeLe4n/Kernel/IPC/Invariant/PerCoreBundle.lean
run_check "INVARIANT" rg -n '^theorem endpointQueueNoDup_smp_iff' SeLe4n/Kernel/IPC/Invariant/PerCoreBundle.lean
run_check "INVARIANT" rg -n '^theorem queueNextBlockingConsistent_smp_iff' SeLe4n/Kernel/IPC/Invariant/PerCoreBundle.lean
run_check "INVARIANT" rg -n '^theorem queueHeadBlockedConsistent_smp_iff' SeLe4n/Kernel/IPC/Invariant/PerCoreBundle.lean
run_check "INVARIANT" rg -n '^theorem default_ipcInvariantFull_smp' SeLe4n/Kernel/IPC/Invariant/PerCoreBundle.lean
run_check "INVARIANT" rg -n '^structure passiveServerIdleFrameOnCore' SeLe4n/Kernel/IPC/Invariant/PerCoreBundlePreservation.lean
run_check "INVARIANT" rg -n '^theorem determineTargetCore_eq_threadHomeCore' SeLe4n/Kernel/IPC/Invariant/PerCoreBundlePreservation.lean
run_check "INVARIANT" rg -n '^theorem endpointSendDual_preserves_ipcInvariantFull_perCore' SeLe4n/Kernel/IPC/Invariant/PerCoreBundlePreservation.lean
run_check "INVARIANT" rg -n '^theorem endpointReceiveDual_preserves_ipcInvariantFull_perCore' SeLe4n/Kernel/IPC/Invariant/PerCoreBundlePreservation.lean
run_check "INVARIANT" rg -n '^theorem endpointCall_preserves_ipcInvariantFull_perCore' SeLe4n/Kernel/IPC/Invariant/PerCoreBundlePreservation.lean
run_check "INVARIANT" rg -n '^theorem endpointReply_preserves_ipcInvariantFull_perCore' SeLe4n/Kernel/IPC/Invariant/PerCoreBundlePreservation.lean
run_check "INVARIANT" rg -n '^theorem endpointReplyRecv_preserves_ipcInvariantFull_perCore' SeLe4n/Kernel/IPC/Invariant/PerCoreBundlePreservation.lean
run_check "INVARIANT" rg -n '^theorem notificationSignal_preserves_ipcInvariantFull_perCore' SeLe4n/Kernel/IPC/Invariant/PerCoreBundlePreservation.lean
run_check "INVARIANT" rg -n '^theorem notificationWait_preserves_ipcInvariantFull_perCore' SeLe4n/Kernel/IPC/Invariant/PerCoreBundlePreservation.lean
run_check "INVARIANT" rg -n '^theorem endpointCallOnCore_preserves_ipcInvariantFull_perCore' SeLe4n/Kernel/IPC/CrossCore/EndpointCallInvariant.lean
# WS-SM SM6.D completion — lookup-congruence transfer layer, boot-frame
# exactness, the cross-core (OnCore) whole-bundle closures + per-core
# flagships for notification/reply/receive/replyRecv (production), and the
# capability-carrying (WithCaps) trio behind the live `.send` dispatch.
run_check "INVARIANT" rg -n '^theorem ipcInvariantFull_of_getElem_eq' SeLe4n/Kernel/IPC/Invariant/LookupCongruence.lean
run_check "INVARIANT" rg -n '^structure OffSchedulerAgrees' SeLe4n/Kernel/IPC/Invariant/LookupCongruence.lean
run_check "INVARIANT" rg -n '^theorem wakeThread_offSchedulerAgrees_of_ready' SeLe4n/Kernel/IPC/Invariant/LookupCongruence.lean
run_check "INVARIANT" rg -n '^theorem consumeCallerReply_offSchedulerAgrees' SeLe4n/Kernel/IPC/Invariant/LookupCongruence.lean
run_check "INVARIANT" rg -n '^theorem passiveServerIdleFrameOnCore_boot_iff' SeLe4n/Kernel/IPC/Invariant/PerCoreBundlePreservation.lean
run_check "INVARIANT" rg -n '^theorem notificationSignalOnCore_post_agrees' SeLe4n/Kernel/IPC/CrossCore/NotificationInvariant.lean
run_check "INVARIANT" rg -n '^theorem notificationSignalOnCore_preserves_ipcInvariantFull_perCore' SeLe4n/Kernel/IPC/CrossCore/NotificationInvariant.lean
run_check "INVARIANT" rg -n '^theorem notificationWaitOnCore_preserves_ipcInvariantFull_perCore' SeLe4n/Kernel/IPC/CrossCore/NotificationInvariant.lean
run_check "INVARIANT" rg -n '^theorem endpointReplyOnCore_post_agrees' SeLe4n/Kernel/IPC/CrossCore/EndpointReplyInvariant.lean
run_check "INVARIANT" rg -n '^theorem endpointReplyOnCore_preserves_ipcInvariantFull_perCore' SeLe4n/Kernel/IPC/CrossCore/EndpointReplyInvariant.lean
run_check "INVARIANT" rg -n '^theorem endpointReceiveDualOnCore_post_agrees' SeLe4n/Kernel/IPC/CrossCore/EndpointReplyInvariant.lean
run_check "INVARIANT" rg -n '^theorem endpointReceiveDualOnCore_preserves_ipcInvariantFull_perCore' SeLe4n/Kernel/IPC/CrossCore/EndpointReplyInvariant.lean
run_check "INVARIANT" rg -n '^theorem endpointReplyOnCore_reuse_freshens' SeLe4n/Kernel/IPC/CrossCore/EndpointReplyInvariant.lean
run_check "INVARIANT" rg -n '^theorem endpointReplyRecvOnCore_preserves_ipcInvariantFull_perCore' SeLe4n/Kernel/IPC/CrossCore/EndpointReplyInvariant.lean
run_check "INVARIANT" rg -n '^theorem ipcUnwrapCaps_passiveServerIdleFrameOnCore' SeLe4n/Kernel/IPC/Invariant/PerCoreBundlePreservation.lean
run_check "INVARIANT" rg -n '^theorem endpointSendDualWithCaps_preserves_ipcInvariantFull_perCore' SeLe4n/Kernel/IPC/Invariant/PerCoreBundlePreservation.lean
run_check "INVARIANT" rg -n '^theorem endpointReceiveDualWithCaps_preserves_ipcInvariantFull_perCore' SeLe4n/Kernel/IPC/Invariant/PerCoreBundlePreservation.lean
run_check "INVARIANT" rg -n '^theorem endpointCallWithCaps_preserves_ipcInvariantFull_perCore' SeLe4n/Kernel/IPC/Invariant/PerCoreBundlePreservation.lean
# WS-SM SM6.E cancellation across cores — the per-core deschedule primitive
# (the wakeThread dual), the cross-core cancellation composite + its SGI
# family, the per-core donation-cancellation arms + home-core replenish
# purge, the lockSet_cancelIpcBlocking / lockSet_cancelDonation footprints
# (+ suspend-footprint coverage incl. the SM6.E consumed-Reply extension),
# the 2PL atomicity theorems, invExt preservation, and the flagship.
run_check "INVARIANT" rg -n '^def descheduleThread' SeLe4n/Kernel/IPC/CrossCore/Cancellation.lean
run_check "INVARIANT" rg -n '^def cancelIpcBlockingOnCore' SeLe4n/Kernel/IPC/CrossCore/Cancellation.lean
run_check "INVARIANT" rg -n '^def cancelBoundDonationOnCore' SeLe4n/Kernel/IPC/CrossCore/Cancellation.lean
run_check "INVARIANT" rg -n '^def cancelDonationOnCore' SeLe4n/Kernel/IPC/CrossCore/Cancellation.lean
run_check "INVARIANT" rg -n '^def lockSet_cancelIpcBlocking' SeLe4n/Kernel/IPC/CrossCore/Cancellation.lean
run_check "INVARIANT" rg -n '^def lockSet_cancelDonation' SeLe4n/Kernel/IPC/CrossCore/Cancellation.lean
run_check "INVARIANT" rg -n '^theorem descheduleThread_emits_sgi_if_remote_current' SeLe4n/Kernel/IPC/CrossCore/Cancellation.lean
run_check "INVARIANT" rg -n '^theorem cancelIpcBlockingOnCore_emits_sgi_if_remote_current' SeLe4n/Kernel/IPC/CrossCore/Cancellation.lean
run_check "INVARIANT" rg -n '^theorem cancelIpcBlockingOnCore_no_sgi_if_not_current' SeLe4n/Kernel/IPC/CrossCore/Cancellation.lean
run_check "INVARIANT" rg -n '^theorem lockSet_consistent_cancelIpcBlocking' SeLe4n/Kernel/IPC/CrossCore/Cancellation.lean
run_check "INVARIANT" rg -n '^theorem lockSet_consistent_cancelDonation' SeLe4n/Kernel/IPC/CrossCore/Cancellation.lean
run_check "INVARIANT" rg -n '^theorem mem_insertOrMerge_write_of_mem_write' SeLe4n/Kernel/Concurrency/Locks/LockSet.lean
run_check "INVARIANT" rg -n '^theorem lockSet_tcbSuspend_consumed_reply_write_mem' SeLe4n/Kernel/IPC/CrossCore/Cancellation.lean
run_check "INVARIANT" rg -n '^theorem cancelIpcBlocking_atomic_under_lockSet' SeLe4n/Kernel/IPC/CrossCore/Cancellation.lean
run_check "INVARIANT" rg -n '^theorem cancelIpcBlockingOnCore_atomic_under_lockSet' SeLe4n/Kernel/IPC/CrossCore/Cancellation.lean
run_check "INVARIANT" rg -n '^theorem cancelDonation_atomic_under_lockSet' SeLe4n/Kernel/IPC/CrossCore/Cancellation.lean
run_check "INVARIANT" rg -n '^theorem cancelDonationOnCore_atomic_under_lockSet' SeLe4n/Kernel/IPC/CrossCore/Cancellation.lean
run_check "INVARIANT" rg -n '^theorem cancelIpcBlockingOnCore_preserves_objects_invExt' SeLe4n/Kernel/IPC/CrossCore/Cancellation.lean
run_check "INVARIANT" rg -n '^theorem cancelBoundDonationOnCore_replenishQueue_purged' SeLe4n/Kernel/IPC/CrossCore/Cancellation.lean
run_check "INVARIANT" rg -n '^theorem cancellation_cross_core_correct' SeLe4n/Kernel/IPC/CrossCore/Cancellation.lean
run_check "INVARIANT" rg -n '^theorem cancelIpcBlocking_preserves_objects_invExt' SeLe4n/Kernel/Lifecycle/Invariant/SuspendPreservation.lean
run_check "INVARIANT" rg -n '^theorem cancelDonation_preserves_objects_invExt' SeLe4n/Kernel/Lifecycle/Invariant/SuspendPreservation.lean
run_check "INVARIANT" rg -n '^theorem removeFromAllEndpointQueues_preserves_objects_invExt' SeLe4n/Kernel/Lifecycle/Operations/CleanupPreservation.lean
run_check "INVARIANT" rg -n '^def runSmpCancellationChecks' tests/SmpCancellationSuite.lean
run_check "INVARIANT" rg -n '^run_check(_with_timeout)? "TRACE" lake exe smp_cancellation_suite' scripts/test_tier2_negative.sh

# WS-SM SM6.F tests + fixtures — the aggregate cross-core IPC / notification
# suites (the acceptance-gate 2-thread cross-core IPC + 4-thread SMP rendezvous
# deliverables), their Tier-2 wiring, the smp_ipc_4core golden trace fixture
# (+ sha256 companion) they verify byte-for-byte, the multi-step round-trip
# pipeline + trace emitters inside the IPC suite, the lakefile exe
# registrations, and the Tier-4 QEMU cross-core IPC handshake exerciser.
run_check "INVARIANT" rg -n '^def runSmpIpcChecks' tests/SmpIpcSuite.lean
run_check "INVARIANT" rg -n '^run_check(_with_timeout)? "TRACE" lake exe smp_ipc_suite' scripts/test_tier2_negative.sh
run_check "INVARIANT" rg -n '^def runSmpNotificationChecks' tests/SmpNotificationSuite.lean
run_check "INVARIANT" rg -n '^run_check(_with_timeout)? "TRACE" lake exe smp_notification_suite' scripts/test_tier2_negative.sh
run_check "INVARIANT" rg -n '^private def roundTrip\?' tests/SmpIpcSuite.lean
run_check "INVARIANT" rg -n '^private def ipcFourCoreTraceLines' tests/SmpIpcSuite.lean
run_check "INVARIANT" rg -n '^private def ntfnRoundTrip\?' tests/SmpNotificationSuite.lean
run_check "INVARIANT" rg -n '^\[smp-ipc-4core\]' tests/fixtures/smp_ipc_4core.expected
run_check "INVARIANT" rg -n 'smp_ipc_4core\.expected' tests/fixtures/smp_ipc_4core.expected.sha256
run_check "INVARIANT" rg -n '^name = "smp_ipc_suite"' lakefile.toml
run_check "INVARIANT" rg -n '^name = "smp_notification_suite"' lakefile.toml
run_check "INVARIANT" rg -n 'test_qemu_smp_ipc\.sh' scripts/test_tier4_smp_bootcheck.sh
# The QEMU exerciser's driver-detection guard and its pass gate must agree on the
# `cross-core-ipc` banner tag (the contract the future SM9.E kernel-image driver
# emits); anchoring the exact pass phrase catches a silent drift between the two.
run_check "INVARIANT" rg -n 'cross-core-ipc: reply delivered across cores' scripts/test_qemu_smp_ipc.sh
# The new aggregate scenario groups (donation / caps / info-flow / live-API /
# cancellation×IPC / contention in the IPC suite; three-waiter drain + checked
# dispatch in the notification suite) — anchored so a rename breaks Tier-3.
run_check "INVARIANT" rg -n '^private def runDonationChecks' tests/SmpIpcSuite.lean
run_check "INVARIANT" rg -n '^private def runCapTransferChecks' tests/SmpIpcSuite.lean
run_check "INVARIANT" rg -n '^private def runFlowCheckedChecks' tests/SmpIpcSuite.lean
run_check "INVARIANT" rg -n '^private def runLiveApiChecks' tests/SmpIpcSuite.lean
run_check "INVARIANT" rg -n '^private def runCancellationCompositionChecks' tests/SmpIpcSuite.lean
run_check "INVARIANT" rg -n '^private def runHandlerContentionChecks' tests/SmpIpcSuite.lean
run_check "INVARIANT" rg -n '^private def runThreeWaiterDrainChecks' tests/SmpNotificationSuite.lean
run_check "INVARIANT" rg -n '^private def runCheckedDispatchChecks' tests/SmpNotificationSuite.lean
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

# WS-SM SM7.A — TLB shootdown descriptor + per-core pending/ack state: the
# staged state module (descriptor, state, path-a accessors, enqueue / drain /
# acknowledge / round-open operations, the maxPendingPerCore capacity bound +
# its preservation theorems, the fold-to-allAcked wait-loop-termination
# anchor), the staged-partition registration, the Rust SHOOTDOWN_ACK per-core
# AtomicBool realisation, the SmpTlbShootdownSuite runner + its Tier-2 wiring
# + lakefile registration.
run_check "INVARIANT" rg -n '^structure TlbShootdownDescriptor' SeLe4n/Kernel/Architecture/TlbShootdown.lean
run_check "INVARIANT" rg -n '^structure TlbShootdownState' SeLe4n/Kernel/Architecture/TlbShootdown.lean
run_check "INVARIANT" rg -n '^def maxPendingPerCore : Nat := 16' SeLe4n/Kernel/Architecture/TlbShootdown.lean
run_check "INVARIANT" rg -n '^def enqueueShootdown' SeLe4n/Kernel/Architecture/TlbShootdown.lean
run_check "INVARIANT" rg -n '^def drainShootdowns' SeLe4n/Kernel/Architecture/TlbShootdown.lean
run_check "INVARIANT" rg -n '^def acknowledgeShootdown' SeLe4n/Kernel/Architecture/TlbShootdown.lean
run_check "INVARIANT" rg -n '^def beginShootdownRound' SeLe4n/Kernel/Architecture/TlbShootdown.lean
run_check "INVARIANT" rg -n '^def pendingBounded' SeLe4n/Kernel/Architecture/TlbShootdown.lean
run_check "INVARIANT" rg -n '^theorem enqueueShootdown_preserves_pendingBounded' SeLe4n/Kernel/Architecture/TlbShootdown.lean
run_check "INVARIANT" rg -n '^theorem drainShootdowns_after_enqueue' SeLe4n/Kernel/Architecture/TlbShootdown.lean
run_check "INVARIANT" rg -n '^theorem allCores_foldl_acknowledgeShootdown_allAcked' SeLe4n/Kernel/Architecture/TlbShootdown.lean
run_check "INVARIANT" rg -n '^theorem beginShootdownRound_ackOnCore_iff' SeLe4n/Kernel/Architecture/TlbShootdown.lean
# (v0.32.73: TlbShootdown was PROMOTED to production — Model/State.lean
# mounts it — so it must NOT reappear in the staged allowlist.
# SM7.B: TlbiForSharing was ALSO promoted — the live
# completeShootdownRounds seam is its first runtime exerciser — so its
# allowlist line is GONE too (anchored negatively via the count below);
# both Staged.lean imports are retained for graph continuity.)
run_check "INVARIANT" bash -c "! rg -q '^SeLe4n\.Kernel\.Architecture\.TlbiForSharing' scripts/staged_module_allowlist.txt"
run_check "INVARIANT" rg -n '^import SeLe4n\.Kernel\.Architecture\.TlbiForSharing' SeLe4n.lean
run_check "INVARIANT" rg -n '^import SeLe4n\.Kernel\.Architecture\.TlbShootdown' SeLe4n/Platform/Staged.lean
run_check "INVARIANT" rg -n '^pub static SHOOTDOWN_ACK' rust/sele4n-hal/src/shootdown.rs
run_check "INVARIANT" rg -n '^pub fn ack_round' rust/sele4n-hal/src/shootdown.rs
run_check "INVARIANT" rg -n '^pub mod shootdown;' rust/sele4n-hal/src/lib.rs
run_check "INVARIANT" rg -n '^def runSmpTlbShootdownChecks' tests/SmpTlbShootdownSuite.lean
run_check "INVARIANT" rg -n '^run_check(_with_timeout)? "TRACE" lake exe smp_tlb_shootdown_suite' scripts/test_tier2_negative.sh
run_check "INVARIANT" rg -n '^name = "smp_tlb_shootdown_suite"' lakefile.toml
# WS-SM SM7.B — the shootdown protocol surface: the three production
# protocol modules + their SeLe4n.lean registration, the headline
# Theorem 3.3.1 and the round corollaries, the initiator-side
# synchronization/termination/timeout theorems, the cross-domain
# lock-set, the live dispatch wiring (shootdown-aware vspace/retype
# arms + the completeShootdownRounds runtime seam + the cooperative
# round-lock acquire), and the Rust realisation (round try-lock,
# bounded wait, boot-registered .tlbShootdownReq handler, online mask,
# full-IAR SGI dispatch).
run_check "INVARIANT" rg -n '^import SeLe4n\.Kernel\.Architecture\.TlbShootdownProtocol' SeLe4n.lean
run_check "INVARIANT" rg -n '^import SeLe4n\.Kernel\.Architecture\.TlbShootdownWait' SeLe4n.lean
run_check "INVARIANT" rg -n '^import SeLe4n\.Kernel\.Architecture\.TlbShootdownLockSet' SeLe4n.lean
run_check "INVARIANT" rg -n '^def tlbShootdownLocal' SeLe4n/Kernel/Architecture/TlbShootdownProtocol.lean
run_check "INVARIANT" rg -n '^def tlbShootdownBroadcast' SeLe4n/Kernel/Architecture/TlbShootdownProtocol.lean
run_check "INVARIANT" rg -n '^def handleTlbShootdownReqOnCore' SeLe4n/Kernel/Architecture/TlbShootdownProtocol.lean
run_check "INVARIANT" rg -n '^theorem tlbShootdownBroadcast_invalidatesAllCores' SeLe4n/Kernel/Architecture/TlbShootdownProtocol.lean
run_check "INVARIANT" rg -n '^theorem tlbShootdownBroadcast_posts_singleton' SeLe4n/Kernel/Architecture/TlbShootdownProtocol.lean
run_check "INVARIANT" rg -n '^theorem shootdownRound_quiescent' SeLe4n/Kernel/Architecture/TlbShootdownProtocol.lean
run_check "INVARIANT" rg -n '^theorem shootdownRound_tlb_no_matching_entry' SeLe4n/Kernel/Architecture/TlbShootdownProtocol.lean
run_check "INVARIANT" rg -n '^theorem tlbShootdown_outer_correct' SeLe4n/Kernel/Architecture/TlbShootdownProtocol.lean
run_check "INVARIANT" rg -n '^def vspaceUnmapPageWithShootdown' SeLe4n/Kernel/Architecture/TlbShootdownProtocol.lean
run_check "INVARIANT" rg -n '^def asidAllocateWithShootdown' SeLe4n/Kernel/Architecture/TlbShootdownProtocol.lean
run_check "INVARIANT" rg -n 'vspaceUnmapPageWithShootdown' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n 'vspaceMapPageCheckedWithShootdownFromState' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n 'lifecycleRetypeDirectWithCleanupShootdown' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n '^def lifecycleRetypeDirectWithCleanupShootdown' SeLe4n/Kernel/Lifecycle/Operations/RetypeWrappers.lean
run_check "INVARIANT" rg -n '^theorem shootdownAck_release_acquire' SeLe4n/Kernel/Architecture/TlbShootdownWait.lean
run_check "INVARIANT" rg -n '^theorem shootdown_wait_loop_terminates' SeLe4n/Kernel/Architecture/TlbShootdownWait.lean
run_check "INVARIANT" rg -n '^theorem shootdown_timeout_handling' SeLe4n/Kernel/Architecture/TlbShootdownWait.lean
run_check "INVARIANT" rg -n '^inductive TlbShootdownLockId' SeLe4n/Kernel/Architecture/TlbShootdownLockSet.lean
run_check "INVARIANT" rg -n '^theorem lockSet_tlbShootdown_correct' SeLe4n/Kernel/Architecture/TlbShootdownLockSet.lean
run_check "INVARIANT" rg -n '^theorem lockSet_tlbShootdown_covers_commit' SeLe4n/Kernel/Architecture/TlbShootdownLockSet.lean
run_check "INVARIANT" rg -n '^def completeShootdownRounds' SeLe4n/Kernel/SyscallDispatchEntry.lean
run_check "INVARIANT" rg -n '^def acquireShootdownRoundLockServicingSelf' SeLe4n/Kernel/SyscallDispatchEntry.lean
run_check "INVARIANT" rg -n 'completeShootdownRounds result' SeLe4n/Kernel/SyscallDispatchEntry.lean
run_check "INVARIANT" rg -n '^pub static SHOOTDOWN_ROUND_LOCK' rust/sele4n-hal/src/shootdown.rs
run_check "INVARIANT" rg -n '^pub fn wait_all_acked_bounded' rust/sele4n-hal/src/shootdown.rs
run_check "INVARIANT" rg -n '^pub fn tlb_shootdown_req_handler' rust/sele4n-hal/src/shootdown.rs
run_check "INVARIANT" rg -n 'register_tlb_shootdown_handler' rust/sele4n-hal/src/boot.rs
run_check "INVARIANT" rg -n '^pub fn dispatch_irq_with_iar' rust/sele4n-hal/src/gic.rs
run_check "INVARIANT" rg -n 'dispatch_sgi\(intid as u8, source_cpu\)' rust/sele4n-hal/src/trap.rs
run_check "INVARIANT" rg -n '^private def runProtocolRoundChecks' tests/SmpTlbShootdownSuite.lean
run_check "INVARIANT" rg -n '^private def runCallerWrapperChecks' tests/SmpTlbShootdownSuite.lean
# SM7.A completion cut — the pure operand module (extracted from the staged
# TlbiForSharing so Model/State can mount the shootdown state), the
# SystemState mount + default-state theorems, the capacity-sufficiency +
# coalescing + round-quiescence surface, the pending-queue lock identifier,
# and the ack-flag FFI seam (Rust exports + Lean externs + typed wrappers).
run_check "INVARIANT" rg -n '^inductive TlbInvalidation' SeLe4n/Kernel/Architecture/TlbInvalidation.lean
run_check "INVARIANT" rg -n '^import SeLe4n\.Kernel\.Architecture\.TlbShootdown' SeLe4n/Model/State.lean
run_check "INVARIANT" rg -n '^  tlbShootdown : SeLe4n\.Kernel\.Architecture\.TlbShootdownState' SeLe4n/Model/State.lean
run_check "INVARIANT" rg -n '^theorem default_tlbShootdown_initial' SeLe4n/Model/State.lean
run_check "INVARIANT" rg -n '^theorem default_tlbShootdown_quiescent' SeLe4n/Model/State.lean
run_check "INVARIANT" rg -n '^theorem foldlM_enqueueShootdown_isSome' SeLe4n/Kernel/Architecture/TlbShootdown.lean
run_check "INVARIANT" rg -n '^def enqueueShootdownOrCoalesce' SeLe4n/Kernel/Architecture/TlbShootdown.lean
run_check "INVARIANT" rg -n '^theorem enqueueShootdownOrCoalesce_preserves_pendingBounded' SeLe4n/Kernel/Architecture/TlbShootdown.lean
run_check "INVARIANT" rg -n '^def completeShootdownOnCore' SeLe4n/Kernel/Architecture/TlbShootdown.lean
run_check "INVARIANT" rg -n '^theorem shootdownRound_restores_quiescent' SeLe4n/Kernel/Architecture/TlbShootdown.lean
run_check "INVARIANT" rg -n '^structure ShootdownQueueLockId' SeLe4n/Kernel/Architecture/TlbShootdown.lean
# SM7.A audit cut — the global round-lock seam (round-serialisation contract)
# and the full-queue coverage theorem for the coalescing enqueue.
run_check "INVARIANT" rg -n '^structure ShootdownRoundLockId' SeLe4n/Kernel/Architecture/TlbShootdown.lean
run_check "INVARIANT" rg -n '^theorem ShootdownRoundLockId\.singleton' SeLe4n/Kernel/Architecture/TlbShootdown.lean
run_check "INVARIANT" rg -n '^theorem enqueueShootdownOrCoalesce_pending_covered' SeLe4n/Kernel/Architecture/TlbShootdown.lean
run_prose_check "INVARIANT" rg -n 'Round serialisation contract' SeLe4n/Kernel/Architecture/TlbShootdown.lean
# SM7.A PR #838 review P1 — offline-core-aware round open: the Rust
# online-masked WAIT (SM7.F.3 turned the masked reset into a masked wait, which
# is where the mask belongs once acknowledgments carry the round generation)
# + the Lean target-masked round-open and its hcov-free capstone.
run_check "INVARIANT" rg -n '^pub fn all_acked_for_round_in_slice' rust/sele4n-hal/src/shootdown.rs
run_check "INVARIANT" rg -n '^def beginShootdownRoundFor' SeLe4n/Kernel/Architecture/TlbShootdown.lean
run_check "INVARIANT" rg -n '^theorem beginShootdownRoundFor_allCores_eq' SeLe4n/Kernel/Architecture/TlbShootdown.lean
# WS-SM SM7.B completion cut — invariant-bundle carriage (pendingBounded as
# the 12th proofLayerInvariantBundle conjunct + preservation across every live
# shootdown-aware transition and the boot bridge), handler commutativity, the
# coalescing-round capstones, the positive diff characterization, remap-only
# map rounds (ok-implies-fresh), the vmalle1 operand collapse, the least-index
# wait, the round-lock CAS model + cross-round publication (with the 4-core
# multi-pair witness), the CSpaceAddr retype-with-shootdown sibling, and the
# Rust test-hardening (_in handler form + genuine-transition tests + the
# multithreaded CAS mutex stress).
run_check "INVARIANT" rg -n 'pendingBounded st\.tlbShootdown' SeLe4n/Kernel/Architecture/Invariant.lean
run_check "INVARIANT" rg -n '^theorem completeShootdownOnCore_preserves_pendingBounded' SeLe4n/Kernel/Architecture/TlbShootdown.lean
run_check "INVARIANT" rg -n '^theorem completeShootdownOnCore_comm' SeLe4n/Kernel/Architecture/TlbShootdown.lean
run_check "INVARIANT" rg -n '^theorem withShootdownRound_preserves_pendingBounded' SeLe4n/Kernel/Architecture/TlbShootdownProtocol.lean
run_check "INVARIANT" rg -n '^theorem vspaceUnmapPageWithShootdown_preserves_pendingBounded' SeLe4n/Kernel/Architecture/TlbShootdownProtocol.lean
run_check "INVARIANT" rg -n '^theorem handleTlbShootdownReqOnCore_comm' SeLe4n/Kernel/Architecture/TlbShootdownProtocol.lean
run_check "INVARIANT" rg -n '^theorem coalescingRound_restores_quiescent' SeLe4n/Kernel/Architecture/TlbShootdownProtocol.lean
run_check "INVARIANT" rg -n '^theorem shootdownChangedTargets_coalescing_of_quiescent' SeLe4n/Kernel/Architecture/TlbShootdownProtocol.lean
run_check "INVARIANT" rg -n '^theorem vspaceUnmapPageWithShootdown_remote_retire_removes' SeLe4n/Kernel/Architecture/TlbShootdownProtocol.lean
run_check "INVARIANT" rg -n '^def vspaceHasTranslation' SeLe4n/Kernel/Architecture/TlbShootdownProtocol.lean
run_check "INVARIANT" rg -n '^theorem vspaceMapPageCheckedWithFlushFromState_ok_fresh' SeLe4n/Kernel/Architecture/TlbShootdownProtocol.lean
run_check "INVARIANT" rg -n '^def collapseShootdownOps' SeLe4n/Kernel/Architecture/TlbShootdownProtocol.lean
run_check "INVARIANT" rg -n '^theorem collapseShootdownOps_effect_eq' SeLe4n/Kernel/Architecture/TlbShootdownProtocol.lean
run_check "INVARIANT" rg -n '^theorem waitAllAckedBounded_least' SeLe4n/Kernel/Architecture/TlbShootdownWait.lean
run_check "INVARIANT" rg -n '^theorem roundLockTryAcquire_mutex' SeLe4n/Kernel/Architecture/TlbShootdownWait.lean
run_check "INVARIANT" rg -n '^theorem shootdownRoundLock_release_acquire' SeLe4n/Kernel/Architecture/TlbShootdownWait.lean
run_check "INVARIANT" rg -n '^theorem shootdownAck_release_acquire_multi_pair_witness' SeLe4n/Kernel/Architecture/TlbShootdownWait.lean
run_check "INVARIANT" rg -n '^theorem storeObject_tlbShootdown_eq' SeLe4n/Model/State.lean
run_check "INVARIANT" rg -n '^theorem bootFromPlatform_tlbShootdown_eq' SeLe4n/Platform/Boot.lean
run_check "INVARIANT" rg -n '^def lifecycleRetypeWithCleanupShootdown' SeLe4n/Kernel/Lifecycle/Operations/RetypeWrappers.lean
run_check "INVARIANT" rg -n '^theorem lifecycleRetypeWithCleanupShootdown_preserves_pendingBounded' SeLe4n/Kernel/Lifecycle/Operations/RetypeWrappers.lean
run_check "INVARIANT" rg -n '^theorem completeShootdownRounds_nil' SeLe4n/Kernel/SyscallDispatchEntry.lean
run_check "INVARIANT" rg -n '^def shootdownRoundLockAcquireFuel' SeLe4n/Kernel/SyscallDispatchEntry.lean
run_check "INVARIANT" rg -n '^theorem shootdownSharingDomain_rpi5' SeLe4n/Kernel/SyscallDispatchEntry.lean
run_check "INVARIANT" rg -n '^def tlbiLocalFullFlush' SeLe4n/Kernel/Concurrency/Runtime.lean
run_check "INVARIANT" rg -n '^def coreOnlineInMask' SeLe4n/Kernel/Concurrency/Runtime.lean
run_check "INVARIANT" rg -n '^pub fn tlb_shootdown_req_handler_in' rust/sele4n-hal/src/shootdown.rs
run_check "INVARIANT" rg -n '^pub fn round_lock_try_acquire_in' rust/sele4n-hal/src/shootdown.rs
run_check "INVARIANT" rg -n 'fn round_lock_mutex_stress' rust/sele4n-hal/src/shootdown.rs
run_check "INVARIANT" rg -n 'fn handler_in_genuine_ack_transition_own_slot_only' rust/sele4n-hal/src/shootdown.rs
run_check "INVARIANT" rg -n '^private def runCompletionCutChecks' tests/SmpTlbShootdownSuite.lean
run_check "INVARIANT" rg -n '^private def runLiveDispatchChecks' tests/SmpTlbShootdownSuite.lean
run_check "INVARIANT" bash -c "test -x scripts/test_qemu_smp_shootdown.sh"
run_check "INVARIANT" rg -n 'test_qemu_smp_shootdown\.sh' scripts/test_tier4_smp_bootcheck.sh
run_check "INVARIANT" rg -n '^theorem shootdownRoundFor_restores_quiescent' SeLe4n/Kernel/Architecture/TlbShootdown.lean
run_check "INVARIANT" rg -n '^private def runMaskedRoundChecks' tests/SmpTlbShootdownSuite.lean
run_check "INVARIANT" rg -n '^pub extern "C" fn ffi_shootdown_ack_round' rust/sele4n-hal/src/ffi.rs
run_check "INVARIANT" rg -n '^pub extern "C" fn ffi_shootdown_all_acked_for_round' rust/sele4n-hal/src/ffi.rs
run_check "INVARIANT" rg -n '^pub extern "C" fn ffi_shootdown_self_service_round' rust/sele4n-hal/src/ffi.rs
run_check "INVARIANT" rg -n 'extern "ffi_shootdown_ack_round"' SeLe4n/Platform/FFI.lean
run_check "INVARIANT" rg -n '^def shootdownAckRound' SeLe4n/Kernel/Concurrency/Runtime.lean
run_check "INVARIANT" rg -n '^theorem shootdownAck_ffi_core_in_range' SeLe4n/Kernel/Concurrency/Runtime.lean
# WS-SM SM7.B debt-closure cut — per-descriptor handler operand mailbox
# (debt (1)): the Rust seqlock mailbox + publish/snapshot/retire primitives,
# the local per-operand TLBI dispatcher + shared op-tag decode, the FFI
# publish seam + Lean wrappers + the live-entry publish call, and the
# genuine per-descriptor / torn-read-fallback tests.  Plus the withLockSet
# pendingBounded carriage (debt (5) slice).
run_check "INVARIANT" rg -n '^pub struct ShootdownOpMailbox' rust/sele4n-hal/src/shootdown.rs
run_check "INVARIANT" rg -n '^pub fn retire_round_ops_in' rust/sele4n-hal/src/shootdown.rs
run_check "INVARIANT" rg -n '^pub fn publish_round_ops_in' rust/sele4n-hal/src/shootdown.rs
run_check "INVARIANT" rg -n 'tlb_shootdown_req_service_in\(&SHOOTDOWN_OPS' rust/sele4n-hal/src/shootdown.rs
run_check "INVARIANT" rg -n '^pub fn tlbi_local' rust/sele4n-hal/src/tlb.rs
run_check "INVARIANT" rg -n '^pub const fn decode_tlb_invalidation' rust/sele4n-hal/src/tlb.rs
run_check "INVARIANT" rg -n '^pub extern "C" fn ffi_shootdown_publish_slot' rust/sele4n-hal/src/ffi.rs
run_check "INVARIANT" rg -n 'fn retire_per_descriptor_counts_operands' rust/sele4n-hal/src/shootdown.rs
run_check "INVARIANT" rg -n 'fn retire_torn_read_falls_back_to_full_flush' rust/sele4n-hal/src/shootdown.rs
run_check "INVARIANT" rg -n 'fn op_tag_decode_conformance' rust/sele4n-hal/src/shootdown.rs
run_check "INVARIANT" rg -n '^opaque ffiShootdownPublishSlot' SeLe4n/Platform/FFI.lean
run_check "INVARIANT" rg -n '^def shootdownPublishSlot' SeLe4n/Kernel/Concurrency/Runtime.lean
run_check "INVARIANT" rg -n '^def publishShootdownOps' SeLe4n/Kernel/SyscallDispatchEntry.lean
run_check "INVARIANT" rg -n 'publishShootdownOps collapsed' SeLe4n/Kernel/SyscallDispatchEntry.lean
run_check "INVARIANT" rg -n '^theorem withLockSet_preserves_pendingBounded' SeLe4n/Kernel/Concurrency/Locks/WithLockSet.lean
run_check "INVARIANT" rg -n '^theorem acquireLockOnObject_tlbShootdown_eq' SeLe4n/Kernel/Concurrency/Locks/WithLockSet.lean
run_check "INVARIANT" rg -n '^private def runDebtClosureChecks' tests/SmpTlbShootdownSuite.lean

# WS-SM SM7.C per-core TLB model — the mounted per-core view, its ops, the
# 13th proofLayerInvariantBundle conjunct, the operational round the live
# seam runs (with its bridge to the SM7.B single-view round + operative
# Theorem 3.3.1), and the live-seam per-core-drain wiring.
run_check "INVARIANT" rg -n '^def tlbInvalidationConsistent_perCore' SeLe4n/Kernel/Architecture/PerCoreTlbModel.lean
run_check "INVARIANT" rg -n '^theorem tlbShootdown_invalidates_perCore' SeLe4n/Kernel/Architecture/PerCoreTlbModel.lean
run_check "INVARIANT" rg -n '^theorem tlbConsistency_cross_subsystem' SeLe4n/Kernel/Architecture/PerCoreTlbModel.lean
run_check "INVARIANT" rg -n '^def handleTlbShootdownReqOnCorePerCore' SeLe4n/Kernel/Architecture/PerCoreTlbModel.lean
run_check "INVARIANT" rg -n '^theorem shootdownRoundPerCore_invalidates_perCore' SeLe4n/Kernel/Architecture/PerCoreTlbModel.lean
run_check "INVARIANT" rg -n '^theorem shootdownRoundPerCore_tlb_eq' SeLe4n/Kernel/Architecture/PerCoreTlbModel.lean
run_check "INVARIANT" rg -n '^theorem tlbInvalidationConsistentCheck_perCore_iff' SeLe4n/Kernel/Architecture/PerCoreTlbModel.lean
run_check "INVARIANT" rg -n 'tlbInvalidationConsistent_perCore st' SeLe4n/Kernel/Architecture/Invariant.lean
# Round 43: this pinned `handleTlbShootdownReqOnCorePerCore`, which has
# appeared in this file only inside comments since the live catch-up was
# restricted to the round window — so the anchor asserted the live per-core
# wiring while checking three docstrings.  Re-pointed at the call the seam
# actually makes; the code view is what exposed it.
run_check "INVARIANT" rg -n 'Architecture.shootdownCatchUpPerCoreInWindow' \
  SeLe4n/Kernel/SyscallDispatchEntry.lean
run_check "INVARIANT" rg -n '^private def runPerCoreTlbOperationalChecks' tests/SmpTlbShootdownSuite.lean
# WS-SM SM7.F.4: live fill + initiator-atomic VSpace seams (the live `.vspaceMap`
# / `.vspaceUnmap` dispatch routes through the per-core wrappers).
run_check "INVARIANT" rg -n '^def vspaceMapPageCheckedWithShootdownFromStatePerCore' SeLe4n/Kernel/Architecture/PerCoreTlbModel.lean
run_check "INVARIANT" rg -n '^theorem vspaceMapPageCheckedWithShootdownFromStatePerCore_preserves_tlbInvalidationConsistent_perCore' SeLe4n/Kernel/Architecture/PerCoreTlbModel.lean
run_check "INVARIANT" rg -n 'vspaceUnmapPageWithShootdownPerCore' SeLe4n/Kernel/Architecture/PerCoreCacheModel.lean
run_check "INVARIANT" rg -n 'vspaceMapPageCheckedWithShootdownFromStatePerCore' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n '^private def runPerCoreTlbLiveLifecycleChecks' tests/SmpTlbShootdownSuite.lean
# WS-SM SM7.F.5: the ACCESS-time fill — a core caches translations it did not
# map (the IPC-buffer walk), live on the per-core syscall entry.
run_check "INVARIANT" rg -n '^def tlbFillIpcBufferOnCore' SeLe4n/Kernel/Architecture/IpcBufferTlbFill.lean
run_check "INVARIANT" rg -n '^theorem tlbFillIpcBufferOnCore_caches_read_translation' SeLe4n/Kernel/Architecture/IpcBufferTlbFill.lean
run_check "INVARIANT" rg -n '^theorem tlbFillIpcBufferOnCore_preserves_tlbInvalidationConsistent_perCore' SeLe4n/Kernel/Architecture/IpcBufferTlbFill.lean
run_check "INVARIANT" rg -n 'tlbFillIpcBufferOnCore' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n '^private def runPerCoreTlbAccessFillChecks' tests/SmpTlbShootdownSuite.lean
# The page-granular IPC-buffer translation the fill rests on: the read and the
# fill must resolve through ONE page computation, not two copies.
run_check "INVARIANT" rg -n '^def VAddr.pageBase' SeLe4n/Prelude.lean
run_check "INVARIANT" rg -n '^def ipcBufferSlotPage' SeLe4n/Kernel/Architecture/IpcBufferRead.lean
run_check "INVARIANT" rg -n 'ipcBufferSlotPage tcb.ipcBuffer idx' SeLe4n/Kernel/Architecture/IpcBufferRead.lean
# WS-SM SM7.F.5: whole-bundle carriage across a `perCoreTlb` write — the
# reusable layer, and the fill's discharge of its single obligation.
run_check "INVARIANT" rg -n '^theorem proofLayerInvariantBundle_setPerCoreTlb' SeLe4n/Kernel/Architecture/Invariant.lean
run_check "INVARIANT" rg -n '^theorem tlbFillIpcBufferOnCore_preserves_proofLayerInvariantBundle' SeLe4n/Kernel/Architecture/IpcBufferTlbFill.lean
# WS-SM SM7.F.4(b)(iii): the retype seam drains the initiator's per-core view.
run_check "INVARIANT" rg -n '^def lifecycleRetypeDirectWithCleanupShootdownPerCore' SeLe4n/Kernel/Lifecycle/Operations/RetypeWrappers.lean
run_check "INVARIANT" rg -n '^theorem lifecycleRetypeDirectWithCleanupShootdownPerCore_initiator_drained' SeLe4n/Kernel/Lifecycle/Operations/RetypeWrappers.lean
run_check "INVARIANT" rg -n 'lifecycleRetypeDirectWithCleanupShootdownPerCore' SeLe4n/Kernel/API.lean
# WS-SM SM7.F.3 — round-generation-tagged descriptors: a commit's catch-up
# drains ONLY the rounds its own commit opened, so a concurrently-committed
# round's freshly-posted work survives for its own catch-up (the SM7.B
# v0.32.79 model-fidelity debt, closed).  The descriptor field, the monotone
# counter, the window predicate + its diff recovery, the selective drain and
# its race-freedom lemma, the per-core catch-up the live seam runs, and the
# generation-carrying Rust acknowledgment channel that replaced the round
# reset (an acknowledgment now names the round it discharged, so a stale
# `.tlbShootdownReq` SGI cannot satisfy a later round's wait).
run_check "INVARIANT" rg -n '^  generation : Nat' SeLe4n/Kernel/Architecture/TlbShootdown.lean
run_check "INVARIANT" rg -n '^  roundGeneration : Nat' SeLe4n/Kernel/Architecture/TlbShootdown.lean
run_check "INVARIANT" rg -n '^def roundDescriptor' SeLe4n/Kernel/Architecture/TlbShootdown.lean
run_check "INVARIANT" rg -n '^def inRoundWindow' SeLe4n/Kernel/Architecture/TlbShootdown.lean
run_check "INVARIANT" rg -n '^def drainShootdownsInWindow' SeLe4n/Kernel/Architecture/TlbShootdown.lean
run_check "INVARIANT" rg -n '^theorem drainShootdownsInWindow_preserves_foreign' SeLe4n/Kernel/Architecture/TlbShootdown.lean
run_check "INVARIANT" rg -n '^theorem drainShootdownsInWindow_eq_drainShootdowns' SeLe4n/Kernel/Architecture/TlbShootdown.lean
run_check "INVARIANT" rg -n '^def completeShootdownOnCoreInWindow' SeLe4n/Kernel/Architecture/TlbShootdown.lean
run_check "INVARIANT" rg -n '^def shootdownRoundWindow' SeLe4n/Kernel/Architecture/TlbShootdownProtocol.lean
run_check "INVARIANT" rg -n '^def handleTlbShootdownReqOnCoreInWindow' SeLe4n/Kernel/Architecture/TlbShootdownProtocol.lean
run_check "INVARIANT" rg -n '^theorem handleTlbShootdownReqOnCoreInWindow_eq_handle' SeLe4n/Kernel/Architecture/TlbShootdownProtocol.lean
run_check "INVARIANT" rg -n '^theorem mem_shootdownPostedOps_iff' SeLe4n/Kernel/Architecture/TlbShootdownProtocol.lean
run_check "INVARIANT" rg -n '^def shootdownCatchUpPerCoreInWindow' SeLe4n/Kernel/Architecture/PerCoreTlbModel.lean
run_check "INVARIANT" rg -n '^theorem shootdownCatchUpPerCoreInWindow_preserves_foreign' SeLe4n/Kernel/Architecture/PerCoreTlbModel.lean
run_check "INVARIANT" rg -n '^theorem shootdownCatchUpPerCoreInWindow_eq_catchUp' SeLe4n/Kernel/Architecture/PerCoreTlbModel.lean
run_check "INVARIANT" rg -n 'shootdownCatchUpPerCoreInWindow st execCore collapsed' SeLe4n/Kernel/SyscallDispatchEntry.lean
run_check "INVARIANT" rg -n 'Architecture.shootdownRoundWindow st st' SeLe4n/Kernel/SyscallDispatchEntry.lean
run_check "INVARIANT" rg -n '^private def runRoundGenerationChecks' tests/SmpTlbShootdownSuite.lean
# The 12th `proofLayerInvariantBundle` conjunct (`pendingBounded`) carried across
# the transition the live catch-up seam runs.  A window drain deliberately leaves
# foreign descriptors queued, so — unlike a whole-queue drain — it does not empty
# the queues and the bound has to be carried rather than fall out.
run_check "INVARIANT" rg -n '^theorem handleTlbShootdownReqOnCorePerCoreInWindow_preserves_pendingBounded' SeLe4n/Kernel/Architecture/PerCoreTlbModel.lean
run_check "INVARIANT" rg -n '^theorem foldl_handleTlbShootdownReqOnCorePerCoreInWindow_preserves_pendingBounded' SeLe4n/Kernel/Architecture/PerCoreTlbModel.lean
run_check "INVARIANT" rg -n '^theorem shootdownCatchUpPerCoreInWindow_preserves_pendingBounded' SeLe4n/Kernel/Architecture/PerCoreTlbModel.lean
# The generation-carrying acknowledgment channel (Rust mirror).  The reset is
# GONE by design — a negative anchor keeps it from coming back, since a reset
# would erase the monotonicity the whole mechanism rests on.
run_check "INVARIANT" rg -n 'pub struct ShootdownAckSlot' rust/sele4n-hal/src/shootdown.rs
run_check "INVARIANT" rg -n 'pub acked_gen: AtomicU64' rust/sele4n-hal/src/shootdown.rs
run_check "INVARIANT" rg -n 'pub fn ack_round_in_slice' rust/sele4n-hal/src/shootdown.rs
run_check "INVARIANT" rg -n 'pub fn all_acked_for_round_in_slice' rust/sele4n-hal/src/shootdown.rs
run_check "INVARIANT" rg -n 'pub fn tlb_shootdown_req_service_in' rust/sele4n-hal/src/shootdown.rs
run_check "INVARIANT" rg -n 'pub fn self_service_round_in' rust/sele4n-hal/src/shootdown.rs
run_check "INVARIANT" rg -n 'fn stale_acknowledgment_cannot_satisfy_a_later_round' rust/sele4n-hal/src/shootdown.rs
run_check "INVARIANT" bash -c "! rg -q 'fn reset_for_round' rust/sele4n-hal/src/shootdown.rs"
run_check "INVARIANT" bash -c "! rg -q 'shootdownResetForRound' SeLe4n/Kernel/SyscallDispatchEntry.lean"

# WS-SM SM7.E — tests + fixtures.  The concurrent-unmap stress (§6) and the
# cross-cluster mock (§7) scenario groups, the per-core handler commutativity
# they rest on (the live catch-up fold's order-independence — SM7.B proved it
# only for the single-view handler, but the live seam folds the per-core one),
# the `.outer` portability seam, the deterministic golden trace fixture (+ its
# sha256 companion), and the Tier-4 concurrent-unmap stress exerciser.
run_check "INVARIANT" rg -n '^theorem setTlbOnCore_comm' SeLe4n/Kernel/Architecture/PerCoreTlbModel.lean
run_check "INVARIANT" rg -n '^theorem handleTlbShootdownReqOnCorePerCore_comm' SeLe4n/Kernel/Architecture/PerCoreTlbModel.lean
run_check "INVARIANT" rg -n '^theorem foldl_handleTlbShootdownReqOnCorePerCore_swap' SeLe4n/Kernel/Architecture/PerCoreTlbModel.lean
run_check "INVARIANT" rg -n '^theorem tlbShootdown_outer_correct' SeLe4n/Kernel/Architecture/TlbShootdownProtocol.lean
run_check "INVARIANT" rg -n '^private def runConcurrentUnmapStressChecks' tests/SmpTlbShootdownSuite.lean
run_check "INVARIANT" rg -n '^private def runConcurrentUnmapDrainChecks' tests/SmpTlbShootdownSuite.lean
run_check "INVARIANT" rg -n '^private def runShootdownBackpressureChecks' tests/SmpTlbShootdownSuite.lean
run_check "INVARIANT" rg -n '^private def runCrossClusterMockChecks' tests/SmpTlbShootdownSuite.lean
run_check "INVARIANT" rg -n '^private def runCrossClusterHazardChecks' tests/SmpTlbShootdownSuite.lean
run_check "INVARIANT" rg -n '^private def runCrossClusterReachChecks' tests/SmpCacheMaintenanceSuite.lean
run_check "INVARIANT" rg -n '^private def shootdownTraceLines' tests/SmpTlbShootdownSuite.lean
run_check "INVARIANT" rg -n '^private def runTraceFixtureCheck' tests/SmpTlbShootdownSuite.lean
run_check "INVARIANT" rg -n '^\[smp-tlb-shootdown\]' tests/fixtures/smp_tlb_shootdown.expected
run_check "INVARIANT" rg -n 'smp_tlb_shootdown\.expected' tests/fixtures/smp_tlb_shootdown.expected.sha256
run_check "INVARIANT" rg -n 'test_qemu_smp_shootdown_stress\.sh' scripts/test_tier4_smp_bootcheck.sh
# The Tier-4 stress exerciser's driver-detection guard and its pass gate must
# agree on the `tlb-shootdown-stress` banner tag (the contract the future SM9.E
# in-image driver emits); anchoring the exact pass phrase catches silent drift.
run_check "INVARIANT" rg -n 'tlb-shootdown-stress: all cores completed' scripts/test_qemu_smp_shootdown_stress.sh
# ============================================================================
# WS-SM SM7.D — cache maintenance broadcast
#
# The instruction-cache broadcast layer (`IC IALLUIS` / `IC IVAU`) and its
# PE-local counterpart (the hazard), the data-cache-at-PoC reach theorems,
# the DMA scope tripwire, the 14th `proofLayerInvariantBundle` conjunct, the
# live `.vspaceUnmap` / `.lifecycleRetype` seams, the FFI + Rust HAL
# realisation, and the suite that exercises all of it.
# ============================================================================
# SM7.D module registration + `CacheModel` / `TlbCacheComposition` promotion.
run_check "INVARIANT" rg -n '^import SeLe4n\.Kernel\.Architecture\.PerCoreCacheModel' SeLe4n.lean
run_check "INVARIANT" rg -n '^import SeLe4n\.Kernel\.Architecture\.CacheInvalidation' SeLe4n/Model/State.lean
run_check "INVARIANT" bash -c "! rg -q '^SeLe4n\.Kernel\.Architecture\.CacheModel' scripts/staged_module_allowlist.txt"
run_check "INVARIANT" bash -c "! rg -q '^SeLe4n\.Kernel\.Architecture\.TlbCacheComposition' scripts/staged_module_allowlist.txt"
run_check "INVARIANT" bash -c "! rg -q 'STATUS: staged' SeLe4n/Kernel/Architecture/CacheModel.lean"
# SM7.D.1 granularity contract: the page operand vs the line-granular IC IVAU.
run_check "INVARIANT" rg -n '^theorem icacheLinesPerPage_covers_page' SeLe4n/Kernel/Architecture/CacheInvalidation.lean
run_check "INVARIANT" rg -n '^pub fn ic_invalidate_page_inner_shareable' rust/sele4n-hal/src/cache.rs
run_check "INVARIANT" rg -n '^pub const ICACHE_LINES_PER_PAGE' rust/sele4n-hal/src/cache.rs
run_check "INVARIANT" rg -n 'fn test_ic_invalidate_page_line_count' rust/sele4n-hal/src/cache.rs
# SM7.D.1 emission ledger: the runtime gets the model's exact operand.
run_check "INVARIANT" rg -n '  pendingIcacheMaintenance :' SeLe4n/Model/State.lean
run_check "INVARIANT" rg -n '^def recordIcacheMaintenance' SeLe4n/Kernel/Architecture/PerCoreCacheModel.lean
run_check "INVARIANT" rg -n '^def clearIcacheMaintenance' SeLe4n/Kernel/Architecture/PerCoreCacheModel.lean
run_check "INVARIANT" rg -n 'theorem recordIcacheMaintenance_of_nil' SeLe4n/Kernel/Architecture/PerCoreCacheModel.lean
run_check "INVARIANT" rg -n 'theorem recordIcacheMaintenance_covered' SeLe4n/Kernel/Architecture/PerCoreCacheModel.lean
# SM7.D ledger soundness: `iallu` is NOT a top element (it issues no DC CVAU),
# so the ledger is a list under a coverage preorder, never a lossy join.
run_check "INVARIANT" rg -n '^def ICacheInvalidation.covers' SeLe4n/Kernel/Architecture/CacheInvalidation.lean
run_check "INVARIANT" rg -n '^theorem ICacheInvalidation.iallu_not_covers_unifyPage' SeLe4n/Kernel/Architecture/CacheInvalidation.lean
run_check "INVARIANT" rg -n '^theorem ICacheInvalidation.covers_trans' SeLe4n/Kernel/Architecture/CacheInvalidation.lean
run_check "INVARIANT" rg -n '^def recordIcacheMaintenanceList' SeLe4n/Kernel/Architecture/CacheInvalidation.lean
run_check "INVARIANT" rg -n '^theorem recordIcacheMaintenanceList_covered' SeLe4n/Kernel/Architecture/CacheInvalidation.lean
run_check "INVARIANT" rg -n '^theorem recordIcacheMaintenanceList_mem_of_mem' SeLe4n/Kernel/Architecture/CacheInvalidation.lean
run_check "INVARIANT" bash -c "! rg -q 'ICacheInvalidation.join' SeLe4n/Kernel/Architecture/CacheInvalidation.lean"
# SM7.D re-type clean-to-PoU: the scrub's zeroing stores must reach the Point of
# Unification BEFORE the instruction caches are invalidated, or the next fetch
# re-fills from the previous owner's content.  `iallu` cannot discharge that.
run_check "INVARIANT" rg -n '  \| cleanRangeIallu \(base : SeLe4n\.PAddr\) \(size : Nat\)' SeLe4n/Kernel/Architecture/CacheInvalidation.lean
run_check "INVARIANT" rg -n '^def byteRangeContains' SeLe4n/Kernel/Architecture/CacheInvalidation.lean
run_check "INVARIANT" rg -n '^theorem byteRangeContains_trans' SeLe4n/Kernel/Architecture/CacheInvalidation.lean
run_check "INVARIANT" rg -n '^theorem ICacheInvalidation.iallu_not_covers_cleanRangeIallu' SeLe4n/Kernel/Architecture/CacheInvalidation.lean
run_check "INVARIANT" rg -n '^theorem ICacheInvalidation.unifyPage_not_covers_cleanRangeIallu' SeLe4n/Kernel/Architecture/CacheInvalidation.lean
run_check "INVARIANT" rg -n '^@\[inline\] def ICacheInvalidation.isDomainWide' SeLe4n/Kernel/Architecture/CacheInvalidation.lean
run_check "INVARIANT" rg -n '^@\[inline\] def ICacheInvalidation.toSize' SeLe4n/Kernel/Architecture/CacheInvalidation.lean
run_check "INVARIANT" rg -n '^def getObjectType\?' SeLe4n/Model/State.lean
run_check "INVARIANT" rg -n '^def retypeIcacheOp' SeLe4n/Kernel/Lifecycle/Operations/RetypeWrappers.lean
run_check "INVARIANT" rg -n '^theorem retypeIcacheOp_cleans_scrub_extent' SeLe4n/Kernel/Lifecycle/Operations/RetypeWrappers.lean
run_check "INVARIANT" rg -n '^theorem retypeIcacheOp_discharges_scrub_obligation' SeLe4n/Kernel/Lifecycle/Operations/RetypeWrappers.lean
run_check "INVARIANT" rg -n '^def dischargesPoUClean' SeLe4n/Kernel/Architecture/PerCoreCacheModel.lean
run_check "INVARIANT" rg -n '^theorem dischargesPoUClean_isDomainWide' SeLe4n/Kernel/Architecture/PerCoreCacheModel.lean
run_check "INVARIANT" rg -n '^def kernelCodeWriteEmitted' SeLe4n/Kernel/Architecture/PerCoreCacheModel.lean
run_check "INVARIANT" rg -n '^theorem kernelCodeWriteSites_emission_pending' SeLe4n/Kernel/Architecture/PerCoreCacheModel.lean
run_check "INVARIANT" rg -n '^pub fn clean_range_pou_then_invalidate_all_inner_shareable' rust/sele4n-hal/src/cache.rs
run_check "INVARIANT" rg -n 'CleanRangeIallu\(u64, u64\)' rust/sele4n-hal/src/cache.rs
run_check "INVARIANT" rg -n 'fn test_clean_range_pou_line_coverage' rust/sele4n-hal/src/cache.rs
# The re-type operand must NOT regress to the bare domain-wide invalidate.
run_check "INVARIANT" bash -c "! rg -q '^  some \\.iallu' SeLe4n/Kernel/Lifecycle/Operations/RetypeWrappers.lean"
# The scrubbed extent has exactly ONE definition, and both the scrub and the
# cache-maintenance operand read it.  A second copy of the arithmetic would let
# the clean silently name a range the scrub does not zero (PR #845 review 4).
run_check "INVARIANT" rg -n '^def scrubExtent' SeLe4n/Kernel/Lifecycle/Operations/ScrubAndUntyped.lean
run_check "INVARIANT" rg -n '^theorem scrubObjectMemory_zeroes_scrubExtent' SeLe4n/Kernel/Lifecycle/Operations/ScrubAndUntyped.lean
run_check "INVARIANT" rg -n '^theorem scrubObjectMemory_cleaned_by_retype' SeLe4n/Kernel/Lifecycle/Operations/RetypeWrappers.lean
run_check "INVARIANT" rg -n 'scrubExtent target objType' SeLe4n/Kernel/Lifecycle/Operations/RetypeWrappers.lean
# Neither consumer may re-derive the extent from `objectTypeAllocSize` itself.
run_check "INVARIANT" bash -c "! rg -q 'objectTypeAllocSize' <(sed -n '/^def retypeIcacheOp /,/^\$/p' SeLe4n/Kernel/Lifecycle/Operations/RetypeWrappers.lean)"
run_check "INVARIANT" bash -c "! rg -q 'objectTypeAllocSize' <(sed -n '/^def scrubObjectMemory /,/^\$/p' SeLe4n/Kernel/Lifecycle/Operations/ScrubAndUntyped.lean)"
# PR #845 review (P2): page alignment is enforced at the mapping boundary, not
# only in the four checked wrappers.  The granule has ONE definition, placed
# below both layers that must agree on it.
run_check "INVARIANT" rg -n '^def pageBytes : Nat := 4096' SeLe4n/Prelude.lean
run_check "INVARIANT" rg -n '^def pageBytes : Nat := SeLe4n.pageBytes' SeLe4n/Kernel/Architecture/CacheInvalidation.lean
run_check "INVARIANT" rg -n 'paddr.toNat % SeLe4n.pageBytes != 0 then none' SeLe4n/Model/Object/Structures.lean
run_check "INVARIANT" rg -n '^theorem mapPage_pageAligned' SeLe4n/Model/Object/Structures.lean
run_check "INVARIANT" rg -n '_hAligned : paddr.toNat % SeLe4n.pageBytes = 0' SeLe4n/Model/Builder.lean
run_check "INVARIANT" rg -n 'paddr.toNat % pageBytes != 0 then .error .alignmentError' SeLe4n/Kernel/Architecture/VSpace.lean
# The Architecture granule must not drift back to a second literal.
run_check "INVARIANT" bash -c "! rg -q '^def pageBytes : Nat := 4096' SeLe4n/Kernel/Architecture/CacheInvalidation.lean"
run_check "INVARIANT" rg -n 'clearIcacheMaintenance st' SeLe4n/Kernel/SyscallDispatchEntry.lean
run_check "INVARIANT" rg -n '^theorem pendingIcacheMaintenance_write_preserves_projection' SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean
# SM7.D.2 the data-side clean-to-PoU obligation + its tripwire.
run_check "INVARIANT" rg -n '^theorem kernelCodeWriteSites_complete' SeLe4n/Kernel/Architecture/PerCoreCacheModel.lean
run_check "INVARIANT" rg -n '^theorem kernelCodeWriteSites_owe_pou_clean' SeLe4n/Kernel/Architecture/PerCoreCacheModel.lean
# SM7.D.1 typed operand + effect algebra + per-core model ops.
run_check "INVARIANT" rg -n '^inductive ICacheInvalidation' SeLe4n/Kernel/Architecture/CacheInvalidation.lean
run_check "INVARIANT" rg -n '^def applyICacheInvalidation' SeLe4n/Kernel/Architecture/PerCoreCacheModel.lean
run_check "INVARIANT" rg -n '^def icFetchOnCore' SeLe4n/Kernel/Architecture/PerCoreCacheModel.lean
run_check "INVARIANT" rg -n '^def icInvalidateOnCore' SeLe4n/Kernel/Architecture/PerCoreCacheModel.lean
run_check "INVARIANT" rg -n '^theorem icInvalidateOnCore_icacheOnCore_ne' SeLe4n/Kernel/Architecture/PerCoreCacheModel.lean
run_check "INVARIANT" rg -n '^def icInvalidateBroadcast' SeLe4n/Kernel/Architecture/PerCoreCacheModel.lean
run_check "INVARIANT" rg -n '^theorem icInvalidateBroadcast_reaches_all_cores' SeLe4n/Kernel/Architecture/PerCoreCacheModel.lean
run_check "INVARIANT" rg -n '^theorem icBroadcastReach_cover' SeLe4n/Kernel/Architecture/PerCoreCacheModel.lean
# SM7.D.1 mounted per-core state + its carriage.
run_check "INVARIANT" rg -n '  perCoreICache : Vector ICacheState numCores' SeLe4n/Model/State.lean
run_check "INVARIANT" rg -n '^theorem default_perCoreICache' SeLe4n/Model/State.lean
run_check "INVARIANT" rg -n '  perCoreICache     : _root_\.Vector ICacheState numCores' SeLe4n/Model/FrozenState.lean
run_check "INVARIANT" rg -n '^theorem freeze_preserves_perCoreICache' SeLe4n/Model/FrozenState.lean
run_check "INVARIANT" rg -n '  perCoreICache : s2\.perCoreICache = s1\.perCoreICache' SeLe4n/Kernel/IPC/Invariant/LookupCongruence.lean
run_check "INVARIANT" rg -n '^theorem bootFromPlatform_perCoreICache_eq' SeLe4n/Platform/Boot.lean
run_check "INVARIANT" rg -n '^theorem perCoreICache_write_preserves_projection' SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean
# SM7.D.2 data-cache at the Point of Coherency (system-wide, no target set).
run_check "INVARIANT" rg -n '^def dcMaintenanceAllCores' SeLe4n/Kernel/Architecture/PerCoreCacheModel.lean
run_check "INVARIANT" rg -n '^theorem dcMaintenanceByVA_reaches_all_cores' SeLe4n/Kernel/Architecture/PerCoreCacheModel.lean
run_check "INVARIANT" rg -n '^theorem icInvalidateOnCore_vs_dcMaintenance_reach' SeLe4n/Kernel/Architecture/PerCoreCacheModel.lean
# SM7.D.3 the DMA scope tripwire.
run_check "INVARIANT" rg -n '^def modeledCoherentAgents' SeLe4n/Kernel/Architecture/PerCoreCacheModel.lean
run_check "INVARIANT" rg -n '^theorem modeledCoherentAgents_no_dma_master' SeLe4n/Kernel/Architecture/PerCoreCacheModel.lean
# SM7.D.4 the 14th proofLayerInvariantBundle conjunct + capstone + checker.
run_check "INVARIANT" rg -n '^def icacheCoherent_perCore' SeLe4n/Kernel/Architecture/PerCoreCacheModel.lean
run_check "INVARIANT" rg -n 'icacheCoherent_perCore st' SeLe4n/Kernel/Architecture/Invariant.lean
run_check "INVARIANT" rg -n '^theorem default_icacheCoherent_perCore' SeLe4n/Kernel/Architecture/PerCoreCacheModel.lean
run_check "INVARIANT" rg -n '^theorem cacheCoherency_cross_subsystem' SeLe4n/Kernel/Architecture/PerCoreCacheModel.lean
run_check "INVARIANT" rg -n '^theorem icacheCoherentCheck_perCore_iff' SeLe4n/Kernel/Architecture/PerCoreCacheModel.lean
# SM7.D.1 live wiring: the two production destroy paths + the runtime seam.
run_check "INVARIANT" rg -n '^def vspaceUnmapPageWithShootdownAndIcacheBroadcast' SeLe4n/Kernel/Architecture/PerCoreCacheModel.lean
run_check "INVARIANT" rg -n '^theorem vspaceUnmapPageWithShootdownAndIcacheBroadcast_preserves_icacheCoherent_perCore' SeLe4n/Kernel/Architecture/PerCoreCacheModel.lean
run_check "INVARIANT" rg -n '^def lifecycleRetypeDirectWithCleanupShootdownPerCoreIcache' SeLe4n/Kernel/Lifecycle/Operations/RetypeWrappers.lean
run_check "INVARIANT" rg -n '^def lifecycleRetypeWithCleanupShootdownPerCoreIcache' SeLe4n/Kernel/Lifecycle/Operations/RetypeWrappers.lean
run_check "INVARIANT" rg -n 'vspaceUnmapPageWithShootdownAndIcacheBroadcast' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n 'lifecycleRetypeDirectWithCleanupShootdownPerCoreIcache' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n '^def completeIcacheMaintenance' SeLe4n/Kernel/SyscallDispatchEntry.lean
run_check "INVARIANT" rg -n 'completeIcacheMaintenance result' SeLe4n/Kernel/SyscallDispatchEntry.lean
# SM7.D FFI + Rust HAL realisation (broadcast primitives + fail-closed decode).
run_check "INVARIANT" rg -n '^opaque ffiIcIalluIs' SeLe4n/Platform/FFI.lean
run_check "INVARIANT" rg -n '^opaque ffiIcMaintenance' SeLe4n/Platform/FFI.lean
run_check "INVARIANT" rg -n '^def icMaintenanceBroadcast' SeLe4n/Platform/FFI.lean
run_check "INVARIANT" rg -n '^pub fn ic_ivau' rust/sele4n-hal/src/cache.rs
run_check "INVARIANT" rg -n '^pub fn ic_invalidate_all_inner_shareable' rust/sele4n-hal/src/cache.rs
run_check "INVARIANT" rg -n '^pub const fn decode_icache_invalidation' rust/sele4n-hal/src/cache.rs
run_check "INVARIANT" rg -n '^pub extern "C" fn cache_ic_ialluis' rust/sele4n-hal/src/ffi.rs
run_check "INVARIANT" rg -n '^pub extern "C" fn cache_ic_maintenance\(op_tag: u32, addr: u64, size: u64\)' rust/sele4n-hal/src/ffi.rs
run_check "INVARIANT" rg -n '^opaque ffiIcMaintenance : UInt32 → UInt64 → UInt64 → BaseIO Unit' SeLe4n/Platform/FFI.lean
# SM7.D suite registration (Tier-2 runner + lakefile executable).
run_check "INVARIANT" rg -n '^def runSmpCacheMaintenanceChecks' tests/SmpCacheMaintenanceSuite.lean
run_check "INVARIANT" rg -n '^run_check(_with_timeout)? "TRACE" lake exe smp_cache_maintenance_suite' scripts/test_tier2_negative.sh
run_check "INVARIANT" rg -n '^name = "smp_cache_maintenance_suite"' lakefile.toml
# SM7.D code-publication syscall `.vspaceUnifyInstruction` (unify point-of-unification):
# the transition, its fail-closed arms, the reach theorem, the ABI mirrors, the
# lock set, the information-flow enforcement entry, and the live dispatch arm.
run_check "INVARIANT" rg -n '^def unifyTargetPaddr' SeLe4n/Kernel/Architecture/PerCoreCacheModel.lean
run_check "INVARIANT" rg -n '^def vspaceUnifyInstructionPage' SeLe4n/Kernel/Architecture/PerCoreCacheModel.lean
run_check "INVARIANT" rg -n '^theorem vspaceUnifyInstructionPage_asid_unbound' SeLe4n/Kernel/Architecture/PerCoreCacheModel.lean
run_check "INVARIANT" rg -n '^theorem vspaceUnifyInstructionPage_unmapped' SeLe4n/Kernel/Architecture/PerCoreCacheModel.lean
run_check "INVARIANT" rg -n '^theorem vspaceUnifyInstructionPage_frame' SeLe4n/Kernel/Architecture/PerCoreCacheModel.lean
run_check "INVARIANT" rg -n '^theorem vspaceUnifyInstructionPage_records_unify' SeLe4n/Kernel/Architecture/PerCoreCacheModel.lean
run_check "INVARIANT" rg -n '^theorem vspaceUnifyInstructionPage_invalidates_all_cores' SeLe4n/Kernel/Architecture/PerCoreCacheModel.lean
run_check "INVARIANT" rg -n '^theorem vspaceUnifyInstructionPage_preserves_icacheCoherent_perCore' SeLe4n/Kernel/Architecture/PerCoreCacheModel.lean
run_check "INVARIANT" rg -n '^  \| vspaceUnifyInstruction' SeLe4n/Model/Object/Types.lean
run_check "INVARIANT" rg -n '^def lockSet_vspaceUnifyInstruction' SeLe4n/Kernel/Concurrency/Locks/LockSetTransitions.lean
run_check "INVARIANT" rg -n '^theorem lockSet_consistent_vspaceUnifyInstruction' SeLe4n/Kernel/Concurrency/Locks/LockSetTransitions.lean
run_check "INVARIANT" rg -n 'vspaceUnifyInstructionPage' SeLe4n/Kernel/InformationFlow/Enforcement/Wrappers.lean
run_check "INVARIANT" rg -n '^theorem dispatchWithCap_vspaceUnifyInstruction_delegates' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n '    VSpaceUnifyInstruction = 29,' rust/sele4n-types/src/syscall.rs
run_check "INVARIANT" rg -n '    VSpaceUnifyInstruction = 29,' rust/sele4n-hal/src/svc_dispatch.rs
run_check "INVARIANT" rg -n 'fn vspace_unify_instruction_roundtrip' rust/sele4n-abi/tests/conformance.rs
run_check "INVARIANT" rg -n '^pub fn unify_instruction_page_inner_shareable' rust/sele4n-hal/src/cache.rs
run_check "INVARIANT" rg -n '^pub fn dc_cvau' rust/sele4n-hal/src/cache.rs

# ============================================================================
# PR #845 review (P1) — VSpace capability binding (confused-deputy closure)
#
# `syscallLookupCap` proves only that the caller holds *a* capability carrying
# the required right.  The three VSpace arms operate on a caller-supplied ASID,
# so without binding the capability to that address space a holder of any
# writable object capability could act on an arbitrary one.  These anchors pin
# the predicate, its fail-closed theorems, the three rejection duals, and the
# regression suite.
# ============================================================================
run_check "INVARIANT" rg -n '^def vspaceCapAuthorizesAsid' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n '^theorem vspaceCapAuthorizesAsid_iff' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n '^theorem vspaceCapAuthorizesAsid_false_of_ne' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n '^theorem vspaceCapAuthorizesAsid_false_of_unbound' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n '^theorem vspaceCapAuthorizesAsid_false_of_not_object' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n '^theorem dispatchWithCap_vspaceMap_unauthorized' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n '^theorem dispatchWithCap_vspaceUnmap_unauthorized' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n '^theorem dispatchWithCap_vspaceUnifyInstruction_unauthorized' SeLe4n/Kernel/API.lean
# The gate must be present in all three live arms.  That is guaranteed by the
# three `…_unauthorized` theorems anchored above rather than by a grep: each
# asserts that its arm returns `.illegalAuthority` when authorization fails, so
# deleting the gate from an arm makes the corresponding theorem unprovable and
# breaks the build.  A textual occurrence count would be both weaker (it cannot
# tell which arm a match came from) and fragile across shells.
run_check "INVARIANT" rg -n '^def runVSpaceCapabilityBindingChecks' tests/VSpaceCapabilityBindingSuite.lean
run_check "INVARIANT" rg -n '^run_check_with_timeout "TRACE" lake exe vspace_capability_binding_suite' scripts/test_tier2_negative.sh
run_check "INVARIANT" rg -n '^name = "vspace_capability_binding_suite"' lakefile.toml
# PR #845 review (P2) — physical-address page alignment.  Both the production
# entry point and the proof-decomposition helper must reject an unaligned PA:
# the descriptor and both HAL cache loops use the aligned base, so accepting one
# would let the model record an operand naming an address hardware never touches.
run_check "INVARIANT" rg -n 'paddr.toNat % pageBytes' SeLe4n/Kernel/Architecture/VSpace.lean
run_check "INVARIANT" rg -n 'alignmentError' SeLe4n/Kernel/Architecture/VSpace.lean
# PR #845 review (P2) — the legacy syscall entry documents WHY it cannot drain
# the ledger (the @[extern] link-gating policy) rather than silently skipping it.
run_prose_check "INVARIANT" rg -n 'deferred, never lost' SeLe4n/Platform/FFI.lean
# PR #845 review (P2) — the syscall is reachable from the safe Rust API.
run_check "INVARIANT" rg -n '^pub fn vspace_unify_instruction' rust/sele4n-sys/src/vspace.rs
run_check "INVARIANT" rg -n '^pub type VSpaceUnifyInstructionArgs' rust/sele4n-abi/src/args/vspace.rs
run_check "INVARIANT" bash -c "! rg -q 'VspaceUnifyInstruction' rust/sele4n-types/src/syscall.rs rust/sele4n-hal/src/svc_dispatch.rs"

# WS-SM SM7.F.4(b)(iii): shared initiator drain + the CSpaceAddr retype sibling.
run_check "INVARIANT" rg -n '^def retypeInitiatorDrain' SeLe4n/Kernel/Lifecycle/Operations/RetypeWrappers.lean
run_check "INVARIANT" rg -n '^def lifecycleRetypeWithCleanupShootdownPerCore' SeLe4n/Kernel/Lifecycle/Operations/RetypeWrappers.lean
run_check "INVARIANT" rg -n '^theorem retypeInitiatorDrain_drained' SeLe4n/Kernel/Lifecycle/Operations/RetypeWrappers.lean
# WS-SM SM7.F.4(b)(iii) residual CLOSED: whole-invariant retype preservation.
run_check "INVARIANT" rg -n '^theorem lifecycleRetypeDirectWithCleanupShootdownPerCore_preserves_tlbInvalidationConsistent_perCore' SeLe4n/Kernel/Lifecycle/Operations/RetypeWrappers.lean
run_check "INVARIANT" rg -n '^theorem lifecycleRetypeWithCleanupShootdownPerCore_preserves_tlbInvalidationConsistent_perCore' SeLe4n/Kernel/Lifecycle/Operations/RetypeWrappers.lean

# ============================================================================
# WS-SM SM8.A — Per-core observable state
#
# The SMP information-flow observer `(core, label)` and the state it observes.
# These anchors pin: the observer and its view, the shared / per-core field
# partition together with its totality tripwire, the decidable slice and both
# strictness witnesses (the slice must never be mistaken for observable
# equality), the boot-core-free read-set characterisation and its cross-core
# frames, clearance monotonicity with its gate lemmas, the RobinHood filter
# characterisation SM8.A.5 completed, and the suite / staged registrations.
# ============================================================================
# SM8.A.1 the observer + its view + the boot-core bridge to the live surface.
run_check "INVARIANT" rg -n '^def IfObserver.ofLabel' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^structure PerCoreObserver' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^def ObservableState.onCore' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^theorem onCore_eq_projectStateOnCore' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^theorem onCore_bootCore' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^def lowEquivalentForObserver' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^def PerCoreObserver.toIfObserver' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^def PerCoreObserver.onBootCore' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^def PerCoreObserver.view' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^theorem lowEquivalentForObserver_iff_lowEquivalentOnCore' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^theorem lowEquivalentForObserver_bootCore' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^theorem lowEquivalentForObserver_refl' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^theorem lowEquivalentForObserver_symm' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^theorem lowEquivalentForObserver_trans' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^def ObservableState.sharedFragment' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^def ObservableState.perCoreFragment' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^def ObservableState.perCoreSlice' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^def ObservableState.sliceOnCore' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^theorem ObservableState.visibilityLe_refl' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^theorem ObservableState.visibilityLe_trans' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^theorem visibilityLe_smp_at' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^theorem machineRegs_beq_self' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^def projectCNode' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^theorem projectKernelObject_cnode' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^theorem lowEquivalent_smp_iff_forall_observer' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
# SM8.A.2 the field partition + its totality tripwire + the headline projection.
run_check "INVARIANT" rg -n '^structure SharedObservableFragment' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^structure PerCoreObservableFragment' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^theorem ObservableState.ext_fragments' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^def ObservableState.ofFragments' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
# The `@[simp]` layer: the fragment round-trip and the thirteen component
# accessors.  Each is `rfl`, so they are the definition-pinning anchors —
# re-pointing a component at a different projection breaks its `rfl`, and a
# rename would silently drop the pin without these.
run_check "INVARIANT" rg -n '^@\[simp\] theorem IfObserver.ofLabel_clearance' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^@\[simp\] theorem ObservableState.ofFragments_eta' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^@\[simp\] theorem ObservableState.ofFragments_perCoreFragment' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^@\[simp\] theorem ObservableState.ofFragments_sharedFragment' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^@\[simp\] theorem PerCoreObserver.toIfObserver_clearance' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^@\[simp\] theorem onCore_activeDomain' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^@\[simp\] theorem onCore_current' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^@\[simp\] theorem onCore_domainSchedule' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^@\[simp\] theorem onCore_domainScheduleIndex' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^@\[simp\] theorem onCore_domainTimeRemaining' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^@\[simp\] theorem onCore_irqHandlers' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^@\[simp\] theorem onCore_machineRegs' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^@\[simp\] theorem onCore_memory' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^@\[simp\] theorem onCore_objectIndex' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^@\[simp\] theorem onCore_objects' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^@\[simp\] theorem onCore_perCoreFragment' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^@\[simp\] theorem onCore_perCoreSlice' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^@\[simp\] theorem onCore_runnable' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^@\[simp\] theorem onCore_serviceRegistry' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^@\[simp\] theorem onCore_services' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^@\[simp\] theorem onCore_sharedFragment' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^theorem ObservableState.fragments_injective' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^theorem onCore_sharedFragment_eq_globalProjection' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^theorem onCore_sharedFragment_determined_by_globalProjection' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^theorem onCore_sharedFragment_core_independent' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^def observableFactorOnCore' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^theorem onCore_isProjection_of_globalProjection' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^theorem onCore_congr_of_globalProjection' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
# SM8.A.3 the decidable slice — the instance AND both strictness witnesses.
# The witnesses are load-bearing: without them a reader could take the decision
# procedure for a decision about observable-state equality, which it is not
# (five ObservableState components are functions over unbounded domains).
run_check "INVARIANT" rg -n '^structure PerCoreObservableSlice' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^def lowEquivalentSliceOnCore' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^instance onCore_decidable' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^theorem lowEquivalentSliceOnCore_of_lowEquivalentOnCore' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^theorem perCoreSlice_erases_register_content' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^theorem perCoreSlice_erases_shared_content' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^def lowEquivalentSliceOnCoreCheckWithRegs' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^theorem lowEquivalentSliceOnCoreCheckWithRegs_of_lowEquivalentOnCore' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^theorem lowEquivalentSliceOnCoreCheckWithRegs_le_slice' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^theorem machineRegs_beq_not_injective' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
# SM8.A.4 the read-set characterisation + the cross-core frames + the excluded
# fields (the machine timer's exclusion restated per core).
run_check "INVARIANT" rg -n '^theorem onCore_perCore_independence' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^theorem onCore_setCurrentOnCore_ne' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^theorem onCore_setRunQueueOnCore_ne' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^theorem onCore_setActiveDomainOnCore_ne' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^theorem onCore_setDomainTimeRemainingOnCore_ne' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^theorem onCore_setDomainScheduleIndexOnCore_ne' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^theorem onCore_setRegsOnCore_ne' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^theorem onCore_setReplenishQueueOnCore' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^theorem onCore_setLastTimeoutErrorsOnCore' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^theorem onCore_scThreadIndex' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^theorem onCore_machineTimer' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^theorem onCore_perCoreTlb' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^theorem onCore_perCoreICache' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^theorem onCore_pendingIcacheMaintenance' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^theorem onCore_tlbShootdown' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^theorem onCore_tlb ' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
# SM8.A.5 gate monotonicity + the visibility order + the CC-1 restatement.
run_check "INVARIANT" rg -n '^theorem objectObservable_monotone' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^theorem threadObservable_monotone' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^theorem serviceObservable_monotone' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^theorem capTargetObservable_monotone' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^theorem memoryAddressObservable_monotone' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^theorem projectCNode_lookup_monotone' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^theorem projectKernelObject_observer_independent_off_cnode' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^theorem onCore_objects_label_invariant_off_cnode' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^theorem filter_sublist_filter_of_imp' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
# SM8.A.5 object-content refinement.  The `objects` clause must compare CONTENT,
# not presence: an `isSome`-only clause lets a wider clearance substitute an
# unrelated object at an id it had already shown.
run_check "INVARIANT" rg -n '^structure cnodeVisibilityLe' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^theorem cnodeVisibilityLe_refl' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^theorem cnodeVisibilityLe_trans' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^theorem eq_of_cnodeVisibilityLe_of_slots_eq' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^def objectVisibilityLe' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^theorem objectVisibilityLe_refl' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^theorem objectVisibilityLe_trans' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^theorem eq_of_objectVisibilityLe_of_not_cnode' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^theorem objectVisibilityLe_cnode' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^theorem projectCNode_visibilityLe_monotone' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^theorem projectKernelObject_visibilityLe_monotone' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^structure ObservableState.visibilityLe' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^theorem ObservableState.visibilityLe_mem_runnable' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^theorem ObservableState.visibilityLe_mem_objectIndex' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^theorem ObservableState.visibilityLe_objects_isSome' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^theorem ObservableState.visibilityLe_objects_eq_of_not_cnode' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^theorem ObservableState.visibilityLe_cnode_lookup' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
# The completeness check on the clause list: a fourteenth `ObservableState`
# component with no clause leaves this proof a goal nothing can close.
run_check "INVARIANT" rg -n '^theorem ObservableState.eq_of_visibilityLe_antisymm' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
# The two list clauses must stay `Sublist` (order-preserving), not membership:
# a run queue's order is its dispatch order.
run_check "INVARIANT" rg -n 'runnable.Sublist' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n 'objectIndex.Sublist' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
# The four scheduling components (CC-1) are unfiltered, so their clauses must be
# EQUALITY.  Omitting them left two states with different `activeDomain`
# dominating each other in both directions.
run_check "INVARIANT" rg -n '^  activeDomain : v₁.activeDomain = v₂.activeDomain' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^  domainTimeRemaining : v₁.domainTimeRemaining = v₂.domainTimeRemaining' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^  domainSchedule : v₁.domainSchedule = v₂.domainSchedule' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^  domainScheduleIndex : v₁.domainScheduleIndex = v₂.domainScheduleIndex' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^theorem onCore_label_monotone' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^def visibilityLe_smp' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^theorem onCore_label_monotone_smp' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^theorem onCore_objects_cnode' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^theorem onCore_objects_cnode_slot_monotone' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^theorem observerView_label_monotone' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
# CC-1 must stay stated against the RAW scheduler reads (content), not merely as
# an equality between two clearances (which any constant function satisfies).
run_check "INVARIANT" rg -n '^theorem onCore_schedulingTransparency' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n 'activeDomainOnCore c' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^theorem onCore_schedulingTransparency_label_invariant' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^theorem onCore_label_monotone_strict' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
# SM8.A.5 substrate: the RobinHood filter-lookup characterisation completed.
# `filter_get_subset` + `filter_get_pred` gave only one direction, so a monotone
# predicate change could not be transported through a CNode's slot filter.
run_check "INVARIANT" rg -n '^theorem RHTable.filter_getElem\?_of_pred' SeLe4n/Kernel/RobinHood/Bridge.lean
run_check "INVARIANT" rg -n '^theorem RHTable.filter_getElem\?_iff' SeLe4n/Kernel/RobinHood/Bridge.lean
# SM8.A.6 suite + module registrations (Tier-2 runner, lakefile, staged anchor).
run_check "INVARIANT" rg -n '^def runSmpInformationFlowChecks' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n '^  runObjectContentOrderChecks' tests/SmpInformationFlowSuite.lean
# The fixture must build the roots its TCBs declare: a TCB whose cspaceRoot /
# vspaceRoot do not resolve fails `KernelObject.wellFormed`, so the evidence
# would be computed on a state no construction path can reach.
run_check "INVARIANT" rg -n 'withObject cnRoot \(\.cnode rootCNodeValue\)' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'withObject vsRoot \(\.vspaceRoot rootVSpaceValue\)' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'every fixture TCB is KernelObject.wellFormed' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n '^import SeLe4n\.Kernel\.InformationFlow\.ObservableStatePerCore' tests/SmpSurfaceAnchors.lean
run_check "INVARIANT" rg -n 'per-core observer surface resolves' tests/SmpSurfaceAnchors.lean
run_check "INVARIANT" rg -n 'per-core independence \+ clearance monotonicity headlines resolve' tests/SmpSurfaceAnchors.lean
run_check "INVARIANT" rg -n '^run_check(_with_timeout)? "TRACE" lake exe smp_information_flow_suite' scripts/test_tier2_negative.sh
run_check "INVARIANT" rg -n '^name = "smp_information_flow_suite"' lakefile.toml
run_check "INVARIANT" rg -n '^import SeLe4n\.Kernel\.InformationFlow\.ObservableStatePerCore' SeLe4n/Platform/Staged.lean
run_check "INVARIANT" rg -n '^SeLe4n\.Kernel\.InformationFlow\.ObservableStatePerCore' scripts/staged_module_allowlist.txt

# ---------------------------------------------------------------------------
# WS-SM SM8.B — per-core non-interference (plan SMP_INFORMATION_FLOW_PLAN.md §5).
# Every public symbol of the two SM8.B modules is pinned, verified by set
# difference against the module sources, so a rename or a silent deletion fails
# Tier 3 even if the dedicated suite still compiles.
run_check "INVARIANT" rg -n '^structure observableSlotsConfinedToCore' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem observableSlotsConfinedToCore_refl' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem observableSlotsConfinedToCore_trans' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem observableSlotsConfinedToCore_of_scheduler_machine_eq' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem observableSlotsConfinedToCore_of_scheduler_regs_eq' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem observableSlotsConfinedToCore_of_eq' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^structure sharedViewUnchanged' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem sharedViewUnchanged_refl' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem sharedViewUnchanged_trans' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem sharedViewUnchanged_of_globalProjection' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem sharedViewUnchanged_of_state_frames' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^@\[simp\] theorem projectStateOnCore_sharedFragment' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^@\[simp\] theorem projectStateOnCore_perCoreFragment' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem crossCoreNonInterference' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem crossCoreNonInterference_onCore' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem crossCoreNonInterference_observer' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem crossCoreNonInterference_of_state_frames' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem lowEquivalent_smp_of_projection_and_confinement' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem nonInterference_perCore' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem nonInterference_perCore_observer' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem composedNonInterference_step_perCore' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem nonInterference_perCore_to_singleCore' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem trace_preserves_projectionOnCore' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem storeObject_confinedToCore' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem storeCapabilityRef_confinedToCore' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem storeTcbIpcState_confinedToCore' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem storeTcbIpcStateAndMessage_confinedToCore' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem storeTcbQueueLinks_confinedToCore' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem storeTcbReceiveComplete_confinedToCore' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem endpointQueuePopHead_confinedToCore' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem endpointQueueEnqueue_confinedToCore' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem linkCallerReply_confinedToCore' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem linkServerStashedReply_confinedToCore' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem consumeCallerReply_confinedToCore' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem cleanupPreReceiveDonation_confinedToCore' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem ensureRunnable_confinedToBootCore' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem removeRunnable_confinedToBootCore' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem setCurrentThread_confinedToBootCore' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem saveOutgoingContext_confinedToCore' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem restoreIncomingContext_confinedToBootCore' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem machineTick_confinedToCore' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem setRunQueueBootCore_confinedToBootCore' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem chooseThread_confinedToCore' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem schedule_confinedToBootCore' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem handleYield_confinedToBootCore' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem timerTick_confinedToBootCore' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem storeTcbIpcState_fromTcb_confinedToCore' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem storeTcbIpcStateAndMessage_fromTcb_confinedToCore' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem notificationSignal_confinedToBootCore' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem notificationWait_confinedToBootCore' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem endpointSendDual_confinedToBootCore' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem returnDonatedSchedContext_confinedToCore' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem cleanupPreReceiveDonationChecked_confinedToCore' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem endpointReceiveDual_confinedToBootCore' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem endpointCall_confinedToBootCore' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem endpointReply_confinedToBootCore' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem endpointReplyRecv_confinedToBootCore' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem attachSlotToCdtNode_confinedToCore' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem detachSlotFromCdt_confinedToCore' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem ensureCdtNodeForSlot_confinedToCore' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem cdtEdge_confinedToCore' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem cspaceLookupSlot_confinedToCore' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem cspaceInsertSlot_confinedToCore' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem cspaceDeleteSlotCore_confinedToCore' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem cspaceDeleteSlot_confinedToCore' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem cspaceCopy_confinedToCore' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem cspaceMove_confinedToCore' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem cspaceMint_confinedToCore' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem cspaceRevoke_confinedToCore' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem cspaceMutate_confinedToCore' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem lifecycleRetypeObject_confinedToCore' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem lifecycleRevokeDeleteRetype_confinedToCore' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem vspaceMapPage_confinedToCore' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem vspaceUnmapPage_confinedToCore' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem vspaceLookup_confinedToCore' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem registerService_confinedToCore' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem registerServiceChecked_confinedToCore' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem nonInterference_perCore_chooseThread' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem nonInterference_perCore_endpointSendDual' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem nonInterference_perCore_cspaceMint' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem nonInterference_perCore_cspaceRevoke' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem nonInterference_perCore_lifecycleRetype' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem nonInterference_perCore_lifecycleRevokeDeleteRetype' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem nonInterference_perCore_notificationSignal' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem nonInterference_perCore_notificationWait' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem nonInterference_perCore_cspaceInsertSlot' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem nonInterference_perCore_schedule' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem nonInterference_perCore_vspaceMapPage' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem nonInterference_perCore_vspaceUnmapPage' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem nonInterference_perCore_vspaceLookup' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem nonInterference_perCore_cspaceCopy' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem nonInterference_perCore_cspaceMove' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem nonInterference_perCore_cspaceDeleteSlot' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem nonInterference_perCore_endpointReply' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem nonInterference_perCore_endpointReceiveDual' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem nonInterference_perCore_endpointCall' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem nonInterference_perCore_endpointReplyRecv' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem nonInterference_perCore_storeObject' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem nonInterference_perCore_setCurrentThread' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem nonInterference_perCore_ensureRunnable' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem nonInterference_perCore_removeRunnable' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem nonInterference_perCore_storeTcbIpcStateAndMessage' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem nonInterference_perCore_storeTcbQueueLinks' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem nonInterference_perCore_cspaceMutate' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem nonInterference_perCore_handleYield' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem nonInterference_perCore_timerTick' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem nonInterference_perCore_syscallDecodeError' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem nonInterference_perCore_registerServiceChecked' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem nonInterference_perCore_syscallDispatch' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem nonInterference_perCore_endpointCallWithDonation' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem nonInterference_perCore_endpointReplyWithReversion' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem nonInterference_perCore_handleInterrupt' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^def kernelOperationPerCoreNiTheorem' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem niStepCoverage_perCore_injective' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem niStepCoverage_perCore_count' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^def perCoreConfinementDerived' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem perCoreConfinementDerived_count' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem niStepCoverage_perCore' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^@\[simp\] theorem projectKernelObject_updateLock' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem updateObjectAt_updateLock_preserves_projectObjects' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem projectState_eq_of_objects_projection_eq' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem updateObjectAt_updateLock_scheduler_eq' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem updateObjectAt_updateLock_machine_eq' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem updateObjectAt_updateLock_objectIndex_eq' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem updateObjectAt_updateLock_services_eq' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem updateObjectAt_updateLock_irqHandlers_eq' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem updateObjectLockAt_preserves_projection' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem updateObjectAt_updateLock_preserves_objects_invExt' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem updateObjectLockAt_preserves_objects_invExt' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem acquireLockOnObject_preserves_projection' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem releaseLockOnObject_preserves_projection' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem acquireLockOnObject_preserves_objects_invExt' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem releaseLockOnObject_preserves_objects_invExt' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem updateObjectLockAt_scheduler_eq' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem updateObjectLockAt_machine_eq' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem acquireLockOnObject_confinedToCore' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem releaseLockOnObject_confinedToCore' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem acquireAll_preserves_objects_invExt' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem releaseAll_preserves_objects_invExt' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem acquireAll_preserves_projection' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem releaseAll_preserves_projection' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem acquireAll_confinedToCore' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem releaseAll_confinedToCore' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem withLockSet_preserves_projection' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem withLockSet_confinedToCore' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem nonInterference_perCore_underLockSet' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem crossCoreNonInterference_of_disjoint_lockSet' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem crossCoreLeakage_bounded' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem crossCoreLeakage_bounded_reconstruction' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem crossCoreLeakage_bounded_by_globalProjection' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem crossCoreTransition_invisible_to_every_observer' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^def enforcementBoundaryPerCore' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
run_check "INVARIANT" rg -n '^theorem enforcementBoundaryPerCore_count' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
# Round 38: the docstring above that theorem restated its number and went stale
# one commit after the theorem moved — the third time in this PR that prose
# repeating a `decide` drifted from it.  Anchoring the PAIR couples them: bump
# the theorem without the sentence and this fails, which is the only mechanism
# that has actually held.
run_prose_check "INVARIANT" rg -n 'per-core boundary has 55 entries' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
run_check "INVARIANT" rg -n 'enforcementBoundaryPerCore\.length = 55' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
run_check "INVARIANT" rg -n '^theorem enforcementBoundaryPerCore_extends_canonical' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
run_check "INVARIANT" rg -n '^def enforcementBoundaryPerCoreComplete' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
run_check "INVARIANT" rg -n '^theorem enforcementBoundaryPerCore_is_complete' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
run_check "INVARIANT" rg -n '^theorem enforcementBoundaryPerCore_entry_is_new' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
run_check "INVARIANT" rg -n '^inductive CovertChannelSeverity' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
run_check "INVARIANT" rg -n '^structure CovertChannel' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
run_check "INVARIANT" rg -n '^def acceptedCovertChannel_scheduling_perCore' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
run_check "INVARIANT" rg -n '^def acceptedCovertChannel_machineTimer' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
run_check "INVARIANT" rg -n '^def acceptedCovertChannel_tcbMetadata' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
run_check "INVARIANT" rg -n '^def acceptedCovertChannel_objectStoreMetadata' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
run_check "INVARIANT" rg -n '^def acceptedCovertChannel_lockContention' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
run_check "INVARIANT" rg -n '^def acceptedCovertChannel_tlbResidency' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
run_check "INVARIANT" rg -n '^def acceptedCovertChannel_icacheResidency' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
run_check "INVARIANT" rg -n '^def acceptedCovertChannelsPerCore' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
run_check "INVARIANT" rg -n '^theorem acceptedCovertChannel_perCoreCount' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
run_check "INVARIANT" rg -n '^theorem acceptedCovertChannel_perCore_ids' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
run_check "INVARIANT" rg -n '^theorem acceptedCovertChannel_modelVisible_count' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
run_check "INVARIANT" rg -n '^theorem acceptedCovertChannel_perCoreInstance_count' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
run_check "INVARIANT" rg -n '^theorem acceptedCovertChannel_hardwareChannels_are_not_modelVisible' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
run_check "INVARIANT" rg -n '^theorem acceptedCovertChannel_smp_additions' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
run_check "INVARIANT" rg -n '^theorem acceptedCovertChannel_lockContention_is_timing_only' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
run_check "INVARIANT" rg -n '^theorem acceptedCovertChannel_residency_excluded_from_view' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
run_check "INVARIANT" rg -n '^theorem acceptedCovertChannel_scheduling_is_model_visible' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
run_check "INVARIANT" rg -n '^def endpointPolicyRestricted_perCore' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
run_check "INVARIANT" rg -n '^theorem endpointPolicyRestricted_perCore_iff' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
run_check "INVARIANT" rg -n '^theorem endpointPolicyRestricted_perCore_at' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
run_check "INVARIANT" rg -n '^theorem endpointPolicyRestricted_perCore_no_overrides' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
run_check "INVARIANT" rg -n '^def endpointFlowCheckAtCore' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
run_check "INVARIANT" rg -n '^theorem endpointFlowCheckAtCore_depends_only_on_subject' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
run_check "INVARIANT" rg -n '^theorem endpointFlowCheckAtCore_stable_under_confined_transition' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
run_check "INVARIANT" rg -n '^theorem endpointFlowCheckAtCore_is_not_constant' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
# NEGATIVE: `endpointFlowCheck_state_independent` was a tautology (`X = X` by
# `rfl`, with unused state/core binders) cited in five prose sites as evidence.
# It must not return: a claim about `endpointFlowCheck` itself can only ever be
# reflexivity, since that function takes neither a state nor a core.
run_negative_check "INVARIANT" rg -n 'endpointFlowCheck_state_independent' SeLe4n/ tests/
run_check "INVARIANT" rg -n '^theorem endpointFlowCheck_restricted_subset_perCore' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
run_check "INVARIANT" rg -n '^theorem endpointPolicyRestricted_perCore_is_necessary' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
run_check "INVARIANT" rg -n '^theorem syscallEntry_preserves_projectionOnCore' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
run_check "INVARIANT" rg -n '^theorem syscallEntry_success_perCore_NI' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
run_check "INVARIANT" rg -n '^theorem syscallEntry_error_perCore_NI' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
run_check "INVARIANT" rg -n '^theorem nonInterference_release_of_perCore' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
run_check "INVARIANT" rg -n '^theorem nonInterference_release_of_perCore_observer' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
# The confinement premise of the four catch-all NI constructors must stay an
# explicit argument: deriving it would be *false* (the live cross-core dispatch
# writes a remote core), so these two pins guard the split.
run_check "INVARIANT" rg -n 'perCoreConfinementDerived_count' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '\| \.syscallDispatchHigh \| \.endpointCallWithDonationHigh' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
# SM8.B.4: the per-object `lock` must stay OUT of the projection.  Without the
# erasure the 2PL bracket is a model-level state channel carrying core
# identities (writerHeld / readers / waiters), re-opening the placement channel
# WS-SM SM5.B closed on `TCB.cpuAffinity`.  Pinned on every projected arm.
run_check "INVARIANT" rg -n 'lock := SeLe4n.Kernel.Concurrency.RwLockState.unheld' SeLe4n/Kernel/InformationFlow/Projection.lean
run_check "INVARIANT" rg -n 'lock := SeLe4n.Kernel.Concurrency.RwLockState.unheld' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean
run_check "INVARIANT" rg -n '^  \| \.endpoint e =>' SeLe4n/Kernel/InformationFlow/Projection.lean
run_check "INVARIANT" rg -n '^  \| \.notification n =>' SeLe4n/Kernel/InformationFlow/Projection.lean
run_check "INVARIANT" rg -n '^  \| \.vspaceRoot v =>' SeLe4n/Kernel/InformationFlow/Projection.lean
run_check "INVARIANT" rg -n '^  \| \.untyped u =>' SeLe4n/Kernel/InformationFlow/Projection.lean
# SM8.B.14 suite + module registrations.
run_check "INVARIANT" rg -n '^  runCrossCoreNonInterferenceChecks' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n '^  runLockSetNonInterferenceChecks' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n '^  runCovertChannelInventoryChecks' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n '^  runCatchAllPremiseChecks' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'NEGATIVE: the RAW lock field genuinely changed' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n '^import SeLe4n\.Kernel\.InformationFlow\.CovertChannelPerCore' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n '^import SeLe4n\.Kernel\.InformationFlow\.CovertChannelPerCore' tests/SmpSurfaceAnchors.lean
run_check "INVARIANT" rg -n 'cross-core non-interference \+ per-core lift headlines resolve' tests/SmpSurfaceAnchors.lean
run_check "INVARIANT" rg -n 'lock-set non-interference \+ the covert-channel inventory resolve' tests/SmpSurfaceAnchors.lean
run_check "INVARIANT" rg -n '^import SeLe4n\.Kernel\.InformationFlow\.NonInterferencePerCore' SeLe4n/Platform/Staged.lean
run_check "INVARIANT" rg -n '^import SeLe4n\.Kernel\.InformationFlow\.CovertChannelPerCore' SeLe4n/Platform/Staged.lean
run_check "INVARIANT" rg -n '^SeLe4n\.Kernel\.InformationFlow\.NonInterferencePerCore' scripts/staged_module_allowlist.txt
run_check "INVARIANT" rg -n '^SeLe4n\.Kernel\.InformationFlow\.CovertChannelPerCore' scripts/staged_module_allowlist.txt

# WS-SM SM8.B (v0.33.5) — non-interference at the genuinely cross-core
# transitions.  The set-of-cores confinement algebra, the home-core frame layer,
# the six write sets and their NI instantiations.
run_check "INVARIANT" rg -n '^structure observableSlotsAgreeOn' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^structure observableSlotsConfinedToCores' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem crossCoreNonInterference_of_agreeOn' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem crossCoreNonInterference_ofCores' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem observableSlotsConfinedToCores_singleton_iff' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem observableSlotsConfinedToCores_mono' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem observableSlotsConfinedToCores_trans' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem storeObject_tcb_determineTargetCore_eq' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_check "INVARIANT" rg -n '^theorem endpointQueuePopHead_determineTargetCore_eq' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_check "INVARIANT" rg -n '^def notificationSignalWriteSet' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_check "INVARIANT" rg -n '^def endpointCallWriteSet' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_check "INVARIANT" rg -n '^theorem notificationSignalWriteSet_eq_lockSet_waiter' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_check "INVARIANT" rg -n '^theorem endpointCallOnCore_confinedToCores' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_check "INVARIANT" rg -n '^theorem endpointCallOnCore_crossCoreNonInterference' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_check "INVARIANT" rg -n '^theorem wakeThread_crossCoreNonInterference_of_visible_thread' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_check "INVARIANT" rg -n 'CrossCoreTransition.all.length = 25' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean

# PR #861 review round 34: the context-restore gate lives in WRAPPERS, never
# inside the transitions.  An in-transition `if contextRestoreSeamLive` reduces
# (the flag is a literal), which collapses every proof about that transition
# onto the dead branch — it kept three theorem names while deleting their
# content and broke SmpPipSuite's P2-5 assertion.  These are NEGATIVE anchors:
# the two transition bodies must not name the flag at all.
# A file-level negative would be wrong: the wrappers live in these same files
# and legitimately name the flag.  Anchor instead on the distinguishing text the
# in-transition form left behind — `resumeThreadOnCore`'s gated local arm ended
# `else .ok (st3, none)`, a shape the un-gated body and the enqueue-only sibling
# both lack.
run_negative_check "INVARIANT" rg -n 'else \.ok \(st3, none\)' \
  SeLe4n/Kernel/Lifecycle/Suspend.lean
# PR #861 review rounds 39/41: the gate's justification is "rejection, not
# misattribution" — challenged twice on the review, both times asserting that a
# vacated core instead falls back to `bootCoreId`.  The claim is a theorem, and
# these anchors keep it cited where the argument is made: a docstring that
# argues from a proof must name it, or the next reader is back to taking the
# prose's word for it.
run_check "INVARIANT" rg -n '^theorem vacatedCore_next_syscall_rejected' \
  SeLe4n/Kernel/SyscallDispatchEntry.lean
# The citation lives in a docstring, so this one genuinely reads prose and says
# so — it is the exception `run_prose_check` exists for, and round 43's whole
# point is that the exception must be declared rather than indistinguishable
# from a code anchor.
run_prose_check "INVARIANT" rg -n 'vacatedCore_next_syscall_rejected' \
  SeLe4n/Kernel/Scheduler/PriorityInheritance/PerCore.lean
# ... and the wrappers that replaced it must exist.
run_check "INVARIANT" rg -n '^def resumeThreadOnCoreLive' SeLe4n/Kernel/Lifecycle/Suspend.lean
run_check "INVARIANT" rg -n '^def resumeThreadEnqueueOnly' SeLe4n/Kernel/Lifecycle/Suspend.lean
run_check "INVARIANT" rg -n '^def priorityRescheduleOnCoreLive' SeLe4n/Kernel/SchedContext/PriorityManagementPerCore.lean
run_check "INVARIANT" rg -n '^def priorityRescheduleEnqueueOnly' SeLe4n/Kernel/SchedContext/PriorityManagementPerCore.lean
# Review round 5: a LIVE inventory entry must name the function the syscall
# dispatch calls.  Three entries named a below-API transition their wrapper does
# strictly more than, so the wrappers get entries — and bounds — of their own.
run_check "INVARIANT" rg -n '^def endpointReplyDispatchWriteSet' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_check "INVARIANT" rg -n '^theorem endpointReplyCrossCoreDispatch_confinedToCores' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_check "INVARIANT" rg -n '^theorem endpointReplyCrossCoreDispatch_crossCoreNonInterference' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_check "INVARIANT" rg -n '^def replyRecvBodyWriteSet' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_check "INVARIANT" rg -n '^theorem replyRecvBody_confinedToCores' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_check "INVARIANT" rg -n '^theorem replyRecvBody_crossCoreNonInterference' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_check "INVARIANT" rg -n '^def suspendThreadOnCoreWriteSet' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_check "INVARIANT" rg -n '^theorem suspendThreadOnCore_confinedToCores' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_check "INVARIANT" rg -n '^theorem suspendThreadOnCore_crossCoreNonInterference' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
# The leaf frames those bounds rest on: per-core confinement reads the domain
# slots and the register banks, and the ARM64 context switch had frames for
# neither.
run_check "INVARIANT" rg -n '^theorem switchToThreadOnCore_confinedToCores' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_check "INVARIANT" rg -n '^theorem handleRescheduleSgiOnCore_confinedToCores' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_check "INVARIANT" rg -n '^theorem suspendRescheduleOnCore_confinedToCores' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_check "INVARIANT" rg -n '^theorem cleanupDonatedSchedContext_machine_eq' SeLe4n/Kernel/Lifecycle/Operations/Cleanup.lean
# The CC-3 witness must depend on the metadata it witnesses: a component
# identity on `objects` stays green if `priority` is erased from the TCB
# projection.  Pin the fields by name.
run_check "INVARIANT" rg -n 'projected.priority = tcb.priority' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
run_check "INVARIANT" rg -n 'projected.ipcState = tcb.ipcState' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
# The confinement checker must compare the WHOLE run queue: `toList` is `flat`,
# which a re-bucketing write leaves untouched.
run_check "INVARIANT" rg -n '^private def runQueueAgreeOn' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n '^  runRunQueueComparisonChecks' tests/SmpInformationFlowSuite.lean
# confinedCheck must not decide the run-queue clause on `toList` alone.
run_negative_check "INVARIANT" rg -n 'decide \(\(st..scheduler.runQueueOnCore c\).toList' tests/SmpInformationFlowSuite.lean
# v0.33.7 audit closure: the live `.call` arm is more than `endpointCallOnCore`
# — it also runs the donation and the PIP chain walk, and the chain walk
# re-buckets on each boosted server's HOME core.  Bounding the live arm needs
# the chain walk's own write set, so these pin it and the union.
run_check "INVARIANT" rg -n '^def pipChainWriteSet' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_check "INVARIANT" rg -n '^theorem propagatePipChainCrossCore_confinedToCores' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_check "INVARIANT" rg -n '^def endpointCallLiveWriteSet' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_check "INVARIANT" rg -n '^theorem endpointCallWriteSet_subset_live' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_check "INVARIANT" rg -n '^theorem applyCallDonation_confinedToCores' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
# v0.33.8: the composed SM6.E cancellation.  Its blocker was that only a
# `scheduler` frame existed for the teardown — per-core confinement reads the
# register banks too, so `cancelIpcBlocking_machine_eq` is what unblocks it.
run_check "INVARIANT" rg -n '^theorem cancelIpcBlocking_machine_eq' SeLe4n/Kernel/Lifecycle/Invariant/SuspendPreservation.lean
run_check "INVARIANT" rg -n '^theorem restoreToReady_machine_eq' SeLe4n/Kernel/Lifecycle/Suspend.lean
run_check "INVARIANT" rg -n '^theorem consumeReplyLink_machine_eq' SeLe4n/Kernel/Lifecycle/Suspend.lean
run_check "INVARIANT" rg -n '^theorem removeFromAllEndpointQueues_machine_eq' SeLe4n/Kernel/Lifecycle/Operations/CleanupPreservation.lean
run_check "INVARIANT" rg -n '^theorem removeFromAllNotificationWaitLists_machine_eq' SeLe4n/Kernel/Lifecycle/Operations/CleanupPreservation.lean
run_check "INVARIANT" rg -n '^theorem cancelIpcBlockingOnCore_confinedToCores' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_check "INVARIANT" rg -n '^theorem cancelIpcBlockingOnCore_crossCoreNonInterference' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_check "INVARIANT" rg -n '^  runComposedCancellationChecks' tests/SmpInformationFlowSuite.lean
# The victim must really occupy the home core's run queue, or §5.2b's negative
# would be testing a transition that wrote nothing.
run_check "INVARIANT" rg -n 'NEGATIVE: it is NOT confined to the executing core 0' tests/SmpInformationFlowSuite.lean
# The flagship two-core case must be exercised at RUNTIME, not only proved: the
# first cut computed both marquee write sets in their degenerate (empty /
# executing-core-only) branches, so the two-element set had no coverage.
run_check "INVARIANT" rg -n '^  runTwoCoreWriteSetChecks' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'so the call.s write set names TWO distinct cores' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'the notification write set names the waiter.s home core' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n '^import SeLe4n\.Kernel\.InformationFlow\.NonInterferenceCrossCore' SeLe4n/Platform/Staged.lean
run_check "INVARIANT" rg -n '^SeLe4n\.Kernel\.InformationFlow\.NonInterferenceCrossCore' scripts/staged_module_allowlist.txt
run_check "INVARIANT" rg -n '^import SeLe4n\.Kernel\.InformationFlow\.NonInterferenceCrossCore' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n '^  runCrossCoreWriteSetChecks' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n '^  runVisibleRemoteWakeChecks' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n '^  runCoreSetAlgebraChecks' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n '^  runResolvedFlowGateChecks' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'NEGATIVE: on core 2 itself the run queue DID move, visibly' tests/SmpInformationFlowSuite.lean
# The compile-time-validated name table (`niName!`) and the enumerated
# confinement split.  NEGATIVE: `perCoreConfinementDerived` must not regain a
# wildcard arm — a wildcard cannot be an exhaustiveness tripwire.
run_check "INVARIANT" rg -n 'syntax \(name := perCoreNiTheoremNameMacro\)' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n 'niName! nonInterference_perCore_chooseThread' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n 'niName! endpointCallOnCore_crossCoreNonInterference' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_negative_check "INVARIANT" rg -n '^  \| _ => true' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
# The axiom sweep enumerates Lean's ELABORATED ENVIRONMENT, not source text.
# Two earlier forms were not exhaustive despite saying so: a regex generator
# that missed `@[simp] theorem`, then a `docs/codebase_map.json`-driven sweep --
# but that map is itself a line-oriented source scan, so elaborator output
# (equation lemmas, match auxiliaries, macro-generated constants) never reached
# the probe.  Run it, do not merely assert it exists: a checked-in tool nobody
# invokes is not a gate.
run_check "INVARIANT" test -x scripts/check_module_axioms.py
run_check "INVARIANT" bash -lc 'source ~/.elan/env && ./scripts/check_module_axioms.py --all-smp-information-flow'
# Pin the mechanism, negatively: the sweep must not go back to reading the map
# as its declaration source.  `env.constants` is the enumeration; the map may be
# read only for the contrast line.
run_check "INVARIANT" rg -n '^theorem schedulingChannel_alphabet_bounded' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
run_check "INVARIANT" rg -n '^theorem schedulingObservationCode_injective' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
# The bound must cover the WHOLE observation: omitting `activeDomain` is licensed
# by `domainConsistentOnCore`, not by the index-bounds invariant (round 7).
run_check "INVARIANT" rg -n '^theorem schedulingObservation_activeDomain_determined' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
run_check "INVARIANT" rg -n '^theorem schedulingChannel_full_observation_determined' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
run_check "INVARIANT" rg -n 'domainConsistentOnCore' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
# The OPERATOR-FACING documents must carry the Q factor.  Round 8 found the
# advisory and the deployment guide still quoting the Q-free figure the kernel
# now disproves — the theorems were fixed and the documents an operator actually
# reads were not.  Pin both, positively and negatively.
run_check "INVARIANT" rg -n 'quantumBound|Q \+ 1|Q\+1' docs/SECURITY_ADVISORY.md
run_check "INVARIANT" rg -n 'schedulingChannel_alphabet_bounded' docs/SECURITY_ADVISORY.md
run_check "INVARIANT" rg -n 'schedulingChannel_alphabet_bounded' docs/DEPLOYMENT_GUIDE.md
# Scoped to the two GUIDANCE documents: the plan legitimately quotes the retracted
# wording when recording why it was wrong, and a history that cannot name its own
# mistakes is worth less than the anchor.
run_negative_check "INVARIANT" rg -n 'No bits-per-switch figure is' docs/SECURITY_ADVISORY.md docs/DEPLOYMENT_GUIDE.md
run_check "INVARIANT" rg -n '^theorem crossCoreTransitionIsLiveArm_count :' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
# Round 9.  (a) The capacity premises are one citable bundle, not three theorem
# signatures an operator must reconstruct.
run_check "INVARIANT" rg -n '^def schedulingCapacityPreconditions' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
run_check "INVARIANT" rg -n '^def schedulingCapacityComparable' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
run_check "INVARIANT" rg -n 'schedulingCapacityPreconditions' docs/SECURITY_ADVISORY.md docs/DEPLOYMENT_GUIDE.md
# (b) The unsupported "sub-bit-per-second" figure must not come back: it
# contradicted the upper bound by three orders of magnitude for one config.
run_prose_negative_check "INVARIANT" rg -n 'Sub-bit-per-second' docs/SECURITY_ADVISORY.md docs/DEPLOYMENT_GUIDE.md SeLe4n/
# (c) The unchanged-schedule premise holds because nothing writes the field.
# If a reconfiguration setter ever lands, this anchor fails and the capacity
# figure must be restated before it can pass again.
# Matches a DEFINITION, not a mention: the docstring that explains the absence
# necessarily names the symbol, and an anchor that cannot tell those apart fires
# on its own justification (this is the third time in this PR).
run_negative_check "INVARIANT" rg -n 'def setDomainSchedule\b' SeLe4n/
# (d) `CovertChannelId.all` cannot silently omit a constructor.
run_check "INVARIANT" rg -n '^theorem CovertChannelId.mem_all' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
# (e) ARCHITECTURAL: a live-arm claim is either backed by a delegation theorem
# in API.lean or explicitly counted as read-off-the-arm.  The eight arms that
# had such a theorem never drifted across nine review rounds; the seven that did
# not drifted three times.  The counts make the residual a tracked quantity.
run_check "INVARIANT" rg -n '^inductive LiveArmEvidence' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_check "INVARIANT" rg -n '^theorem crossCoreLiveArmDelegationBacked_count' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_check "INVARIANT" rg -n '^theorem crossCoreLiveArm_readOffTheArm_count' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_check "INVARIANT" rg -n '^theorem dispatchWithCap_tcbSuspend_delegates' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n '^theorem dispatchWithCapChecked_receive_delegates' SeLe4n/Kernel/API.lean
# Round 11: the evidence must carry a PROOF indexed by the syscall, not a name.
# A name check says a declaration exists; it does not say the declaration is
# about the arm citing it.  `syscallDelegates` makes the obligation a Prop
# computed from the syscall, so a proof cannot be borrowed between arms, and
# undelegated syscalls map to `False` so evidence cannot be fabricated.
run_check "INVARIANT" rg -n '^def syscallDelegates' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n 'delegationProof \(sid : SyscallId\) \(proof : syscallDelegates sid\)' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
# (f) Round 35: the three entries that emptied the per-core routing allowlist.
# Two of them exist to say "this live arm takes a core and writes NONE", which
# the inventory could not express before; the third carries the destroy sweep's
# occupancy bound.  All three arrive delegation-backed.
run_check "INVARIANT" rg -n '^def threadOccupiedCores' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_check "INVARIANT" rg -n '^theorem removeRunnableFromAllCores_confinedToCores' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_check "INVARIANT" rg -n '^theorem cleanupTcbReferences_confinedToCores' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_check "INVARIANT" rg -n '^def lifecycleRetypeWriteSet' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_check "INVARIANT" rg -n '^theorem lifecyclePreRetypeCleanup_confinedToCores' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_check "INVARIANT" rg -n '^theorem lifecycleRetypeDirectWithCleanupShootdownPerCoreIcache_confinedToCores' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_check "INVARIANT" rg -n '^theorem lifecycleRetypeDirectWithCleanupShootdownPerCoreIcache_crossCoreNonInterference' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_check "INVARIANT" rg -n '^theorem syscallDelegates_lifecycleRetype' SeLe4n/Kernel/API.lean
# Round 39 (SECURITY): the destroy path refuses to destroy a RUNNING thread.
# Without it the all-cores sweep clears the current slot of whichever core runs
# the target — the executing core included — and nothing schedules a successor,
# so a thread holding a `.retype` capability to its own TCB wedges its core.
# Anchored positively (the guard exists, and the pipeline calls it) and
# negatively (the rejection cannot be softened to a warning or dropped).
run_check "INVARIANT" rg -n '^def threadCurrentOnSomeCore' SeLe4n/Kernel/Lifecycle/Operations/Cleanup.lean
# Rounds 39/40: the unbind's preemption guard and its scheduling point must read
# the SAME core.  The guard was keyed on the affinity home while
# `schedContextUnbindOnCore` reschedules at `runningCoreOf?`; those diverge for
# an unbound-affinity thread on a secondary core.  Pinned positively (the guard
# reads the running core) and negatively (it must not go back to the home core).
run_check "INVARIANT" rg -n 'let runCore\? := runningCoreOf\? st tid' SeLe4n/Kernel/SchedContext/Operations.lean
run_negative_check "INVARIANT" rg -n 'let wasCurrent := \(st\.scheduler\.currentOnCore unbindHome\)' SeLe4n/Kernel/SchedContext/Operations.lean
run_check "INVARIANT" rg -n '^def schedContextUnbindWriteSet' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
# `runningCoreOf?` moved down so the unbind path can see it; the `export` keeps
# `Lifecycle.Suspend.runningCoreOf?` resolving for every existing reference.
run_check "INVARIANT" rg -n '^def runningCoreOf\?' SeLe4n/Kernel/Scheduler/Operations/Core.lean
run_check "INVARIANT" rg -n '^export SeLe4n\.Kernel \(runningCoreOf\?\)' SeLe4n/Kernel/Lifecycle/Suspend.lean
run_check "INVARIANT" rg -n '^def retypeRunningTargetRejected' SeLe4n/Kernel/Lifecycle/Operations/Cleanup.lean
run_check "INVARIANT" rg -n 'if threadCurrentOnSomeCore st tcb\.tid then' SeLe4n/Kernel/Lifecycle/Operations/CleanupPreservation.lean
run_negative_check "INVARIANT" bash -c "rg -q 'threadCurrentOnSomeCore' SeLe4n/Kernel/Lifecycle/Operations/CleanupPreservation.lean && ! rg -q 'revocationRequired' SeLe4n/Kernel/Lifecycle/Operations/CleanupPreservation.lean"
run_check "INVARIANT" rg -n '^theorem syscallDelegates_vspaceMap' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n '^theorem syscallDelegates_vspaceUnmap' SeLe4n/Kernel/API.lean
# The gate's whole point is that its exception list empties.  Pinned NEGATIVELY:
# any allowlist row at all — the file is a JSON array, so a `"syscall"` key is
# exactly one waiver — fails this check.  A gate whose waiver list can quietly
# regrow has stopped being a gate, which is the argument the three entries above
# were written to settle.
run_negative_check "INVARIANT" rg -n '"syscall"' scripts/per_core_routing_allowlist.json
run_check "INVARIANT" rg -n '^theorem crossCoreLiveArmEvidence_syscall_matches' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_negative_check "INVARIANT" rg -n 'delegationTheorem \(theoremName : String\)' SeLe4n/
# The sibling enumeration fail-open, fixed alongside CovertChannelId.all.
run_check "INVARIANT" rg -n '^theorem CrossCoreTransition.mem_all' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
# CC-1's mitigation must state the PROVEN bound, not disclaim one: retracting a
# claim to match weaker code is the direction the project forbids.
run_prose_negative_check "INVARIANT" rg -n 'No capacity bound is claimed' SeLe4n/
run_check "INVARIANT" rg -n 'log2\(\|domainSchedule\| \* \(quantumBound \+ 1\)\)' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
run_check "INVARIANT" rg -n 'env.constants.toList' scripts/check_module_axioms.py
run_check "INVARIANT" rg -n 'getModuleIdxFor\?' scripts/check_module_axioms.py
run_check "INVARIANT" rg -n 'Lean.collectAxioms' scripts/check_module_axioms.py
# The old mechanism's fingerprint: a `#print axioms` probe built from map
# declaration names.  Its absence is what keeps the sweep on `env.constants`.
run_negative_check "INVARIANT" rg -n 'print axioms' scripts/check_module_axioms.py

# PR #861 review round 10/12: the last boot-pinned live arms.  Each reroute is
# pinned positively (the per-core operation exists and the arm's delegation
# theorem names it) and negatively (the boot-pinned call site is gone from the
# arm).  The negatives match the CALL SITE, not the mention: the single-core
# operations remain in the tree as the pre-SMP surface and are named in prose.
run_check "INVARIANT" rg -n '^def endpointSendDualOnCore' SeLe4n/Kernel/IPC/CrossCore/EndpointSend.lean
run_check "INVARIANT" rg -n '^def endpointSendDualWithCapsOnCore' SeLe4n/Kernel/IPC/CrossCore/EndpointSend.lean
run_check "INVARIANT" rg -n '^def endpointSendCrossCoreDispatchChecked' SeLe4n/Kernel/IPC/CrossCore/EndpointSend.lean
run_check "INVARIANT" rg -n '^theorem dispatchWithCap_send_delegates' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n '^theorem dispatchWithCapChecked_send_delegates' SeLe4n/Kernel/API.lean
run_negative_check "INVARIANT" rg -n 'match endpointSendDualWithCaps epId' SeLe4n/Kernel/API.lean
run_negative_check "INVARIANT" rg -n 'match endpointSendDualChecked ctx epId' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n '^def migrateRunQueueBucketOnCore' SeLe4n/Kernel/SchedContext/PriorityManagement.lean
run_check "INVARIANT" rg -n '^def setPriorityOnCore' SeLe4n/Kernel/SchedContext/PriorityManagementPerCore.lean
run_check "INVARIANT" rg -n '^def setMCPriorityOnCore' SeLe4n/Kernel/SchedContext/PriorityManagementPerCore.lean
run_check "INVARIANT" rg -n '^theorem dispatchWithCap_tcbSetPriority_delegates' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n '^theorem dispatchWithCap_tcbSetMCPriority_delegates' SeLe4n/Kernel/API.lean
run_negative_check "INVARIANT" rg -n 'PriorityManagement.setPriorityOp st$' SeLe4n/Kernel/API.lean
run_negative_check "INVARIANT" rg -n 'PriorityManagement.setMCPriorityOp st$' SeLe4n/Kernel/API.lean
# The bucket migration must not go back to reading only the boot core's queue.
run_negative_check "INVARIANT" rg -n 'runQueueOnCore bootCoreId' SeLe4n/Kernel/SchedContext/PriorityManagement.lean
# CC-1: the rate factor is the TICK rate.  The pacing theorem is what stops the
# guidance drifting back to the domain-switch frequency, and the run-length
# capacity is stated per observation so the two factors travel together.
run_check "INVARIANT" rg -n '^theorem schedulingObservation_changes_on_domain_tick' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
run_check "INVARIANT" rg -n '^theorem schedulingChannel_trace_capacity' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
run_check "INVARIANT" rg -n '^theorem boundedCodeTraces_length' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
# Round 13: the trace bound quantifies the RUN preconditions, whose schedule
# clause is what turns the code count into a capacity claim.  The negative
# forbids the weaker pointwise premise returning to the theorem's signature.
run_check "INVARIANT" rg -n '^def schedulingCapacityRun' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
run_check "INVARIANT" rg -n '^theorem schedulingChannel_trace_determines_observations' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
run_negative_check "INVARIANT" rg -n 'hPre : ∀ s ∈ run, schedulingCapacityPreconditions' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
run_check "INVARIANT" rg -n 'tickFreq' docs/SECURITY_ADVISORY.md
run_negative_check "INVARIANT" rg -n 'switchFreq bits/second' docs/SECURITY_ADVISORY.md docs/DEPLOYMENT_GUIDE.md
# The axiom sweep must fail closed on a nonzero exit, not only on a Lean
# diagnostic: `lake` can fail before Lean runs at all.
run_check "INVARIANT" rg -n 'proc.returncode != 0' scripts/check_module_axioms.py

# PR #861 review round 2: the live `.call` arm is bounded by a write set that
# mirrors the dispatch's own control flow, not by hand-supplied intermediate
# states.  NEGATIVE: `endpointCallLiveWriteSet` must stay a composition rule —
# if it regains the job of guessing the chain, the reduction below is dead.
run_check "INVARIANT" rg -n '^def endpointCallDispatchChainWriteSet' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_check "INVARIANT" rg -n '^def endpointCallDispatchWriteSet' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_check "INVARIANT" rg -n '^theorem endpointCallCrossCoreDispatch_confinedToCores' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_check "INVARIANT" rg -n '^theorem endpointCallDispatchWriteSet_eq_live_of_rendezvous' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_check "INVARIANT" rg -n '^theorem endpointCallCrossCoreDispatch_crossCoreNonInterference' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_check "INVARIANT" rg -n '^theorem endpointCallWithCapsOnCore_confinedToCores' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_check "INVARIANT" rg -n '^theorem ipcUnwrapCaps_preserves_machine' SeLe4n/Kernel/IPC/Operations/CapTransfer.lean

# PR #861 review round 4 (P1): the three live cross-core arms the inventory used
# to omit — a bound-delivery signal, a receive rendezvousing with a blocked
# sender, and the composed `replyRecv`.  Each needs a write set, a confinement
# lemma and an NI instantiation, and the inventory must count all eleven.
run_check "INVARIANT" rg -n '^def notificationSignalBoundWriteSet' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_check "INVARIANT" rg -n '^theorem notificationSignalBoundOnCore_confinedToCores' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_check "INVARIANT" rg -n '^theorem notificationSignalBoundOnCore_crossCoreNonInterference' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_check "INVARIANT" rg -n '^def endpointReceiveDualWriteSet' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_check "INVARIANT" rg -n '^theorem endpointReceiveDualOnCore_confinedToCores' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_check "INVARIANT" rg -n '^theorem endpointReceiveDualOnCore_crossCoreNonInterference' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_check "INVARIANT" rg -n '^def endpointReplyRecvWriteSet' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_check "INVARIANT" rg -n '^theorem endpointReplyRecvOnCore_confinedToCores' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_check "INVARIANT" rg -n '^theorem endpointReplyRecvOnCore_crossCoreNonInterference' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_check "INVARIANT" rg -n '^theorem crossCoreNiTheorem_count : CrossCoreTransition\.all\.length = 25' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
# Round 14: all three SchedContext arms this cut made remote writers are audited.
# The negative is the point — `crossCoreRemoteWriterPendingAudit` was the counted
# gap while two were unproven, and it must not come back as an empty list, which
# would read as coverage.
run_check "INVARIANT" rg -n '^theorem schedContextBind_confinedToCores' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_check "INVARIANT" rg -n '^theorem schedContextConfigure_confinedToCores' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_check "INVARIANT" rg -n '^theorem schedContextBind_crossCoreNonInterference' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_check "INVARIANT" rg -n '^theorem schedContextConfigure_crossCoreNonInterference' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_check "INVARIANT" rg -n '^theorem storeObject_schedContext_determineTargetCore_eq' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_negative_check "INVARIANT" rg -n 'def crossCoreRemoteWriterPendingAudit' SeLe4n/
run_check "INVARIANT" rg -n '^def crossCoreTransitionIsLiveArm' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_check "INVARIANT" rg -n '^  runLiveCrossCoreArmChecks' tests/SmpInformationFlowSuite.lean
# The home-core frames those confinement proofs rest on: a dequeue and a badge
# store must be proven non-migrations, or the write sets could not name a
# pre-state home core at all.
run_check "INVARIANT" rg -n '^theorem endpointQueueRemoveDual_tcb_cpuAffinity_backward' SeLe4n/Kernel/IPC/DualQueue/Transport.lean
run_check "INVARIANT" rg -n '^theorem endpointQueueRemoveDual_determineTargetCore_eq' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_check "INVARIANT" rg -n '^theorem storeTcbReceiveComplete_determineTargetCore_eq' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean

# PR #861 review round 4 (P2): every covert-channel entry is tied to a projection
# theorem through a total, compile-time-validated table, so a new channel cannot
# be filed without deciding what proves its classification.
run_check "INVARIANT" rg -n '^inductive CovertChannelId' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
run_check "INVARIANT" rg -n '^def covertChannelEvidenceName' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
run_check "INVARIANT" rg -n '^theorem covertChannelEntry_eq_inventory' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
run_check "INVARIANT" rg -n 'niName! acceptedCovertChannel_machineTimer_excluded_from_view' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean

# PR #861 review round 18: the model's context switches have no hardware
# restore seam yet (the SVC path returns into the original caller's frame, the
# timer ISR discards the result, and SGI INTID 0 has no registered handler).
# Registered as a checked partition so SM9.E cannot wire the first restore
# without updating it.  The `_restore_pending` theorem is the load-bearing one:
# it says the gap is TOTAL, so any wiring breaks it.
run_check "INVARIANT" rg -n '^inductive ContextSwitchSite' SeLe4n/Kernel/Scheduler/PriorityInheritance/PerCore.lean
run_check "INVARIANT" rg -n '^theorem contextSwitchSites_restore_pending' SeLe4n/Kernel/Scheduler/PriorityInheritance/PerCore.lean
run_check "INVARIANT" rg -n '^theorem contextSwitchSites_complete' SeLe4n/Kernel/Scheduler/PriorityInheritance/PerCore.lean

# PR #861 review round 17: the citation table above validates only that a name
# resolves, so it accepted a witness filed against the wrong channel.  The
# binding obligation is the dependently-typed one, whose arms are checked
# against `covertChannelEntry id`.  Pinned as a *dependent* signature — the
# `(id : CovertChannelId) → id.evidenceProp` shape is what makes a misattributed
# proof a type error, so a revert to `CovertChannelId → String` fails here.
run_check "INVARIANT" rg -n '^def CovertChannelId.evidenceProp' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
run_check "INVARIANT" rg -n '^def covertChannelEvidence : \(id : CovertChannelId\) → id\.evidenceProp' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
# Each `evidenceProp` arm must read the entry through `covertChannelEntry id`
# rather than naming a constant: that indirection is what ties the arm to the id.
run_check "INVARIANT" rg -n '\(covertChannelEntry \.machineTimer\)\.modelVisible = false' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean

# PR #861 review round 4 (P2): CC-1's mitigation no longer claims a capacity
# figure no theorem supports.  NEGATIVE: the log2 bits-per-switch claim must not
# come back — `schedulingCovertChannel_bounded_width` proves transparency only.
run_check "INVARIANT" rg -n '^theorem schedulingChannelIndex_alphabet_bounded' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
run_check "INVARIANT" rg -n '^theorem schedulingChannel_not_bounded_by_scheduleLength' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
run_prose_negative_check "INVARIANT" rg -n 'bits per domain switch' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
# Round 42: the CC-1 docstring quoted the retracted rate as "at switch
# frequency", which the single-spelling ban above did not cover.  Both
# spellings are forbidden now — the figure is paced by ticks, not switches.
run_prose_negative_check "INVARIANT" rg -n 'at switch frequency' \
  SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean

# PR #861 review round 2 (P2) / round 4 (P2): the per-core enforcement boundary
# audits the LIVE cross-core wrappers, not only the single-core table.
run_check "INVARIANT" rg -n '^def crossCoreEnforcementEntries' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
run_check "INVARIANT" rg -n '^def syscallIdToEnforcementNamePerCore' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
run_check "INVARIANT" rg -n '^theorem enforcementBoundaryPerCore_is_complete_crossCore' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
run_check "INVARIANT" rg -n '^theorem enforcementBoundaryPerCore_crossCore_classes_match' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
run_check "INVARIANT" rg -n '^theorem syscallIdToEnforcementNamePerCore_differs_at_fifteen' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean

# ---------------------------------------------------------------------------
# WS-SM SM8.C — the per-core declassification audit
# (plan SMP_INFORMATION_FLOW_PLAN.md §4.3 / §5 SM8.C.1 … SM8.C.7).
# ---------------------------------------------------------------------------
# SM8.C.1: the record carries the originating core and a TYPED basis.  Both are
# pinned negatively as well: a default on the core field would silently
# attribute every event to the boot core, and reverting the basis to a bare
# `String` would take `authorizationBasis_perCore` with it.
run_check "INVARIANT" rg -n '^  originatingCore : Concurrency.CoreId' SeLe4n/Kernel/InformationFlow/AuditRecord.lean
run_check "INVARIANT" rg -n '^  authorizationBasis : DeclassificationBasis' SeLe4n/Kernel/InformationFlow/AuditRecord.lean
run_check "INVARIANT" rg -n '^inductive DeclassificationBasis' SeLe4n/Kernel/InformationFlow/AuditRecord.lean
run_negative_check "INVARIANT" rg -n 'originatingCore : Concurrency.CoreId :=' SeLe4n/Kernel/InformationFlow/AuditRecord.lean
run_negative_check "INVARIANT" rg -n 'authorizationBasis : String' SeLe4n/Kernel/InformationFlow/AuditRecord.lean
# The external rendering must stay byte-identical to the pre-SM8.C string field.
run_check "INVARIANT" rg -n 'DeclassificationPolicy.canDeclassify"' SeLe4n/Kernel/InformationFlow/AuditRecord.lean
run_check "INVARIANT" rg -n '^theorem declassificationEvent_originatingCore_valid' SeLe4n/Kernel/InformationFlow/AuditRecord.lean
run_check "INVARIANT" rg -n '^theorem declassificationAuditLog_originatingCores_valid' SeLe4n/Kernel/InformationFlow/AuditRecord.lean
# SM8.C.1: the producer.  Before this cut `DeclassificationEvent` had no writer
# at all, so the audit trail was a type nothing constructed.
run_check "INVARIANT" rg -n '^def declassifyStoreOnCore' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
run_check "INVARIANT" rg -n '^theorem declassifyStoreOnCore_records_one' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
run_check "INVARIANT" rg -n '^theorem declassifyStoreOnCore_denied_no_audit_entry' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
# SM8.C.3: attribution — the source domain is READ from the executing core's
# running subject.  The negative witness is what makes the wrapper load-bearing.
run_check "INVARIANT" rg -n '^def declassifyStoreFromCore' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
run_check "INVARIANT" rg -n '^theorem declassifyStoreFromCore_event_attributable' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
run_check "INVARIANT" rg -n '^theorem declassifyStoreOnCore_admits_unattributable' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
# SM8.C.4: the per-core views partition the log exactly.
run_check "INVARIANT" rg -n '^def auditLogOnCore' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
run_check "INVARIANT" rg -n '^theorem declassificationAuditLog_partitions_by_core' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
run_check "INVARIANT" rg -n '^theorem DeclassificationEvent_perCore_audit' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
# SM8.C.2: the cross-core chain, and the theorem that decides the design — a
# per-core log would have lost it.
run_check "INVARIANT" rg -n '^theorem crossCoreChain_not_within_one_view' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
run_check "INVARIANT" rg -n '^theorem declassificationChain_recorded_across_cores' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
run_check "INVARIANT" rg -n '^theorem declassificationAuditLog_timestamp_identifies_event' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
# SM8.C.6: the rules, including the SM8.B consumer.  The endpoint rule must be
# stated against the STATE-RESOLVED gate: `endpointFlowCheck` takes neither a
# state nor a core, so a per-core claim about it would carry a decorative `c`.
run_check "INVARIANT" rg -n '^theorem endpointOverride_is_not_a_declassification_basis' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
run_check "INVARIANT" rg -n 'endpointFlowCheckAtCore ctx epPolicy endpointId st c = true' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
run_check "INVARIANT" rg -n 'endpointFlowCheck_restricted_subset_perCore' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
run_check "INVARIANT" rg -n '^theorem declassificationChain_hop_authorization_does_not_compose' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
run_check "INVARIANT" rg -n '^def chainLaunders' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
# SM8.C.5: `authorizationBasis_perCore`, and the dependently-typed rule evidence
# that makes a misattributed proof a type error rather than a stale string.
run_check "INVARIANT" rg -n '^theorem authorizationBasis_perCore' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
run_check "INVARIANT" rg -n '^def DeclassificationRuleId.evidenceProp' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
run_check "INVARIANT" rg -n '^def declassificationRuleEvidence : \(id : DeclassificationRuleId\) → id\.evidenceProp' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
run_check "INVARIANT" rg -n 'niName! chainCompositionAuthorized_sound' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
run_check "INVARIANT" rg -n '^theorem declassificationRules_count' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
# The declassification's own per-core non-interference, plus the statement that
# auditing adds no observable state.
run_check "INVARIANT" rg -n '^theorem declassifyStoreOnCore_perCore_NI' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
run_check "INVARIANT" rg -n '^theorem declassifyStoreOnCore_state_trail_independent' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
# SM8.C.7: the runtime scenarios and their load-bearing negatives.
run_check "INVARIANT" rg -n '^  runDeclassificationProducerChecks' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n '^  runDeclassificationAttributionChecks' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n '^  runDeclassificationPartitionChecks' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n '^  runDeclassificationChainChecks' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n '^  runDeclassificationRuleChecks' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n '^  runDeclassificationBasisChecks' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n '^  runDeclassificationNonInterferenceChecks' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'NEGATIVE: no single core.s view contains the whole chain' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'NEGATIVE: the unattributed form records a domain its subject does not hold' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'NEGATIVE: authorize 2 . 0 too and the same chain no longer launders' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n '^import SeLe4n\.Kernel\.InformationFlow\.DeclassificationPerCore' tests/SmpInformationFlowSuite.lean
# The staged module must stay in the build graph and on the allowlist.
run_check "INVARIANT" rg -n '^import SeLe4n\.Kernel\.InformationFlow\.DeclassificationPerCore' SeLe4n/Platform/Staged.lean
run_check "INVARIANT" rg -n '^SeLe4n\.Kernel\.InformationFlow\.DeclassificationPerCore' scripts/staged_module_allowlist.txt
run_check "INVARIANT" rg -n 'SeLe4n\.Kernel\.InformationFlow\.DeclassificationPerCore' scripts/check_module_axioms.py
# SM8.B registered debt (a), CLOSED: the configured per-endpoint flow policy is
# now carried by `LabelingContext` and read by the four endpoint-keyed gates.
# The gate CONJOINS rather than replaces, which is what makes V6-G's
# `endpointPolicyRestricted` structural — pinned positively (the definition) and
# negatively (no gate site may go back to a bare `securityFlowsTo`).
run_check "INVARIANT" rg -n '^  endpointPolicy : EndpointFlowPolicy' SeLe4n/Kernel/InformationFlow/Policy.lean
run_check "INVARIANT" rg -n '^def endpointOverrideAllows' SeLe4n/Kernel/InformationFlow/Policy.lean
run_check "INVARIANT" rg -n '^def endpointFlowGate' SeLe4n/Kernel/InformationFlow/Policy.lean
run_check "INVARIANT" rg -n 'securityFlowsTo srcLabel dstLabel && endpointOverrideAllows' SeLe4n/Kernel/InformationFlow/Policy.lean
run_check "INVARIANT" rg -n '^theorem endpointFlowGate_implies_securityFlowsTo' SeLe4n/Kernel/InformationFlow/Policy.lean
run_check "INVARIANT" rg -n '^theorem endpointFlowGate_is_not_securityFlowsTo' SeLe4n/Kernel/InformationFlow/Policy.lean
run_check "INVARIANT" rg -n 'endpointFlowGate ctx endpointId senderLabel endpointLabel' SeLe4n/Kernel/InformationFlow/Enforcement/Wrappers.lean
run_check "INVARIANT" rg -n 'endpointFlowGate ctx endpointId endpointLabel receiverLabel' SeLe4n/Kernel/InformationFlow/Enforcement/Wrappers.lean
run_check "INVARIANT" rg -n 'endpointFlowGate ctx endpointId callerLabel endpointLabel' SeLe4n/Kernel/InformationFlow/Enforcement/Wrappers.lean
run_check "INVARIANT" rg -n 'endpointFlowGate ctx epId' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n 'endpointFlowGate ctx endpointId' SeLe4n/Kernel/IPC/CrossCore/EndpointSend.lean
run_check "INVARIANT" rg -n 'endpointFlowGate ctx endpointId' SeLe4n/Kernel/IPC/CrossCore/EndpointCallDispatch.lean
run_negative_check "INVARIANT" rg -n 'if !securityFlowsTo \(ctx\.endpointLabelOf epId\)' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n '^theorem liveEndpointOverride_is_not_a_declassification_basis' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean

# ---------------------------------------------------------------------------
# WS-SM SM8.C.8 / SM8.C.9 — the mounted audit trail and the live `.declassify`
# syscall.
# ---------------------------------------------------------------------------
# SM8.C.8: the trail is durable kernel state with a FAIL-CLOSED capacity bound.
# The negative pin is the load-bearing one: a ring buffer that drops an entry
# would leave an authorized downgrade with no record, which is the exact failure
# the phase exists to exclude, so `recordDeclassificationChecked` must have no
# arm that returns a truncated log.
run_check "INVARIANT" rg -n '^  declassificationAuditLog : SeLe4n.Kernel.DeclassificationAuditLog' SeLe4n/Model/State.lean
run_check "INVARIANT" rg -n '^  declassificationAuditLog : SeLe4n.Kernel.DeclassificationAuditLog$' SeLe4n/Model/FrozenState.lean
run_check "INVARIANT" rg -n '^def maxDeclassificationAuditEntries' SeLe4n/Kernel/InformationFlow/AuditRecord.lean
run_check "INVARIANT" rg -n '^def auditLogBounded' SeLe4n/Kernel/InformationFlow/AuditRecord.lean
run_check "INVARIANT" rg -n '^def recordDeclassificationChecked' SeLe4n/Kernel/InformationFlow/AuditRecord.lean
run_check "INVARIANT" rg -n 'auditLogBounded st.declassificationAuditLog' SeLe4n/Kernel/Architecture/Invariant.lean
run_check "INVARIANT" rg -n '^theorem proofLayerInvariantBundle_setDeclassificationAuditLog' SeLe4n/Kernel/Architecture/Invariant.lean
run_check "INVARIANT" rg -n '^theorem declassificationAuditLog_write_preserves_projection' SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean
run_check "INVARIANT" rg -n '^theorem freeze_preserves_declassificationAuditLog' SeLe4n/Model/FrozenState.lean
run_check "INVARIANT" rg -n '^theorem bootFromPlatform_declassificationAuditLog_eq' SeLe4n/Platform/Boot.lean
run_negative_check "INVARIANT" rg -n 'declassificationAuditLog := log.drop|declassificationAuditLog := log.tail' SeLe4n
# SM8.C.5: the flat rendering is NOT injective, so the trust bit ships as data.
run_check "INVARIANT" rg -n '^structure RenderedDeclassificationBasis' SeLe4n/Kernel/InformationFlow/AuditRecord.lean
run_check "INVARIANT" rg -n '^theorem render_not_injective' SeLe4n/Kernel/InformationFlow/AuditRecord.lean
run_check "INVARIANT" rg -n '^theorem renderTagged_injective' SeLe4n/Kernel/InformationFlow/AuditRecord.lean
# SM8.C.9: the live syscall.  The unchecked dispatch must FAIL CLOSED — there is
# no unchecked declassification, because "unchecked" would authorize every
# downgrade — and the default policy must deny.
run_check "INVARIANT" rg -n '^  \| declassify' SeLe4n/Model/Object/Types.lean
run_check "INVARIANT" rg -n '^def declassificationDecision' SeLe4n/Kernel/InformationFlow/Enforcement/Soundness.lean
run_check "INVARIANT" rg -n '^theorem declassifyStore_eq_decision_bind' SeLe4n/Kernel/InformationFlow/Enforcement/Soundness.lean
run_check "INVARIANT" rg -n '^def authorizeDeclassificationOnCore' SeLe4n/Kernel/InformationFlow/Declassification.lean
run_check "INVARIANT" rg -n '^theorem authorizeDeclassificationOnCore_frame' SeLe4n/Kernel/InformationFlow/Declassification.lean
run_check "INVARIANT" rg -n '^theorem authorizeDeclassificationOnCore_never_unaudited' SeLe4n/Kernel/InformationFlow/Declassification.lean
# The decision runs BEFORE the capacity check, so a caller the policy refuses
# learns nothing about trail occupancy — which is a function of how many
# authorized downgrades other subjects performed.  Checking capacity first would
# make that a channel from every declassifying subject to every caller.
run_check "INVARIANT" rg -n '^theorem authorizeDeclassificationOnCore_denied_before_capacity' SeLe4n/Kernel/InformationFlow/Declassification.lean
run_check "INVARIANT" rg -n 'NEGATIVE: a policy-refused caller learns nothing about trail occupancy' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n '^def declassifyObjectFromCore' SeLe4n/Kernel/InformationFlow/Declassification.lean
run_check "INVARIANT" rg -n '^theorem declassifyObjectFromCore_destination_is_target_domain' SeLe4n/Kernel/InformationFlow/Declassification.lean
run_check "INVARIANT" rg -n '^theorem declassifyObjectFromCore_preserves_proofLayerInvariantBundle' SeLe4n/Kernel/InformationFlow/Declassification.lean
run_check "INVARIANT" rg -n '\| \.declassify => fun _ => \.error \.declassificationDenied' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n '^theorem dispatchWithCap_declassify_denied' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n '^theorem dispatchWithCapChecked_declassify_delegates' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n '^theorem syscallDelegates_declassify' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n 'declassificationPolicy : DeclassificationPolicy := \{ canDeclassify := fun _ _ => false \}' SeLe4n/Kernel/InformationFlow/Policy.lean
run_check "INVARIANT" rg -n '^def lockSet_declassify' SeLe4n/Kernel/Concurrency/Locks/LockSetTransitions.lean
run_check "INVARIANT" rg -n '^theorem lockSet_declassify_size_le' SeLe4n/Kernel/Concurrency/Locks/Deadlock.lean
run_check "INVARIANT" rg -n 'policyGated "declassifyObjectFromCore"' SeLe4n/Kernel/InformationFlow/Enforcement/Wrappers.lean
run_check "INVARIANT" rg -n '\| declassifyDispatch' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_check "INVARIANT" rg -n 'Declassify = 30' rust/sele4n-types/src/syscall.rs
run_check "INVARIANT" rg -n 'Declassify = 30' rust/sele4n-hal/src/svc_dispatch.rs
run_check "INVARIANT" rg -n 'AuditLogCapacityExceeded = 54' rust/sele4n-types/src/error.rs
run_check "INVARIANT" rg -n '^pub fn declassify' rust/sele4n-sys/src/declassify.rs
# SM8.C.3 (**enforcement, not convention**): a production or live module must
# not call the UNATTRIBUTED forms directly — the attributed wrappers
# (`declassifyStoreFromCore`, `declassifyObjectFromCore`) are the only doors,
# because §3's negative witness shows the unattributed form records a source
# domain no state supports.  `API.lean` is the live dispatch and must name only
# the attributed entry point.
run_negative_check "INVARIANT" rg -n 'declassifyStoreOnCore|authorizeDeclassificationOnCore' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n 'declassifyObjectFromCore \(liftLegacyContext ctx\)' SeLe4n/Kernel/API.lean
# SM8.C §11/§12: scope witnesses and run-level completeness.
run_check "INVARIANT" rg -n '^theorem recordDeclassification_admits_ill_formed' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
run_check "INVARIANT" rg -n '^theorem declassificationChainLinked_is_syntactic' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
run_check "INVARIANT" rg -n '^theorem declassificationSubjectDomain_is_core_selected' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
run_check "INVARIANT" rg -n '^theorem declassification_refusal_is_unrecorded' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
run_check "INVARIANT" rg -n '^def declassifyRun' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
run_check "INVARIANT" rg -n '^theorem declassifyRun_records_each' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
run_check "INVARIANT" rg -n '^theorem declassifyRun_frame' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
# SM8.C: V6-G at the label level — the gate is restricted for EVERY context.
run_check "INVARIANT" rg -n '^theorem endpointGateRestricted_always' SeLe4n/Kernel/InformationFlow/Policy.lean
run_check "INVARIANT" rg -n '^theorem endpointGateRestricted_survives_widening_override' SeLe4n/Kernel/InformationFlow/Policy.lean
# SM8.C: the gates the endpoint policy deliberately does NOT govern, as checked
# facts rather than prose.
run_check "INVARIANT" rg -n '^theorem notificationSignalChecked_endpointPolicy_independent' SeLe4n/Kernel/InformationFlow/Enforcement/Wrappers.lean
run_check "INVARIANT" rg -n '^theorem endpointReplyChecked_endpointPolicy_independent' SeLe4n/Kernel/InformationFlow/Enforcement/Wrappers.lean
run_check "INVARIANT" rg -n '^theorem endpointSendDualChecked_endpointPolicy_dependent' SeLe4n/Kernel/InformationFlow/Enforcement/Wrappers.lean
# SM8.C.7: the new runtime scenario groups and the golden fixture.
run_check "INVARIANT" rg -n '^  runLiveDeclassifyChecks' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n '^  runDeclassifyCapacityChecks' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n '^  runDeclassifyRunChecks' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n '^  runDeclassifyRenderingChecks' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n '^  runDeclassifyChainTopologyChecks' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n '^  runDeclassTraceFixtureCheck' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'NEGATIVE: an unconfigured deployment cannot declassify' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'at capacity the live syscall REFUSES the downgrade rather than dropping the record' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'NEGATIVE: the flat rendering collides' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n '^\[smp-declassification\]' tests/fixtures/smp_declassification_audit.expected
run_check "INVARIANT" rg -n 'smp_declassification_audit\.expected' tests/fixtures/smp_declassification_audit.expected.sha256
# The new production module must stay OUT of the staged allowlist — the live
# `.declassify` arm imports it, so staging it would break the partition gate.
run_negative_check "INVARIANT" rg -n 'SeLe4n\.Kernel\.InformationFlow\.(AuditRecord|Declassification)$' scripts/staged_module_allowlist.txt

# SM8.C: the two enforcement families, completed.  Both were documented as
# covering "all policy-gated operations" while covering seven of twelve; the
# four IPC/notification wrappers that landed after the families were written
# now belong to them, as does the declassification.  Anchored per member,
# because a count alone cannot say WHICH entry lost its theorem.
run_check "INVARIANT" rg -n '^theorem endpointCallChecked_denied_preserves_state' SeLe4n/Kernel/InformationFlow/Enforcement/Soundness.lean
run_check "INVARIANT" rg -n '^theorem enforcement_sufficiency_endpointCall' SeLe4n/Kernel/InformationFlow/Enforcement/Soundness.lean
run_check "INVARIANT" rg -n '^theorem endpointReplyChecked_denied_preserves_state' SeLe4n/Kernel/InformationFlow/Enforcement/Soundness.lean
run_check "INVARIANT" rg -n '^theorem enforcement_sufficiency_endpointReply' SeLe4n/Kernel/InformationFlow/Enforcement/Soundness.lean
run_check "INVARIANT" rg -n '^theorem notificationWaitChecked_denied_preserves_state' SeLe4n/Kernel/InformationFlow/Enforcement/Soundness.lean
run_check "INVARIANT" rg -n '^theorem enforcement_sufficiency_notificationWait' SeLe4n/Kernel/InformationFlow/Enforcement/Soundness.lean
run_check "INVARIANT" rg -n '^theorem endpointReplyRecvChecked_denied_preserves_state' SeLe4n/Kernel/InformationFlow/Enforcement/Soundness.lean
run_check "INVARIANT" rg -n '^theorem enforcement_sufficiency_endpointReplyRecv' SeLe4n/Kernel/InformationFlow/Enforcement/Soundness.lean
run_check "INVARIANT" rg -n '^theorem declassifyObjectFromCore_denied_preserves_state' SeLe4n/Kernel/InformationFlow/Declassification.lean
run_check "INVARIANT" rg -n '^theorem authorizeDeclassificationOnCore_denied_preserves_state' SeLe4n/Kernel/InformationFlow/Declassification.lean
run_check "INVARIANT" rg -n '^theorem enforcement_sufficiency_declassify' SeLe4n/Kernel/InformationFlow/Declassification.lean
# The boundary count is pinned by a theorem; `enforcementBoundary`'s own
# docstring must NOT restate it, which is how it came to read "33 entries"
# across six expansions.
run_prose_negative_check "INVARIANT" rg -n 'classification table \([0-9]+ entries\)' SeLe4n/Kernel/InformationFlow/Enforcement/Wrappers.lean
run_check "INVARIANT" rg -n 'enforcementBoundaryExtended.length = 39' SeLe4n/Kernel/InformationFlow/Enforcement/Soundness.lean
run_check "INVARIANT" rg -n '^  runEndpointPolicyGateChecks' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'NEGATIVE: a widening override cannot open a flow the lattice denies' tests/SmpInformationFlowSuite.lean


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
run_check "INVARIANT" rg -n '^theorem dispatchWithCap_call_uses_crossCoreDispatch' SeLe4n/Kernel/API.lean
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
# WS-SM SM6.A (v0.31.67): the cross-core SGI-firing dispatch entry
# `lean_syscall_dispatch_cross_core` (`SyscallDispatchEntry`) is PROMOTED to the
# production library (`SeLe4n.lean`) with its `PriorityInheritance.PerCore` +
# `Concurrency.Runtime` closure, and the Rust extern is flipped to it (line 993):
# the live syscall fires the diff-recovered cross-core `.reschedule` SGIs.  The
# boot-pinned `syscall_dispatch_inner` (line 966) remains in `Platform.FFI` as the
# single-core entry.
run_check "INVARIANT" rg -n '^@\[export lean_syscall_dispatch_cross_core\]' SeLe4n/Kernel/SyscallDispatchEntry.lean
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
# WS-RC R2.B.4 / WS-SM SM6.A: Rust ↔ Lean symbol alignment — the FFI inner
# symbol the Rust HAL extern-imports must match a Lean `@[export]` name in the
# production closure.  Post-v0.31.67 the live entry is the cross-core
# `lean_syscall_dispatch_cross_core` (`@[export]` in `SyscallDispatchEntry`, now
# promoted into the `SeLe4n.lean` production library), so the Rust extern names
# it; the boot-pinned `syscall_dispatch_inner` (`@[export]` in `Platform.FFI`,
# line 966) stays as the single-core entry.
run_check "INVARIANT" rg -n 'fn lean_syscall_dispatch_cross_core' rust/sele4n-hal/src/svc_dispatch.rs
# WS-SM SM6.E: the suspend atomicity bracket is flipped to the cross-core
# entry `suspend_thread_cross_core` (`@[export]` in `SyscallDispatchEntry`,
# backed by the verified per-core `suspendThreadOnCore`: home-core deschedule
# + remote `.reschedule` SGI after the commit).  The boot-pinned
# `suspend_thread_inner` (`@[export]` in `Platform.FFI`) stays as the
# single-core entry.
run_check "INVARIANT" rg -n 'fn suspend_thread_cross_core' rust/sele4n-hal/src/ffi.rs
run_check "INVARIANT" rg -n '^@\[export suspend_thread_cross_core\]' SeLe4n/Kernel/SyscallDispatchEntry.lean
run_check "INVARIANT" rg -n '^def suspendThreadOnCore' SeLe4n/Kernel/IPC/CrossCore/Cancellation.lean
run_check "INVARIANT" rg -n '^theorem suspendThreadOnCore_sgi_remote_reschedule' SeLe4n/Kernel/IPC/CrossCore/Cancellation.lean
run_check "INVARIANT" rg -n '^theorem crossCoreSgiBody_remote_deschedule' SeLe4n/Kernel/Scheduler/PriorityInheritance/PerCore.lean
# WS-SM SM6.E (PR #831 review 2): disinheritance scheduling points — the
# suspend's D4-N capture -> clear -> revert-from-server order, the local
# preemption gate on a deboosted executing-core current, the diff seam's
# deboosted-current rule (a still-current remote server whose effective
# priority dropped is poked), and the declared PIP chain-walk obligation.
run_check "INVARIANT" rg -n '^def currentEffectivePrio\?' SeLe4n/Kernel/Lifecycle/Suspend.lean
run_check "INVARIANT" rg -n '^def currentDeboostedFrom' SeLe4n/Kernel/Lifecycle/Suspend.lean
run_check "INVARIANT" rg -n '^def suspendRescheduleOnCore' SeLe4n/Kernel/IPC/CrossCore/Cancellation.lean
run_check "INVARIANT" rg -n '^theorem suspendRescheduleOnCore_sgi_shape' SeLe4n/Kernel/IPC/CrossCore/Cancellation.lean
run_check "INVARIANT" rg -n '^theorem crossCoreSgiBody_remote_deboost_current' SeLe4n/Kernel/Scheduler/PriorityInheritance/PerCore.lean
run_check "INVARIANT" rg -n '^@\[inline\] def pipChainStart_tcbSuspend' SeLe4n/Kernel/Concurrency/Locks/LockSetTransitions.lean
# PR #831 review 4: the running-core resolution (an unbound victim current on
# a secondary core is descheduled + poked on THAT core), the re-keyed diff
# rules, and the write-set-honest sweeps + neighbour-TCB footprint members.
# Rounds 39/40: the definition moved to `Scheduler/Operations/Core.lean` so the
# unbind path can key its guard on it; `Suspend.lean` re-exports the name.
run_check "INVARIANT" rg -n '^def runningCoreOf\?' SeLe4n/Kernel/Scheduler/Operations/Core.lean
run_check "INVARIANT" rg -n '^theorem currentScan_boot_of_single_core' SeLe4n/Kernel/Scheduler/PriorityInheritance/PerCore.lean
run_check "INVARIANT" rg -n '^def cancelSpliceNeighbors\?' SeLe4n/Kernel/IPC/CrossCore/Cancellation.lean
# Audit closure (v0.32.66): running-core footprint triple, EDF deadline rules,
# current-uniqueness invariant slice, donation-side observer capstone.
run_check "INVARIANT" rg -n '^def sortedSchedCoreTriple' SeLe4n/Kernel/IPC/CrossCore/Cancellation.lean
run_check "INVARIANT" rg -n '^def currentThreadUniqueAcrossCores' SeLe4n/Kernel/Scheduler/Invariant/PerCore.lean
run_check "INVARIANT" rg -n '^theorem cancelDonationOnCore_observer_atomic' SeLe4n/Kernel/IPC/CrossCore/Cancellation.lean

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
#check @SeLe4n.Kernel.dispatchWithCap_call_uses_crossCoreDispatch
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
-- WS-SM SM5.E: idleThreadId (+ injectivity) moved to SeLe4n.Kernel.Scheduler.IdleThread.
#check @SeLe4n.Kernel.idleThreadId_injective
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
#check @SeLe4n.Model.KernelObjectType.variants_count_exactly_eight
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
-- SM3.B.3 audit-pass-5 — PIP-chain-walk start markers (+ SM6.E suspend).
#check @SeLe4n.Kernel.Concurrency.pipChainStart_endpointCall
#check @SeLe4n.Kernel.Concurrency.pipChainStart_endpointReply
#check @SeLe4n.Kernel.Concurrency.pipChainStart_replyRecv
#check @SeLe4n.Kernel.Concurrency.pipChainStart_tcbSuspend
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
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake build SeLe4n.Kernel.Concurrency.Locks.WithLockSetInventory'
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake env lean --stdin <<"EOF"
import SeLe4n.Kernel.Concurrency.LockSet
import SeLe4n.Kernel.Concurrency.Locks.WithLockSet
import SeLe4n.Kernel.Concurrency.Locks.LockSetHeld
import SeLe4n.Kernel.Concurrency.Locks.LockSet2PL
import SeLe4n.Kernel.Concurrency.Locks.DynamicChainExtension
import SeLe4n.Kernel.Concurrency.Locks.WithLockSetInventory

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
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake build SeLe4n.Kernel.Concurrency.Locks.DeadlockInventory'
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake env lean --stdin <<"EOF"
import SeLe4n.Kernel.Concurrency.LockSet
import SeLe4n.Kernel.Concurrency.Locks.Deadlock
import SeLe4n.Kernel.Concurrency.Locks.DeadlockInventory

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
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake build SeLe4n.Kernel.Concurrency.Locks.SerializabilityInventory'
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake env lean --stdin <<"EOF"
import SeLe4n.Kernel.Concurrency.LockSet
import SeLe4n.Kernel.Concurrency.Locks.Serializability
import SeLe4n.Kernel.Concurrency.Locks.SerializabilityInventory

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
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake build SeLe4n.Kernel.Scheduler.Operations.CrossCoreWakeInventory'
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake env lean --stdin <<"EOF"
import SeLe4n.Kernel.Scheduler.Operations.PerCoreWake
import SeLe4n.Kernel.Scheduler.Operations.CrossCoreWakeInventory
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
#check @determineTargetCore_admits_thread

-- SM5.C.1 enqueueRunnableOnCore lemmas.
#check @enqueueRunnableOnCore_preserves_objects_invExt
#check @enqueueRunnableOnCore_preserves_runQueueOnCore_wellFormed
#check @enqueueRunnableOnCore_mem_runQueueOnCore
#check @enqueueRunnableOnCore_makes_ready
#check @enqueueRunnableOnCore_preserves_woken_thread_fields
#check @enqueueRunnableOnCore_runQueueOnCore_ne
#check @enqueueRunnableOnCore_currentOnCore
#check @enqueueRunnableOnCore_getTcb?_ne
#check @enqueueRunnableOnCore_no_tcb_noop
#check @enqueueRunnableOnCore_eq_self_of_runnable
#check @runnableOnSomeCore

-- SM5.C.2/.4/.10 wake-semantics theorems.
#check @wakeThread_state_eq_enqueue
#check @wakeThread_emits_sgi_if_remote
#check @wakeThread_no_sgi_if_local
#check @wakeThread_sgi_is_reschedule
#check @wakeThread_target_runQueue_contains
#check @wakeThread_target_admits_thread
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
#check @handleRescheduleSgiOnCore_keeps_current_when_outranked
#check @candidateOutranksCurrentOnCore

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

-- WS-SM SM5.F.4: cross-core PIP wake dispatch + coalescing (Concurrency.Runtime).
#check @dedupCrossCoreSgis
#check @fireCrossCoreSgis
#check @dedupCrossCoreSgis_subset
#check @dedupCrossCoreSgis_nodup_cores

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
#check @crossCoreWakeTheorems
#check @crossCoreWakeTheorems_count
#check @crossCoreWakeTheorems_lockSet_count
#check @crossCoreWakeTheorems_target_count
#check @crossCoreWakeTheorems_enqueue_count
#check @crossCoreWakeTheorems_wake_count
#check @crossCoreWakeTheorems_handler_count
#check @crossCoreWakeTheorems_preservation_count
#check @crossCoreWakeTheorems_latencyAffinityEmit_count
#check @crossCoreWakeTheorems_partition_sum
#check @crossCoreWakeTheorems_identifiers_nodup
#check @crossCoreWakeTheorems_descriptions_nodup
EOF'

# WS-SM SM5.D — per-core timer tick surface anchors.  Covers the SM5.D.2/.4/.5/.6/.9
# production transitions (`timerTickOnCore` / `timerTickBudgetOnCore` /
# `processReplenishmentsDueOnCore` / `decrementDomainTimeOnCore` /
# `scheduleEffectiveOnCore` / `switchDomainOnCore`+`scheduleDomainOnCore`, in
# `Scheduler.Operations.Core`), the SM5.D.3 cross-domain lock-set (+
# `ReplenishQueueLockId` / `SchedLockId.replenishQueue` order facts), SM5.D.6
# domain-rotation theorems, the SM5.D.4 cross-core wake (`cbsReplenish_can_wake_remote_core`),
# the SM5.D.5 budget tick + the IPC-timeout objects-`invExt` preservation chain,
# the SM5.D.2 headlines + objects-`invExt` preservation, SM5.D.7 WCRT bound,
# SM5.D.8 decidability, and the SM5.D.1 export seam.  A rename / removal of any
# SM5.D symbol fails here at elaboration time before the test suite.
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake build SeLe4n.Kernel.Scheduler.Operations.PerCoreTimerTick'
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake build SeLe4n.Kernel.Scheduler.Operations.PerCoreRunLoop'
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake build SeLe4n.Kernel.PerCoreTimerEntry'
run_check "INVARIANT" bash -lc 'source ~/.elan/env && cat > /tmp/sm5d_surface.lean <<EOF
import SeLe4n.Kernel.Scheduler.Operations.PerCoreTimerTick
import SeLe4n.Kernel.Scheduler.Operations.PerCoreRunLoop
import SeLe4n.Kernel.PerCoreTimerEntry
open SeLe4n.Kernel
-- SM5.D.2/.4/.5/.6/.9 production transitions.
#check @timerTickOnCore
#check @timerTickBudgetOnCore
#check @processReplenishmentsDueOnCore
#check @processOneReplenishmentOnCore
#check @replenishWakeTarget
#check @decrementDomainTimeOnCore
#check @scheduleEffectiveOnCore
#check @saveOutgoingContextOnCore
#check @switchDomainOnCore
#check @scheduleDomainOnCore
#check @tcbBlockingInfo
-- SM5.D.3 lock-set + replenish-queue lock domain.
#check @ReplenishQueueLockId
#check @ReplenishQueueLockId.le_total
#check @ReplenishQueueLockId.replenishQueueLockLevel
#check @SchedLockId.object_lt_replenishQueue
#check @SchedLockId.runQueue_lt_replenishQueue
#check @timerTickOnCoreLockSet
#check @timerTickOnCoreLockSet_length
#check @timerTickOnCoreLockSet_write_only
#check @timerTickOnCoreLockSet_contains_objStore_write
#check @timerTickOnCoreLockSet_contains_runQueue_write
#check @timerTickOnCoreLockSet_contains_replenishQueue_write
#check @timerTickOnCoreLockSet_keys_nodup
#check @timerTickOnCoreLockSet_pairwise_le
#check @timerTickOnCoreLockSet_size_le_maxLockSetSize
-- SM5.D.6 domain accounting (audit-pass-2: pure non-boundary decrement).
#check @decrementDomainTimeOnCore_decrements
#check @decrementDomainTimeOnCore_activeDomainOnCore
#check @decrementDomainTimeOnCore_domainTimeRemainingOnCore_ne
#check @decrementDomainTimeOnCore_preserves_domainTimeRemainingPositiveOnCore
#check @decrementDomainTimeOnCore_objects_eq
-- SM5.D.4 CBS replenishment + cross-core wake.
#check @cbsReplenish_can_wake_remote_core
#check @runningOnSomeCore
#check @processOneReplenishmentOnCore_local_no_sgi
#check @processOneReplenishmentOnCore_no_sgi_if_no_target
#check @processOneReplenishmentOnCore_preserves_objects_invExt
#check @processReplenishmentsDueOnCore_preserves_objects_invExt
#check @processReplenishmentsDueOnCore_preserves_runQueueOnCore_wellFormed
#check @processReplenishmentsDueOnCore_machine_eq
-- SM5.D.5 budget tick + IPC-timeout objects preservation chain.
#check @timerTickBudgetOnCore_unbound_not_preempted
#check @timerTickBudgetOnCore_unbound_preempts
#check @timerTickBudgetOnCore_preserves_objects_invExt
#check @revertPriorityInheritance_preserves_objects_invExt
#check @timeoutThread_preserves_objects_invExt
#check @timeoutBlockedThreads_preserves_objects_invExt
#check @scheduleEffectiveOnCore_preserves_objects_invExt
-- SM5.D.2 headlines + preservation.
#check @timerTickOnCore_eq_prepared
#check @timerTickOnCorePrepared
#check @timerTickOnCorePreDomain
#check @timerTickOnCore_idle
#check @timerTickOnCore_advances_per_core
#check @timerTickOnCore_clears_lastTimeoutErrors
#check @timerTickOnCore_preempts_local
#check @timerTickOnCore_preserves_objects_invExt
-- SM5.D.6 audit-pass-2 capstone: the budget-only tick preserves currentThreadInActiveDomain.
#check @timerTickOnCore_preserves_currentThreadInActiveDomainOnCore
#check @scheduleEffectiveOnCore_establishes_currentThreadInActiveDomainOnCore
#check @scheduleEffectiveOnCore_getTcb?_domain
#check @timerTickBudgetOnCore_notPreempted_getTcb?_domain
-- SM5.D.8 decidability.
#check @timerTickOnCoreSucceeds
#check @timerTickOnCoreEmitsSgi
#check @timerTickBudgetOnCorePreempts
-- SM5.I per-core run-loop step + the live timer-entry driver.
#check @perCoreTimerTickStep
#check @perCoreTimerTickStep_invalid_core
#check @perCoreTimerTickStep_ok
#check @perCoreTimerTickStep_error
#check @perCoreTimerTickStep_sgis_eq_tick
#check @perCoreTimerTickStep_preserves_objects_invExt
#check @perCoreTimerTickStep_ok_currentThreadValidOnCore
#check @perCoreTimerTickEntry
#check @perCoreTimerTickEntry_def
-- SM5.D.6 full per-core domain re-dispatch (§4b).
#check @switchDomainOnCore_singleDomain_noop
#check @switchDomainOnCore_preserves_objects_invExt
#check @switchDomainOnCore_sets_currentOnCore_none
#check @switchDomainOnCore_rotates
#check @scheduleDomainOnCore_decrements
#check @scheduleDomainOnCore_preserves_objects_invExt
-- SM5.D.5/.6 per-core invariant preservation (§7 B1/B2/B3).
#check @decrementDomainTimeOnCore_preserves_currentThreadValidOnCore
#check @decrementDomainTimeOnCore_preserves_queueCurrentConsistentOnCore
#check @decrementDomainTimeOnCore_preserves_runnableThreadsAreTCBsOnCore
#check @decrementDomainTimeOnCore_preserves_runQueueOnCoreWellFormed
#check @saveOutgoingContextOnCore_scheduler_eq
#check @saveOutgoingContextOnCore_getTcb?_isSome
#check @scheduleEffectiveOnCore_establishes_currentThreadValidOnCore
#check @scheduleEffectiveOnCore_establishes_queueCurrentConsistentOnCore
#check @scheduleEffectiveOnCore_preserves_runQueueOnCoreWellFormed
#check @scheduleEffectiveOnCore_preserves_runnableThreadsAreTCBsOnCore
#check @timerTickBudgetOnCore_notPreempted_scheduler_eq
#check @timerTickBudgetOnCore_notPreempted_getTcb?_tid
#check @timerTickBudgetOnCore_notPreempted_preserves_runQueueOnCoreWellFormed
#check @timerTickOnCore_preserves_currentThreadValidOnCore
#check @timerTickOnCorePrepared_runQueueOnCore_wellFormed
#check @timerTickOnCore_preserves_runQueueOnCoreWellFormed
#check @timerTickOnCore_preserves_queueCurrentConsistentOnCore
EOF
lake env lean /tmp/sm5d_surface.lean'
# WS-SM SM5.D audit-pass-1: build the 99-entry SM5.D theorem inventory so a
# renamed / removed SM5.D theorem fails at the inventory's elaboration.
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake build SeLe4n.Kernel.Scheduler.Operations.PerCoreTimerInventory'

# WS-SM SM5.E — per-core idle thread surface anchors.  Covers the SM5.E.5
# idleThread_priority_zero + field lemmas, the SM5.E.3 enqueueIdleThreadOnCore
# run-queue primitive (frame / membership / preservation), the SM5.E.6 keystone
# chooseThreadOnCore_always_succeeds (+ idleThreadEnqueuedOnCore discharge +
# enqueueIdleThreadOnCore_chooseThreadOnCore_succeeds non-vacuity witness), and the
# SM5.E.4 idleThread_core_locality (affinity-based + frame companion).  The idle
# definitions live in Platform.Boot (SM4.G).  A rename / removal of any SM5.E
# symbol fails here at elaboration time before the test suite.
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake build SeLe4n.Kernel.Scheduler.Operations.PerCoreIdle'
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake build SeLe4n.Kernel.Scheduler.Operations.PerCoreDispatch'
# WS-SM SM5.E: build the SM5.E theorem inventory so a renamed / removed
# SM5.E theorem fails at the inventory's elaboration.  This must precede the
# surface probe below, which *imports* the inventory: `lake env lean` only
# reads `.olean`s, it never builds them, and the inventory is staged-only (it
# is outside the default `lake build` target), so probing first would fail on
# a tree where the staged closure has not been built.
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake build SeLe4n.Kernel.Scheduler.Operations.PerCoreIdleInventory'
run_check "INVARIANT" bash -lc 'source ~/.elan/env && cat > /tmp/sm5e_surface.lean <<EOF
import SeLe4n.Kernel.Scheduler.Operations.PerCoreIdle
import SeLe4n.Kernel.Scheduler.Operations.PerCoreIdleInventory
import SeLe4n.Kernel.Scheduler.Operations.PerCoreDispatch
open SeLe4n.Kernel
open SeLe4n.Platform.Boot (createIdleThread)
-- SM5.E.1/.2/.5 idle definitions + field lemmas.
#check @idleThreadId
#check @createIdleThread
#check @idleThread_priority_zero
#check @createIdleThread_domain_zero
#check @createIdleThread_cpuAffinity
#check @createIdleThread_tid
-- SM5.E.3 enqueue op + frame / membership / preservation.
#check @enqueueIdleThreadOnCore
#check @enqueueIdleThreadOnCore_objects
#check @enqueueIdleThreadOnCore_scheduler
#check @enqueueIdleThreadOnCore_runQueueOnCore_self
#check @enqueueIdleThreadOnCore_runQueueOnCore_ne
#check @enqueueIdleThreadOnCore_activeDomainOnCore
#check @enqueueIdleThreadOnCore_currentOnCore
#check @enqueueIdleThreadOnCore_mem_runQueueOnCore_self
#check @enqueueIdleThreadOnCore_getTcb?_self
#check @enqueueIdleThreadOnCore_getTcb?_ne
#check @enqueueIdleThreadOnCore_preserves_objects_invExt
#check @enqueueIdleThreadOnCore_preserves_runQueueOnCore_wellFormed
#check @enqueueIdleThreadOnCore_preserves_runnableThreadsAreTCBsOnCore
-- SM5.E.6 chooseThreadOnCore_always_succeeds.
#check @idleThreadEnqueuedOnCore
#check @enqueueIdleThreadOnCore_establishes_idleThreadEnqueuedOnCore
#check @chooseThreadOnCore_always_succeeds
#check @enqueueIdleThreadOnCore_chooseThreadOnCore_succeeds
-- SM5.E.4 core locality + no-starvation.
#check @runQueueAffinityConsistentOnCore
#check @idleThread_core_locality
#check @idleThread_core_locality_of_enqueue
#check @idleThread_core_locality_forall
#check @enqueueIdleThreadOnCore_preserves_runQueueAffinityConsistentOnCore_self
#check @enqueueIdleThreadOnCore_selection_inputs_framed
#check @idleThread_no_starvation
-- SM5.E.3 per-core invariant preservation (SM5.I consumption surface).
#check @enqueueIdleThreadOnCore_preserves_currentThreadValidOnCore
#check @enqueueIdleThreadOnCore_preserves_queueCurrentConsistentOnCore
#check @enqueueIdleThreadOnCore_preserves_currentThreadInActiveDomainOnCore
#check @enqueueIdleThreadOnCore_mem_idempotent
-- SM5.E.3 lock-set footprint.
#check @enqueueIdleThreadOnCoreLockSet
#check @enqueueIdleThreadOnCoreLockSet_write_only
#check @enqueueIdleThreadOnCoreLockSet_object_before_runQueue
#check @enqueueIdleThreadOnCoreLockSet_pairwise_le
-- SM5.E.6 decidable companion.
#check @idleAvailableOnCoreB
#check @chooseThreadOnCore_always_succeeds_of_idleAvailableB
#check @idleThreadEnqueuedOnCore_idleAvailableOnCoreB
-- SM5.E idle-aware dispatcher (SM5.I seed): production defs + establishment.
-- Post-fold: idle dispatch lives in scheduleEffectiveOnCore none branch
-- (idleFallbackOnCore); scheduleOrIdleOnCore is the SM5.E name for it.
#check @idleDispatchableOnCore
#check @dispatchIdleOnCore
#check @idleFallbackOnCore
#check @scheduleOrIdleOnCore
#check @scheduleOrIdleOnCore_runs_idle
#check @scheduleOrIdleOnCore_preserves_objects_invExt
#check @scheduleOrIdleOnCore_establishes_currentThreadValidOnCore
#check @scheduleOrIdleOnCore_establishes_queueCurrentConsistentOnCore
#check @scheduleOrIdleOnCore_preserves_runQueueOnCoreWellFormed
#check @scheduleOrIdleOnCore_establishes_currentThreadInActiveDomainOnCore
#check @scheduleOrIdleOnCore_preserves_runnableThreadsAreTCBsOnCore
#check @dispatchIdleOnCore_currentOnCore
#check @dispatchIdleOnCore_objects
#check @dispatchIdleOnCore_runQueueOnCore
#check @scheduleEffectiveOnCore_currentNone_imp_chooseEffectiveNone
#check @scheduleOrIdleOnCore_idle_starves_no_eligible_thread
#check @scheduleDomainOnCore_runs_idle
-- SM5.E inventory witnesses.
#check @perCoreIdleTheorems_count
#check @perCoreIdleTheorems_partition_sum
#check @perCoreIdleTheorems_identifiers_nodup
EOF
lake env lean /tmp/sm5e_surface.lean'

# WS-SM SM5.F — per-core PIP surface anchors.  Covers the SM5.F.1
# computeMaxWaiterPriorityOnCore per-core slice + per-core <= global decomposition,
# SM5.F.2 updatePipBoostOnCore (per-core bucket migration) + pipBoostWithWake
# cross-core PIP wake, SM5.F.3 pipBoost_perCore_consistent, SM5.F.4
# propagatePipChainCrossCore donation chain across cores, SM5.F.5/.6
# restoreToReadyOnCore / restoreToReadyWithWake, SM5.F.7 blockingGraphOnCore_consistent
# + SM5.F.8 blockingAcyclic_perCore, and SM5.F.9 priorityInheritance_perCore_witness.
# The per-core PIP transition defs are production-reached.  A rename / removal of
# any SM5.F symbol fails here at elaboration time before the test suite.
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake build SeLe4n.Kernel.Scheduler.PriorityInheritance.PerCore'
# WS-SM SM5.F: build the SM5.F theorem inventory so a renamed / removed
# SM5.F theorem fails at the inventory's elaboration.  This must precede the
# surface probe below, which *imports* the inventory: `lake env lean` only
# reads `.olean`s, it never builds them, and the inventory is staged-only (it
# is outside the default `lake build` target), so probing first would fail on
# a tree where the staged closure has not been built.
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake build SeLe4n.Kernel.Scheduler.PriorityInheritance.PerCoreInventory'
run_check "INVARIANT" bash -lc 'source ~/.elan/env && cat > /tmp/sm5f_surface.lean <<EOF
import SeLe4n.Kernel.Scheduler.PriorityInheritance.PerCore
import SeLe4n.Kernel.Scheduler.PriorityInheritance.PerCoreInventory
open SeLe4n.Kernel.PriorityInheritance
open SeLe4n.Kernel.Lifecycle.Suspend (restoreToReadyOnCore restoreToReadyWithWake)
-- SM5.F.1 computeMaxWaiterPriorityOnCore + decomposition + frame.
#check @computeMaxWaiterPriorityOnCore
#check @optPriorityVal
#check @computeMaxWaiterPriorityOnCore_no_waiters
#check @computeMaxWaiterPriorityOnCore_le_global
#check @computeMaxWaiterPriorityOnCore_frame
-- SM5.F.2 updatePipBoostOnCore + bridge / frame / preservation.
#check @updatePipBoostOnCore
#check @updatePipBoost_eq_updatePipBoostOnCore_bootCore
#check @updatePipBoostOnCore_preserves_objects_invExt
#check @updatePipBoostOnCore_objects_ne
#check @updatePipBoostOnCore_preserves_objectIndex
#check @updatePipBoostOnCore_preserves_blockingServer
#check @updatePipBoostOnCore_preserves_blockingAcyclic
#check @updatePipBoostOnCore_runQueueOnCore_ne
#check @updatePipBoostOnCore_currentOnCore
#check @updatePipBoostOnCore_getTcb?_pipBoost
-- SM5.F.3 pipBoost_perCore_consistent.
#check @optPriorityVal_pipBoost_le_effectiveSchedParams
#check @pipBoost_perCore_consistent
-- SM5.F.2 pipBoostWithWake (cross-core PIP wake).
#check @pipBoostWithWake
#check @pipBoostWithWake_state
#check @pipBoostWithWake_no_sgi_if_local
#check @pipBoostWithWake_emits_sgi_if_remote
#check @pipBoostWithWake_no_sgi_if_noop
#check @pipBoostWithWake_sgi_is_reschedule
#check @pipBoostWithWake_emits_at_most_one_sgi
#check @pipBoostWithWake_preserves_objects_invExt
#check @pipBoostWithWake_preserves_blockingAcyclic
#check @pipBoostWithWake_bootCore_unbound
-- SM5.F.4 propagatePipChainCrossCore (donation chain across cores).
#check @propagatePipChainCrossCore
#check @propagatePipChainCrossCore_zero
#check @propagatePipChainCrossCore_step
#check @propagatePipChainCrossCoreState
#check @propagatePipChainCrossCoreState_step
#check @propagatePipChainCrossCore_preserves_objects_invExt
#check @propagatePipChainCrossCore_preserves_blockingAcyclic
#check @propagatePipChainCrossCore_zero_sgis
#check @propagatePipChainCrossCore_no_sgis_head_terminal
#check @propagatePipChainCrossCore_head_sgi_remote
-- SM5.F.5/.6 restoreToReadyOnCore / restoreToReadyWithWake.
#check @restoreToReadyOnCore
#check @restoreToReadyWithWake
#check @restoreToReady_objects_invExt
#check @restoreToReadyOnCore_preserves_objects_invExt
#check @restoreToReadyOnCore_currentOnCore
#check @restoreToReadyOnCore_runQueueOnCore_ne
#check @restoreToReadyOnCore_pipBoost_recomputed
#check @restoreToReadyWithWake_state
#check @restoreToReadyWithWake_no_sgi_if_local
#check @restoreToReadyWithWake_emits_sgi_if_remote
#check @restoreToReadyWithWake_sgi_is_reschedule
#check @restoreToReadyWithWake_preserves_objects_invExt
-- SM5.F.7/.8 per-core blocking graph.
#check @blockingServerOnCore
#check @blockingServerOnCore_eq_global_of_onCore
#check @blockingServerOnCore_none_of_offCore
#check @blockingServerOnCore_implies_global
#check @blockingServerOnCore_subgraph
#check @blockingGraphOnCore_consistent
#check @blockingChainOnCore
#check @blockingChainOnCore_subset
#check @blockingAcyclicOnCore
#check @blockingAcyclic_perCore
-- SM5.F.9 aggregate witness + inventory witnesses.
#check @priorityInheritance_perCore_witness
#check @perCorePipTheorems_count
#check @perCorePipTheorems_partition_sum
#check @perCorePipTheorems_identifiers_nodup
-- SM5.F completion pass: B5 full decomposition, B6 dominance, B7 home-core
-- stability + chain SGI completeness, C9 runnability gate, B8 full witness,
-- D11 memory-model HB, F13 complete resume, and the cross-core wake dispatch.
#check @computeMaxWaiterPriority_eq_sup_perCore
#check @computeMaxWaiterPriority_value
#check @computeMaxWaiterPriorityOnCore_value
#check @updatePipBoostOnCore_getTcb?_cpuAffinity
#check @updatePipBoostOnCore_eq_self_of_getTcb?_none
#check @updatePipBoostOnCore_preserves_determineTargetCore
#check @updatePipBoostOnCore_establishes_perCore_dominance
#check @pipBoostWithWake_no_sgi_if_not_runnable
#check @propagatePipChainCrossCore_head_emission_mem
#check @propagatePipChainCrossCore_tail_sgis_mem
#check @propagatePipChainCrossCore_sgis_all_reschedule
#check @propagatePipChainCrossCore_sgi_length_le_fuel
#check @propagatePipChainCrossCore_second_link_sgi_remote
#check @propagatePipChainCrossCore_singleCore_no_sgis
#check @propagatePipChainCrossCoreState_singleCore_eq_propagate
#check @pipBoostOrdering_synchronizesWith
#check @pipBoostOrdering_happensBefore
#check @resumeReadyMidState_getTcb?_ready
#check @resumeReadyMidState_objects_invExt
#check @resumeReadyMidState_scheduler_eq
#check @SeLe4n.Kernel.preemptCurrentOnCore_getTcb?_ne_current
#check @SeLe4n.Kernel.switchToThreadOnCore_getTcb?_ne_current
#check @SeLe4n.Kernel.handleRescheduleSgiOnCore_getTcb?_ne_current
#check @resumeThreadOnCore_sets_threadState
#check @resumeThreadOnCore_preserves_objects_invExt
#check @resumeThreadOnCore_rejects_non_inactive
#check @resumeThreadOnCore_rejects_non_tcb
#check @resumeThreadOnCore_local_no_sgi
#check @resumeThreadOnCore_remote_sgi
#check @restoreToReadyWithWake_sets_threadState
#check @priorityInheritance_perCore_witness_full
#check @computeCrossCoreSgis
#check @computeCrossCoreSgis_all_reschedule
#check @computeCrossCoreSgis_nil_single_core
#check @crossCoreWakeDispatch
#check @crossCoreWakeDispatch_singleCore
#check @pipChainWakeDispatch
#check @pipChainWakeDispatch_singleCore
#check @emitBoostWakeSgi
#check @perCorePipTheorems_memoryModel_count
#check @perCorePipTheorems_dispatch_count
EOF
lake env lean /tmp/sm5f_surface.lean'

# WS-SM SM5.G: per-core domain scheduling.  SM5.G.2 advanceDomainOnCore (pure
# rotation) + frames + single-step + the advanceDomainOnCoreN iteration & cyclic
# theorem, SM5.G.2 bridge switchDomainOnCore_activeDomain_eq_advanceDomainOnCore,
# SM5.G.3 activeDomainOnCore_isInDomainSchedule establishment/SMP-preservation + the
# plan §3.7 Theorem 3.7.1 membership form, SM5.G.4 chooseThreadOnCore_respects_activeDomain,
# SM5.G.5 cross-core domain independence + the advanceDomainOnCoreLockSet footprint.
# A rename / removal of any SM5.G symbol fails here at elaboration time.
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake build SeLe4n.Kernel.Scheduler.Operations.PerCoreDomain'
# WS-SM SM5.G: build the SM5.G theorem inventory so a renamed / removed
# SM5.G theorem fails at the inventory's elaboration.  This must precede the
# surface probe below, which *imports* the inventory: `lake env lean` only
# reads `.olean`s, it never builds them, and the inventory is staged-only (it
# is outside the default `lake build` target), so probing first would fail on
# a tree where the staged closure has not been built.
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake build SeLe4n.Kernel.Scheduler.Operations.PerCoreDomainInventory'
run_check "INVARIANT" bash -lc 'source ~/.elan/env && cat > /tmp/sm5g_surface.lean <<EOF
import SeLe4n.Kernel.Scheduler.Operations.PerCoreDomain
import SeLe4n.Kernel.Scheduler.Operations.PerCoreDomainInventory
open SeLe4n.Kernel
-- SM5.G.2 rotation + frames + single-step.
#check @advanceDomainOnCore
#check @advanceDomainOnCore_empty
#check @advanceDomainOnCore_objects
#check @advanceDomainOnCore_getTcb?
#check @advanceDomainOnCore_domainSchedule
#check @advanceDomainOnCore_runQueueOnCore
#check @advanceDomainOnCore_currentOnCore
#check @advanceDomainOnCore_activeDomainOnCore_ne
#check @advanceDomainOnCore_domainTimeRemainingOnCore_ne
#check @advanceDomainOnCore_domainScheduleIndexOnCore_ne
#check @advanceDomainOnCore_rotates
#check @advanceDomainOnCore_domainTimeRemainingOnCore_self
#check @advanceDomainOnCore_domainScheduleIndexOnCore_self
#check @advanceDomainOnCore_index_lt
-- SM5.G.2 cyclic.
#check @advanceDomainOnCoreN
#check @advanceDomainOnCoreN_zero
#check @advanceDomainOnCoreN_succ
#check @advanceDomainOnCoreN_domainSchedule
#check @advanceDomainOnCoreN_index
#check @advanceDomainOnCore_cyclic
-- SM5.G.2 bridge to production.
#check @switchDomainOnCore_activeDomain_eq_advanceDomainOnCore
-- SM5.G.3 isInDomainSchedule (Thm 3.7.1).
#check @advanceDomainOnCore_establishes_activeDomainOnCore_isInDomainSchedule
#check @advanceDomainOnCore_preserves_activeDomainOnCore_isInDomainSchedule_ne
#check @advanceDomainOnCore_preserves_isInDomainSchedule_smp
#check @activeDomainOnCore_isInDomainSchedule_mem
#check @activeDomainOnCore_isInDomainSchedule_mem_of_smp
#check @advanceDomainOnCore_activeDomain_mem
-- SM5.G.4 respects_activeDomain.
#check @chooseBestRunnableBy_result_eligible
#check @chooseBestInBucket_result_eligible
#check @chooseThreadOnCore_respects_activeDomain
#check @chooseThreadEffectiveOnCore_respects_activeDomain
-- SM5.G.5 cross-core independence + footprint.
#check @advanceDomainOnCore_independent_of_other_core
#check @advanceDomainOnCore_perCore_independence
#check @advanceDomainOnCoreLockSet
#check @advanceDomainOnCoreLockSet_length
#check @advanceDomainOnCoreLockSet_write_only
#check @advanceDomainOnCoreLockSet_contains_runQueue_write
#check @advanceDomainOnCoreLockSet_keys_nodup
#check @advanceDomainOnCoreLockSet_disjoint_of_ne
-- SM5.G completion (audit-pass): query accessor, full bridge, invariants, live preservation.
#check @SeLe4n.Model.SystemState.activeDomainOnCore
#check @activeDomainOnCore_systemState_mem
#check @switchDomainOnCore_domainTriple_eq_advanceDomainOnCore
#check @switchDomainOnCore_domainScheduleIndexOnCore_self
#check @switchDomainOnCore_domainTimeRemainingOnCore_self
#check @advanceDomainOnCoreLockSet_pairwise_le
#check @advanceDomainOnCore_frames_outside_core
#check @domainScheduleIndexInBoundsOnCore
#check @advanceDomainOnCore_establishes_domainScheduleIndexInBoundsOnCore
#check @advanceDomainOnCore_cyclic_of_inBounds
#check @domainConsistentOnCore
#check @advanceDomainOnCore_establishes_domainConsistentOnCore
#check @advanceDomainOnCore_cyclic_activeDomain
#check @scheduleEffectiveOnCore_activeDomainOnCore
#check @scheduleEffectiveOnCore_domainSchedule
#check @switchDomainOnCore_domainSchedule
#check @switchDomainOnCore_preserves_activeDomainOnCore_isInDomainSchedule
#check @switchDomainOnCore_preserves_domainScheduleIndexInBoundsOnCore
#check @scheduleDomainOnCore_preserves_activeDomainOnCore_isInDomainSchedule
#check @chooseThreadEffectiveOnCore_respects_activeDomain
-- SM5.G §11 deep-audit: the SM5.G invariants maintained by the live domain tick.
#check @domainScheduleIndexInBoundsOnCore_frame
#check @domainConsistentOnCore_frame
#check @scheduleEffectiveOnCore_domainScheduleIndexOnCore
#check @decrementDomainTimeOnCore_domainScheduleIndexOnCore
#check @scheduleDomainOnCore_preserves_domainScheduleIndexInBoundsOnCore
#check @switchDomainOnCore_preserves_domainConsistentOnCore
#check @scheduleDomainOnCore_preserves_domainConsistentOnCore
#check @perCoreDomainTheorems_count
#check @perCoreDomainTheorems_partition_sum
#check @perCoreDomainTheorems_query_count
#check @perCoreDomainTheorems_invariant_count
#check @perCoreDomainTheorems_livePreservation_count
EOF
lake env lean /tmp/sm5g_surface.lean'

# WS-SM SM5.H: per-core CBS.  SM5.H.2 replenishOnCore (per-core CBS replenishment-
# scheduling primitive) + frames, SM5.H.3/.6/.5 validity/pipeline-order/affinity
# preservation, SM5.H.4 migrateSchedContextReplenishment (SchedContext replenishment
# migration on affinity change) + setThreadCpuAffinityWithMigration composite + the
# headline restoration schedContextMigration_consistent, SM5.H.5 the plan §3.8 Theorem
# 3.8.1 affinity invariant replenishQueueAffinityConsistentOnCore, SM5.H.7 the aggregate
# perCoreCbsInvariant + CBS budget-bound accounting.  A rename / removal of any SM5.H
# symbol fails here at elaboration time.
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake build SeLe4n.Kernel.Scheduler.Operations.PerCoreCbs'
# WS-SM SM5.H: build the SM5.H theorem inventory so a renamed / removed
# SM5.H theorem fails at the inventory's elaboration.  This must precede the
# surface probe below, which *imports* the inventory: `lake env lean` only
# reads `.olean`s, it never builds them, and the inventory is staged-only (it
# is outside the default `lake build` target), so probing first would fail on
# a tree where the staged closure has not been built.
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake build SeLe4n.Kernel.Scheduler.Operations.PerCoreCbsInventory'
run_check "INVARIANT" bash -lc 'source ~/.elan/env && cat > /tmp/sm5h_surface.lean <<EOF
import SeLe4n.Kernel.Scheduler.Operations.PerCoreCbs
import SeLe4n.Kernel.Scheduler.Operations.PerCoreCbsInventory
open SeLe4n.Kernel
-- SM5.H.1 / .5 the affinity-consistency invariant.
#check @replenishQueueAffinityConsistentOnCore
#check @replenishQueueAffinityConsistent_smp
#check @replenishQueueAffinityConsistent_smp_at
#check @default_replenishQueueAffinityConsistentOnCore
#check @default_replenishQueueAffinityConsistent_smp
#check @replenishQueueAffinityConsistentOnCore_frame
-- SM5.H.2 the replenishOnCore primitive + frames.
#check @replenishOnCore
#check @replenishOnCore_objects
#check @replenishOnCore_machine
#check @replenishOnCore_getTcb?
#check @replenishOnCore_getSchedContext?
#check @replenishOnCore_determineTargetCore
#check @replenishOnCore_replenishQueueOnCore_self
#check @replenishOnCore_replenishQueueOnCore_ne
#check @replenishOnCore_runQueueOnCore
#check @replenishOnCore_currentOnCore
#check @replenishOnCore_activeDomainOnCore
#check @replenishOnCore_mem
-- SM5.H.3 / .6 / .5 replenishOnCore preservation.
#check @replenishOnCore_preserves_replenishQueueValidOnCore
#check @replenishOnCore_preserves_replenishQueueValidOnCore_ne
#check @replenishOnCore_preserves_replenishQueueValid_smp
#check @replenishOnCore_preserves_replenishmentPipelineOrderOnCore
#check @replenishOnCore_preserves_replenishmentPipelineOrderOnCore_ne
#check @replenishOnCore_preserves_replenishQueueAffinityConsistentOnCore
-- SM5.H.4 the migration operation + frames + structural + validity/pipeline.
#check @migrateSchedContextReplenishment
#check @migrateSchedContextReplenishment_noop
#check @migrateSchedContextReplenishment_objects
#check @migrateSchedContextReplenishment_machine
#check @migrateSchedContextReplenishment_getSchedContext?
#check @migrateSchedContextReplenishment_determineTargetCore
#check @migrateSchedContextReplenishment_replenishQueueOnCore_to
#check @migrateSchedContextReplenishment_replenishQueueOnCore_from
#check @migrateSchedContextReplenishment_replenishQueueOnCore_other
#check @migrateSchedContextReplenishment_fromCore_excludes_scId
#check @migrateSchedContextReplenishment_mem_toCore
#check @migrateSchedContextReplenishment_preserves_replenishQueueValid_smp
#check @migrateSchedContextReplenishment_preserves_replenishmentPipelineOrder_smp
-- SM5.H.4 affinity-write helpers.
#check @determineTargetCore_congr_getTcb?
#check @setThreadCpuAffinity_determineTargetCore_ne
#check @setThreadCpuAffinity_getSchedContext?
-- SM5.H.4 / .5 migration affinity behaviour + composite + headline.
#check @migrateSchedContextReplenishment_establishes_affinityConsistentOnCore_to
#check @migrateSchedContextReplenishment_establishes_affinityConsistentOnCore_from
#check @migrateSchedContextReplenishment_preserves_affinityConsistentOnCore_other
#check @setThreadCpuAffinityWithMigration
#check @setThreadCpuAffinityWithMigration_error_of_no_tcb
#check @setThreadCpuAffinityWithMigration_bound_state_eq
#check @setThreadCpuAffinityWithMigration_unbound_state_eq
#check @schedContextMigration_consistent
-- SM5.H.7 per-core CBS invariant + budget accounting.
#check @perCoreCbsInvariant
#check @default_perCoreCbsInvariant
#check @replenishOnCore_preserves_perCoreCbsInvariant
#check @consumeBudget_preserves_le_budget
#check @applyRefill_preserves_le_budget
#check @scheduleReplenishment_replenishments_bounded
-- SM5.H.2 (B8) the faithful sc-based scheduling primitive.
#check @replenishScOnCore
#check @replenishScOnCore_eq
#check @replenishScOnCore_preserves_replenishmentPipelineOrderOnCore
-- SM5.H.4 (§6c/§11) the full-thread-migration run-queue move + scheduler preservation.
#check @migrateRunQueueOnAffinityChange
#check @migrateRunQueueOnAffinityChange_preserves_runQueueOnCoreWellFormed
#check @migrateSchedContextReplenishment_runQueueOnCore
#check @setThreadCpuAffinityWithMigration_preserves_runQueueOnCoreWellFormed
#check @migrateRunQueueOnAffinityChange_preserves_schedContextRunQueueConsistent_perCore
-- SM5.H.4 (§9) object-store invariant preservation.
#check @replenishOnCore_preserves_objects_invExt
#check @setThreadCpuAffinityWithMigration_preserves_objects_invExt
-- SM5.H.4 (§12 B7) the binding-uniqueness grounding + grounded headline.
#check @schedContextBindingConsistent_boundThread_unique
#check @schedContextMigration_consistent_of_bindingConsistent
-- SM5.H.4 (§13 A5) the composite per-core CBS invariant preservation.
#check @setThreadCpuAffinityWithMigration_preserves_replenishQueueValid_smp
#check @setThreadCpuAffinityWithMigration_preserves_replenishmentPipelineOrder_smp
#check @setThreadCpuAffinityWithMigration_preserves_perCoreCbsInvariant_smp
-- SM5.H.4 (§10) the cross-domain lock-set footprints.
#check @replenishOnCoreLockSet
#check @migrateSchedContextReplenishmentLockSet
#check @migrateRunQueueOnAffinityChangeLockSet
#check @setThreadCpuAffinityWithMigrationLockSet
#check @setThreadCpuAffinityWithMigrationLockSet_pairwise_le_of_core_le
-- Codex review safety items pulled forward: #5 (unconditional ascending lock order,
-- no reverse-direction migration deadlock) + #2 (reject rebinding a running thread to
-- a core its new affinity forbids).
#check @setThreadCpuAffinityWithMigrationLockSet_pairwise_le
#check @setThreadCpuAffinityWithMigration_rejects_running_on_forbidden_core
-- SM5.H.2 (A2/A4, §14) the live-tick CBS bridge.
#check @timeoutBlockedThreads_replenishQueueOnCore
#check @timerTickBudgetOnCore_bound_exhausted_replenish_eq
#check @timerTickBudgetOnCore_preserves_replenishQueueValidOnCore
-- SM5.H.4 (C10, the migration cross-core memory-model HB).
#check @affinityMigrationOrdering_synchronizesWith
#check @affinityMigrationOrdering_happensBefore
-- SM5.H.4 audit-pass-2 (D15 composite, §17): the full affinity composite preserves
-- SM4.C run-queue↔budget consistency on every core.
#check @setThreadCpuAffinity_getTcb?_self
#check @setThreadCpuAffinity_preserves_schedContextRunQueueConsistent_perCore
#check @migrateSchedContextReplenishment_preserves_schedContextRunQueueConsistent_perCore
#check @setThreadCpuAffinityWithMigration_preserves_schedContextRunQueueConsistent_perCore
-- SM5.H.4 audit-pass-2 (B8/SGI + C10 tightened, §18): the composite cross-core
-- .reschedule SGI characterisation, pinned to the memory-model happens-before.
#check @setThreadCpuAffinityWithMigration_sgi_eq
#check @setThreadCpuAffinityWithMigration_no_sgi_if_local
#check @setThreadCpuAffinityWithMigration_emits_reschedule_of_remote_runnable
#check @setThreadCpuAffinityWithMigration_sgi_happensBefore
-- SM5.H.4 the tcbSetAffinity syscall wiring (production-reached).
#check @setThreadCpuAffinityOp
#check @decodeAffinity
-- SM5.H inventory.
#check @perCoreCbsTheorems_count
#check @perCoreCbsTheorems_partition_sum
#check @perCoreCbsTheorems_identifiers_nodup
#check @perCoreCbsTheorems_lockSet_count
#check @perCoreCbsTheorems_liveTick_count
#check @perCoreCbsTheorems_memoryModel_count
EOF
lake env lean /tmp/sm5h_surface.lean'

# WS-SM SM5.I: the live per-core timer tick preserves perCoreCbsInvariant.
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake build SeLe4n.Kernel.Scheduler.Operations.PerCoreTickCbsPreservation'
run_check "INVARIANT" bash -lc 'source ~/.elan/env && cat > /tmp/sm5i_tick_cbs.lean <<EOF
import SeLe4n.Kernel.Scheduler.Operations.PerCoreTickCbsPreservation
open SeLe4n.Kernel
-- validity (unconditional) + pipeline-order (positive periods) conjuncts.
#check @timerTickOnCore_preserves_replenishQueueValidOnCore
#check @timerTickOnCore_preserves_replenishmentPipelineOrderOnCore
-- the machine-timer chain (the tick reads but never advances the global timer).
#check @timerTickOnCore_machine_timer_eq
#check @timerTickBudgetOnCore_machine
#check @timeoutBlockedThreads_machine
#check @scheduleEffectiveOnCore_machine_timer
-- the supporting replenish-queue + pipeline frames.
#check @processReplenishmentsDueOnCore_preserves_replenishQueueValidOnCore
#check @processReplenishmentsDueOnCore_preserves_replenishmentPipelineOrderOnCore
#check @popDue_remaining_subset
-- the aggregate (validity + pipeline discharged, affinity-consistency the placement-gated input).
#check @timerTickOnCore_preserves_perCoreCbsInvariant
EOF
lake env lean /tmp/sm5i_tick_cbs.lean'

# WS-SM SM5.I affinity discharge: timerTickOnCore preserves replenish-queue affinity-consistency.
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake build SeLe4n.Kernel.Scheduler.Operations.PerCoreTickCbsAffinity'
run_check "INVARIANT" bash -lc 'source ~/.elan/env && cat > /tmp/sm5i_tick_affinity.lean <<EOF
import SeLe4n.Kernel.Scheduler.Operations.PerCoreTickCbsAffinity
open SeLe4n.Kernel
-- foundation: object-store insert atoms + the affinity-transfer keystone.
#check @affinityConsistent_transfer
#check @determineTargetCore_insert_tcb
#check @getSchedContext?_insert_tcb_eq
#check @getTcb?_insert_schedContext_eq
#check @getSchedContext?_boundThread_insert_schedContext
-- per-op determineTargetCore + boundThread frames.
#check @enqueueRunnableOnCore_determineTargetCore
#check @refillSchedContext_boundThread
#check @scheduleEffectiveOnCore_determineTargetCore
#check @processReplenishmentsDueOnCore_determineTargetCore
#check @processReplenishmentsDueOnCore_boundThread
-- the proven prepared + schedule per-phase affinity preservation.
#check @timerTickOnCorePrepared_preserves_replenishQueueAffinityConsistentOnCore
#check @scheduleEffectiveOnCore_preserves_replenishQueueAffinityConsistentOnCore
-- the headline + the strengthened aggregate (affinity DERIVED, budget-phase frame the residual).
#check @timerTickOnCore_preserves_replenishQueueAffinityConsistentOnCore
#check @timerTickOnCore_preserves_perCoreCbsInvariant_discharged
EOF
lake env lean /tmp/sm5i_tick_affinity.lean'

# WS-SM SM5.I — per-core invariant suite surface anchors (SM5.I.10).  Covers the
# schedulerInvariantStructural_perCore / _smp safety invariant + its projections /
# bridges / default-state / frame, the per-arbitrary-core SMP-preservation engine,
# the ten <op>_preserves_schedulerInvariantStructural_smp theorems (SM5.I.8
# "preservation by every transition") + the helper lemmas, and the SM5.I.1–I.7/I.9
# suite index.  A rename / removal of any SM5.I symbol fails here at elaboration
# time before the test suite.
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake build SeLe4n.Kernel.Scheduler.Invariant.PerCoreInvariantSuite'
# WS-SM SM5.I: build the SM5.I theorem inventory so a renamed / removed
# SM5.I theorem fails at the inventory's elaboration.  This must precede the
# surface probe below, which *imports* the inventory: `lake env lean` only
# reads `.olean`s, it never builds them, and the inventory is staged-only (it
# is outside the default `lake build` target), so probing first would fail on
# a tree where the staged closure has not been built.
run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake build SeLe4n.Kernel.Scheduler.Invariant.PerCoreInvariantSuiteInventory'
run_check "INVARIANT" bash -lc 'source ~/.elan/env && cat > /tmp/sm5i_suite.lean <<EOF
import SeLe4n.Kernel.Scheduler.Invariant.PerCoreInvariantSuite
import SeLe4n.Kernel.Scheduler.Invariant.PerCoreInvariantSuiteInventory
open SeLe4n.Kernel
-- §1 structural invariant + engine (SM5.I.5/I.7).
#check @schedulerInvariantStructural_perCore
#check @schedulerInvariantStructural_smp
#check @schedulerInvariantStructural_perCore_to_queueCurrentConsistent
#check @schedulerInvariantStructural_perCore_to_currentThreadValid
#check @schedulerInvariantStructural_perCore_to_runnableThreadsAreTCBs
#check @schedulerInvariantStructural_perCore_to_runQueueOnCoreWellFormed
#check @schedulerInvariantStructural_perCore_aggregateForall
#check @schedulerInvariantStructural_smp_at
#check @schedulerInvariant_perCore_to_structural
#check @schedulerInvariant_smp_to_structural
#check @default_schedulerInvariantStructural_perCore
#check @default_schedulerInvariantStructural_smp
#check @schedulerInvariantStructural_perCore_frame
#check @schedulerInvariantStructural_smp_of_establish_and_frame
-- §3 preservation by every transition (SM5.I.8).
#check @advanceDomainOnCore_preserves_schedulerInvariantStructural_smp
#check @enqueueRunnableOnCore_preserves_runnableThreadsAreTCBsOnCore
#check @enqueueRunnableOnCore_preserves_schedulerInvariantStructural_smp
#check @wakeThread_preserves_schedulerInvariantStructural_smp
#check @idleFallbackOnCore_currentOnCore_ne
#check @idleFallbackOnCore_runQueueOnCore_ne
#check @scheduleEffectiveOnCore_independent_of_other_core
#check @scheduleEffectiveOnCore_preserves_schedulerInvariantStructural_smp
#check @scheduleOrIdleOnCore_preserves_schedulerInvariantStructural_smp
#check @preemptCurrentOnCore_getTcb?_isSome
#check @preemptCurrentOnCore_runQueue_resolves
#check @switchToThreadOnCore_getTcb?_isSome
#check @switchToThreadOnCore_preserves_runnableThreadsAreTCBsOnCore
#check @switchToThreadOnCore_preserves_schedulerInvariantStructural_smp
#check @handleRescheduleSgiOnCore_preserves_schedulerInvariantStructural_smp
#check @enqueueIdleThreadOnCore_preserves_schedulerInvariantStructural_smp
#check @replenishOnCore_preserves_schedulerInvariantStructural_smp
#check @decrementDomainTimeOnCore_preserves_schedulerInvariantStructural_smp
-- §4 suite index (SM5.I.1–I.4/I.6/I.9).
#check @currentOnCore_validThreadIfSome
#check @runQueueOnCore_wellFormed_of_structural
#check @schedContextRunQueueConsistent_perCore_of_crossSubsystem
#check @priorityInheritance_perCore_iff_blockingAcyclic
#check @schedulerInvariant_smp_dominates_structural
#check @schedulerInvariantStructural_perCore_pairwise
#check @crossSubsystemInvariant_smp_dominates_structural
-- SM5.I.8 / SM5.F budget-tick closure: the qcc-free run-queue safety sub-bundle
-- preserved through timerTickBudgetOnCore (incl. the bound-budget-exhausted
-- timeoutBlockedThreads path) + the FULLY CLOSED per-core timer-tick capstone.
#check @runQueueSafetyOnCore
#check @schedulerInvariantStructuralRegNodup_perCore_to_runQueueSafety
#check @ensureRunnable_preserves_runQueueSafetyOnCore
#check @updatePipBoost_preserves_runQueueSafetyOnCore
#check @revertPriorityInheritance_preserves_runQueueSafetyOnCore
#check @timeoutThread_preserves_runQueueSafetyOnCore
#check @timeoutBlockedThreads_preserves_runQueueSafetyOnCore
#check @replenishOnCore_preserves_runQueueSafetyOnCore
#check @timerTickBudgetOnCore_preserves_runQueueSafetyOnCore
#check @timerTickOnCorePrepared_preserves_runQueueSafetyOnCore
#check @timerTickOnCore_preserves_schedulerInvariantStructuralRegNodup_perCore
#check @timerTickOnCore_preserves_schedulerInvariantStructuralRegNodup_perCore_of_pre
#check @timerTickOnCore_preserves_schedulerInvariantStructuralRegNodup_perCore_closed
-- SM5.I inventory witnesses.
#check @perCoreInvariantSuiteTheorems_count
#check @perCoreInvariantSuiteTheorems_partition_sum
#check @perCoreInvariantSuiteTheorems_budgetClosure_count
#check @perCoreInvariantSuiteTheorems_identifiers_nodup
-- §5 global slice-invariant strengthening (allThreadsTimeSlicePositive) + the
-- Strong SMP invariant + the AK2-B priority carrier (PR-A) / alignment (PR-C).
#check @allThreadsTimeSlicePositive
#check @timeSlicePositiveOnCore_of_allThreads
#check @currentTimeSlicePositiveOnCore_of_allThreads
#check @default_allThreadsTimeSlicePositive
#check @enqueueRunnableOnCore_preserves_allThreadsTimeSlicePositive
#check @wakeThread_preserves_allThreadsTimeSlicePositive
#check @updatePipBoost_preserves_allThreadsTimeSlicePositive
#check @revertPriorityInheritance_preserves_allThreadsTimeSlicePositive
#check @endpointQueueRemove_preserves_allThreadsTimeSlicePositive
#check @timeoutThread_preserves_allThreadsTimeSlicePositive
#check @timeoutBlockedThreads_preserves_allThreadsTimeSlicePositive
#check @timerTickBudgetOnCore_preserves_allThreadsTimeSlicePositive
#check @processReplenishmentsDueOnCore_preserves_allThreadsTimeSlicePositive
#check @timerTickOnCorePrepared_preserves_allThreadsTimeSlicePositive
#check @saveOutgoingContextOnCore_preserves_allThreadsTimeSlicePositive
#check @scheduleEffectiveOnCore_preserves_allThreadsTimeSlicePositive
#check @timerTickOnCore_preserves_allThreadsTimeSlicePositive
#check @preemptCurrentOnCore_preserves_allThreadsTimeSlicePositive
#check @switchToThreadOnCore_preserves_allThreadsTimeSlicePositive
#check @handleRescheduleSgiOnCore_preserves_allThreadsTimeSlicePositive
#check @enqueueIdleThreadOnCore_preserves_allThreadsTimeSlicePositive
#check @switchDomainOnCore_preserves_allThreadsTimeSlicePositive
#check @scheduleDomainOnCore_preserves_allThreadsTimeSlicePositive
#check @scheduleOrIdleOnCore_preserves_allThreadsTimeSlicePositive
-- the Strong SMP invariant (RegNodup + global slice → 8 of 11 conjuncts).
#check @schedulerInvariantStrong_smp
#check @schedulerInvariantStrong_smp_to_regNodup_smp
#check @schedulerInvariantStrong_smp_to_allThreads
#check @schedulerInvariantStrong_smp_to_timeSlicePositive
#check @schedulerInvariantStrong_smp_to_currentTimeSlicePositive
#check @schedulerInvariant_smp_and_allThreads_to_strong
#check @default_schedulerInvariantStrong_smp
#check @advanceDomainOnCore_preserves_schedulerInvariantStrong_smp
#check @replenishOnCore_preserves_schedulerInvariantStrong_smp
#check @decrementDomainTimeOnCore_preserves_schedulerInvariantStrong_smp
#check @enqueueRunnableOnCore_preserves_schedulerInvariantStrong_smp
#check @wakeThread_preserves_schedulerInvariantStrong_smp
#check @scheduleEffectiveOnCore_preserves_schedulerInvariantStrong_smp
#check @scheduleOrIdleOnCore_preserves_schedulerInvariantStrong_smp
#check @switchToThreadOnCore_preserves_schedulerInvariantStrong_smp
#check @handleRescheduleSgiOnCore_preserves_schedulerInvariantStrong_smp
#check @enqueueIdleThreadOnCore_preserves_schedulerInvariantStrong_smp
#check @switchDomainOnCore_preserves_schedulerInvariantStrong_smp
#check @scheduleDomainOnCore_preserves_schedulerInvariantStrong_smp
-- AK2-B priority carrier (PR-A) + the SC↔TCB priority alignment (PR-C).
#check @boundThreadPriorityConsistent
#check @boundThreadPriorityConsistent_frame
#check @default_boundThreadPriorityConsistent
#check @resolveEffectivePrioDeadline_fst_eq_effectiveRunQueuePriority_of_agree
EOF
lake env lean /tmp/sm5i_suite.lean'

finalize_report
