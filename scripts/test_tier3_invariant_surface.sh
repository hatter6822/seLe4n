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
run_check "INVARIANT" rg -n '^\s*\| illegalState' SeLe4n/Model/KernelError.lean
run_check "INVARIANT" rg -n '^\s*\| illegalAuthority' SeLe4n/Model/KernelError.lean
run_check "INVARIANT" rg -n '^\s*\| invalidTypeTag' SeLe4n/Model/KernelError.lean
run_check "INVARIANT" rg -n '^def lifecycleRetypeObject' SeLe4n/Kernel/Lifecycle/Operations/CleanupPreservation.lean
run_check "INVARIANT" rg -n '^theorem lifecycleRetypeObject_error_illegalState' SeLe4n/Kernel/Lifecycle/Operations/ScrubAndUntyped.lean
run_check "INVARIANT" rg -n '^theorem lifecycleRetypeObject_error_illegalAuthority' SeLe4n/Kernel/Lifecycle/Operations/ScrubAndUntyped.lean
run_check "INVARIANT" rg -n '^theorem lifecycleRetypeObject_success_updates_object' SeLe4n/Kernel/Lifecycle/Operations/ScrubAndUntyped.lean

# M5-B/Q1: Service registry transition anchors (lifecycle ops removed in Q1).
run_check "INVARIANT" rg -n '^def storeServiceEntry' SeLe4n/Kernel/Service/Operations.lean
run_check "INVARIANT" rg -n '^def serviceHasPathTo' SeLe4n/Kernel/Service/Operations.lean
run_check "INVARIANT" rg -n '^def serviceRegisterDependency' SeLe4n/Kernel/Service/Operations.lean
run_check "INVARIANT" rg -n '^theorem serviceRegisterDependency_error_self_loop' SeLe4n/Kernel/Service/Operations.lean
run_check "INVARIANT" rg -n '^\s*\| policyDenied' SeLe4n/Model/KernelError.lean
run_check "INVARIANT" rg -n '^\s*\| dependencyViolation' SeLe4n/Model/KernelError.lean

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
run_check "INVARIANT" rg -n '^\s*\| cyclicDependency' SeLe4n/Model/KernelError.lean
run_check "INVARIANT" rg -n '^def serviceDependencyAcyclic' SeLe4n/Kernel/Service/Invariant/Acyclicity.lean
run_check "INVARIANT" rg -n '^theorem serviceRegisterDependency_preserves_acyclicity' SeLe4n/Kernel/Service/Invariant/Acyclicity.lean

# WS-D4 F-11/Q1: serviceRestart failure anchors removed in Q1; replaced with graph invariant anchors.
run_check "INVARIANT" rg -n 'theorem serviceGraphInvariant_of_storeServiceState_sameDeps' SeLe4n/Kernel/Service/Invariant/Acyclicity.lean
run_check "INVARIANT" rg -n '^theorem serviceRegisterDependency_preserves_serviceGraphInvariant' SeLe4n/Kernel/Service/Invariant/Acyclicity.lean

# WS-D4 F-12 double-wait prevention + uniqueness invariant anchors must remain present.
run_check "INVARIANT" rg -n '^\s*\| alreadyWaiting' SeLe4n/Model/KernelError.lean
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
run_check "INVARIANT" rg -n '^\s*\| untypedRegionExhausted' SeLe4n/Model/KernelError.lean
run_check "INVARIANT" rg -n '^\s*\| untypedTypeMismatch' SeLe4n/Model/KernelError.lean
run_check "INVARIANT" rg -n '^\s*\| untypedDeviceRestriction' SeLe4n/Model/KernelError.lean
run_check "INVARIANT" rg -n '^\s*\| untypedAllocSizeTooSmall' SeLe4n/Model/KernelError.lean
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
# `cross-core-ipc` banner tag (the contract the future SM10.E kernel-image driver
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
# agree on the `tlb-shootdown-stress` banner tag (the contract the future SM10.E
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
# PR #845 review (P2), closed by removal (WS-RA): the legacy syscall entry
# that could not drain the ledger (`syscallDispatchInner`) is deleted with the
# bit-63 protocol, so the deferral concern it documented no longer exists —
# the removal note that replaced it must say so, and the export must not
# return (the negative anchor above).
run_prose_check "INVARIANT" rg -n 'vestigial .syscall_dispatch_inner. export is REMOVED' SeLe4n/Platform/FFI.lean
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
run_prose_check "INVARIANT" rg -n 'per-core boundary has 58 entries' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
run_check "INVARIANT" rg -n 'enforcementBoundaryPerCore\.length = 58' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
run_check "INVARIANT" rg -n '^theorem enforcementBoundaryPerCore_extends_canonical' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
run_check "INVARIANT" rg -n '^def enforcementBoundaryPerCoreComplete' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
run_check "INVARIANT" rg -n '^theorem enforcementBoundaryPerCore_is_complete' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
# WS-SM SM8.E.3 retired `enforcementBoundaryPerCore_entry_is_new` (it asserted
# the canonical list did NOT carry the bracket, true only until the promotion)
# in favour of the three theorems that survive it: the canonical list classifies
# the bracket capability-only, it is classified exactly once across the per-core
# list, and the wrappers do not carry a second copy.  The negative anchor is
# what stops the retired form coming back beside them.
run_check "INVARIANT" rg -n '^theorem enforcementBoundary_classifies_withLockSet' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
run_check "INVARIANT" rg -n '^theorem enforcementBoundaryPerCore_classifies_withLockSet_once' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
run_check "INVARIANT" rg -n '^theorem crossCoreEnforcementEntries_omits_withLockSet' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
run_negative_check "INVARIANT" rg -n '^theorem enforcementBoundaryPerCore_entry_is_new' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
# …and the per-core list must not re-append the bracket it now inherits.
run_negative_check "INVARIANT" rg -n 'enforcementBoundaryExtended \+\+ \[\.capabilityOnly "withLockSet"\]' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
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
# SM9.A.4b took the inventory 26 -> 28 with the two audit readers, both of
# which take an executing core and carry an EMPTY write set.
run_check "INVARIANT" rg -n 'CrossCoreTransition.all.length = 30' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean

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
run_check "INVARIANT" rg -n '^theorem crossCoreNiTheorem_count : CrossCoreTransition\.all\.length = 30' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
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
# Registered as a checked partition so SM10.E cannot wire the first restore
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
# SM9.A.1a moved the timestamp layer DOWN to `AuditRecord.lean`, below
# `Model/State`, so the production drain can state its preservation — the same
# extraction SM7.A performed for `TlbInvalidation`.  The per-core consumer is
# `auditLogOnCore_timestamp_identifies_event`, which is `start`-parameterised
# because a drained trail no longer begins at 0.
run_check "INVARIANT" rg -n '^theorem declassificationAuditLog_timestamp_identifies_event' SeLe4n/Kernel/InformationFlow/AuditRecord.lean
run_check "INVARIANT" rg -n '^theorem auditLogOnCore_timestamp_identifies_event' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
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
# Scoped to the PRODUCER surface (PR #870 round 6): the forbidden arm is a
# recorder that truncates instead of failing closed, and it can only live in
# the record/producer modules.  The authorized remover (`AuditRead.lean`'s
# drain) and theorem statements about the drained shape
# (`auditDrain_moves_partial_readers_status`) legitimately spell a dropped
# trail, so a repo-wide pattern would forbid statements about the very
# operation the phase ships.
run_negative_check "INVARIANT" rg -n 'declassificationAuditLog := log.drop|declassificationAuditLog := log.tail' SeLe4n/Kernel/InformationFlow/AuditRecord.lean SeLe4n/Kernel/InformationFlow/Declassification.lean SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
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
# (SM8.C's `declassificationChainLinked_is_syntactic` was retired by SM9.D,
# which makes it genuinely false; its successor is anchored — with the
# retirement negative — in the SM9.D block below.)
run_check "INVARIANT" rg -n '^theorem declassificationChainLinked_is_causal' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
run_check "INVARIANT" rg -n '^theorem declassificationSubjectDomain_is_core_selected' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
run_check "INVARIANT" rg -n '^theorem declassifyStoreOnCore_refusal_has_no_post_state' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
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

# SM8.C (PR #863 review): `liftLegacyContext` must lift the legacy lattice
# FAITHFULLY, not as the `linearOrder` over-approximation it used to carry.  The
# equality is the property; the counterexample is what stops a regression to the
# linear order from building; and the NEGATIVE anchor forbids the old wiring.
run_check "INVARIANT" rg -n '^def DomainFlowPolicy.legacyLattice' SeLe4n/Kernel/InformationFlow/Policy.lean
run_check "INVARIANT" rg -n '^@\[simp\] theorem legacyLattice_canFlow_embed' SeLe4n/Kernel/InformationFlow/Policy.lean
run_check "INVARIANT" rg -n '^theorem linearOrder_is_not_faithful_to_legacy' SeLe4n/Kernel/InformationFlow/Policy.lean
run_check "INVARIANT" rg -n '^theorem DomainFlowPolicy.legacyLattice_wellFormed' SeLe4n/Kernel/InformationFlow/Policy.lean
run_check "INVARIANT" rg -n 'policy := .legacyLattice' SeLe4n/Kernel/InformationFlow/Policy.lean
run_negative_check "INVARIANT" rg -n 'policy := .linearOrder' SeLe4n/Kernel/InformationFlow/Policy.lean
run_check "INVARIANT" rg -n '^  runFaithfulLegacyLiftChecks' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'NEGATIVE: linearOrder disagrees on exactly one of the 16 pairs' tests/SmpInformationFlowSuite.lean
# The boundary count is pinned by a theorem; `enforcementBoundary`'s own
# docstring must NOT restate it, which is how it came to read "33 entries"
# across six expansions.
run_prose_negative_check "INVARIANT" rg -n 'classification table \([0-9]+ entries\)' SeLe4n/Kernel/InformationFlow/Enforcement/Wrappers.lean
# WS-SM SM8.E.3 took the canonical boundary 39 -> 40 with the 2PL bracket;
# SM9.A.11 took it 40 -> 42 with the two audit readers.
run_check "INVARIANT" rg -n 'enforcementBoundaryExtended.length = 43' SeLe4n/Kernel/InformationFlow/Enforcement/Soundness.lean
run_check "INVARIANT" rg -n '^  runEndpointPolicyGateChecks' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'NEGATIVE: a widening override cannot open a flow the lattice denies' tests/SmpInformationFlowSuite.lean

# ---------------------------------------------------------------------------
# WS-SM SM8.D — information flow under fine locks
# (plan SMP_INFORMATION_FLOW_PLAN.md §5 SM8.D.1 … SM8.D.6).
# ---------------------------------------------------------------------------
# SM8.D.1: the lock-erased content, and the FACTORING that makes "an observer
# sees nothing of the lock" a statement about the field rather than about a
# particular write.  `projectKernelObject_setLock` is the load-bearing one: it
# quantifies over every value the field could hold.
# The setter and the erased content live beside the SM3.A.10 `objectLockOf`
# getter, not in the staged information-flow module: they are model vocabulary,
# and a `KernelObject` setter reachable only through a staged module would be
# the wrong layering.  Pinned in both directions.
run_check "INVARIANT" rg -n '^def setLock' SeLe4n/Model/Object/Structures.lean
run_check "INVARIANT" rg -n '^def eraseLock' SeLe4n/Model/Object/Structures.lean
run_check "INVARIANT" rg -n '^@\[simp\] theorem eraseLock_wellFormed' SeLe4n/Model/Object/Structures.lean
run_negative_check "INVARIANT" rg -n '^def KernelObject.setLock' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^@\[simp\] theorem projectKernelObject_setLock' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^theorem projectKernelObject_eq_eraseLock' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^theorem onCore_lock_invisible' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^theorem onCore_lock_indistinguishable' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^def lockWritesOnly' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^theorem lockWritesOnly_preserves_onCore' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^theorem withLockSet_lockWritesOnly' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
# The non-vacuity witness: a lock write is a REAL write, so `eraseLock` is an
# abstraction over content that moves.  Without it every §1..§5 result would be
# indistinguishable from "the bracket does nothing".
run_check "INVARIANT" rg -n '^theorem KernelObject.updateLock_not_identity' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
# SM8.D.2 / SM8.D.3 (model half): reader multiplicity and writer exclusion, the
# latter stated for the BLOCKED acquirer itself — which is the plan D.3 row's
# refutation rather than a restatement of it.
run_check "INVARIANT" rg -n '^theorem readerMultiplicity_not_observable' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^theorem readerMultiplicity_not_observable_at_reachable_witness' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^theorem writerExclusion_not_observable' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^theorem blockedAcquirer_observes_nothing' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
# SM8.D.3 (timing half): the CC-5 bound.  The alphabet must reserve a code for
# the un-admitted case (`+ 2`, not `+ 1`) or a zero-step delay and "no sample"
# collapse onto each other and `lockContentionCode_injective` stops holding.
run_check "INVARIANT" rg -n '^theorem lockContention_delay_bounded' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^theorem lockContentionChannel_alphabet_bounded' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^theorem lockContentionChannel_trace_capacity' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n 'lockContentionDelayBound maxDelay \+ 2' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^theorem lockContentionCode_injective' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^theorem lockContentionAlphabet_at_least_two' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^theorem acceptedCovertChannel_lockContention_bounded' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
# The observation is keyed to the acquisition it measures.  `admissionStep` is
# the core's FIRST admission in the whole execution, so an observation built on
# it truncates a repeat acquirer's genuine wait to zero; `admissionStepAfter` is
# the enqueue-relative form the channel needs, and the negative anchor forbids a
# regression to the first-admission reading.
run_check "INVARIANT" rg -n '^def RwLockExecution.admissionStepAfter' SeLe4n/Kernel/Concurrency/Locks/RwLock.lean
run_check "INVARIANT" rg -n '^theorem rwLock_writer_admissionStepAfter_bounded' SeLe4n/Kernel/Concurrency/Locks/RwLock.lean
run_check "INVARIANT" rg -n 'e.admissionStepAfter c enqueueStep' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^theorem lockContentionObservation_is_own_acquisition' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_negative_check "INVARIANT" rg -n 'e\.admissionStep c\)\.map' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
# The CC-5 treatment has all three parts CC-1 has: alphabet, PACING, capacity.
# Without the pacing bound the run capacity would count observations with no
# wall-clock window attached, which is what an earlier cut did by modelling a
# run as a list of unrelated executions.
run_check "INVARIANT" rg -n '^theorem RwLockExecution.distinct_steps_length_le' SeLe4n/Kernel/Concurrency/Locks/RwLock.lean
run_check "INVARIANT" rg -n '^theorem lockContentionChannel_observation_rate_bounded' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n 'enqueueSteps : List Nat' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
# The fairness premise is load-bearing, and the RPi5 figure is split into the
# grounded core count and SM2.C-defer D-3.7's PLACEHOLDER release budget.
run_check "INVARIANT" rg -n '^theorem lockContention_unbounded_without_fairness' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^theorem starvingExecution_writer_never_releases' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^theorem lockContentionDelayBound_rpi5_coreFactor' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^theorem lockContentionAlphabet_at_release_budget' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
# A prose check: the subject IS the docstring sentence that keeps the 3077
# figure from being read as a measured deployment property.
run_prose_check "INVARIANT" rg -n 'placeholder, not a measured deployment figure' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
# The blocked READER, which is the plan's D.3 row's own subject: the structural
# depth cap, the operational admission fact, and — after SM2.C-defer D-3.10 —
# the TEMPORAL bound, which the writer-only liveness chain could not supply.
run_check "INVARIANT" rg -n '^theorem queueWaitDepth_bounded' SeLe4n/Kernel/Concurrency/Locks/RwLock.lean
run_check "INVARIANT" rg -n '^theorem readerWaitDepth_bounded' SeLe4n/Kernel/Concurrency/Locks/RwLock.lean
run_check "INVARIANT" rg -n '^theorem reader_at_head_admitted_by_writer_release' SeLe4n/Kernel/Concurrency/Locks/RwLock.lean
run_check "INVARIANT" rg -n '^theorem readerContentionDepth_bounded' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^theorem blockedReader_admitted_by_writer_release' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
# The mode-generic liveness chain: the keystone, its `.write` instance (which
# checks the generalisation against the theorem it generalises), the mode-exact
# admission that makes a reader's admission an admission AS A READER, and the
# two bounds SM8.D consumes.
run_check "INVARIANT" rg -n '^theorem queueWaitDepth_monotone_under_effective_release' SeLe4n/Kernel/Concurrency/Locks/RwLock.lean
run_check "INVARIANT" rg -n '^theorem queueWaitDepth_monotone_under_effective_release_write' SeLe4n/Kernel/Concurrency/Locks/RwLock.lean
run_check "INVARIANT" rg -n '^theorem queueWaitDepth_non_increase_step_queued' SeLe4n/Kernel/Concurrency/Locks/RwLock.lean
run_check "INVARIANT" rg -n '^theorem fair_progress_one_step_mode' SeLe4n/Kernel/Concurrency/Locks/RwLock.lean
run_check "INVARIANT" rg -n '^theorem rwLock_queued_liveness' SeLe4n/Kernel/Concurrency/Locks/RwLock.lean
run_check "INVARIANT" rg -n '^theorem rwLock_reader_liveness' SeLe4n/Kernel/Concurrency/Locks/RwLock.lean
run_check "INVARIANT" rg -n '^theorem rwLock_queued_admissionStepAfter_bounded' SeLe4n/Kernel/Concurrency/Locks/RwLock.lean
run_check "INVARIANT" rg -n '^theorem rwLock_reader_admissionStepAfter_bounded' SeLe4n/Kernel/Concurrency/Locks/RwLock.lean
run_check "INVARIANT" rg -n '^theorem queued_reader_not_write_holder_after_step' SeLe4n/Kernel/Concurrency/Locks/RwLock.lean
run_check "INVARIANT" rg -n '^theorem queued_writer_not_reader_after_step' SeLe4n/Kernel/Concurrency/Locks/RwLock.lean
run_check "INVARIANT" rg -n '^theorem queued_persists_or_admitted_at_mode' SeLe4n/Kernel/Concurrency/Locks/RwLock.lean
run_check "INVARIANT" rg -n '^theorem blockedReaderContention_delay_bounded' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^theorem writerContention_delay_bounded' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
# The CC-5 bound and its two claim entries take the access mode as a parameter;
# the NEGATIVE forbids a regression that re-pins the *claim* to a queued writer,
# which would silently drop the blocked reader — the plan's D.3 subject — back
# out of the bound while leaving the writer instance passing every anchor above.
run_check "INVARIANT" rg -n '\(c : CoreId\) \(m : AccessMode\) \(kEnq : Nat\)' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_negative_check "INVARIANT" rg -n 'AccessMode.write\) ∈ \(e.stateAt kEnq\).waiters →' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
# The severity is a judgement; what it is a judgement *about* is pinned.
run_check "INVARIANT" rg -n '^theorem acceptedCovertChannel_lockContention_severity_basis' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
# The declared-footprint entry CONSUMES the resolver, and fails closed for every
# syscall SM3.C.9 has not declared.  The negative forbids a return to the form
# whose resolution hypothesis was unused.
run_check "INVARIANT" rg -n '^def syscallEntryUnderDeclaredLockSet' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^theorem syscallEntryUnderDeclaredLockSet_undeclared' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_negative_check "INVARIANT" rg -n '_hFootprint' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
# ...and the footprint's inputs come from the entry's OWN decode, not from
# arguments supplied alongside it.  The negative forbids the free-parameter
# shape, under which a caller could bracket `.tcbSuspend`'s footprint around
# whatever the caller's registers happened to decode to.
run_check "INVARIANT" rg -n '^def entryDecode' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^def entryCapTarget' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
# The resolved target passes the same AL7-A sentinel guard the live `.tcbSuspend`
# arm applies, so no footprint is declared for a call the dispatch will reject.
run_check "INVARIANT" rg -n '^theorem entryCapTarget_rejects_sentinel' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
# The footprint is resolved before its own CNode read lock is held, so the
# revalidating bracket re-resolves after the growing phase and fails closed on a
# change — the resolve/acquire race, closed rather than assumed away.
run_check "INVARIANT" rg -n '^def syscallEntryUnderRevalidatedLockSet' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^theorem syscallEntryUnderRevalidatedLockSet_footprint_stable' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^theorem syscallEntryUnderRevalidatedLockSet_refuses_on_change' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^theorem syscallEntryUnderRevalidatedLockSetModel_refines' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
# The bracket's scope is the OBJECT domain; the two domains it cannot express are
# registered as data with owners rather than left to a comment.
run_check "INVARIANT" rg -n '^inductive UncoveredLockDomain' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^theorem declaredFootprintUncoveredDomains_complete' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
# The declared-footprint witness carries the confinement core too.
run_check "INVARIANT" rg -n '^theorem suspendUnderDeclaredLockSet_preserves_projectionOnCore_atCore' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n 'toValid\?' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
# PR #864 review round 5.  The revalidation guard takes the observed post-acquire
# state as an INPUT: derived from `s` alone it could only ever see the acquire,
# which writes nothing the resolver reads, so the refusal branch was unreachable.
run_check "INVARIANT" rg -n '\(s observed : SystemState\)' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^def syscallEntryUnderRevalidatedLockSetModel' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^theorem syscallEntryUnderRevalidatedLockSetModel_refines' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^theorem revalidationRefusalReachable' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
# NEGATIVE: the guard must not go back to re-deriving the observed state from `s`,
# which is what made its refusal unreachable.
run_negative_check "INVARIANT" rg -n '\(lockSetAcquiredState S lockCore s\) = some S' \
  SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
# The resolution may not leave the CNode the footprint read-locks: a `LockSet` is
# capped at `maxLockSetSize`, a CSpace path is not, so deeper paths fail closed.
run_check "INVARIANT" rg -n '^theorem entryCapTarget_single_level' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n 'ref\.cnode' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
# The splice's neighbour-TCB writes ride the endpoint write lock (the
# queue-owning-object umbrella) — the seventh member of a coverage family that
# stopped at six, exactly where the umbrella began.
run_check "INVARIANT" rg -n '^theorem suspendFootprint_splice_neighbors_under_endpoint_lock' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n 'cancelSpliceNeighbors\?' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
# The suite exercises the declared path POSITIVELY and demonstrates the refusal;
# before round 5 every declared-footprint result in the group was `none`.
run_check "INVARIANT" rg -n 'NEGATIVE: a capability replaced under the growing phase is refused' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'decode through a write cap resolves a real footprint' tests/SmpInformationFlowSuite.lean
# PR #864 review round 6.  The revalidated entry continues from `observed` — the
# state the guard checked — not from `s`; running from `s` would discard exactly
# the intervening commits the revalidation just accepted.
run_check "INVARIANT" rg -n '^def continueFromAcquired' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^theorem withLockSet_eq_continueFromAcquired' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^def syscallEntryFromAcquired' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^theorem syscallEntryUnderLockSet_eq_fromAcquired' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^theorem syscallEntryUnderRevalidatedLockSet_not_refines_in_general' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
# NEGATIVE: a general refinement against the plain bracket would re-assert the
# defect — it held only while the action was being run from `s`.
run_negative_check "INVARIANT" rg -n '^theorem syscallEntryUnderRevalidatedLockSet_refines' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
# The splice-coverage theorem must discriminate: its neighbour clauses name the
# neighbour and its link back to the victim, so an unrelated TCB cannot satisfy
# them.  A constant-function arm proved only that the endpoint lock is present.
run_check "INVARIANT" rg -n 'tcbQueueLinkIntegrity' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n 'queueNext = some targetTid' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n 'queuePrev = some targetTid' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
# The CC-5 non-closure witness holds the OBSERVING core fixed; `aheadCore` is
# queued in front of it and is never the core read.
run_check "INVARIANT" rg -n '^def aheadCore' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n 'the two reachable codes are read by the SAME core' tests/SmpInformationFlowSuite.lean
# NEGATIVE: the witness must not go back to comparing two different waiters.
run_negative_check "INVARIANT" rg -n 'lockContentionCode twoWaiterExecution aheadCore' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
# The claim inventory's secure-flow arm is quantified over the confinement core,
# so an `…_atCore` regression breaks it instead of elaborating anyway.
run_check "INVARIANT" rg -n 'niName! syscallEntryUnderLockSet_preserves_projectionOnCore_atCore' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
# PR #864 review round 7.  The CSpace guard is structural: the root consumes
# every bit, so the resolution cannot recurse — checking only the final
# `ref.cnode` would accept a path that leaves the root and cycles back to it.
run_check "INVARIANT" rg -n 'rootCn.depth . rootCn.guardWidth . rootCn.radixWidth' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
# The revalidated bracket distinguishes three outcomes, requires the observed
# state to HOLD the footprint, and releases it on refusal.
run_check "INVARIANT" rg -n '^inductive RevalidatedEntryOutcome' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n 'lockSetHeld lockCore S observed' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^theorem syscallEntryUnderRevalidatedLockSet_refused_releases' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
# NEGATIVE: the refusal branch must not go back to returning `none`, which is
# what stranded the acquired footprint on the caller.
run_negative_check "INVARIANT" rg -n 'observed = none := by' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
# CC-5's bound is denominated in LOCK OPERATIONS; reading it as time needs an
# explicit per-critical-section ceiling.
run_check "INVARIANT" rg -n '^def elapsedBetween' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^theorem elapsedBetween_le' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^theorem lockContention_wallClock_bounded' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
# PR #864 review round 9.  The rate bound must be in elapsed time, not lock
# operations; the domain inventory must quantify over constructors; and the
# Biba predicate's lock erasure is a stated scope, not an unnoticed gap.
run_check "INVARIANT" rg -n '^theorem elapsedBetween_ge' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^theorem lockContentionChannel_rate_per_elapsed_time' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
# PR #864 review round 10 (both P1).  The rate must be measured over the
# execution's OWN window — `ops.length` intervals, not one more — and the
# elapsed-time rate must be CONSUMED by the severity basis and the claim
# inventory, not merely proven nearby.
run_check "INVARIANT" rg -n 'elapsedBetween cost 0 e.ops.length' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n 'hPos : ∀ k ∈ steps, 1 ≤ k' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
# NEGATIVE: measuring through `ops.length + 1` sums an interval the execution
# does not occupy, letting an observation be paid for after it ended.
run_negative_check "INVARIANT" rg -n 'elapsedBetween cost 0 \(e.ops.length \+ 1\)' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^theorem UncoveredLockDomain.mem_all' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^theorem lockAcquisition_modifies_trusted_object_and_is_not_counted' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
# NEGATIVE: the completeness theorem must not go back to comparing the domain
# list against a literal, which a third constructor would leave elaborating.
run_negative_check "INVARIANT" rg -n 'Prod.fst\) = \[.schedulerDomain, .dynamicPipChain\]' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n 'NEGATIVE: an observed state that does not hold the footprint is refused' tests/SmpInformationFlowSuite.lean
# The queue-owning-object umbrella is an AUTHORIZATION statement, not an
# exclusion one.  The protocol it would need is violated today by a footprint
# that writes a queued neighbour without the endpoint lock, and that gap is a
# theorem plus a registered domain rather than prose.
run_check "INVARIANT" rg -n '^def queueOwnershipRespected' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^theorem suspendFootprint_respects_queueOwnership' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^theorem lockSet_tcbSetPriority_omits_endpointLock' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^theorem queueOwnership_violated_by_tcbSetPriority' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '\.queueOwnershipProtocol, "' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n 'NEGATIVE: tcbSetPriority writes a queued neighbour with no endpoint lock' tests/SmpInformationFlowSuite.lean
# NEGATIVE: the splice docstring must not go back to claiming the umbrella
# closes the gap — exclusion needs every writer of a queued TCB to hold the
# endpoint lock, which `queueOwnership_violated_by_tcbSetPriority` refutes.
run_negative_check "INVARIANT" rg -n 'there is no hole to close' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
# The severity basis carries the fairness and enqueue-edge premises themselves,
# not merely the code inequality they make meaningful.
run_check "INVARIANT" rg -n 'contentionWitnesses_fair.1, contentionWitnesses_fair.2' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n 'contentionWitnesses_in_premises.1, contentionWitnesses_in_premises.2' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
# The multi-reader witness carries REACHABILITY, not merely well-formedness: a
# wf-only existential could be satisfied by a lock word no execution produces,
# which is the opposite of the non-vacuity the theorem claims.
run_check "INVARIANT" rg -n '^theorem rwLock_reader_multiplicity_reachable' SeLe4n/Kernel/Concurrency/Locks/RwLock.lean
run_check "INVARIANT" rg -n 'RwLockReachable shared' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^def declaredLockSetForEntry' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^theorem declaredLockSetForEntry_binds_decode' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^theorem declaredLockSetForEntry_is_suspend_footprint' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^theorem entryDecode_none_entry_error' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
# The anti-drift tie runs on BOTH sides.  The failing side alone stays true and
# silent if the duplicated prefix diverges while the helper still succeeds, so
# the success side pins the live entry to the helper's exact tid and decode.
run_check "INVARIANT" rg -n '^theorem entryDecode_some_entry_dispatches' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n 'dispatchSyscallChecked ctx decoded tid' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
# The revalidation refusal is attributable to the resolution change rather than
# to a lost grant, and the fixture witnessing it has genuine acquire lineage.
run_check "INVARIANT" rg -n '^theorem syscallEntryUnderRevalidatedLockSet_refuses_on_change_while_held' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n 'private def suspendAcquiredState' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'the observed state still HOLDS the declared footprint' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'NEGATIVE: the pre-acquire state does not hold the footprint' tests/SmpInformationFlowSuite.lean
# NEGATIVE: the foreign-commit fixture must not go back to being built straight
# from the pre-acquire state, which holds none of the declared locks and so
# refuses for the wrong reason.
run_negative_check "INVARIANT" rg -n '\{ suspendEntryState with' tests/SmpInformationFlowSuite.lean
run_negative_check "INVARIANT" rg -n 'syscallEntryUnderDeclaredLockSet ctx sid callerTid targetTid' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
# The 2PL bracket's grant condition is a checked fact in BOTH directions: the
# growing phase grants an uncontended footprint and provably does not grant a
# contended one, so the contract cannot silently claim mutual exclusion again.
run_check "INVARIANT" rg -n '^theorem lockSetAcquiredState_grants_when_free' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^theorem lockSetAcquiredState_does_not_grant_when_contended' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_prose_negative_check "INVARIANT" rg -n 'state where every lock in .S. has been' SeLe4n/Kernel/Concurrency/Locks/WithLockSet.lean
# The CC-5 run requires DISTINCT enqueue steps, so the per-execution capacity
# figure follows for every accepted run rather than for well-behaved ones.
run_check "INVARIANT" rg -n 'enqueueSteps.Nodup' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^theorem lockContentionChannel_run_capacity' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^theorem lockContentionRun_rejects_repeated_step' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
# A run entry must be a genuine enqueue EDGE, not merely a step at which the core
# happens to be queued — otherwise one acquisition contributes one entry per
# waiting step and the capacity figure counts the same behaviour repeatedly.
run_check "INVARIANT" rg -n '^theorem lockContentionRun_rejects_still_queued_step' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^theorem lockContentionRun_steps_are_edges' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
# The non-closure claim rests on REACHABLE codes, not on the allocated
# alphabet's arithmetic floor: an accepted acquisition's code is at least two, so
# the two codes the floor counts are exactly the two it cannot produce.
run_check "INVARIANT" rg -n '^theorem lockContentionChannel_two_codes_reachable' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^theorem acceptedContentionCode_ge_two' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^theorem contentionWitnesses_fair' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^theorem contentionWitnesses_in_premises' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
# The combined flow witness carries the executing core, not only the boot core.
run_check "INVARIANT" rg -n '^theorem secureInformationFlow_underFineLocks_atCore' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
# BOTH integrity orders are pinned by the dependent claim inventory: a single arm
# would keep elaborating if the authority-order result were weakened.
run_check "INVARIANT" rg -n 'authorityIntegrityUnderLocks' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n 'FineLockClaimId.all.length = 11' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
# The declared suspend footprint locks the CALLER's CSpace root — the CNode the
# capability resolution reads — not the victim's.  The negative forbids a return
# to the victim-root form.
run_check "INVARIANT" rg -n 'caller.cspaceRoot' SeLe4n/Kernel/Concurrency/Locks/LockSetForSyscall.lean
run_negative_check "INVARIANT" rg -n 'lockSet_tcbSuspend callerTid victim.cspaceRoot' SeLe4n/Kernel/Concurrency/Locks/LockSetForSyscall.lean
# The bracket's non-interference is parameterized by the core it runs on; the
# boot form is an instance, not the statement.
run_check "INVARIANT" rg -n '^theorem syscallEntryUnderLockSet_preserves_projectionOnCore_atCore' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^theorem lowEquivalent_smp_of_projectionOnCore_and_confinement' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem sharedViewUnchanged_of_projectionOnCore' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
# The decidable refuter, and the non-degenerate witness context for the two
# integrity write rules.
run_check "INVARIANT" rg -n '^def lockWritesOnlyCheck' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^theorem lockWritesOnly_lockWritesOnlyCheck' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^theorem writeRulesWitnessContext_nontrivial' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
# SM8.D.4: BOTH integrity directions.  seLe4n's `integrityFlowsTo` deliberately
# reverses standard BIBA, so a result about only one of them would say nothing
# about a deployment configured with the other — and `writeRules_differ` is what
# records that the two are not the same claim twice.
run_check "INVARIANT" rg -n '^theorem bibaIntegrity_underLockSet' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^theorem authorityIntegrity_underLockSet' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^theorem writeRules_differ' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^theorem lockWrite_carries_no_subject_data' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^theorem lockPhases_integrity_clean_on_every_core' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
# SM8.D.5: the witness, and the per-core live-entry preservation theorem SM8.B.12
# lacked (`syscallEntry_preserves_projection` covers the boot-pinned entry; the
# SMP dispatch seam calls the checked one).
run_check "INVARIANT" rg -n '^theorem syscallEntryChecked_preserves_projection' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^def syscallEntryUnderLockSet' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^theorem syscallEntryUnderLockSet_preserves_projectionOnCore' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^theorem syscallEntryUnderLockSet_failClosed' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^theorem secureInformationFlow_underFineLocks' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^theorem suspendUnderDeclaredLockSet_preserves_projectionOnCore' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
# The fail-closed conclusion is `lockWritesOnly`, NOT state equality: under fine
# locks the literal `st' = st` claim the unbracketed `…_denied_preserves_state`
# family makes is false, and restoring it would be a claim the bracket cannot
# support.  Pinned negatively.
run_negative_check "INVARIANT" rg -n 'syscallEntryUnderLockSet .*\)\.1 = s$' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
# SM8.D: the claim inventory with dependently-typed evidence — a claim mapped at
# the wrong theorem is a type error, not a stale string.
run_check "INVARIANT" rg -n '^def FineLockClaimId.evidenceProp' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^def fineLockClaimEvidence : \(id : FineLockClaimId\) → id\.evidenceProp' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^theorem fineLockClaims_cover_subTasks' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n 'niName! syscallEntryUnderLockSet_failClosed_invisible' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
# The module is staged, and registered as such in both places.
run_check "INVARIANT" rg -n '^import SeLe4n.Kernel.InformationFlow.FineLockFlow' SeLe4n/Platform/Staged.lean
run_check "INVARIANT" rg -n '^SeLe4n.Kernel.InformationFlow.FineLockFlow' scripts/staged_module_allowlist.txt
run_check "INVARIANT" rg -n 'SeLe4n.Kernel.InformationFlow.FineLockFlow' scripts/check_module_axioms.py
# SM8.D.6: the runtime scenarios and their load-bearing negatives.
run_check "INVARIANT" rg -n '^  runFineLockInvisibilityChecks' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n '^  runReaderMultiplicityChecks' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n '^  runWriterExclusionChecks' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n '^  runLockContentionBoundChecks' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n '^  runFineLockIntegrityChecks' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n '^  runFineLockEntryChecks' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n '^  runFineLockClaimInventoryChecks' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'NEGATIVE: the four raw lock words are pairwise distinct' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'NEGATIVE: the raw lock records core 1 holding and core 0 queued' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'NEGATIVE: core 0 acquired uncontended, so it never enqueued' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'NEGATIVE: the alphabet is never 1' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'NEGATIVE: the acquire really did write the trusted object' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'NEGATIVE: the scenario sub-task carries no Lean claim' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n '^  runRepeatAcquirerChecks' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n '^  runFairnessPremiseChecks' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n '^  runContentionRateChecks' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n '^  runBlockedReaderChecks' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n '^  runContentionFigureChecks' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n '^  runDeclaredFootprintChecks' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n '^  runFineLockSuccessPathChecks' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n '^  runFineLockTraceFixtureCheck' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'NEGATIVE: the first-admission reading would report a delay of 0' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'NEGATIVE: it is never admitted, so the observation is the reserved code' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'NEGATIVE: the alphabet tracks the budget' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'NEGATIVE: the HIGH observer' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'NEGATIVE: a resolvable suspend footprint does not bracket a' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'NEGATIVE: the reader is not queued as a writer' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'the blocked READER.s delay is bounded in time' tests/SmpInformationFlowSuite.lean
# The golden fine-lock contention trace and its hash companion; the trace
# carries the reader's temporal figures, so a regression to the writer-only
# bound changes the fixture rather than passing silently.
run_check "INVARIANT" rg -n '^\[smp-fine-lock\]' tests/fixtures/smp_fine_lock_contention.expected
run_check "INVARIANT" rg -n 'blocked reader in time' tests/fixtures/smp_fine_lock_contention.expected
run_check "INVARIANT" rg -n 'smp_fine_lock_contention\.expected' tests/fixtures/smp_fine_lock_contention.expected.sha256

# ---------------------------------------------------------------------------
# WS-SM SM8.E — tests + closure
# (plan SMP_INFORMATION_FLOW_PLAN.md §5 SM8.E.1 … SM8.E.3).
# ---------------------------------------------------------------------------
# SM8.E.1: the SM8 headline surface in the anchor file the plan names, across
# all five sub-phases.  The import is pinned as well as the labels, because a
# dropped import removes every anchor below it in one edit.
run_check "INVARIANT" rg -n '^import SeLe4n\.Kernel\.InformationFlow\.DeclassificationPerCore' tests/SmpSurfaceAnchors.lean
run_check "INVARIANT" rg -n '^import SeLe4n\.Kernel\.InformationFlow\.FineLockFlow' tests/SmpSurfaceAnchors.lean
run_check "INVARIANT" rg -n 'the declassification producer, its attribution and its partition resolve' tests/SmpSurfaceAnchors.lean
run_check "INVARIANT" rg -n 'cross-core chains, the laundering detector and the basis check resolve' tests/SmpSurfaceAnchors.lean
run_check "INVARIANT" rg -n 'the mounted trail, the live syscall and its fail-closed bound resolve' tests/SmpSurfaceAnchors.lean
run_check "INVARIANT" rg -n 'fine-lock invisibility, the contention bound and the integrity twins resolve' tests/SmpSurfaceAnchors.lean
run_check "INVARIANT" rg -n 'the canonical enforcement boundary carries the two-phase-locking bracket' tests/SmpSurfaceAnchors.lean
# The two channel-capacity theorems the plan's own "what SM8 proves" list names
# and the SM8.D landing left unanchored here.  A bound on the per-acquisition
# delay is not a bound on the channel; the alphabet and the run-length capacity
# are what turn it into one.
run_check "INVARIANT" rg -n 'lockContentionChannel_alphabet_bounded' tests/SmpSurfaceAnchors.lean
run_check "INVARIANT" rg -n 'lockContentionChannel_trace_capacity' tests/SmpSurfaceAnchors.lean

# SM8.E.2: the phase-level golden trace, its runner, its hash companion, and the
# runtime group whose load-bearing negatives make the fixture meaningful.
run_check "INVARIANT" rg -n '^  runPhaseSurfaceChecks' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n '^  runInformationFlowTraceFixtureCheck' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n '^private def informationFlowTraceLines' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'NEGATIVE: the same signal on a LOW notification IS visible' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'NEGATIVE: it IS visible at the core it landed on' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'NEGATIVE: the remote wake is not confined to the EXECUTING core' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'SCOPE: the decidable slice cannot see a badge write' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n '^\[smp-information-flow\]' tests/fixtures/smp_information_flow.expected
run_check "INVARIANT" rg -n 'enforcement boundary: canonical 43' tests/fixtures/smp_information_flow.expected
run_check "INVARIANT" rg -n 'smp_information_flow\.expected' tests/fixtures/smp_information_flow.expected.sha256
# The FIXTURE's independence probe must land on a core whose current thread the
# low observer can SEE, or the reported set is `allCores` and the line is
# vacuous.  Pinned in both directions on the trace line's own wording ("at
# cores:", which is what distinguishes it from §4.1's proof-carrying assertion
# "…is invisible on cores 0, 2 and 3" — that group instantiates
# `crossCoreNonInterference` at named theorems and is correct as written).
run_check "INVARIANT" rg -n "a write to core 0's current slot is invisible at cores" tests/fixtures/smp_information_flow.expected
run_negative_check "INVARIANT" rg -n "a write to core 1's current slot is invisible at cores" tests/SmpInformationFlowSuite.lean

# SM8.E.2 substrate: the operation taxonomy enumerated ONCE, and tied to the
# type.  The counts that read it were 35-element literals, which could not
# notice a thirty-sixth constructor however loudly their docstrings claimed to.
run_check "INVARIANT" rg -n '^def KernelOperation.all' SeLe4n/Kernel/InformationFlow/Invariant/Composition.lean
run_check "INVARIANT" rg -n '^theorem KernelOperation.mem_all' SeLe4n/Kernel/InformationFlow/Invariant/Composition.lean
run_check "INVARIANT" rg -n '^theorem KernelOperation.all_nodup' SeLe4n/Kernel/InformationFlow/Invariant/Composition.lean
run_check "INVARIANT" rg -n 'KernelOperation.all.length = 35' SeLe4n/Kernel/InformationFlow/Invariant/Composition.lean
run_check "INVARIANT" rg -n 'KernelOperation.all.filter perCoreConfinementDerived' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n '^theorem perCoreConfinementNotDerived_count' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean
run_check "INVARIANT" rg -n 'KernelOperation.all.map kernelOperationPerCoreNiTheorem' SeLe4n/Kernel/InformationFlow/NonInterferencePerCore.lean


# ---------------------------------------------------------------------------
# WS-SM SM9.A — the declassification audit trail's READER
# (plan SMP_DECLASSIFICATION_COMPLETION_PLAN.md §4 SM9.A.1 … SM9.A.13).
# ---------------------------------------------------------------------------
# SM8.C shipped a durable, bounded, FAIL-CLOSED trail that nothing could read,
# so a deployment performing `maxDeclassificationAuditEntries` authorized
# downgrades stopped being able to declassify at all until reboot.  SM9.A is
# the read side.  The module is production and sits BELOW the projection layer,
# so it can be consumed by the live syscall arms without pulling the SM8.A/B
# non-interference closure into the dispatch path.
# The live `.auditRead` / `.auditDrain` arms are in `Kernel/API.lean`, so the
# module is production-reachable through the dispatch closure rather than
# through a staged aggregator — which is why it must NOT appear in the staged
# allowlist.  Both directions are pinned.
run_check "INVARIANT" rg -n '^import SeLe4n\.Kernel\.InformationFlow\.AuditRead' SeLe4n/Kernel/API.lean
run_negative_check "INVARIANT" rg -n '^SeLe4n\.Kernel\.InformationFlow\.AuditRead\b' scripts/staged_module_allowlist.txt
run_check "INVARIANT" rg -n '^def auditLogVisibleTo' SeLe4n/Kernel/InformationFlow/AuditRead.lean

# SM9.A.1: the visible view is a genuine sublist, and — the no-gap-leak
# property — a function of the reader's clearance ALONE.  Under a sparse global
# index a partial reader's indices would shift around a hidden entry, telling it
# both that one exists and exactly where.
run_check "INVARIANT" rg -n '^theorem auditLogVisibleTo_sublist' SeLe4n/Kernel/InformationFlow/AuditRead.lean
run_check "INVARIANT" rg -n '^theorem auditLogVisibleTo_hidden_insert' SeLe4n/Kernel/InformationFlow/AuditRead.lean
run_check "INVARIANT" rg -n '^theorem auditLogVisibleTo_determined_by_clearance' SeLe4n/Kernel/InformationFlow/AuditRead.lean

# SM9.A.1a: the persistent timestamp epoch.  Sequenced BEFORE drain, because a
# drain without it reuses timestamps: `timestamp := log.length` after removing a
# prefix collides with a surviving entry, falsifying the identification theorem.
run_check "INVARIANT" rg -n 'declassificationAuditEpoch : Nat := 0' SeLe4n/Model/State.lean
run_check "INVARIANT" rg -n '^def auditTimestampsFrom' SeLe4n/Kernel/InformationFlow/AuditRecord.lean
run_check "INVARIANT" rg -n '^def declassificationTrailWellFormed' SeLe4n/Kernel/InformationFlow/Declassification.lean
run_check "INVARIANT" rg -n 'timestamp := epoch \+ log\.length' SeLe4n/Kernel/InformationFlow/Declassification.lean
run_check "INVARIANT" rg -n '^theorem declassificationTrail_timestamp_identifies_event' SeLe4n/Kernel/InformationFlow/Declassification.lean
run_check "INVARIANT" rg -n '^theorem storeObject_declassificationAuditEpoch_eq' SeLe4n/Model/State.lean
# The witness that the PRE-EPOCH producer is genuinely unsound once drain
# exists.  Kept as a theorem so a regression to `timestamp := log.length` fails
# to build rather than quietly reintroducing the collision.
run_check "INVARIANT" rg -n '^theorem preEpochTimestamp_reused_after_drain' SeLe4n/Kernel/InformationFlow/AuditRecord.lean
# NEGATIVE: the producer must never stamp an entry from the log length alone.
run_negative_check "INVARIANT" rg -n 'timestamp := log\.length' SeLe4n/Kernel/InformationFlow/Declassification.lean

# SM9.A.2: the arbitrary-length chunk protocol.  All four exported fields are
# unbounded `Nat`s, so a fixed low/high pair would only move the truncation
# point to `2^64`; the reader fails closed above the accepted width rather than
# silently truncating, and the basis DESIGNATION ships too (exporting the trust
# bit alone collapses every `integratorOverride` to one value).
run_check "INVARIANT" rg -n '^def auditFieldChunk' SeLe4n/Kernel/InformationFlow/AuditRead.lean
run_check "INVARIANT" rg -n '^def maxAuditFieldChunks' SeLe4n/Kernel/InformationFlow/AuditRead.lean
run_check "INVARIANT" rg -n '^theorem auditReadField_reconstructs' SeLe4n/Kernel/InformationFlow/AuditRead.lean
run_check "INVARIANT" rg -n '^theorem auditReadBasis_reconstructs_designation' SeLe4n/Kernel/InformationFlow/AuditRead.lean
run_check "INVARIANT" rg -n '^theorem auditFieldBound_unreachable_in_kernel' SeLe4n/Kernel/InformationFlow/AuditRead.lean
run_check "INVARIANT" rg -n 'auditFieldTooLarge' SeLe4n/Model/KernelError.lean
# SM9.A.2: `status` is a SINGLE read.  Chunking it traded aliasing for tearing
# on the first interleaved drain, which is what the negative witness records.
run_check "INVARIANT" rg -n '^theorem auditReadStatus_atomic' SeLe4n/Kernel/InformationFlow/AuditRead.lean
run_check "INVARIANT" rg -n '^theorem auditStatusSplitRead_tears' SeLe4n/Kernel/InformationFlow/AuditRead.lean

# SM9.A.2: the two reader classes.  A partial reader gets VIEW-LOCAL indices and
# learns nothing of the global position; a fully-dominating monitor gets global
# identities so it can correlate across drains.  The per-observer drain token
# the first design specified is unbuildable — labels are an unbounded `Nat`, so
# there is no finite family to key state by.
run_check "INVARIANT" rg -n '^theorem auditReadIndex_is_view_local' SeLe4n/Kernel/InformationFlow/AuditRead.lean
run_check "INVARIANT" rg -n '^theorem dominatingReader_sees_global_identity' SeLe4n/Kernel/InformationFlow/AuditRead.lean
run_check "INVARIANT" rg -n '^theorem auditRead_hides_global_position' SeLe4n/Kernel/InformationFlow/AuditRead.lean
run_check "INVARIANT" rg -n '^theorem observerScopedGeneration_not_mountable' SeLe4n/Kernel/InformationFlow/AuditRead.lean

# SM9.A.3: drain under the §3.4 dominance gate.  A partial-visibility prefix
# drain reveals the POSITIONS of hidden entries and repeated drains enumerate
# the hidden layout, so drain is authorized only for a caller dominating every
# recorded source AND destination (PR #870 round 3 — the bridge is
# `_of_labeling`, both halves) — and the gate is derived from the
# CONFIGURATION, never from the rows the trail currently holds (drain a trail
# to `[]` and a rows-derived predicate goes vacuously true exactly where it
# matters).
run_check "INVARIANT" rg -n '^def auditDrainVisiblePrefix' SeLe4n/Kernel/InformationFlow/AuditRead.lean
run_check "INVARIANT" rg -n '^theorem auditDrain_requires_full_dominance_of_labeling' SeLe4n/Kernel/InformationFlow/AuditRead.lean
run_check "INVARIANT" rg -n '^theorem auditDrain_partial_reader_drains_nothing' SeLe4n/Kernel/InformationFlow/AuditRead.lean
run_check "INVARIANT" rg -n '^theorem auditMonitorGate_is_configuration_derived' SeLe4n/Kernel/InformationFlow/AuditRead.lean
run_check "INVARIANT" rg -n '^theorem auditMonitorGate_records_derived_unsound' SeLe4n/Kernel/InformationFlow/AuditRead.lean
run_check "INVARIANT" rg -n '^theorem auditDrain_preserves_wellFormed_at_epoch' SeLe4n/Kernel/InformationFlow/AuditRead.lean
run_check "INVARIANT" rg -n '^theorem auditDrain_next_timestamp_fresh' SeLe4n/Kernel/InformationFlow/AuditRead.lean
run_check "INVARIANT" rg -n '^theorem auditDrain_preserves_proofLayerInvariantBundle' SeLe4n/Kernel/InformationFlow/AuditRead.lean
# The monitor clearance is CONFIGURATION on the labeling context, so an
# unconfigured deployment has no reader at all and keeps the cliff.
run_check "INVARIANT" rg -n 'auditMonitorClearance : Option SecurityDomain := none' SeLe4n/Kernel/InformationFlow/Policy.lean
run_check "INVARIANT" rg -n '^theorem auditDrain_unconfigured_denied' SeLe4n/Kernel/InformationFlow/AuditRead.lean
# PR #870 round 2: the READ side is deny-by-default too — the configuration
# gate refuses every caller when no validated monitor clearance is configured,
# so a boot-provisioned `.auditTrail` capability opens nothing (capability
# provisioning is an axis the labeling context cannot see).  A misconfigured
# clearance validates to `none` and is refused identically.  The gate
# inventory is `auditRead_gates_are_five` (round 6 added the monitor gate at
# the live entry); the undercounting three- and four-gate names must not
# return.
run_check "INVARIANT" rg -n '^theorem auditRead_unconfigured_denied' SeLe4n/Kernel/InformationFlow/AuditRead.lean
run_check "INVARIANT" rg -n '^theorem misconfiguredDeployment_cannot_read' SeLe4n/Kernel/InformationFlow/AuditRead.lean
run_check "INVARIANT" rg -n '^theorem auditRead_gates_are_five' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
run_negative_check "INVARIANT" rg -n 'auditRead_gates_are_three' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
run_negative_check "INVARIANT" rg -n 'auditRead_gates_are_four' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
# PR #870 round 3: visibility filters on EVERY disclosed domain — the filter's
# predicate is the source/destination conjunction, an entry whose destination
# the reader is not cleared for is in no position of its view, and a visible
# entry's target object is one whose own domain flows to the reader (the same
# discipline `capTargetObservable` applies in the projection).  The retired
# source-only dominance bridge must not return.
run_check "INVARIANT" rg -n '^def auditEntryVisibleTo' SeLe4n/Kernel/InformationFlow/AuditRead.lean
run_check "INVARIANT" rg -n '^theorem auditLogVisibleTo_cleared_dst' SeLe4n/Kernel/InformationFlow/AuditRead.lean
run_check "INVARIANT" rg -n '^theorem auditLogVisibleTo_hides_undominated_destination' SeLe4n/Kernel/InformationFlow/AuditRead.lean
run_check "INVARIANT" rg -n '^theorem incomparableDowngrade_hidden_from_source_reader' SeLe4n/Kernel/InformationFlow/AuditRead.lean
run_check "INVARIANT" rg -n '^theorem auditVisibleEntry_target_domain_flows' SeLe4n/Kernel/InformationFlow/AuditRead.lean
run_check "INVARIANT" rg -n '^theorem auditDrain_requires_full_dominance_of_labeling' SeLe4n/Kernel/InformationFlow/AuditRead.lean
run_check "INVARIANT" rg -n '^theorem validatedAuditMonitorClearance_dominates_objects' SeLe4n/Kernel/InformationFlow/AuditRead.lean
run_negative_check "INVARIANT" rg -n 'auditDrain_requires_full_dominance_of_subjects' SeLe4n/Kernel/InformationFlow/AuditRead.lean

# SM9.A.4a: the reader-visibility discipline.  The clause set is a TOTAL
# FUNCTION on `ReadableStructure`, not a list — a `mem_all` over a
# hand-maintained type cannot force a newly mounted readable field to add a
# constructor, whereas a missing case in a total function is a build error.
run_check "INVARIANT" rg -n '^def readableStructureAgrees' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
run_check "INVARIANT" rg -n '^def auditObservationalEquivalence' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
run_check "INVARIANT" rg -n '^theorem auditReadOp_structure_total' SeLe4n/Kernel/InformationFlow/AuditRead.lean
run_check "INVARIANT" rg -n '^theorem readableStructure_list_gate_insufficient' SeLe4n/Kernel/InformationFlow/AuditRead.lean
# NEGATIVE: the fusion's enforcement is the wildcard-free exhaustive match — the
# `∃`-shaped totality theorems above hold of ANY total function, wildcard arms
# included, so they cannot pin it.  These anchors are what does: a wildcard arm
# inserted into either total function is caught here even though every named
# theorem would stay green.  (Span-scoped: the run walks the definition's own
# arm block — arm lines, deeper-indented clause bodies, and the blank lines the
# code view leaves where comments were — and stops at the next declaration.)
run_negative_check "INVARIANT" rg -Un 'def AuditReadOp\.readsStructure[^\n]*\n((  \|[^\n]*| *)\n)*  \|\s*_' SeLe4n/Kernel/InformationFlow/AuditRead.lean
run_negative_check "INVARIANT" rg -Un 'def readableStructureAgrees[^\n]*\n((    [^\n]*|  \|[^\n]*| *)\n)*  \|\s*_' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
# The lemma `lowEquivalent` CANNOT supply: `ObservableState` does not contain
# the trail, so "low-equivalent states give identical visible views" is false
# and could not have been the flow argument.
run_check "INVARIANT" rg -n '^theorem lowEquivalent_does_not_determine_visible_view' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
# SM9.A.4b: the reader is a function of the visible view alone, so it opens no
# channel — the not-CC-8 argument, stated once.
run_check "INVARIANT" rg -n '^theorem auditRead_no_channel' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
run_check "INVARIANT" rg -n '^theorem auditReadFromCore_no_channel' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
run_check "INVARIANT" rg -n '^theorem auditDrain_preserves_projectionOnCore' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
run_check "INVARIANT" rg -n '^theorem auditReadFromCore_perCore_NI' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean

# SM9.A.5: the retry protocol — an append cannot move an index-keyed read.
run_check "INVARIANT" rg -n '^theorem auditRead_stable_under_append' SeLe4n/Kernel/InformationFlow/AuditRead.lean
run_check "INVARIANT" rg -n '^theorem auditRead_bracketed_detects_drain' SeLe4n/Kernel/InformationFlow/AuditRead.lean

# SM9.A.6 / SM9.A.7: the ABI, both halves.  Two syscalls, count 31 -> 33, and
# the Rust mirrors that must agree with them.
run_check "INVARIANT" rg -n '\| \.auditRead\s+=> 31' SeLe4n/Model/Object/Types.lean
run_check "INVARIANT" rg -n '\| \.auditDrain\s+=> 32' SeLe4n/Model/Object/Types.lean
run_check "INVARIANT" rg -n '31 => some \.auditRead' SeLe4n/Model/Object/Types.lean
run_check "INVARIANT" rg -n '32 => some \.auditDrain' SeLe4n/Model/Object/Types.lean
run_check "INVARIANT" rg -n '^def count : Nat := 34' SeLe4n/Model/Object/Types.lean
run_check "INVARIANT" rg -n 'AuditRead = 31' rust/sele4n-types/src/syscall.rs
run_check "INVARIANT" rg -n 'AuditDrain = 32' rust/sele4n-types/src/syscall.rs
run_check "INVARIANT" rg -n 'pub const COUNT: usize = 34;' rust/sele4n-types/src/syscall.rs
run_check "INVARIANT" rg -n 'AuditFieldTooLarge = 55' rust/sele4n-types/src/error.rs

# SM9.A.8: the safe wrappers.  Without them the syscalls are hand-encode-only,
# which is the gap v0.32.98 closed for `.vspaceUnifyInstruction`.
run_check "INVARIANT" rg -n 'pub fn audit_read' rust/sele4n-sys/src/audit.rs
run_check "INVARIANT" rg -n 'pub fn audit_drain' rust/sele4n-sys/src/audit.rs
run_check "INVARIANT" rg -n '^pub mod audit;' rust/sele4n-sys/src/lib.rs

# SM9.A.9: authority is a dedicated `CapTarget`, NOT the `.read`/`.write` right
# alone.  `syscallLookupCap` never constrains `cap.target`, so a rights-only
# gate would repeat the v0.32.97 confused-deputy class exactly — a thread
# holding a writable capability to its own TCB would drain the audit trail.
run_check "INVARIANT" rg -n '^  \| auditTrail' SeLe4n/Model/Object/Types.lean
run_check "INVARIANT" rg -n '^def extractAuditAuthority' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n '^theorem extractAuditAuthority_rejects_non_audit_capability' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n '^theorem auditTrailRead_cannot_drain' SeLe4n/Model/Object/Types.lean
# NEGATIVE: the audit arms must not be gated on the right alone.  A dispatch arm
# that inspects `cap.rights` without first extracting the `.auditTrail` target
# is the confused deputy this sub-task exists to close.
run_negative_check "INVARIANT" rg -n 'auditRead =>.*hasRight' SeLe4n/Kernel/API.lean

# SM9.A.10: the live arms.  Each writes its result into the caller's return
# register via WS-RA's `writeReturnFrameToTcb` — without which the reader
# computes correctly and hands back the caller's own preloaded `x0`.  Both are
# `.word`-shaped, so the boundary READS the staged frame rather than
# constructing a unit one.
run_check "INVARIANT" rg -n '\.auditRead\s+=> \.word' SeLe4n/Kernel/Architecture/SyscallReturn.lean
run_check "INVARIANT" rg -n '\.auditDrain\s+=> \.word' SeLe4n/Kernel/Architecture/SyscallReturn.lean
run_check "INVARIANT" rg -n '^theorem dispatchArm_auditRead_matches_returnShape' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n '^theorem dispatchArm_auditDrain_matches_returnShape' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n '^theorem syscallDelegates_auditRead' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n '^theorem syscallDelegates_auditDrain' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n '^theorem auditReadFromCore_toUInt64_lossless' SeLe4n/Kernel/InformationFlow/AuditRead.lean
# Fail-closed on the UNCHECKED path, and by default: there is no audit read
# that bypasses the flow gate, and an unconfigured deployment has no reader.
run_check "INVARIANT" rg -n '^theorem dispatchWithCap_auditRead_denied' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n '^theorem unconfiguredDeployment_has_no_audit_reader' SeLe4n/Kernel/API.lean
# PR #870 round 2: the arm-level read refusal and the universal half of the
# acceptance witness — no capability whatsoever makes an audit syscall succeed
# in an unconfigured deployment.
run_check "INVARIANT" rg -n '^theorem dispatchWithCapChecked_auditRead_default_denied' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n '^theorem unconfiguredDeployment_audit_never_succeeds' SeLe4n/Kernel/API.lean
# PR #870 round 5: the audit pair validates the capability's TARGET before its
# rights — the checked dispatch routes them through the resolve-only lookup
# (one shared resolution, so lookup and resolve cannot drift), and the arms
# own both gates in the documented order.  The composed-path witnesses are the
# two dispatchSyscallChecked-level theorems.
run_check "INVARIANT" rg -n '^def syscallResolveCap' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n '^def syscallChecksTargetFirst' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n 'syscallChecksTargetFirst decoded.syscallId' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n '^theorem syscallResolveCap_of_lookup' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n '^theorem dispatchWithCapChecked_audit_insufficient_right_denied' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n '^theorem dispatchSyscallChecked_audit_target_first' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n '^theorem dispatchSyscallChecked_audit_right_checked_second' SeLe4n/Kernel/API.lean
# PR #870 round 4: the cross-core inventory's audit entries map to the
# DISPATCH-level composition — transition plus WS-RA return-frame staging,
# the state the checked dispatch actually commits.  The transition-only
# mapping must not return.
run_check "INVARIANT" rg -n '^theorem auditReadDispatch_crossCoreNonInterference' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_check "INVARIANT" rg -n '^theorem auditDrainDispatch_crossCoreNonInterference' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_check "INVARIANT" rg -n 'niName! auditReadDispatch_crossCoreNonInterference' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_check "INVARIANT" rg -n 'niName! auditDrainDispatch_crossCoreNonInterference' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_negative_check "INVARIANT" rg -n 'niName! auditReadFromCore_crossCoreNonInterference' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_negative_check "INVARIANT" rg -n 'niName! auditDrainVisiblePrefix_crossCoreNonInterference' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean

# PR #870 round 6: the live facility is MONITOR-ONLY.  A monitor's drain moves
# a partial reader's visible length — one bit per drain from the dominating
# monitor to a lower subject, the very signal hiding the drain generation was
# meant to remove — so the live entry excludes the receiver: a resolved
# subject the monitor gate refuses is refused the read.  The channel stays
# exhibited at the model reader, and every surviving live reader dominates
# every subject domain, so an observed drain is an authorized flow.  The
# retracted round-2 sentence (partial readers live in configured deployments)
# must not return.
run_check "INVARIANT" rg -n 'if auditMonitorAuthorized ctx monitorClearance reader then' SeLe4n/Kernel/InformationFlow/AuditRead.lean
run_check "INVARIANT" rg -n '^theorem auditReadFromCore_partial_reader_denied' SeLe4n/Kernel/InformationFlow/AuditRead.lean
run_check "INVARIANT" rg -n '^theorem auditReadFromCore_ok_is_monitor' SeLe4n/Kernel/InformationFlow/AuditRead.lean
run_check "INVARIANT" rg -n '^theorem auditDrain_moves_partial_readers_status' SeLe4n/Kernel/InformationFlow/AuditRead.lean
run_check "INVARIANT" rg -n '^theorem auditReadFromCore_observer_dominates_subjects' SeLe4n/Kernel/InformationFlow/AuditRead.lean
run_check "INVARIANT" rg -n '^  runAuditDrainSignalChecks' tests/SmpInformationFlowSuite.lean
run_prose_negative_check "INVARIANT" rg -n 'Partial readers are unchanged where they belong' SeLe4n/

# SM9.A.11 / SM9.A.12 / SM9.A.13: the registries.  Enforcement boundary,
# lock sets, the frozen-ops classifier, and the per-core routing gate — which
# passes with ZERO allowlisted exceptions.
# PR #870 review: the boundary label is the LIVE entry point (the subject-resolution
# seam), never the inner query that takes a caller-supplied reader domain.
run_check "INVARIANT" rg -n 'capabilityOnly "auditReadFromCore"' SeLe4n/Kernel/InformationFlow/Enforcement/Wrappers.lean
run_negative_check "INVARIANT" rg -n 'capabilityOnly "auditReadWord"' SeLe4n/Kernel/InformationFlow/Enforcement/Wrappers.lean
run_check "INVARIANT" rg -n 'capabilityOnly "auditDrainVisiblePrefix"' SeLe4n/Kernel/InformationFlow/Enforcement/Wrappers.lean
run_check "INVARIANT" rg -n 'enforcementBoundaryPerCore.length = 58' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
run_check "INVARIANT" rg -n '^def lockSet_auditRead' SeLe4n/Kernel/Concurrency/Locks/LockSetTransitions.lean
run_check "INVARIANT" rg -n '^def lockSet_auditDrain' SeLe4n/Kernel/Concurrency/Locks/LockSetTransitions.lean
# PR #870 round 6 (the lock domain): a declared footprint covers the COMMITTED
# dispatch — both audit arms and `.serviceQuery` stage their returned word into
# the caller's TCB via `writeReturnFrameToTcb`, so the caller lock is `.write`,
# tied to each footprint by name; the audit pair join the §6b size family and
# the §6c aggregate (which the plan's SM9.A.12 row claimed at landing).  The
# retracted sentence arguing a caller write lock "would over-declare a
# footprint" must not return.
run_check "INVARIANT" rg -n '^theorem lockSet_auditRead_staging_write_mem' SeLe4n/Kernel/Concurrency/Locks/LockSetTransitions.lean
run_check "INVARIANT" rg -n '^theorem lockSet_auditDrain_staging_write_mem' SeLe4n/Kernel/Concurrency/Locks/LockSetTransitions.lean
run_check "INVARIANT" rg -n '^theorem lockSet_serviceQuery_staging_write_mem' SeLe4n/Kernel/Concurrency/Locks/LockSetTransitions.lean
run_check "INVARIANT" rg -n '^theorem lockSet_auditRead_size_le' SeLe4n/Kernel/Concurrency/Locks/Deadlock.lean
run_check "INVARIANT" rg -n '^theorem lockSet_auditDrain_size_le' SeLe4n/Kernel/Concurrency/Locks/Deadlock.lean
run_prose_negative_check "INVARIANT" rg -n 'would over-declare a footprint' SeLe4n/Kernel/Concurrency/Locks/LockSetTransitions.lean
run_check "INVARIANT" rg -n 'auditReadFromCore#inert' scripts/per_core_routing_aliases.json
run_check "INVARIANT" rg -n 'SeLe4n\.Kernel\.InformationFlow\.AuditRead' scripts/check_module_axioms.py
# The two audit readers join the cross-core inventory with an EMPTY write set:
# they take an executing core (the reader's clearance is resolved from the
# subject it runs) and write no core's scheduler slots at all.
run_check "INVARIANT" rg -n 'auditReadDispatch' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_check "INVARIANT" rg -n 'auditDrainDispatch' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_check "INVARIANT" rg -n '^theorem auditReadFromCore_crossCoreNonInterference' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean

# PR #870 round 7: the trail's SINGLETON DISCIPLINE, both halves.
# (P1) The occupancy channel is registered as CC-8 rather than patched a third
# time at the receiver surface: bounded + fail-closed + drainable makes the
# fill level an irreducible inter-domain observable — every policy-authorized
# declassifier reads full/not-full off its own syscall outcome, and a
# monitor-controlled drain flips lower-domain declassification results.
run_check "INVARIANT" rg -n '^def acceptedCovertChannel_auditOccupancy' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
run_check "INVARIANT" rg -n '^theorem acceptedCovertChannel_auditOccupancy_capacity_gates' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
run_check "INVARIANT" rg -n '^theorem auditOccupancy_alphabet_bounded' SeLe4n/Kernel/InformationFlow/AuditRead.lean
run_check "INVARIANT" rg -n '^theorem declassify_capacity_refusal_of_full' SeLe4n/Kernel/InformationFlow/AuditRead.lean
run_check "INVARIANT" rg -n '^theorem auditDrain_flips_declassify_outcome' SeLe4n/Kernel/InformationFlow/AuditRead.lean
run_check "INVARIANT" rg -n '^theorem acceptedCovertChannel_auditOccupancy_bounded' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
# The retracted round-6 sentence — the reader's authorization used to conclude
# no eighth channel entry was owed — must not return in that docstring.
run_prose_negative_check "INVARIANT" rg -n 'is \*\*not owed\*\*' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
# (P2) The state-level serialization subject: the SM3.A.10 `.objStore`
# singleton convention made structural — one canonical spelling, declared in
# all three audit-state footprints, non-disjoint by theorem.  The retracted
# claim that the service registry's writes serialise implicitly via the
# table-level lock must not return; that gap is registered debt, not covered.
run_check "INVARIANT" rg -n '^@\[inline\] def stateLevelLock' SeLe4n/Kernel/Concurrency/Locks/LockSetTransitions.lean
run_check "INVARIANT" rg -n '^theorem lockSet_declassify_stateLevel_write_mem' SeLe4n/Kernel/Concurrency/Locks/LockSetTransitions.lean
run_check "INVARIANT" rg -n '^theorem lockSet_auditRead_stateLevel_read_mem' SeLe4n/Kernel/Concurrency/Locks/LockSetTransitions.lean
run_check "INVARIANT" rg -n '^theorem lockSet_auditDrain_stateLevel_write_mem' SeLe4n/Kernel/Concurrency/Locks/LockSetTransitions.lean
run_check "INVARIANT" rg -n '^theorem auditState_footprints_share_serialization' SeLe4n/Kernel/Concurrency/Locks/LockSetTransitions.lean
run_check "INVARIANT" rg -n '^theorem stateLevelLock_objId_irrelevant' SeLe4n/Kernel/Concurrency/Locks/WithLockSet.lean
run_prose_negative_check "INVARIANT" rg -n 'serialise implicitly via the table-level' SeLe4n/Kernel/Concurrency/Locks/LockSetTransitions.lean

# SM9.A tests: the anchors, the elaboration examples, the seven runtime groups
# and the acceptance gate.  §9.8 is the plan's own acceptance criterion run for
# effect on the live transition: fill -> refuse -> read -> drain -> declassify
# again, with the post-drain timestamp provably fresh.
run_check "INVARIANT" rg -n '^  runAuditVisibleViewChecks' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n '^  runAuditChunkProtocolChecks' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n '^  runAuditReaderClassChecks' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n '^  runAuditMonitorGateChecks' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n '^  runAuditDrainChecks' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n '^  runAuditEpochChecks' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n '^  runAuditLiveArmChecks' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n '^  runAuditCapacityCliffChecks' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'STEP 5: the downgrade refused at capacity now SUCCEEDS' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'NEGATIVE: the PRE-EPOCH rule would have stamped this entry 0' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'NEGATIVE: an unconfigured deployment still has the cliff' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n '^private def auditReaderTraceLines' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'audit view: trail 3 entries' tests/fixtures/smp_information_flow.expected
run_check "INVARIANT" rg -n 'audit ABI: auditRead=31 auditDrain=32 syscalls=34' tests/fixtures/smp_information_flow.expected
# The end-to-end ABI witness: the returned word is the SELECTED one, not the
# caller's own preloaded `x0`.  Without the staged frame the assertion below
# would read back whatever the caller left there.
run_check "INVARIANT" rg -n "10a: .status. returns the visible length \\(2\\), not the caller's own x0" tests/SyscallReturnAbiSuite.lean
run_check "INVARIANT" rg -n '10b: a field read returns the SELECTED entry' tests/SyscallReturnAbiSuite.lean
run_check "INVARIANT" rg -n '10c: NEGATIVE — an all-rights capability to an ordinary object is rejected' tests/SyscallReturnAbiSuite.lean
run_check "INVARIANT" rg -n '10e: NEGATIVE — an unconfigured deployment cannot drain' tests/SyscallReturnAbiSuite.lean
run_check "INVARIANT" rg -n 'audit status .visible length 2, monitor.' tests/fixtures/syscall_return_abi.expected
run_check "INVARIANT" rg -n 'audit drain of one entry .new visible length 1.' tests/fixtures/syscall_return_abi.expected

# ============================================================================
# WS-SM SM9.B — refusal auditing
# (plan SMP_DECLASSIFICATION_COMPLETION_PLAN.md §4 SM9.B.1 … SM9.B.10).
# ============================================================================
#
# SM8.C's trail records authorized downgrades and nothing else, so a monitor
# could not distinguish "no attempts" from "many attempts, all denied".  A
# kernel transition's `.error` arm carries no post-state, so the writer had to
# be the layer that already commits one for every kernel error: the FFI seam.

# SM9.B.1 / SM9.B.2: the record and its ledger, in a leaf below `Model/State`
# (the §6 mount checklist's step 1).  `KernelError` moved to its own
# import-free leaf in the same cut so the record can name it typed rather than
# storing a bare discriminant `Nat`.
run_check "INVARIANT" rg -n '^structure DeclassificationRefusal' SeLe4n/Kernel/InformationFlow/RefusalRecord.lean
run_check "INVARIANT" rg -n '^structure RefusalLedger' SeLe4n/Kernel/InformationFlow/RefusalRecord.lean
run_check "INVARIANT" rg -n '^def recordRefusal' SeLe4n/Kernel/InformationFlow/RefusalRecord.lean
run_check "INVARIANT" rg -n '^def refusalRingSize' SeLe4n/Kernel/InformationFlow/RefusalRecord.lean
run_check "INVARIANT" rg -n '^def maxRefusalCount' SeLe4n/Kernel/InformationFlow/RefusalRecord.lean
run_check "INVARIANT" rg -n '^inductive KernelError where' SeLe4n/Model/KernelError.lean
run_check "INVARIANT" rg -n '^import SeLe4n.Model.KernelError' SeLe4n/Kernel/InformationFlow/RefusalRecord.lean
run_check "INVARIANT" rg -n '^import SeLe4n.Kernel.InformationFlow.RefusalRecord' SeLe4n/Model/State.lean
# The bound is STRUCTURAL — the ring is a `Vector` and the counters are `Fin`s,
# so there is no 17th `proofLayerInvariantBundle` conjunct and no capacity
# obligation on any writer.  The pins below say that the ledger never joined the
# bundle; a cut that adds it there must delete them.
#
# Deliberately NOT a blanket `declassificationRefusals` negative over the whole
# file: the mount owes a *carriage* layer there whatever it holds (no field write
# transports the bundle definitionally — v0.32.151), and a negative that forbade
# the identifier outright would forbid the carriage too.  What must stay absent
# is the field being READ as a conjunct: the `st.declassificationRefusals`
# projection, and anything conjoined after the bundle's last conjunct — which is
# how every conjunct from the 12th to the 16th was actually added.
run_check "INVARIANT" rg -n '^theorem refusalLedger_bounded_structurally' SeLe4n/Kernel/InformationFlow/RefusalRecord.lean
run_check "INVARIANT" rg -n '^theorem refusalCounter_bound_is_structural' SeLe4n/Kernel/InformationFlow/RefusalRecord.lean
run_check "INVARIANT" rg -n '^    auditLogBounded st\.declassificationAuditLog$' SeLe4n/Kernel/Architecture/Invariant.lean
run_negative_check "INVARIANT" rg -n 'auditLogBounded st\.declassificationAuditLog ' SeLe4n/Kernel/Architecture/Invariant.lean
run_negative_check "INVARIANT" rg -n 'st\.declassificationRefusals' SeLe4n/Kernel/Architecture/Invariant.lean
# Saturation, the counted eviction, and the retention window.
run_check "INVARIANT" rg -n '^theorem recordRefusal_saturates' SeLe4n/Kernel/InformationFlow/RefusalRecord.lean
run_check "INVARIANT" rg -n '^theorem recordRefusal_ring_wraps_counted' SeLe4n/Kernel/InformationFlow/RefusalRecord.lean
run_check "INVARIANT" rg -n '^theorem recordRefusal_no_loss' SeLe4n/Kernel/InformationFlow/RefusalRecord.lean
# The ring's own limitation, stated rather than implied absent: a subject can
# flood the ring, but the eviction is COUNTED, so a monitor knows its view is
# incomplete rather than reading 32 rows and believing it saw everything.
run_check "INVARIANT" rg -n '^theorem refusalLedger_eviction_is_counted' SeLe4n/Kernel/InformationFlow/RefusalRecord.lean
run_check "INVARIANT" rg -n '^theorem recordRefusal_never_refuses' SeLe4n/Kernel/InformationFlow/RefusalRecord.lean
# The version, and the bracket it exists for — the trail's own `status` token
# does not move on a ledger write, so a monitor bracketing with it would
# assemble a hybrid record and never detect it.
run_check "INVARIANT" rg -n '^@\[simp\] theorem refusalLedger_version_advances_on_record' SeLe4n/Kernel/InformationFlow/RefusalRecord.lean
run_check "INVARIANT" rg -n '^theorem refusalRead_bracketed_detects_overwrite' SeLe4n/Kernel/InformationFlow/RefusalRecord.lean
run_check "INVARIANT" rg -n '^theorem auditStatus_does_not_detect_refusal_write' SeLe4n/Kernel/InformationFlow/AuditRead.lean
run_check "INVARIANT" rg -n '^theorem refusalStatus_detects_refusal_write' SeLe4n/Kernel/InformationFlow/AuditRead.lean
# The seam-resolved source domain: not reconstructible from the rest of the
# record, and not from the state either — the context is an argument.
run_check "INVARIANT" rg -n '^theorem refusalRecord_domain_is_seam_resolved' SeLe4n/Kernel/InformationFlow/RefusalRecord.lean
run_check "INVARIANT" rg -n '^theorem refusalRecord_domain_is_seam_resolved_at_seam' SeLe4n/Platform/FFI.lean

# SM9.B.9: the seam's filter is a TOTAL function over `SyscallId`, not a list.
# The third taxonomy in this plan fixed the same way (after `ReadableStructure`
# and `ContentFlowSite`): a theorem quantified over a hand-maintained list stays
# true when SM9.C's second declassifying syscall joins neither.
run_check "INVARIANT" rg -n '^inductive RefusalSeamClass' SeLe4n/Kernel/InformationFlow/RefusalRecord.lean
run_check "INVARIANT" rg -n '^def refusalSeamClass' SeLe4n/Kernel/InformationFlow/RefusalRecord.lean
run_check "INVARIANT" rg -n '^theorem refusalSeamClass_total' SeLe4n/Kernel/InformationFlow/RefusalRecord.lean
run_check "INVARIANT" rg -n '^theorem refusalSeam_list_gate_insufficient' SeLe4n/Kernel/InformationFlow/RefusalRecord.lean
run_check "INVARIANT" rg -n '^theorem refusalSeamClass_records_iff' SeLe4n/Kernel/InformationFlow/RefusalRecord.lean
# NEGATIVE: the seam must not filter on a hardcoded `.declassify` literal — that
# is precisely the design SM9.C silently defeats.
run_negative_check "INVARIANT" rg -n 'syscallId.*==.*SyscallId.declassify' SeLe4n/Platform/FFI.lean
# NEGATIVE: and the classification must stay wildcard-free, or a syscall added
# tomorrow falls through to `.exempt` with nothing failing to compile.  The
# pattern covers every wildcard-arm spelling (the definition's own arms use dot
# notation, so a maintainer would write `| _ => .exempt`, which the earlier
# `RefusalSeamClass`-spelled anchor could never match); the module holds no
# legitimate wildcard arm, so the whole file is in scope.
run_negative_check "INVARIANT" rg -n '\|\s*_\s*=>' SeLe4n/Kernel/InformationFlow/RefusalRecord.lean

# SM9.B.9: the write itself, and the three security theorems.
run_check "INVARIANT" rg -n '^def recordSyscallRefusal' SeLe4n/Platform/FFI.lean
run_check "INVARIANT" rg -n 'recordSyscallRefusal ctx executingCore syscallId tid ke x0 stRegs' SeLe4n/Platform/FFI.lean
run_check "INVARIANT" rg -n '^theorem refusalWrite_declassificationAuditLog_eq' SeLe4n/Platform/FFI.lean
run_check "INVARIANT" rg -n '^theorem refusalWrite_cannot_exhaust_trail' SeLe4n/Platform/FFI.lean
run_check "INVARIANT" rg -n '^theorem refusalLedger_write_is_caller_invisible' SeLe4n/Platform/FFI.lean
run_check "INVARIANT" rg -n '^theorem syscallDispatchFromAbi_records_refusal' SeLe4n/Platform/FFI.lean
run_check "INVARIANT" rg -n '^theorem syscallDispatchFromAbi_exempt_refusal_frames_ledger' SeLe4n/Platform/FFI.lean
run_check "INVARIANT" rg -n '^theorem recordSyscallRefusal_frame' SeLe4n/Platform/FFI.lean
run_check "INVARIANT" rg -n '^theorem recordSyscallRefusal_readReturnFrame_eq' SeLe4n/Platform/FFI.lean
run_check "INVARIANT" rg -n '^theorem recordSyscallRefusal_ledger_congr' SeLe4n/Platform/FFI.lean

# SM9.B.3 … SM9.B.8: the §6 mount checklist, run for the third time.  The
# frozen field is REQUIRED (no default), so a silent drop is a compile error.
run_check "INVARIANT" rg -n '^  declassificationRefusals : SeLe4n.Kernel.RefusalLedger' SeLe4n/Model/State.lean
run_check "INVARIANT" rg -n '^  declassificationRefusals : SeLe4n.Kernel.RefusalLedger$' SeLe4n/Model/FrozenState.lean
run_check "INVARIANT" rg -n '^theorem freeze_preserves_declassificationRefusals' SeLe4n/Model/FrozenState.lean
run_check "INVARIANT" rg -n 'sst.declassificationRefusals = fst.declassificationRefusals' SeLe4n/Model/FreezeProofs.lean
run_check "INVARIANT" rg -n '^@\[simp\] theorem default_declassificationRefusals' SeLe4n/Model/State.lean
run_check "INVARIANT" rg -n '^theorem storeObject_declassificationRefusals_eq' SeLe4n/Model/State.lean
run_check "INVARIANT" rg -n 'declassificationRefusals :$' SeLe4n/Kernel/IPC/Invariant/LookupCongruence.lean
run_check "INVARIANT" rg -n '^theorem applyMachineConfig_declassificationRefusals_eq' SeLe4n/Platform/Boot.lean
run_check "INVARIANT" rg -n '^theorem bootFromPlatform_declassificationRefusals_eq' SeLe4n/Platform/Boot.lean
run_check "INVARIANT" rg -n '^theorem declassificationRefusals_write_preserves_projection' SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean
run_check "INVARIANT" rg -n '^theorem onCore_declassificationRefusals' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean

# SM9.B.10: the reader joins the fused `ReadableStructure` taxonomy — a read
# operation cannot exist without naming a structure, and a structure cannot
# exist without a clause in a TOTAL clause function.
run_check "INVARIANT" rg -n '\| declassificationRefusalLedger' SeLe4n/Kernel/InformationFlow/AuditRead.lean
run_check "INVARIANT" rg -n '\| .declassificationRefusalLedger =>' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
run_check "INVARIANT" rg -n '^inductive RefusalReadField' SeLe4n/Kernel/InformationFlow/AuditRead.lean
run_check "INVARIANT" rg -n '^def refusalTagsWord' SeLe4n/Kernel/InformationFlow/AuditRead.lean
run_check "INVARIANT" rg -n '^theorem refusalTagsWord_roundtrip' SeLe4n/Kernel/InformationFlow/AuditRead.lean
run_check "INVARIANT" rg -n '^theorem refusalTagsWord_reason_is_abi_discriminant' SeLe4n/Kernel/InformationFlow/AuditRead.lean
run_check "INVARIANT" rg -n '^theorem refusalStatusWord_roundtrip' SeLe4n/Kernel/InformationFlow/AuditRead.lean
run_check "INVARIANT" rg -n '^theorem refusalCountersWord_roundtrip' SeLe4n/Kernel/InformationFlow/AuditRead.lean
run_check "INVARIANT" rg -n '^theorem refusalSlotField_reconstructs' SeLe4n/Kernel/InformationFlow/AuditRead.lean
# The gate: full dominance, computed from the CONFIGURATION and never from the
# ring's surviving rows — the ring evicts while the counters are cumulative.
run_check "INVARIANT" rg -n '^theorem refusalLedger_requires_full_dominance' SeLe4n/Kernel/InformationFlow/AuditRead.lean
run_check "INVARIANT" rg -n '^theorem refusalLedger_partial_reader_learns_nothing' SeLe4n/Kernel/InformationFlow/AuditRead.lean
run_check "INVARIANT" rg -n '^theorem refusalLedger_gate_is_configuration_derived' SeLe4n/Kernel/InformationFlow/AuditRead.lean
run_check "INVARIANT" rg -n '^theorem refusalLedger_records_gate_unsound' SeLe4n/Kernel/InformationFlow/AuditRead.lean
run_check "INVARIANT" rg -n '^theorem refusalRead_requires_monitor_at_entry' SeLe4n/Kernel/InformationFlow/AuditRead.lean
# The ABI mirror, both sides.  The count is the decoder's boundary in opcode
# slots, not the number of `AuditReadOp` constructors — several carry an index
# and a chunk — so it is pinned as a number against both sides rather than
# re-derived from the enum.  This is the ONE place it is pinned: a second copy
# added next to a new opcode's anchors is how it last went stale, sitting at 29
# after the Lean side moved to 30.
run_check "INVARIANT" rg -n '^def auditReadOpcodeCount : Nat := 30' SeLe4n/Kernel/InformationFlow/AuditRead.lean
run_check "INVARIANT" rg -n 'AUDIT_READ_OPCODE_COUNT: u64 = 30' rust/sele4n-sys/src/audit.rs
# WS-SM SM9.C.1: and the count is the DECODER's boundary on the Rust side, not
# a restatement of the enum's own last variant — which is what let this mirror
# sit at 21 while Lean moved to 25, invisible to every Rust test.
run_check "INVARIANT" rg -n 'pub const fn from_u64\(v: u64\) -> Option<Self>' rust/sele4n-sys/src/audit.rs
run_check "INVARIANT" rg -n 'fn opcode_density_makes_the_count_meaningful' rust/sele4n-sys/src/audit.rs
run_check "INVARIANT" rg -n 'RefusalStatus = 12' rust/sele4n-sys/src/audit.rs
run_check "INVARIANT" rg -n 'RefusalRequestedTarget = 20' rust/sele4n-sys/src/audit.rs
run_check "INVARIANT" rg -n 'REFUSAL_RING_SIZE: u64 = 32' rust/sele4n-sys/src/audit.rs
run_check "INVARIANT" rg -n 'MAX_REFUSAL_COUNT: u64 = 65535' rust/sele4n-sys/src/audit.rs
run_check "INVARIANT" rg -n 'REFUSAL_TAG_SLOTS: u64 = 256' rust/sele4n-sys/src/audit.rs
run_check "INVARIANT" rg -n 'fn refusal_word_decoders_roundtrip' rust/sele4n-sys/src/audit.rs

# SM9.B.10: the retirement.  `refusalIsUnrecorded`'s statement is now FALSE, so
# the constructor is retired and replaced by the property that survives — and
# the negative forbids its return, in the SM8.E pattern.
run_check "INVARIANT" rg -n 'refusalsAreCountedAndAttributed' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
run_check "INVARIANT" rg -n '^theorem declassificationRefusals_are_counted_and_attributed' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
run_negative_check "INVARIANT" rg -n '\| refusalIsUnrecorded$' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
run_negative_check "INVARIANT" rg -n '^theorem declassification_refusal_is_unrecorded' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
# …and the general congruence now frames EVERY readable structure, so its old
# trail-only name must not come back.
run_check "INVARIANT" rg -n '^theorem auditObservationalEquivalence_of_readableFramed' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
run_negative_check "INVARIANT" rg -n '^theorem auditObservationalEquivalence_of_trailFramed' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
run_check "INVARIANT" rg -n '^theorem recordSyscallRefusal_preserves_auditObservationalEquivalence' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
run_check "INVARIANT" rg -n '^theorem recordSyscallRefusal_perCore_NI' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
# The SM9.A round-7 note, discharged WITH the ledger rather than in a later
# round: the serialization subject is the state-level lock the recording
# syscall's footprint already declares (and the first conjunct is the tripwire
# that forces SM9.C.8's second recording syscall to declare its own), and the
# occupancy owes no ninth channel entry — a theorem, because each of CC-8's
# four carriers is absent here.
run_check "INVARIANT" rg -n '^theorem lockSet_refusalSeam_writer_declares_stateLevel_write' SeLe4n/Kernel/Concurrency/Locks/LockSetTransitions.lean
run_check "INVARIANT" rg -n '^theorem refusalLedger_occupancy_is_not_a_covert_channel' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
run_check "INVARIANT" rg -n '^theorem computeCrossCoreSgis_recordSyscallRefusal_eq' SeLe4n/Kernel/SyscallDispatchEntry.lean
# SM9.B.3: the bundle carriage the mount owes — unconditional, because the
# ledger is bounded by its TYPE and no conjunct reads it.  Without this layer a
# bundle proof for the committed dispatch is blocked exactly where the v0.32.151
# diagnosis says it is (three conjuncts fail `isDefEq` for structural reasons).
run_check "INVARIANT" rg -n '^theorem proofLayerInvariantBundle_setDeclassificationRefusals' SeLe4n/Kernel/Architecture/Invariant.lean
run_check "INVARIANT" rg -n '^theorem recordSyscallRefusal_preserves_proofLayerInvariantBundle' SeLe4n/Platform/FFI.lean
# …and the correction that made it necessary, kept on the record: a
# conjunct-free mounted field still owes a carriage block, so the plan's step 8
# must not drift back to "the 17th conjunct also costs the carriage block".
run_prose_check "INVARIANT" rg -n 'every mounted field owes' docs/planning/SMP_DECLASSIFICATION_COMPLETION_PLAN.md
run_prose_negative_check "INVARIANT" rg -n 'no five-lemma carriage block' SeLe4n/Kernel/InformationFlow/RefusalRecord.lean
run_check "INVARIANT" rg -n 'the accepted-channel inventory stays at eight' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'flooding the ring evicts, but the eviction is COUNTED' tests/SmpInformationFlowSuite.lean

# SM9.B tests: the six runtime groups, their load-bearing negatives, and the
# golden-fixture lines.
run_check "INVARIANT" rg -n '^  runRefusalLedgerChecks' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n '^  runRefusalSeamClassChecks' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n '^  runRefusalSeamWriteChecks' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n '^  runRefusalReaderChecks' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n '^  runRefusalGateChecks' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n '^  runRefusalAcceptanceChecks' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'NEGATIVE: an under-cleared caller reads NOTHING of the ledger' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'NEGATIVE: yet the cumulative counters still carry the hidden attempt' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'NEGATIVE: a hand-maintained list passes vacuously while missing a recording syscall' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'NEGATIVE: a policy-refused caller learns nothing about trail occupancy' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'NEGATIVE: an exempt syscall.s refusal leaves the ledger untouched' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'including a field wide enough to need several chunks' tests/SmpInformationFlowSuite.lean
# Audit cut: the refusal opcodes exercised through the LIVE entry point
# (`auditReadFromCore`), not only through the model reader — the positive at
# the monitor's core, the refusal at a partial reader's core, the unconfigured
# refusal, and the boundary-to-live-read acceptance composition whose
# load-bearing half is that the caller's whole return frame is `errorFrame` of
# the recorded reason.
run_check "INVARIANT" rg -n 'LIVE ENTRY: the monitor.s core reads the refusal status, losslessly' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'NEGATIVE: the live entry refuses a partial reader.s core for every refusal op' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'NEGATIVE: an unconfigured deployment has no refusal reader either' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'END TO END: the committed refusal reads back live' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n '^private def refusalLedgerTraceLines' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'refusal seam: recordingSyscalls=2' tests/fixtures/smp_information_flow.expected
run_check "INVARIANT" rg -n 'refusal write: attempts=1 version=1 trailMoved=false' tests/fixtures/smp_information_flow.expected
run_check "INVARIANT" rg -n 'refusal read .partial.: status=SeLe4n.Model.KernelError.illegalAuthority' tests/fixtures/smp_information_flow.expected
run_check "INVARIANT" rg -n 'audit ABI: auditRead=31 auditDrain=32 syscalls=34 opcodes=30 readableStructures=2' tests/fixtures/smp_information_flow.expected

# ============================================================================
# WS-SM SM9.C — the data-carrying declassification
# (plan SMP_DECLASSIFICATION_COMPLETION_PLAN.md §4 SM9.C.1 … SM9.C.9).
# ============================================================================
#
# SM8.C's `.declassify` authorizes a downgrade and moves no data — its store is
# the model's *simulation* of a transfer.  SM9.C performs the real delivery, and
# is the tree's first deliberately visible flow, so its bound is a write set
# plus a recording obligation rather than an equality of projections.

# SM9.C.1: the transition, in a PRODUCTION module (the live arm calls it, so
# staging it would break the production/staged partition gate).
run_check "INVARIANT" rg -n '^def notificationSignalDeclassifiedOnCore' SeLe4n/Kernel/InformationFlow/DeclassifiedSignal.lean
run_check "INVARIANT" rg -n '^def notificationSignalDeclassifiedCrossCoreDispatch' SeLe4n/Kernel/InformationFlow/DeclassifiedSignal.lean
run_check "INVARIANT" rg -n '^def declassifiedSignalPlan' SeLe4n/Kernel/InformationFlow/DeclassifiedSignal.lean
run_check "INVARIANT" rg -n '^def declassifiedSignalReceiver\?' SeLe4n/Kernel/InformationFlow/DeclassifiedSignal.lean
run_check "INVARIANT" rg -n '^import SeLe4n.Kernel.InformationFlow.DeclassifiedSignal' SeLe4n/Kernel/API.lean
run_negative_check "INVARIANT" rg -n '^SeLe4n\.Kernel\.InformationFlow\.DeclassifiedSignal$' scripts/staged_module_allowlist.txt

# SM9.C.1: the TWO hops, each with its own refusal discriminant.  The injectivity
# is what keeps a monitor able to tell an unauthorized caller from an authorized
# caller aimed at an unauthorized sink — the two call for opposite responses.
run_check "INVARIANT" rg -n '^inductive DeclassifiedSignalHop' SeLe4n/Kernel/InformationFlow/DeclassifiedSignal.lean
run_check "INVARIANT" rg -n '^def DeclassifiedSignalHop.refusal' SeLe4n/Kernel/InformationFlow/DeclassifiedSignal.lean
run_check "INVARIANT" rg -n '^theorem DeclassifiedSignalHop.refusal_injective' SeLe4n/Kernel/InformationFlow/DeclassifiedSignal.lean
run_check "INVARIANT" rg -n '^  \| declassificationDeniedAtReceiver' SeLe4n/Model/KernelError.lean
run_check "INVARIANT" rg -n 'declassificationDeniedAtReceiver *=> 56' SeLe4n/Kernel/Architecture/SyscallReturn.lean
# NEGATIVE: the second hop must not collapse onto the first's discriminant —
# that is exactly the information a refusal ledger exists to preserve.
run_negative_check "INVARIANT" rg -n 'notificationToReceiver => \.declassificationDenied$' SeLe4n/Kernel/InformationFlow/DeclassifiedSignal.lean

# SM9.C.1: the headline properties.  The badge really crosses; the resolved
# receiver is gated; every authorized downgrade is recorded; and no entry names
# an edge no policy authorized (which a single record for a two-hop delivery
# could not have said).
run_check "INVARIANT" rg -n '^theorem declassifiedSignal_delivers_badge' SeLe4n/Kernel/InformationFlow/DeclassifiedSignal.lean
run_check "INVARIANT" rg -n '^theorem declassifiedSignal_gates_resolved_receiver' SeLe4n/Kernel/InformationFlow/DeclassifiedSignal.lean
run_check "INVARIANT" rg -n '^theorem declassifiedSignal_never_unaudited' SeLe4n/Kernel/InformationFlow/DeclassifiedSignal.lean
run_check "INVARIANT" rg -n '^theorem declassifiedSignal_no_invented_edge' SeLe4n/Kernel/InformationFlow/DeclassifiedSignal.lean
run_check "INVARIANT" rg -n '^theorem declassifiedSignal_audits_each_hop' SeLe4n/Kernel/InformationFlow/DeclassifiedSignal.lean
run_check "INVARIANT" rg -n '^theorem declassifiedSignal_audits_actual_destination' SeLe4n/Kernel/InformationFlow/DeclassifiedSignal.lean
run_check "INVARIANT" rg -n '^theorem declassifiedSignal_ordinary_eq_signal' SeLe4n/Kernel/InformationFlow/DeclassifiedSignal.lean
run_check "INVARIANT" rg -n '^theorem declassifiedSignal_denied_before_capacity' SeLe4n/Kernel/InformationFlow/DeclassifiedSignal.lean
# The unconfigured deployment: NOT "the syscall fails" — a hop the base lattice
# already permits is an ordinary signal — but "no downgrade happens", which is
# the security claim the weaker phrasing would be mistaken for.
run_check "INVARIANT" rg -n '^theorem declassifiedSignal_default_policy_never_downgrades' SeLe4n/Kernel/InformationFlow/DeclassifiedSignal.lean
run_check "INVARIANT" rg -n '^theorem declassifiedSignal_default_policy_eq_signal' SeLe4n/Kernel/InformationFlow/DeclassifiedSignal.lean

# SM9.C.1: the ACTOR — a two-hop delivery's second event has a source domain
# that is nobody's subject domain, so attributability cannot read `srcDomain`.
run_check "INVARIANT" rg -n '^structure DeclassificationActor' SeLe4n/Kernel/InformationFlow/AuditRecord.lean
run_check "INVARIANT" rg -n '^  actor : DeclassificationActor' SeLe4n/Kernel/InformationFlow/AuditRecord.lean
run_check "INVARIANT" rg -n '^theorem attributionFromRunningSubject_over_actor' SeLe4n/Kernel/InformationFlow/DeclassifiedSignal.lean
run_check "INVARIANT" rg -n '^theorem secondHop_actor_differs_from_flowSource' SeLe4n/Kernel/InformationFlow/DeclassifiedSignal.lean
run_check "INVARIANT" rg -n '^theorem secondHopEvent_names_firstHop' SeLe4n/Kernel/InformationFlow/DeclassifiedSignal.lean
# NEGATIVE: the actor field must stay REQUIRED — a default would attribute every
# event to whatever it names while compiling everywhere.
run_negative_check "INVARIANT" rg -n '^  actor : DeclassificationActor :=' SeLe4n/Kernel/InformationFlow/AuditRecord.lean
# The visibility filter reads every disclosed domain, the actor's included.
run_check "INVARIANT" rg -n 'ctx.policy.canFlow e.actor.domain reader' SeLe4n/Kernel/InformationFlow/AuditRead.lean
run_check "INVARIANT" rg -n '^theorem auditLogVisibleTo_cleared_actor' SeLe4n/Kernel/InformationFlow/AuditRead.lean
# NEGATIVE: the retired trail invariant.  A two-hop delivery's second event has
# a *thread* domain as its destination while its target is a TCB, so
# `auditTrailDestinationsAreTargetDomains` is FALSE of it; the object-identity
# discipline moved into the filter itself, which is strictly stronger.
run_negative_check "INVARIANT" rg -n 'auditTrailDestinationsAreTargetDomains' SeLe4n/Kernel/InformationFlow/AuditRead.lean

# SM9.C.3 / SM9.C.4: the invariant surface the delivery inherits, transferred
# through the frame (post-state = SM6.B's with one field replaced).
run_check "INVARIANT" rg -n '^theorem notificationSignalDeclassifiedOnCore_frame' SeLe4n/Kernel/InformationFlow/DeclassifiedSignal.lean
run_check "INVARIANT" rg -n '^theorem notificationSignalDeclassifiedOnCore_preserves_proofLayerInvariantBundle' SeLe4n/Kernel/InformationFlow/DeclassifiedSignal.lean
run_check "INVARIANT" rg -n '^theorem notificationSignalDeclassifiedOnCore_preserves_auditLogBounded' SeLe4n/Kernel/InformationFlow/DeclassifiedSignal.lean
run_check "INVARIANT" rg -n '^theorem notificationSignalDeclassifiedOnCore_preserves_ipcInvariant' SeLe4n/Kernel/InformationFlow/DeclassifiedSignal.lean
run_check "INVARIANT" rg -n '^theorem notificationSignalDeclassifiedOnCore_ipcInvariantFull_transfer' SeLe4n/Kernel/InformationFlow/DeclassifiedSignal.lean
run_check "INVARIANT" rg -n '^theorem notificationSignalDeclassifiedOnCore_ipcInvariantFull_perCore_transfer' SeLe4n/Kernel/InformationFlow/DeclassifiedSignal.lean
run_check "INVARIANT" rg -n '^theorem notificationSignalDeclassifiedOnCore_preserves_trailActors' SeLe4n/Kernel/InformationFlow/DeclassifiedSignal.lean

# SM9.C.5 / SM9.C.6: the effect footprint, defined ONCE and read by both the
# non-interference theorem and the confinement proof, and the non-implication
# that keeps it from being mistaken for a permission.
run_check "INVARIANT" rg -n '^structure DeclassificationEffectFootprint' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_check "INVARIANT" rg -n '^def declassifiedSignalEffectFootprint' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_check "INVARIANT" rg -n '^theorem footprint_does_not_authorize' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_check "INVARIANT" rg -n '^theorem notificationSignalDeclassifiedOnCore_confinedToCores' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_check "INVARIANT" rg -n '^theorem declassificationRelativeNonInterference' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_check "INVARIANT" rg -n '^theorem declassifiedSignalDispatch_confinedToCores' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_check "INVARIANT" rg -n '^theorem declassifiedSignalDispatch_crossCoreNonInterference' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
# The footprint's cores ARE SM6.B's write set — one definition, not two that can
# drift (the failure mode v0.32.101 and v0.33.16 both caught).
run_check "INVARIANT" rg -n 'cores := notificationSignalBoundWriteSet st notificationId' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
# NEGATIVE: the footprint must take no policy — that is what makes
# `footprint_does_not_authorize` provable rather than merely plausible.
run_negative_check "INVARIANT" rg -n 'def declassifiedSignalEffectFootprint.*DeclassificationPolicy' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean

# SM9.C.7: the taxonomy `KernelOperation` deliberately does NOT grow.  Every
# `NonInterferenceStep` constructor concludes the projection is *unchanged*, so
# an operation whose purpose is an authorized visible flow cannot correspond to
# one; both declassifying operations live in `CrossCoreTransition` instead.
run_prose_check "INVARIANT" rg -n 'What this taxonomy deliberately does not hold' SeLe4n/Kernel/InformationFlow/Invariant/Composition.lean
run_check "INVARIANT" rg -n '^theorem kernelOperation_count : KernelOperation.all.length = 35' SeLe4n/Kernel/InformationFlow/Invariant/Composition.lean
run_negative_check "INVARIANT" rg -n 'declassifiedSignal' SeLe4n/Kernel/InformationFlow/Invariant/Composition.lean

# SM9.C.8: the syscall, both Rust mirrors and the seam classification the total
# `refusalSeamClass` forced it to supply.
run_check "INVARIANT" rg -n '^  \| declassifySignal' SeLe4n/Model/Object/Types.lean
run_check "INVARIANT" rg -n 'def count : Nat := 34' SeLe4n/Model/Object/Types.lean
run_check "INVARIANT" rg -n 'DeclassifySignal = 33' rust/sele4n-types/src/syscall.rs
run_check "INVARIANT" rg -n 'DeclassifySignal = 33' rust/sele4n-hal/src/svc_dispatch.rs
run_check "INVARIANT" rg -n 'DeclassificationDeniedAtReceiver = 56' rust/sele4n-types/src/error.rs
run_check "INVARIANT" rg -n '^pub fn declassify_signal' rust/sele4n-sys/src/declassify.rs
run_check "INVARIANT" rg -n 'assert_clears\("declassify_signal", SyscallId::DeclassifySignal\)' rust/sele4n-abi/tests/conformance.rs
run_check "INVARIANT" rg -n '\| \.declassify \| \.declassifySignal => \.records' SeLe4n/Kernel/InformationFlow/RefusalRecord.lean
run_check "INVARIANT" rg -n '^theorem refusalSeamClass_records_count' SeLe4n/Kernel/InformationFlow/RefusalRecord.lean

# SM9.C.8: the lock set — the ordinary signal's, PLUS the state-level write its
# trail append needs.  Composed rather than rewritten, so the notification half
# cannot drift from the syscall it wraps.
run_check "INVARIANT" rg -n '^def lockSet_declassifySignal' SeLe4n/Kernel/Concurrency/Locks/LockSetTransitions.lean
run_check "INVARIANT" rg -n '^theorem lockSet_declassifySignal_stateLevel_write_mem' SeLe4n/Kernel/Concurrency/Locks/LockSetTransitions.lean
run_check "INVARIANT" rg -n '^theorem lockSet_declassifySignal_extends_notificationSignal' SeLe4n/Kernel/Concurrency/Locks/LockSetTransitions.lean
run_check "INVARIANT" rg -n '^theorem lockSet_consistent_declassifySignal' SeLe4n/Kernel/Concurrency/Locks/LockSetTransitions.lean
run_check "INVARIANT" rg -n '^theorem lockSet_declassifySignal_size_le' SeLe4n/Kernel/Concurrency/Locks/Deadlock.lean
run_check "INVARIANT" rg -n 'lockSet_declassifySignal a b c d e f' SeLe4n/Kernel/Concurrency/Locks/Deadlock.lean
run_check "INVARIANT" rg -n 'sid = \.declassify ∨ sid = \.declassifySignal' SeLe4n/Kernel/Concurrency/Locks/LockSetTransitions.lean
# NEGATIVE: the footprint must be composed, not a fresh list — a rewritten one
# stops tracking `lockSet_notificationSignal` the moment SM6.B's changes.
run_negative_check "INVARIANT" rg -Un 'def lockSet_declassifySignal(.*\n){1,8}.*lockSetOfList' SeLe4n/Kernel/Concurrency/Locks/LockSetTransitions.lean

# SM9.C.9: the arm is tied to the dispatch by a THEOREM, and the per-core
# routing gate passes with zero allowlisted exceptions.
run_check "INVARIANT" rg -n '^theorem dispatchWithCapChecked_declassifySignal_delegates' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n '^theorem dispatchWithCap_declassifySignal_denied' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n '^theorem dispatchWithCapChecked_declassifySignal_default_no_downgrade' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n '^theorem syscallDelegates_declassifySignal' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n '\| declassifySignalDispatch' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_check "INVARIANT" rg -n 'notificationSignalDeclassifiedCrossCoreDispatch#inert' scripts/per_core_routing_aliases.json
run_check "INVARIANT" rg -n 'policyGated "notificationSignalDeclassifiedCrossCoreDispatch"' SeLe4n/Kernel/InformationFlow/Enforcement/Wrappers.lean
# NEGATIVE: it must NOT be classified capability-only — that would say the
# notification capability alone authorizes the downgrade, which it does not.
run_negative_check "INVARIANT" rg -n 'capabilityOnly "notificationSignalDeclassifiedCrossCoreDispatch"' SeLe4n/Kernel/InformationFlow/Enforcement/Wrappers.lean

# SM9.C tests: the six runtime groups, their load-bearing negatives, and the
# golden-fixture lines.
run_check "INVARIANT" rg -n '^  runDeclassifiedSignalHopChecks' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n '^  runDeclassifiedSignalReceiverGateChecks' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n '^  runDeclassifiedSignalDeliveryChecks' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n '^  runDeclassifiedSignalRelativeNiChecks' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n '^  runDeclassifiedSignalDefaultChecks' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n '^  runDeclassifiedSignalAbiChecks' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'NEGATIVE: the second event.s SOURCE is not its actor.s domain' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'NEGATIVE: no recorded event names the composite 2 . 0 the policy withholds' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'NEGATIVE: the refused receiver IS in the effect footprint' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'NEGATIVE: with no receiver there is no second hop' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'NEGATIVE: this is NOT plain non-interference' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'NEGATIVE: an unrecorded downgrade is refutable' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'NEGATIVE: an idle core cannot declassify' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'NEGATIVE: it does not share the ordinary signal.s boundary entry' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n '^private def declassifiedSignalTraceLines' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'declassifying signal: hops=2 actorDomain=2 notificationDomain=1 receiverDomain=0' tests/fixtures/smp_information_flow.expected
run_check "INVARIANT" rg -n 'declassifying signal footprint: notification=1016 receiver=1021 cores=\[2\]' tests/fixtures/smp_information_flow.expected
run_check "INVARIANT" rg -n 'declassifying signal run: ok records=2' tests/fixtures/smp_information_flow.expected
run_check "INVARIANT" rg -n 'declassifying signal ABI: id=33' tests/fixtures/smp_information_flow.expected

# WS-SM SM9.C.1 (audit cut) — the failed hop reaches the monitor.  The refusal
# record names the resolved receiver of a refused second hop, the seam
# re-resolves it from the pre-state (the "seam cannot see it" premise the
# SM9.B landing recorded was wrong — the seam holds the pre-state and x0), a
# theorem pins the two resolutions equal, and the monitor reads the field back
# through its own opcode pair.
run_check "INVARIANT" rg -n 'refusedReceiver : Option SeLe4n.ThreadId' SeLe4n/Kernel/InformationFlow/RefusalRecord.lean
run_check "INVARIANT" rg -n '^def refusedSignalReceiver\?' SeLe4n/Platform/FFI.lean
run_check "INVARIANT" rg -n '^theorem refusedSignalReceiver\?_resolves' SeLe4n/Platform/FFI.lean
run_check "INVARIANT" rg -n '^def refusalReceiverFor' SeLe4n/Platform/FFI.lean
run_check "INVARIANT" rg -n '^theorem refusalReceiverFor_other' SeLe4n/Platform/FFI.lean
run_check "INVARIANT" rg -n '^theorem refusalRecord_names_failed_hop' SeLe4n/Platform/FFI.lean
run_check "INVARIANT" rg -n '^theorem declassifiedSignalPlan_deniedAtReceiver_resolves' SeLe4n/Kernel/InformationFlow/DeclassifiedSignal.lean
run_check "INVARIANT" rg -n '^theorem declassifiedSignalHopAuthorization_error_refusal' SeLe4n/Kernel/InformationFlow/DeclassifiedSignal.lean
run_check "INVARIANT" rg -n 'refusalReceiverChunkCount \(slot : Nat\)' SeLe4n/Kernel/InformationFlow/AuditRead.lean
run_check "INVARIANT" rg -n 'RefusalReceiverChunks = 25' rust/sele4n-sys/src/audit.rs
run_check "INVARIANT" rg -n 'RefusalReceiver = 26' rust/sele4n-sys/src/audit.rs
run_check "INVARIANT" rg -n 'a refused second hop names the resolved receiver' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'NEGATIVE: a first-hop refusal records no receiver' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'NEGATIVE: the discriminant alone does not trigger the resolution' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'declassifying signal failed hop: reason=56 recordedReceiver=1021' tests/fixtures/smp_information_flow.expected
# The record-level fill is keyed on BOTH coordinates — a reason-only key would
# run the notification resolver against a future syscall's unrelated operand.
run_check "INVARIANT" rg -n 'sid = SyscallId.declassifySignal ∧ ke = KernelError.declassificationDeniedAtReceiver' SeLe4n/Platform/FFI.lean
# The SM8.E defect class stays closed: the thirteenth policy-gated entry's
# members of BOTH enforcement families exist.
run_check "INVARIANT" rg -n '^theorem enforcement_sufficiency_declassifySignal' SeLe4n/Kernel/InformationFlow/DeclassifiedSignal.lean
run_check "INVARIANT" rg -n '^theorem notificationSignalDeclassifiedOnCore_denied_preserves_state' SeLe4n/Kernel/InformationFlow/DeclassifiedSignal.lean
# The retired deferral premise must not return: the record's docstring no
# longer claims the seam cannot see the resolved receiver.
run_prose_negative_check "INVARIANT" rg -n 'so the seam cannot see it; .which. hop failed can ride' SeLe4n/Kernel/InformationFlow/RefusalRecord.lean

# WS-SM SM9.C (PR #872 review) — the plain-waiter gate.  Deliberately
# asymmetric with the ordinary checked signal (which gates the receiver on the
# bound path only and trusts wait-time admission): provably a no-op on
# checked-admitted waiters, and its one-bit refusal disclosure exhibited as a
# theorem rather than hidden.
run_check "INVARIANT" rg -n '^theorem declassifiedSignalPlan_admitted_receiver_error_is_first_hop' SeLe4n/Kernel/InformationFlow/DeclassifiedSignal.lean
run_check "INVARIANT" rg -n '^theorem declassifiedSignalPlan_outcome_depends_on_receiver' SeLe4n/Kernel/InformationFlow/DeclassifiedSignal.lean
run_check "INVARIANT" rg -n 'a checked-admitted plain waiter never triggers the receiver refusal' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'DISCLOSURE: refusal-vs-success reveals the denied plain waiter' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'NEGATIVE: the symmetric alternative delivers the badge to the denied receiver' tests/SmpInformationFlowSuite.lean

# WS-SM SM9.C (PR #872 review, round 2) — the target gate: the operand must be
# a live notification BEFORE any policy is consulted (the sibling
# `.declassify` discipline), so an invalid capability is never a policy
# oracle; wrong-kind/absent answer the ordinary signal's own errors.
run_check "INVARIANT" rg -n '^theorem notificationSignalDeclassifiedOnCore_wrong_kind' SeLe4n/Kernel/InformationFlow/DeclassifiedSignal.lean
run_check "INVARIANT" rg -n '^theorem notificationSignalDeclassifiedOnCore_absent_target' SeLe4n/Kernel/InformationFlow/DeclassifiedSignal.lean
run_check "INVARIANT" rg -n '^theorem notificationSignalDeclassifiedOnCore_invalid_target_policy_blind' SeLe4n/Kernel/InformationFlow/DeclassifiedSignal.lean
run_check "INVARIANT" rg -n '^theorem declassifiedSignalReceiver\?_some_notification' SeLe4n/Kernel/InformationFlow/DeclassifiedSignal.lean
run_check "INVARIANT" rg -n 'a wrong-kind target answers invalidCapability under every policy' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'NEGATIVE: a wrong-kind target no longer reports the caller' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'an absent target answers objectNotFound, policy-blind' tests/SmpInformationFlowSuite.lean
# The gate lives in the transition, ahead of the plan — pin the match order.
run_check "INVARIANT" rg -n 'match st.getNotification\? notificationId with' SeLe4n/Kernel/InformationFlow/DeclassifiedSignal.lean

# ============================================================================
# WS-SM SM9.D — causal declassification provenance
# (plan SMP_DECLASSIFICATION_COMPLETION_PLAN.md §5 SM9.D.1 … SM9.D.18).
# ============================================================================
# SM8's laundering detector was SYNTACTIC: it matched domains, so it fired on
# causally unrelated hops and — scoped to declassification *edges* — missed the
# real chain, in which an ORDINARY delivery moves the content between two
# downgrades.  SM9.D replaces domain matching with recorded provenance.

# SM9.D.1: the taint value, in a PRODUCTION leaf below `AuditRecord.lean` (the
# audit event carries one, and that module sits below `Model/State.lean`).
run_check "INVARIANT" rg -n '^structure DeclassificationTaint where' SeLe4n/Kernel/InformationFlow/Taint.lean
run_check "INVARIANT" rg -n '^def maxTaintTags : Nat := 8' SeLe4n/Kernel/InformationFlow/Taint.lean
# The bound is a REFINEMENT FIELD, so it holds of every value rather than only
# of recorded ones — which is why there is no seventeenth
# `proofLayerInvariantBundle` conjunct (the shape SM9.B's ledger established).
run_check "INVARIANT" rg -n 'tags_bounded : tags.length ≤ maxTaintTags' SeLe4n/Kernel/InformationFlow/Taint.lean
run_check "INVARIANT" rg -n '^theorem taint_bounded_structurally' SeLe4n/Kernel/InformationFlow/Taint.lean
# Overflow saturates UPWARD: for a detector, over-approximation is the safe
# direction — losing a real link is what must not happen.
run_check "INVARIANT" rg -n '^theorem taintSaturate_over_approximates' SeLe4n/Kernel/InformationFlow/Taint.lean
run_check "INVARIANT" rg -n '^theorem join_saturated_covers_all' SeLe4n/Kernel/InformationFlow/Taint.lean
# The side table is a KEYED association list under a total lookup, not an
# `RHTable`: a hash table's lookup-after-insert law needs `invExt`, which would
# force the bundle conjunct this design avoids.  The canonical form — at most one
# row per object, none empty-valued — is a FIELD, so the length claim holds of
# every value of the type rather than only of the ones the API builds.
#
# This pin replaced one requiring the old `abbrev TaintTable := ObjId → …`, which
# sat here contradicting the negative check below (added with the keyed cut) —
# the two could not both pass, so the tier failed until one was corrected.
run_check "INVARIANT" rg -n '^structure TaintTable where' SeLe4n/Kernel/InformationFlow/Taint.lean
run_check "INVARIANT" rg -n '^  canonical : TaintEntries\.Canonical entries' SeLe4n/Kernel/InformationFlow/Taint.lean
run_check "INVARIANT" rg -n '^theorem TaintEntries\.canonical_erase' SeLe4n/Kernel/InformationFlow/Taint.lean
run_check "INVARIANT" rg -n '^theorem entries_live' SeLe4n/Kernel/InformationFlow/Taint.lean

# SM9.D.2 – SM9.D.6: the §6 `SystemState` mount checklist, run for the fourth
# time.  The frozen field is REQUIRED (a silent drop is a compile error) and the
# bundle carriage is unconditional (v0.32.151: three conjuncts do not transport
# by `rfl` across an arbitrary field write).
run_check "INVARIANT" rg -n 'declassificationTaint : SeLe4n.Kernel.TaintTable' SeLe4n/Model/State.lean
run_check "INVARIANT" rg -n 'declassificationTaint : SeLe4n.Kernel.TaintTable' SeLe4n/Model/FrozenState.lean
run_check "INVARIANT" rg -n '^theorem freeze_preserves_declassificationTaint' SeLe4n/Model/FrozenState.lean
run_check "INVARIANT" rg -n '^theorem storeObject_declassificationTaint_eq' SeLe4n/Model/State.lean
run_check "INVARIANT" rg -n '^theorem bootFromPlatform_declassificationTaint_eq' SeLe4n/Platform/Boot.lean
run_check "INVARIANT" rg -n 'declassificationTaint :$' SeLe4n/Kernel/IPC/Invariant/LookupCongruence.lean
run_check "INVARIANT" rg -n '^theorem proofLayerInvariantBundle_setDeclassificationTaint' SeLe4n/Kernel/Architecture/Invariant.lean
# Information flow: the table is OUTSIDE `ObservableState`.  Provenance names
# `(object, declassification identity)` pairs, so projecting it would be a
# content channel out of exactly the boundary the audit polices.
run_check "INVARIANT" rg -n '^theorem declassificationTaint_write_preserves_projection' SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean
run_check "INVARIANT" rg -n '^theorem onCore_declassificationTaint' SeLe4n/Kernel/InformationFlow/ObservableStatePerCore.lean

# SM9.D.13a: the recorded snapshot on the audit event.  UNDEFAULTED, because a
# default would attribute an empty history to every event while compiling
# everywhere; and the tags are GLOBAL identities, so the field is read by the
# detector and never exported through SM9.A's chunk protocol.
run_check "INVARIANT" rg -n 'predecessorTags : DeclassificationTaint' SeLe4n/Kernel/InformationFlow/AuditRecord.lean
run_check "INVARIANT" rg -n '^def declassificationEventNames' SeLe4n/Kernel/InformationFlow/AuditRecord.lean
run_check "INVARIANT" rg -n '^abbrev declassificationActorTaint' SeLe4n/Kernel/InformationFlow/Declassification.lean
run_check "INVARIANT" rg -n '^abbrev declassifyStoreEventWithTags' SeLe4n/Kernel/InformationFlow/Declassification.lean
# The multi-hop recorder threads the snapshot, so hop 2 names hop 1 within one
# transition — the property `recordDeclassifiedHops_two` now carries.
run_check "INVARIANT" rg -n '^def recordDeclassifiedHopsFrom' SeLe4n/Kernel/InformationFlow/DeclassifiedSignal.lean
run_check "INVARIANT" rg -n 'declassificationEventNames e₂ e₁ = true' SeLe4n/Kernel/InformationFlow/DeclassifiedSignal.lean

# SM9.D.7 – SM9.D.11: the propagation sites, as DATA with a total
# classification.  Totality over `SyscallId` is necessary and not sufficient —
# a new syscall must add an arm, but the arm can be wrong — so the
# COMPLETENESS of the classification is a Tier-1 reach gate over the call
# graph, not a theorem.
run_check "INVARIANT" rg -n '^inductive ContentFlowClass where' SeLe4n/Kernel/InformationFlow/TaintPropagation.lean
run_check "INVARIANT" rg -n '^def contentFlowClass : SyscallId → ContentFlowClass' SeLe4n/Kernel/InformationFlow/TaintPropagation.lean
run_check "INVARIANT" rg -n '^theorem contentFlowClass_total' SeLe4n/Kernel/InformationFlow/TaintPropagation.lean
# NEGATIVE: the classification must stay wildcard-free (same anchor shape as
# the seam's — `contentFlowClass_total` is ∃-shaped and holds of a wildcarded
# function too, so only this pins the mechanism).
run_negative_check "INVARIANT" rg -Un 'def contentFlowClass : SyscallId → ContentFlowClass[^\n]*\n((  \|[^\n]*| *)\n)*  \|\s*_' SeLe4n/Kernel/InformationFlow/TaintPropagation.lean
# NEGATIVE: the PLANNERS are wildcard-free over `SyscallId` too — the
# classification alone forces a class decision, but before this pin the edge,
# clear and bypass planners each ended in `| _, _ => []`, so a ninth
# `.movesContent` syscall would have elaborated and run with an empty edge
# plan: content moving with no provenance following it, the one direction the
# module must never err in.  The planners now match every syscall explicitly
# (per-arm wrong-shape fallbacks stay), so no two-discriminant wildcard may
# return anywhere in the module.
run_negative_check "INVARIANT" rg -n '\|\s*_\s*,\s*_\s*=>' SeLe4n/Kernel/InformationFlow/TaintPropagation.lean
# NEGATIVE (PR #877 review): nor the UNARY respelling of the same hole.  The
# restructure split the pair match into nested matches, so `| _ => []` written
# at the *syscall* level of any planner elaborates exactly as the pair
# wildcard did — and the pair anchor above cannot see it.  Indentation is the
# scope: every legitimate wildcard in this module is a capability-shape or
# argument-shape fallback nested at 8+ spaces, while def-level and
# syscall-level arms sit at 2–6 — so a shallow unary wildcard anywhere in the
# module is a planner (or future helper) declining its per-syscall decision,
# and there is deliberately no allowlisted instance.
run_negative_check "INVARIANT" rg -n '^ {0,6}\| *_' SeLe4n/Kernel/InformationFlow/TaintPropagation.lean
run_check "INVARIANT" rg -n '^DECLARED_TAINT_WRITERS = ' scripts/check_content_flow_coverage.py
run_check "INVARIANT" rg -n '^CONTENT_CHANNELS = ' scripts/check_content_flow_coverage.py
run_check "BUILD" rg -n 'check_content_flow_coverage.py' scripts/test_tier1_build.sh
run_check "BUILD" rg -n 'check_content_flow_coverage.py. --self-test' scripts/test_tier1_build.sh
# Taint follows CONTENT, so it propagates through ordinary IPC delivery — the
# hop the SM8 edge-scoped design could not see.
#
# The two endpoint-keyed forms are deliberately ABSENT and pinned as such below:
# an endpoint holds no content of its own, so it is not a taint sink and not a
# taint source.  Their replacements are the content-derived pair — the sender
# reaches the rendezvous receiver, and a receiver reads the blocked sender at
# `sendQ.head` directly.  Keeping a positive anchor on a deleted theorem beside
# the negative that forbids it makes the tier unsatisfiable, which is how this
# pair was found.
run_check "INVARIANT" rg -n '^theorem taintPropagation_send_to_receiver' SeLe4n/Kernel/InformationFlow/TaintPropagation.lean
run_check "INVARIANT" rg -n '^theorem taintPropagation_receive_from_sender' SeLe4n/Kernel/InformationFlow/TaintPropagation.lean
run_check "INVARIANT" rg -n '^theorem taintPropagation_reply_to_caller' SeLe4n/Kernel/InformationFlow/TaintPropagation.lean
run_check "INVARIANT" rg -n '^theorem taintPropagation_signal_to_notification' SeLe4n/Kernel/InformationFlow/TaintPropagation.lean
run_check "INVARIANT" rg -n '^theorem taintPropagation_wait_from_notification' SeLe4n/Kernel/InformationFlow/TaintPropagation.lean
run_check "INVARIANT" rg -n '^theorem taintOrigination_target' SeLe4n/Kernel/InformationFlow/TaintPropagation.lean
run_check "INVARIANT" rg -n '^theorem taintOrigination_actor' SeLe4n/Kernel/InformationFlow/TaintPropagation.lean
# The diff recovery is characterised in both directions: a pure append IS the
# appended suffix, and a commit that advanced the epoch (the drain) originates
# nothing — so "recovered from the trail's own diff" is checked, not read off
# `drop`'s behaviour on a shortened list.
run_check "INVARIANT" rg -n '^theorem newlyRecordedEvents_append' SeLe4n/Kernel/InformationFlow/TaintPropagation.lean
run_check "INVARIANT" rg -n '^theorem newlyRecordedEvents_drained' SeLe4n/Kernel/InformationFlow/TaintPropagation.lean
# SM9.D.12: the retype CLEARS rather than frames — it commits `storeObject` at
# the same id, so a framed retype would leave a destroyed object's tags on its
# replacement.  The two imprecisions must not be conflated.
run_check "INVARIANT" rg -n '^theorem retypeClearsTaint' SeLe4n/Kernel/InformationFlow/TaintPropagation.lean
run_check "INVARIANT" rg -n '^theorem retypedObject_taint_empty' SeLe4n/Kernel/InformationFlow/TaintPropagation.lean
run_check "INVARIANT" rg -n '^theorem staleTaint_is_not_saturation' SeLe4n/Kernel/InformationFlow/TaintPropagation.lean
# The live write sites: BOTH dispatchers, applied to the state each was given.
# PR #873 round 6 moved the seam down from the two entries, because
# `dispatchSyscall`'s docstring points integrators at `dispatchSyscallChecked`
# for production entry and a seam above it was one an integrator never reached.
run_check "INVARIANT" rg -n 'applySyscallTaint' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n '^theorem dispatchSyscallChecked_applies_taint_plan' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n '^theorem dispatchSyscall_applies_taint_plan' SeLe4n/Kernel/API.lean
# That the entries do NOT re-apply it is enforced where it can be enforced
# exactly: `DECLARED_TAINT_CONSUMERS` in the Tier-1 content-flow gate names the
# two dispatchers and fails on any other constant that reaches the taint API, so
# a second application at an entry is a build failure rather than a text pin.
run_check "INVARIANT" rg -n 'SeLe4n.Kernel.dispatchSyscallChecked' scripts/check_content_flow_coverage.py

# PR #873 round 6: relying on declared footprints as a complete serialization
# discipline is GATED on the uncovered-domain inventory being empty, so the
# per-key taint store (and every other registered domain) is a precondition of
# SM3.C.9's fine locks rather than work that may land alongside them.
run_check "INVARIANT" rg -n '^def fineLockDisciplineComplete' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^theorem fineLockDisciplineComplete_is_false' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^theorem fineLockDiscipline_requires_every_domain_covered' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^theorem taintPerKeyStore_blocks_fineLockDiscipline' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean

# PR #873 round 6: **a queued capability transfer installs, like a rendezvous
# one.**  The `.receive` arm ran the bare per-core receive, which delivers a
# parked sender's message wholesale and installs none of the capabilities it
# carries, while an immediate rendezvous transferred them — so IPC semantics
# depended on which side reached the endpoint first.  The authority is the
# SENDER's, carried on the message (`capsGranted`), because the sender's endpoint
# capability is gone by the time a receiver dequeues a parked send.
run_check "INVARIANT" rg -n '  capsGranted : Bool' SeLe4n/Model/Object/Types.lean
run_check "INVARIANT" rg -n '^def endpointReceiveDualWithCapsOnCore' SeLe4n/Kernel/IPC/CrossCore/EndpointReply.lean
run_check "INVARIANT" rg -n '^theorem endpointReceiveDualWithCapsOnCore_no_caps' SeLe4n/Kernel/IPC/CrossCore/EndpointReply.lean
run_check "INVARIANT" rg -n 'endpointReceiveDualWithCapsOnCore epId tid replyIdOpt' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n 'capsGranted := cap.rights.mem .grant' SeLe4n/Kernel/API.lean
# The enforcement inventory names the operation the arm REACHES, so it moved with
# the reroute — and the bare transition must not come back as the classified arm.
run_check "INVARIANT" rg -n 'policyGated "endpointReceiveDualWithCapsOnCore"' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
run_negative_check "INVARIANT" rg -n 'policyGated "endpointReceiveDualOnCore"' SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean
# The receive-side grant gate is the message's, not the receiver's endpoint
# rights: consulting the receiver's is a different principal's authority and left
# the orderings disagreeing when a granting sender met a non-granting receiver.
run_check "INVARIANT" rg -n 'receiverSlotBase msg.capsGranted' SeLe4n/Kernel/IPC/DualQueue/WithCaps.lean
run_negative_check "INVARIANT" rg -n 'endpointReceiveDualWithCaps endpointId receiver replyId endpointRights' SeLe4n/Kernel/IPC/DualQueue/WithCaps.lean
# The regression that measures the property rather than one ordering's outcome.
run_check "INVARIANT" rg -n 'ipcCapTransferArrivalOrder' tests/OperationChainSuite.lean

# PR #873 round 7: **and the same for `.replyRecv`**, the arm that is a receive
# without being spelled `.receive`.  Its receive leg ran inside `replyRecvBody`
# on the BARE per-core transition, so an seL4-MCS server loop (`Recv` once, then
# `ReplyRecv` forever) received capabilities on its first request and silently
# none afterwards.  The body now takes the receiver's CSpace root and receive
# slot and RETURNS the transfer summary, so `extraCaps` is the installed count.
run_check "INVARIANT" rg -n 'endpointReceiveDualWithCapsOnCore epId tid \(some rid\)' SeLe4n/Kernel/API.lean
run_negative_check "INVARIANT" rg -n 'endpointReceiveDualOnCore epId tid \(some rid\)' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n 'replyRecvBody epId tid rid prevCaller msg gate.cspaceRoot' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n 'replyRecvCapTransferArrivalOrder' tests/OperationChainSuite.lean

# PR #873 round 8 (SECURITY): **a receive that dequeued nothing installs
# nothing.**  The blocking branch returns the receiver's OWN id and leaves
# `pendingMessage` untouched, so deciding by that field alone re-unwrapped a
# message the receiver had held since its last receive — an extra copy of
# authority minted with no sender.  The gate is the endpoint's pre-state send
# queue, which is what the bare transition itself branches on.
run_check "INVARIANT" rg -n '^def receiveRendezvousSender\?' SeLe4n/Kernel/IPC/DualQueue/Transport.lean
run_check "INVARIANT" rg -n '^def receiveInstallsCaps' SeLe4n/Kernel/IPC/DualQueue/Transport.lean
run_check "INVARIANT" rg -n '^theorem endpointReceiveDualWithCapsOnCore_blocked_installs_nothing' SeLe4n/Kernel/IPC/CrossCore/EndpointReply.lean
run_check "INVARIANT" rg -n '^theorem endpointReceiveDualWithCaps_blocked_installs_nothing' SeLe4n/Kernel/IPC/DualQueue/WithCaps.lean
run_check "INVARIANT" rg -n 'receiveWithoutSenderInstallsNothing' tests/OperationChainSuite.lean
# And the install's declared footprint: `ipcTransferSingleCap` writes the
# receiver's own CSpace root, which both receive-shaped footprints declared READ.
run_check "INVARIANT" rg -n '^theorem lockSet_endpointReceive_capsInstall_write_mem' SeLe4n/Kernel/IPC/CrossCore/EndpointReply.lean
run_check "INVARIANT" rg -n '^theorem lockSet_replyRecv_capsInstall_write_mem' SeLe4n/Kernel/IPC/CrossCore/EndpointReply.lean
run_check "INVARIANT" rg -n 'receiveInstallsCaps st endpointObjId' SeLe4n/Kernel/IPC/CrossCore/EndpointReply.lean
# The inventory must name the function the dispatch calls: both receive-shaped
# live arms reach the WithCaps form now, so the bare transition is a below-API
# entry and the live-arm claim sits on the new one.  The negative forbids the
# claim drifting back onto the bare transition.
run_check "INVARIANT" rg -n '^theorem endpointReceiveDualWithCapsOnCore_confinedToCores' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_check "INVARIANT" rg -n '^theorem endpointReceiveDualWithCapsOnCore_crossCoreNonInterference' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_check "INVARIANT" rg -n '\| \.endpointReceiveDualWithCaps => \.delegationProof \.receive' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean
run_negative_check "INVARIANT" rg -n '\| \.endpointReceiveDual => \.delegationProof \.receive' SeLe4n/Kernel/InformationFlow/NonInterferenceCrossCore.lean

# PR #873 round 6 (SM9.D.13a): the origination diff is SKIPPED for the arms that
# provably cannot append.  `newlyRecordedEvents` costs two O(n) walks of a trail
# bounded only at the 256-entry cliff, and it ran on every successful syscall.
# The skip is licensed by a total classifier whose set is a checked value, and
# whose answer the Tier-1 content-flow gate verifies against the call graph.
run_check "INVARIANT" rg -n '^def syscallRecordsDeclassification' SeLe4n/Kernel/InformationFlow/TaintPropagation.lean
run_check "INVARIANT" rg -n '^theorem syscallRecordsDeclassification_iff' SeLe4n/Kernel/InformationFlow/TaintPropagation.lean
run_check "INVARIANT" rg -n '^theorem syscallRecordsDeclassification_independent_of_class' SeLe4n/Kernel/InformationFlow/TaintPropagation.lean
run_check "INVARIANT" rg -n '^def planOriginationTags' SeLe4n/Kernel/InformationFlow/TaintPropagation.lean
run_check "INVARIANT" rg -n '  originates : Bool' SeLe4n/Kernel/InformationFlow/TaintPropagation.lean
run_check "INVARIANT" rg -n '^theorem planOriginationTags_eq_of_no_events' SeLe4n/Kernel/InformationFlow/TaintPropagation.lean
run_check "INVARIANT" rg -n 'theorem syscallTaintPlan_originates' SeLe4n/Kernel/InformationFlow/TaintPropagation.lean
# The drain writes the trail and still originates nothing — the load-bearing
# exemption behind `.auditDrain` answering `false`, and what the Tier-1 gate
# requires to be present before it honours that exemption.  Both branches:
# a non-empty drain moves the epoch, a zero-length one does not.
# PR #873 round 6: `.declassify`'s target can be an object of ANY kind, so the
# kind inventory admits every one — and the consistency theorem is stated over
# EVERY `targetLock`, not only the default `none` it used to be provable at.
# `lockSet_declassify_nonTarget_kinds` is what keeps the fixed part tight.
run_check "INVARIANT" rg -n '^theorem permittedKinds_declassify_admits_every_kind' SeLe4n/Kernel/Concurrency/Locks/LockSetTransitions.lean
run_check "INVARIANT" rg -n '^theorem lockSet_declassify_nonTarget_kinds' SeLe4n/Kernel/Concurrency/Locks/LockSetTransitions.lean
run_check "INVARIANT" rg -n 'cnRoot : ObjId\) \(targetLock : Option LockId := none\)' SeLe4n/Kernel/Concurrency/Locks/LockSetTransitions.lean
run_check "INVARIANT" rg -n '^theorem newlyRecordedEvents_of_drop' SeLe4n/Kernel/InformationFlow/TaintPropagation.lean
run_check "INVARIANT" rg -n '^theorem newlyRecordedEvents_auditDrain' SeLe4n/Kernel/InformationFlow/TaintPropagation.lean
run_check "INVARIANT" rg -n 'AUDIT_APPEND_EXEMPT' scripts/check_content_flow_coverage.py
run_check "INVARIANT" rg -n 'CF_AUDIT_ARM' scripts/check_content_flow_coverage.py
# The gates must see private definitions: Lean mangles `private def` to
# `_private.…`, which answers `isInternal`, and both one-writer sweeps filtered
# on exactly that.
run_check "INVARIANT" rg -n 'privateToUserName' scripts/check_content_flow_coverage.py
run_negative_check "INVARIANT" rg -n 'if n.isInternal' scripts/check_content_flow_coverage.py

# SM9.D.14 – SM9.D.16: the detector.  `declassificationChainLinked` keeps its
# name and gains the causal conjunct; the TABLE-derived alternative is retained
# as a REFUTED design, since re-evaluating a historical event against the
# current table invents links a retype has cleared and loses links acquired
# after the fact.
run_check "INVARIANT" rg -n '^def declassificationChainCausal' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
run_check "INVARIANT" rg -n '^def chainCausalFromTable' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
run_check "INVARIANT" rg -n '^theorem chainCausal_is_history_local' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
run_check "INVARIANT" rg -n '^theorem chainCausal_not_table_derived' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
run_check "INVARIANT" rg -n '^theorem chainCausal_survives_subject_retype' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
run_check "INVARIANT" rg -n '^theorem chainLaunders_sound_under_causal_provenance' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
run_check "INVARIANT" rg -n '^theorem causalChain_residual_over_approximation' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
run_check "INVARIANT" rg -n '^theorem declassificationChainLinked_is_causal' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
run_check "INVARIANT" rg -n '^theorem chainLaunders_residual_is_saturation' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
# The verdict a monitor reads — one OPAQUE bit per adjacent pair, never the
# recorded tags (global declassification identities, which the view-local entry
# indices exist to hide).  Without it the causal detector would be an
# improvement only the model can see.
run_check "INVARIANT" rg -n 'chainNamesPredecessor \(index : Nat\)' SeLe4n/Kernel/InformationFlow/AuditRead.lean
run_check "INVARIANT" rg -n '^theorem chainVerdict_ok' SeLe4n/Kernel/InformationFlow/AuditRead.lean
run_check "INVARIANT" rg -n '^theorem chainVerdict_index_zero_refused' SeLe4n/Kernel/InformationFlow/AuditRead.lean
run_check "INVARIANT" rg -n '^theorem chainVerdict_view_local' SeLe4n/Kernel/InformationFlow/AuditRead.lean
run_check "INVARIANT" rg -n '^theorem chainVerdict_reconstructs_causal' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
run_check "INVARIANT" rg -n 'ChainNamesPredecessor = 27' rust/sele4n-sys/src/audit.rs
run_check "INVARIANT" rg -n 'the causality verdict reaches a monitor' tests/SmpInformationFlowSuite.lean
# PR #873 review: the GENERAL causality verdict.  `predecessorTags` may name any
# earlier event and `declassificationChainCausal` runs over an arbitrary
# non-contiguous subchain, so an adjacency-only query cannot test a hop an
# interleaved event split out of adjacency.  Opcode 28 is appended (never a
# renumber — an ABI number is a contract) and reads two view-local indices.
run_check "INVARIANT" rg -n 'chainNamesEntry \(later earlier : Nat\)' SeLe4n/Kernel/InformationFlow/AuditRead.lean
run_check "INVARIANT" rg -n '^theorem chainEntryVerdict_ok' SeLe4n/Kernel/InformationFlow/AuditRead.lean
run_check "INVARIANT" rg -n '^theorem chainEntryVerdict_refused' SeLe4n/Kernel/InformationFlow/AuditRead.lean
run_check "INVARIANT" rg -n '^theorem chainEntryVerdict_view_local' SeLe4n/Kernel/InformationFlow/AuditRead.lean
run_check "INVARIANT" rg -n '^theorem chainEntryVerdict_names_iff' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
run_check "INVARIANT" rg -n 'ChainNamesEntry = 28' rust/sele4n-sys/src/audit.rs
run_check "INVARIANT" rg -n 'NEGATIVE: the same domain-composing pair with no snapshot reads 0' tests/SmpInformationFlowSuite.lean
run_check "TRACE" rg -n 'causality verdict: monitorReads=' tests/fixtures/smp_information_flow.expected
# PR #873 review round 5: capability provenance is OUT OF SCOPE, consistently.
# A CNode holds no tracked content, so a tag written on a CSpace root has no
# operation able to clear it — deleting the capability that carried it leaves a
# specific unsaturated predecessor behind, which `staleTaint_is_not_saturation`
# forbids.  It was also redundant: a transfer moves authority, and every content
# flow the authority enables is declared where that content actually moves.
run_check "INVARIANT" rg -n '^theorem senderTaintEdges_content_only' SeLe4n/Kernel/InformationFlow/TaintPropagation.lean

# PR #873 round 9: the taint table is keyed, so it is bounded by the objects
# that currently carry provenance rather than by how many writes have happened.
# A function-backed table recorded history: the ordinary store/consume cycle is
# value-changing in both directions, so the no-op write guards never covered it.
run_check "INVARIANT" rg -n '^structure TaintTable where' SeLe4n/Kernel/InformationFlow/Taint.lean
run_check "INVARIANT" rg -n '^def taintEntriesErase' SeLe4n/Kernel/InformationFlow/Taint.lean
run_check "INVARIANT" rg -n '^theorem storeThenClear_no_growth' SeLe4n/Kernel/InformationFlow/Taint.lean
run_check "INVARIANT" rg -n '^theorem clearAt_set_entries' SeLe4n/Kernel/InformationFlow/Taint.lean
run_check "INVARIANT" rg -n 'five store/consume cycles leave the taint table with no entries at all' tests/SmpInformationFlowSuite.lean
# NEGATIVE: the function representation must not come back — it is what made the
# table a record of every write.
run_negative_check "INVARIANT" rg -n 'abbrev TaintTable := SeLe4n\.ObjId' SeLe4n/Kernel/InformationFlow/Taint.lean

# PR #873 review round 5: a laundering chain that spans an audit drain is
# queryable again.  Monitor-only and gated on `auditMonitorAuthorized` alone —
# a gate that read the reader's current view would answer differently for two
# states with identical views but different hidden entries, which is a count of
# what the reader cannot see.
run_check "INVARIANT" rg -n '\| chainNamesArchived \(later timestamp : Nat\)' SeLe4n/Kernel/InformationFlow/AuditRead.lean
run_check "INVARIANT" rg -n '^theorem chainArchivedVerdict_names_iff' SeLe4n/Kernel/InformationFlow/AuditRead.lean
run_check "INVARIANT" rg -n '^theorem chainArchivedVerdict_denied_for_non_monitor' SeLe4n/Kernel/InformationFlow/AuditRead.lean
run_check "INVARIANT" rg -n '^theorem chainArchivedVerdict_refuses_live_timestamp' SeLe4n/Kernel/InformationFlow/AuditRead.lean
# The count itself is pinned once, with the ABI mirror above; only this
# opcode's own value belongs here.
run_check "INVARIANT" rg -n 'ChainNamesArchived = 29' rust/sele4n-sys/src/audit.rs
# NEGATIVE: the carrier and its gate must not come back.
run_negative_check "INVARIANT" rg -n '^def capTransferTaintSinks' SeLe4n/Kernel/InformationFlow/TaintPropagation.lean
run_negative_check "INVARIANT" rg -n '^theorem taintPropagation_send_to_receiver_cspace' SeLe4n/Kernel/InformationFlow/TaintPropagation.lean
run_negative_check "INVARIANT" rg -n '^theorem taintPropagation_cspace_provenance_forwarded' SeLe4n/Kernel/InformationFlow/TaintPropagation.lean
# PR #873 review round 3: the two orderings of a capability transfer must agree,
# and the CSpace provenance must reach a SUBJECT or it can never reach an audit
# event.  A parked sender names no receiver, so the receive declares the CNode
# sink itself; and consuming a message taints the consumer from its own root.
# …and the clear path is elided like the join path: `contentFlowClears` fires on
# every wait and every direct-to-waiter signal, so an unguarded clear would
# rebuild the closure chain the join elision removed.
run_check "INVARIANT" rg -n '^theorem clearAt_eq_of_empty' SeLe4n/Kernel/InformationFlow/Taint.lean
# …and the disjoint-write-set claim APPLIES both plans rather than restating the
# frame lemma (the tautology class this workstream has now hit three times).
run_check "INVARIANT" rg -n '^theorem taintWriteKeys_disjoint_order_independent' SeLe4n/Kernel/InformationFlow/TaintPropagation.lean
# PR #873: IPC capability transfer records its derivation edge from the slot the
# capability was REALLY resolved from.  CDT nodes are keyed by the full SlotRef,
# so the previous synthetic parent (slot 0 of the sender's root) put every
# transferred copy under a node that revoking the true source never visits: the
# copy survived a revoke meant to destroy it, and an unrelated capability at the
# stand-in address was destroyed by a revoke that had nothing to do with it.
run_check "INVARIANT" rg -n '^structure TransferCap' SeLe4n/Model/Object/Types.lean
run_check "INVARIANT" rg -n 'srcNode : CdtNodeId' SeLe4n/Model/Object/Types.lean
run_check "INVARIANT" rg -n 'caps : Array TransferCap' SeLe4n/Model/Object/Types.lean
run_check "INVARIANT" rg -n 'ipcTransferSingleCap tc.cap tc.srcNode' SeLe4n/Kernel/IPC/Operations/CapTransfer.lean
# …and a reusable slot ADDRESS must not come back as the carried identity: a
# parked send outlives the slot, so an address names whatever occupies it later.
run_negative_check "INVARIANT" rg -n 'srcRef : SlotRef' SeLe4n/Model/Object/Types.lean
# The synthetic parent must not come back.  The type change makes it awkward
# rather than impossible — a caller could still synthesise a SlotRef — so the
# address itself is pinned out of the transfer path.
run_negative_check "INVARIANT" rg -n 'cnode := senderCspaceRoot, slot := SeLe4n.Slot.ofNat 0' SeLe4n/Kernel/IPC/Operations/CapTransfer.lean
run_negative_check "INVARIANT" rg -n 'cnode := senderRoot, slot := SeLe4n.Slot.ofNat 0' SeLe4n/Kernel/IPC/Operations/CapTransfer.lean
# …and the end-to-end regression: revoking the REAL source destroys the
# transferred copy, while revoking the old stand-in address does not.  Both
# verdicts swap under the defect, which is what makes the pair load-bearing.
run_check "INVARIANT" rg -n 'chain12b: revoking the real source destroys the transferred cap' tests/OperationChainSuite.lean
run_check "INVARIANT" rg -n 'chain12b: revoking an unrelated slot leaves the transferred cap alone' tests/OperationChainSuite.lean
# PR #873 review rounds 4-7: bound delivery is ONE classification, not three
# re-derivations.  The clear, the declared edges and the origination filter each
# used to re-read `declassifiedSignalReceiver?` — which cannot tell a bound
# target from a waiter — and disagreed three times in three rounds.
run_check "INVARIANT" rg -n '^inductive SignalDelivery where' SeLe4n/Kernel/InformationFlow/TaintPropagation.lean
run_check "INVARIANT" rg -n '^def signalDelivery ' SeLe4n/Kernel/InformationFlow/TaintPropagation.lean
run_check "INVARIANT" rg -n '^def signalBypassedNotification' SeLe4n/Kernel/InformationFlow/TaintPropagation.lean
run_check "INVARIANT" rg -n '^theorem signalDelivery_bound_leaves_notification_alone' SeLe4n/Kernel/InformationFlow/TaintPropagation.lean
run_check "INVARIANT" rg -n '^theorem signalDelivery_waiter_empties_notification' SeLe4n/Kernel/InformationFlow/TaintPropagation.lean
# A bypass is NOT a clear: the notification keeps a stored badge and its
# provenance, but the fresh event is not originated onto it.
run_check "INVARIANT" rg -n 'bypassed : List SeLe4n.ObjId' SeLe4n/Kernel/InformationFlow/TaintPropagation.lean
run_check "INVARIANT" rg -n '^theorem bypassedObject_not_originated' SeLe4n/Kernel/InformationFlow/TaintPropagation.lean
# PR #873 round 7: a BARE downgrade releases nothing into an IDLE target, so it
# originates nothing there.  `.declassify` carries no payload, and against an
# empty notification the tag was fictitious — a later unrelated signal joined it,
# `.notificationWait` carried it on, and a downgrade behind that receiver named a
# predecessor for content that never existed.  The second check is the direction
# that keeps the skip from becoming an under-approximation.
run_check "INVARIANT" rg -n '^def declassifyBypassedTarget ' SeLe4n/Kernel/InformationFlow/TaintPropagation.lean
run_check "INVARIANT" rg -n '^def declassifyBypassedTargets ' SeLe4n/Kernel/InformationFlow/TaintPropagation.lean
run_check "INVARIANT" rg -n '^theorem declassify_idle_notification_bypassed' SeLe4n/Kernel/InformationFlow/TaintPropagation.lean
run_check "INVARIANT" rg -n '^theorem declassify_pending_notification_not_bypassed' SeLe4n/Kernel/InformationFlow/TaintPropagation.lean
# PR #873 round 9: and the ACTOR half.  Round 7 suppressed the target pair and
# left `(sourceSubject, timestamp)` standing, so the subject kept an identity it
# never released — and `declassificationActorTaint` snapshots the ACTOR, so its
# next downgrade recorded that identity as a predecessor.  A no-release event now
# contributes neither pair, dropped per event rather than filtered by key.
run_check "INVARIANT" rg -n '  noRelease : List SeLe4n.ObjId' SeLe4n/Kernel/InformationFlow/TaintPropagation.lean
run_check "INVARIANT" rg -n '^@\[simp\] theorem originationTags_cons_noRelease' SeLe4n/Kernel/InformationFlow/TaintPropagation.lean
run_check "INVARIANT" rg -n '^theorem originationTags_cons_release' SeLe4n/Kernel/InformationFlow/TaintPropagation.lean
# PR #873 round 9: a non-archived timestamp is a malformed OPERAND, not an
# authority failure — the gate is checked first, so an unauthorized caller still
# learns nothing about the trail's extent.
run_check "INVARIANT" rg -n '^theorem chainArchivedVerdict_refuses_live_timestamp' SeLe4n/Kernel/InformationFlow/AuditRead.lean
run_negative_check "INVARIANT" rg -n '&& decide \(timestamp <' SeLe4n/Kernel/InformationFlow/AuditRead.lean
# PR #873 round 10: four gate-soundness corrections.  Two stop the anchor gate
# inventing failures (a search MODE and a search SCOPE are part of what an
# anchor pins), and two stop the content-flow gate under-reading (a walk that
# stops with an unexpanded frontier, and three dispatchers merged under one
# syscall name so a healthy arm masked a broken sibling).
run_check "INVARIANT" rg -n '^def _mode_allows' scripts/check_anchor_consistency.py
run_check "INVARIANT" rg -n '^def _scope_contains' scripts/check_anchor_consistency.py
run_check "INVARIANT" rg -n '^def arm_key' scripts/check_content_flow_coverage.py
run_check "INVARIANT" rg -n 'FAIL_CLOSED_ARMS' scripts/check_content_flow_coverage.py
run_check "INVARIANT" rg -n 'CF_TRUNCATED' scripts/check_content_flow_coverage.py
# PR #873 round 11: `pendingMessage` agrees with the blocking state in BOTH
# directions.  The invariant used to constrain only the two collecting states and
# say `True` of the two delivering ones, which made "a parked sender carries its
# message" a convention every consumer had to re-derive -- and the consumers that
# forgot were the round-7 frozen dequeue and the round-11 live one.  Four pins:
# the invariant's delivering half, its executable mirror (the harness could not
# see the violation either), the dequeue's fail-closed complement for states that
# carry no invariant, and the converse theorem `receiverTaintEdges` reads against.
run_check "INVARIANT" rg -n '\.blockedOnSend _ => tcb\.pendingMessage\.isSome' SeLe4n/Kernel/IPC/Invariant/Defs.lean
run_check "INVARIANT" rg -n '\.blockedOnCall _ => tcb\.pendingMessage\.isSome' SeLe4n/Kernel/IPC/Invariant/Defs.lean
run_check "INVARIANT" rg -n 'blockedThreadPendingMessageChecks' SeLe4n/Testing/InvariantChecks.lean
run_check "INVARIANT" rg -n 'headTcb\.pendingMessage\.isNone' SeLe4n/Kernel/IPC/DualQueue/Core.lean
run_check "INVARIANT" rg -n '^theorem endpointQueuePopHead_send_sender_carries_message' SeLe4n/Kernel/IPC/Invariant/Defs.lean
run_check "INVARIANT" rg -n 'receiveRefusesMessagelessParkedSender' tests/OperationChainSuite.lean
# PR #873 round 12: two defaults inverted, for the same reason each time -- a set
# of remembered exceptions is a list of the cases someone thought of.  The
# downgrade's origination is now established from the target actually holding
# tracked content, so a kind this model tracks none for bypasses by construction;
# and the field-write detector no longer infers "this is an update" from a
# projection being present, so no spelling of the rebuild can hide a second
# writer.  The negatives pin that neither default comes back.
run_check "INVARIANT" rg -n '^def declassifyTargetHoldsContent' SeLe4n/Kernel/InformationFlow/TaintPropagation.lean
run_check "INVARIANT" rg -n '^theorem declassifyBypassedTarget_of_untracked_kind' SeLe4n/Kernel/InformationFlow/TaintPropagation.lean
run_check "INVARIANT" rg -n '^theorem declassifyTargetHoldsContent_covers_every_tracked_field' SeLe4n/Kernel/InformationFlow/TaintPropagation.lean
run_check "INVARIANT" rg -n 'cfPlantedRebuildTaintWriter' scripts/check_content_flow_coverage.py
run_check "INVARIANT" rg -n 'STATE_CONSTRUCTORS' scripts/check_content_flow_coverage.py
run_negative_check "INVARIANT" rg -n 'let isUpdate' scripts/check_content_flow_coverage.py
# And the other half of the same relation, which the executable mirror exposed: a
# receive that blocks clears the message it is not going to deliver.  The negative
# is load-bearing -- a bare `storeTcbIpcState` there is the shape that carried a
# consumed message into `.blockedOnReceive` and made the preservation theorem
# depend on an `hReceiverMsg` hypothesis nothing established.
run_check "INVARIANT" rg -n 'storeTcbIpcStateAndMessage st. receiver \(\.blockedOnReceive endpointId\) none' SeLe4n/Kernel/IPC/DualQueue/Transport.lean
run_check "INVARIANT" rg -n 'storeTcbIpcStateAndMessage st. receiver \(\.blockedOnReceive endpointId\) none' SeLe4n/Kernel/IPC/CrossCore/EndpointReply.lean
run_negative_check "INVARIANT" rg -n 'storeTcbIpcState st. receiver \(\.blockedOnReceive endpointId\)' SeLe4n/Kernel/IPC/DualQueue/Transport.lean SeLe4n/Kernel/IPC/CrossCore/EndpointReply.lean
# PR #873 round 13: **an in-flight derivation is a derived capability.**  A
# capability-bearing send that parks carries its derivation in the sender's
# `pendingMessage` and becomes a CDT child only when a receiver collects it, so a
# revoke walked a subtree the pending transfer was not in, reported success, and
# the later receive installed the snapshot and added the child edge AFTER the
# revocation.  The fix is at the operation that defines the guarantee rather than
# at a third reader of the pending-transfer predicate: both revoke wrappers end by
# consuming the carried derivations, over the revoked root and its whole subtree.
run_check "INVARIANT" rg -n '^def revokePendingTransfersFrom' SeLe4n/Kernel/Capability/Operations.lean
run_check "INVARIANT" rg -n '^theorem revokePendingTransfersFrom_frame' SeLe4n/Kernel/Capability/Operations.lean
# PR #873 round 17: that consumption was an epilogue appended at each entry
# point, and there were FOUR hand-written traversals to append it to.  Two got
# it; a successful `cspaceRevokeCdtStrict` or `cspaceRevokeCdtTransactional`
# returned its folded state with the derivation still parked, and the receiver's
# later collect installed it.  The entry points are now one scaffold at four
# traversals, so the prologue and the epilogue are not a variant's to write.
run_check "INVARIANT" rg -n '^def revokeCdtScaffold' SeLe4n/Kernel/Capability/Operations.lean
run_check "INVARIANT" rg -n 'revokePendingTransfersFrom out.state \(rootNode :: out.revokedNodes\)' SeLe4n/Kernel/Capability/Operations.lean
# The tie is definitional -- four `rfl`s, so a variant that stopped being the
# scaffold would fail to elaborate rather than fail to be listed.
run_check "INVARIANT" rg -n '^theorem cspaceRevokeCdt_routes_through_scaffold' SeLe4n/Kernel/Capability/Operations.lean
run_check "INVARIANT" rg -n '^theorem cspaceRevokeCdtStreaming_routes_through_scaffold' SeLe4n/Kernel/Capability/Operations.lean
run_check "INVARIANT" rg -n '^theorem cspaceRevokeCdtStrict_routes_through_scaffold' SeLe4n/Kernel/Capability/Operations.lean
run_check "INVARIANT" rg -n '^theorem cspaceRevokeCdtTransactional_routes_through_scaffold' SeLe4n/Kernel/Capability/Operations.lean
# Held over an arbitrary traversal, so it covers the four that exist and the ones
# that do not exist yet.
run_check "INVARIANT" rg -n '^theorem revokeCdtScaffold_ok_consumed_or_nothing_derived' SeLe4n/Kernel/Capability/Operations.lean
# The exact pre-fix return of both reporting variants: the fold's state handed
# back with no consumption.  Load-bearing negative -- this is the shape that let
# a revoke report success while the capability was still on its way.
run_negative_check "INVARIANT" rg -n 'ok \(\{ report with deletedSlots := report.deletedSlots.reverse \}, stFinal\)' SeLe4n/Kernel/Capability/Operations.lean
# Consuming from a TCB is a write to the object store, so the seven-conjunct
# capability bundle has to survive it -- proved, not assumed, and in the Invariant
# layer because Operations cannot name the bundle.
run_check "INVARIANT" rg -n '^theorem revokePendingTransfersFrom_preserves_capabilityInvariantBundle' SeLe4n/Kernel/Capability/Invariant/Preservation/Revoke.lean
# The transactional variant had NO preservation theorem: the strict one restated
# its fold inline instead of naming it, so there was nothing for a second variant
# over the same fold to reuse.
run_check "INVARIANT" rg -n '^theorem revokeCdtReportingStep_preserves' SeLe4n/Kernel/Capability/Invariant/Preservation/Revoke.lean
run_check "INVARIANT" rg -n '^theorem cspaceRevokeCdtTransactional_preserves_capabilityInvariantBundle' SeLe4n/Kernel/Capability/Invariant/Preservation/Revoke.lean
# And the regression names revocation rather than one function: it ran
# `cspaceRevokeCdt` alone, which is why it could not see the other three.
run_check "INVARIANT" rg -n 'revokeConsumesPendingTransfer' tests/OperationChainSuite.lean
run_check "INVARIANT" rg -n '^private def revocationEntryPoints' tests/OperationChainSuite.lean
run_check "INVARIANT" rg -n 'revocationEntryPoints.length == 4' tests/OperationChainSuite.lean
# And the send-side half of round 6's ordering independence.  The wrappers took
# the grant authority TWICE -- the `endpointRights` argument for the rendezvous
# arm, `msg.capsGranted` for the parked one -- and never tied them, so a caller
# passing granting rights on a message at the field's default transferred on
# rendezvous and nothing after parking, and one passing a CLAIMED grant on a
# non-granting endpoint transferred after parking.  Deriving the field from the
# endpoint's rights makes the two inputs one, in both directions.
run_check "INVARIANT" rg -n 'endpointSendDual endpointId sender \{ msg with capsGranted := endpointRights.mem .grant \}' SeLe4n/Kernel/IPC/DualQueue/WithCaps.lean
run_check "INVARIANT" rg -n 'endpointCall endpointId caller \{ msg with capsGranted := endpointRights.mem .grant \}' SeLe4n/Kernel/IPC/DualQueue/WithCaps.lean
run_check "INVARIANT" rg -n 'endpointSendDualOnCore endpointId sender \{ msg with capsGranted := endpointRights.mem .grant \}' SeLe4n/Kernel/IPC/CrossCore/EndpointSend.lean
run_check "INVARIANT" rg -n 'endpointCallOnCore endpointId caller \{ msg with capsGranted := endpointRights.mem .grant \}' SeLe4n/Kernel/IPC/CrossCore/EndpointCallDispatch.lean
# The regression drives the property from the UNSTAMPED message `chain12c`'s
# fixture deliberately does not prepare -- `chain12c` sets the field from the same
# rights it passes, so it cannot see the two inputs disagree.
run_check "INVARIANT" rg -n 'endpointGrantDecidesBothOrderings' tests/OperationChainSuite.lean
# The CDT node allocator's global counter is the footprint gap the caps path
# opened: minting a node for a source slot writes `cdtNextNode` while the send's
# declared footprint holds the source CNode in READ mode and declares no
# state-level write.  Registered rather than papered over, so enabling fine locks
# has to delete the entry deliberately.
run_check "INVARIANT" rg -n 'cdtNodeAllocation' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '\(\.cdtNodeAllocation, "' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
# PR #873 round 14: **the frozen/live correspondence, as something that runs.**
# Each frozen operation re-implements a live transition, and which one it
# re-implements was recorded in a markdown table and a `mirrors X` sentence.
# Nothing ran either, so a frozen operation could drift and stay green -- which
# is how five separate divergences reached review rather than the build.  The
# table was itself wrong: row 5 named `notificationSignal` while the operation
# mirrors the bound-aware composition the live arm runs.
run_check "INVARIANT" rg -n '^def frozenObjectAgrees' SeLe4n/Kernel/FrozenOps/Agreement.lean
run_check "INVARIANT" rg -n '^def frozenStateAgrees' SeLe4n/Kernel/FrozenOps/Agreement.lean
run_check "INVARIANT" rg -n '^def frozenRunAgrees' SeLe4n/Kernel/FrozenOps/Agreement.lean
# The interlock: `frozenOpCoverage` says a frozen operation EXISTS for a
# syscall, which every divergence also satisfied.  Claiming it now obliges
# either a differential scenario or a stated reason, decided over
# `SyscallId.all` so a new constructor forces the choice.
run_check "INVARIANT" rg -n '^def frozenOpDifferentiallyChecked' SeLe4n/Kernel/FrozenOps/Agreement.lean
# PR #873 round 17: keyed by SYSCALL, one scenario satisfied a whole syscall --
# `.send` read "checked" on a fixture with no receiver waiting while the
# rendezvous branch had never been compared.  The unit of the claim is now the
# unit of the transition, and the per-syscall view is derived from it rather
# than asserted beside it.
run_check "INVARIANT" rg -n '^inductive FrozenOpBranch' SeLe4n/Kernel/FrozenOps/Agreement.lean
run_check "INVARIANT" rg -n '^def frozenBranchDifferentiallyChecked' SeLe4n/Kernel/FrozenOps/Agreement.lean
run_check "INVARIANT" rg -n '^theorem frozenBranch_checked_or_reasoned' SeLe4n/Kernel/FrozenOps/Agreement.lean
run_check "INVARIANT" rg -n '^theorem frozenBranchUncheckedReason_only_when_unchecked' SeLe4n/Kernel/FrozenOps/Agreement.lean
# The vacuity guard: without it a syscall with no branches listed satisfies the
# `all` and claims to be checked.
run_check "INVARIANT" rg -n 'FrozenOpBranch.all.any \(fun b => b.syscall == sid\)' SeLe4n/Kernel/FrozenOps/Agreement.lean
# A `.blockedOnCall` head is parked for its reply, not woken: the branch the
# frozen receive could not previously express, since it took no reply id.
run_check "INVARIANT" rg -n 'senderWasCall' SeLe4n/Kernel/FrozenOps/Operations.lean
run_check "INVARIANT" rg -n '^def frozenLinkCallerReply' SeLe4n/Kernel/FrozenOps/Core.lean
run_check "INVARIANT" rg -n 'differentialReceiveFromBlockedCallerAgrees' tests/FrozenOpsSuite.lean
# PR #873 round 17: on a rendezvous the message goes straight from the argument
# into the receiver's TCB, so the live send never resolved `sender` -- a caller
# naming a nonexistent thread delivered anyway and the receiver held a message
# attributed to it.  Only the parking arm failed, and only because it happens to
# store into the sender's own TCB.  The frozen mirror refused on both arms, and
# the frozen behaviour was the correct one, so the live path is what changed.
run_check "INVARIANT" rg -n 'match st.getTcb\? sender with' SeLe4n/Kernel/IPC/DualQueue/Transport.lean
# …and the per-core mirror in lockstep, which is what the refinement theorem ties.
run_check "INVARIANT" rg -n 'match st.getTcb\? sender with' SeLe4n/Kernel/IPC/CrossCore/EndpointSend.lean
run_check "INVARIANT" rg -n 'differentialSendFromAbsentSenderAgrees' tests/FrozenOpsSuite.lean
# PR #873 audit: the branch above was CLAIMED checked while its scenario compared
# only the refusal ordering, and the known divergence sat on the delivery
# ordering -- live `storeTcbReceiveComplete` clears the receiver's stashed reply
# object (D3/F-1) where the frozen mirror kept it.  The mirror is now field-exact
# and the delivery ordering is compared with the stash seeded.
run_check "INVARIANT" rg -n 'pendingMessage := some msg, pendingReceiveReply := none' SeLe4n/Kernel/FrozenOps/Operations.lean
run_check "INVARIANT" rg -n 'differentialSendRendezvousDeliversAgrees' tests/FrozenOpsSuite.lean
run_check "INVARIANT" rg -n 'the live delivery clears the stash' tests/FrozenOpsSuite.lean
# The consuming waiter is the calling thread: it never blocked, so the live
# `notificationWait` leaves the scheduler alone and the frozen mirror must too.
run_negative_check "INVARIANT" rg -n 'fun stR => frozenEnsureRunnable stR waiter' SeLe4n/Kernel/FrozenOps/Operations.lean
run_check "INVARIANT" rg -n '^theorem frozenOpCoverage_obliges_differential_check' SeLe4n/Kernel/FrozenOps/Agreement.lean
run_check "INVARIANT" rg -n '^theorem frozenOpDifferentiallyChecked_implies_covered' SeLe4n/Kernel/FrozenOps/Agreement.lean
# An excuse left behind after the scenario lands would re-open the escape hatch.
run_check "INVARIANT" rg -n '^theorem frozenOpUncheckedReason_only_when_unchecked' SeLe4n/Kernel/FrozenOps/Agreement.lean
# The scenarios, and the negative that makes them evidence rather than
# decoration: a comparison returning `true` for everything would pass all six.
run_check "INVARIANT" rg -n 'differentialNotificationSignalAgrees' tests/FrozenOpsSuite.lean
run_check "INVARIANT" rg -n 'differentialRefusalsAgree' tests/FrozenOpsSuite.lean
run_check "INVARIANT" rg -n 'differentialComparisonHasBite' tests/FrozenOpsSuite.lean
# The corrected row.  The wrong one must not come back.
run_prose_check "INVARIANT" rg -n 'frozenNotificationSignal.*notificationSignalBound' SeLe4n/Kernel/FrozenOps/Operations.lean
run_prose_negative_check "INVARIANT" rg -n '\| 5 \| .frozenNotificationSignal.*\| .notificationSignal. ' SeLe4n/Kernel/FrozenOps/Operations.lean
# PR #873 round 14: **the authority is checked where the resource is committed.**
# Resolving an extra capability mints a persistent CDT node and marks its slot
# as having a transfer in flight; Grant was consulted only later, at the unwrap.
# So a sender holding Write but not Grant spent the bounded node counter on
# every send, and `cspaceDeleteSlot` / the CNode retype answered
# `.revocationRequired` for a derivation the unwrap was always going to deny.
# The contract is definitional -- the state is untouched, not merely the caps
# denied -- so it is `rfl` rather than a scenario.
run_check "INVARIANT" rg -n '^theorem resolveExtraCaps_ungranted' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n '^theorem resolveExtraCapsDetailed_ungranted' SeLe4n/Kernel/API.lean
# And each live arm passes the endpoint capability's own bit, which the
# delegation theorems restate and therefore prove rather than assert.
run_check "INVARIANT" rg -n 'resolveExtraCaps gate.cspaceRoot extraCapAddrs gate.capDepth \(cap.rights.mem .grant\)' SeLe4n/Kernel/API.lean
run_negative_check "INVARIANT" rg -n 'resolveExtraCaps gate.cspaceRoot extraCapAddrs gate.capDepth st' SeLe4n/Kernel/API.lean
# The anchor gate's two fail-open holes, which are one defect: "I could not
# analyse this" was read as "this is fine".  A category label outside the
# parser's grammar made the helper line miss detection entirely, so the anchor
# left the comparison while the gate reported PASS; and a fixed-string positive
# against a regex negative returned no literal core, which was read as no
# contradiction even though the literal the positive demands is matched by the
# negative's wildcard.
run_check "BUILD" rg -n 'HELPER_NAME_RE' scripts/check_anchor_consistency.py
run_check "BUILD" rg -n '^def _regex_matches_literal' scripts/check_anchor_consistency.py
# PR #873 round 15: **the frozen scheduler kept no run queue.**  No frozen
# operation ever wrote `scheduler.byPriority`, which is the only field
# `frozenChooseThread` selects from -- so a woken thread was `.ready` and
# permanently unselectable, and a suspended one stayed in its bucket still
# marked `.ready`.  The docstring asserted the opposite and named `membership`,
# a `FrozenSet` whose keys cannot change and which selection never reads.
run_check "INVARIANT" rg -n '^def frozenEnsureRunnable' SeLe4n/Kernel/FrozenOps/Core.lean
run_check "INVARIANT" rg -n '^def frozenRemoveRunnable' SeLe4n/Kernel/FrozenOps/Core.lean
# The builder could not express a runnable thread at all, which is why every
# frozen test started from a state the live kernel cannot produce.
run_check "INVARIANT" rg -n '^def markRunnable' SeLe4n/Model/Builder.lean
# Every wake enqueues and every block dequeues -- the pairs the live transitions
# maintain with `ensureRunnable` / `removeRunnable`.
run_check "INVARIANT" rg -n 'frozenEnsureRunnable' SeLe4n/Kernel/FrozenOps/Operations.lean
run_check "INVARIANT" rg -n 'frozenRemoveRunnable' SeLe4n/Kernel/FrozenOps/Operations.lean
# The relation compares the buckets, not just the current thread; comparing
# `current` alone is what let the wake divergence through the differential
# scenarios that were built to catch exactly this class.
run_check "INVARIANT" rg -n 'let queueAgree' SeLe4n/Kernel/FrozenOps/Agreement.lean
# The reply scenario asserts BOTH sides succeed before comparing them: it used to
# agree because both refused with `.replyCapInvalid`, which is agreement about
# nothing happening.
run_check "INVARIANT" rg -n 'FO-031 control: the live reply succeeds' tests/FrozenOpsSuite.lean
# The corrected claims must not come back.
run_prose_negative_check "INVARIANT" rg -n 'run queue manipulation is skipped' SeLe4n/Kernel/FrozenOps/Operations.lean
run_prose_negative_check "INVARIANT" rg -n 'run queue insertion.{0,12}is skipped' SeLe4n/Kernel/FrozenOps/Operations.lean
# PR #873 round 16: **the relation stopped being an inclusion list.**  Every
# finding against it was "you forgot to compare X" -- the per-object lock, the
# returned value -- which is the enumerate-what-you-remembered shape this branch
# has been closing all along.  The re-represented variants are destructured, so
# a field nobody compares is an unused binding and a new field breaks the
# pattern; the returned values are compared through a relation the caller must
# supply rather than matched away as `_`.
run_check "INVARIANT" rg -n 'flock == llock' SeLe4n/Kernel/FrozenOps/Agreement.lean
run_check "INVARIANT" rg -n 'resultAgrees fa la' SeLe4n/Kernel/FrozenOps/Agreement.lean
# A frozen operation is the SYSCALL, not the bare transition: with no dispatcher
# it applies the provenance step inline, while the live kernel applies it after
# the transition at the seam.  Comparing against a bare transition compared two
# layers and passed only while every taint was empty.
run_check "INVARIANT" rg -n '^private def liveWithTaint' tests/FrozenOpsSuite.lean
run_check "INVARIANT" rg -n 'differentialTaintedSignalAgrees' tests/FrozenOpsSuite.lean
# …and the coverage claim is checked against the list the runner executes, in
# both directions, so it can no longer be true of a scenario that does not exist.
run_check "INVARIANT" rg -n '^private def differentialScenarios' tests/FrozenOpsSuite.lean
run_check "INVARIANT" rg -n 'differentialRegistryMatchesClaim' tests/FrozenOpsSuite.lean
# The anchor gate carries file filters into the comparison: `-g '"'"'*.md'"'"'` and
# `-g '"'"'*.lean'"'"' search disjoint files and cannot contradict, while an unfiltered
# negative covers any filtered positive.
run_check "BUILD" rg -n '_FILE_FILTER_OPTIONS' scripts/check_anchor_consistency.py
# PR #873 round 17: the content-flow gate's arm splitter recognised only a
# constructor immediately followed by `=>`, so a grouped arm
# (`| .auditRead | .auditDrain =>`) produced no reach key for either -- and its
# text was attributed to the preceding arm.  The missing-arm check was satisfied
# by the dispatcher that spells them separately, so the grouped pair was never
# verified fail-closed.  `recording_classification` in the same file already
# expanded groups: two parsers over one syntax, one of them right.
run_check "BUILD" rg -n '^def split_dispatch_arms' scripts/check_content_flow_coverage.py
run_check "BUILD" rg -n 'the arm splitter dropped a grouped arm' scripts/check_content_flow_coverage.py
# Sequence-coded test identifiers must not come back in the renamed scenarios.
run_negative_check "INVARIANT" rg -n 'private def fo0(2[2-9]|3[0-3])_' tests/FrozenOpsSuite.lean
run_negative_check "INVARIANT" rg -n 'private def chain12[b-h][A-Z]' tests/OperationChainSuite.lean
# PR #873 round 17: **the frozen wake refused a transition the kernel performs.**
# The enqueue went through `FrozenMap.set`, which answers `none` for an absent
# key, so a thread woken at a priority holding no bucket got `.illegalState` --
# while the live `ensureRunnable` creates the bucket through `RunQueue.insert`.
# A passive server blocked at freeze time is exactly that case.  The fixed key
# set was a property of `set`, not of the representation: `data` is an `Array`
# and `indexMap` an `RHTable`, and both grow.
run_check "INVARIANT" rg -n '^def FrozenMap.insert' SeLe4n/Model/FrozenState.lean
run_check "INVARIANT" rg -n '^theorem FrozenMap.insert_get\?_self' SeLe4n/Model/FrozenState.lean
run_check "INVARIANT" rg -n '^theorem FrozenMap.insert_preserves_wellFormed' SeLe4n/Model/FrozenState.lean
run_check "INVARIANT" rg -n 'st.scheduler.byPriority.insert prio' SeLe4n/Kernel/FrozenOps/Core.lean
# The refusal must not come back.
run_negative_check "INVARIANT" rg -n 'byPriority.set prio' SeLe4n/Kernel/FrozenOps/Core.lean
# Every actor in the differential scenarios sat at priority 0, so the missing-key
# branch never ran and the harness built to catch frozen/live divergence could
# not see this one.  The control asserts the bucket really is absent first.
run_check "INVARIANT" rg -n 'differentialWakeAtUnqueuedPriorityAgrees' tests/FrozenOpsSuite.lean
run_check "INVARIANT" rg -n 'FO-034: control' tests/FrozenOpsSuite.lean
# PR #873 round 17: the taint side table's contract named `syscallEntryChecked`
# as its writer's seam.  Round 6 moved the write down to the dispatchers because
# the unchecked one reached the transitions without passing through it, and the
# contract went on naming the old layer for eleven rounds.  It now names the
# seams the content-flow gate checks.
run_prose_check "INVARIANT" rg -n 'dispatchSyscallChecked., each applying it' SeLe4n/Model/State.lean
run_prose_check "INVARIANT" rg -n 'check_content_flow_coverage.py. validates each' SeLe4n/Model/State.lean
run_prose_check "INVARIANT" rg -n 'run at both dispatchers' SeLe4n/Kernel/Architecture/Invariant.lean
# The single-seam claim must not come back at either site.
run_prose_negative_check "INVARIANT" rg -n 'at the per-core syscall entry' SeLe4n/Model/State.lean
run_prose_negative_check "INVARIANT" rg -n 'run at .API.syscallEntryChecked' SeLe4n/Kernel/Architecture/Invariant.lean
# PR #873 round 7: a CLEAR is a taint write too, so the retype's cleared key
# rides its own object lock — the third member of `taintWriteKeys` the key-local
# declaration had skipped.  The fixed four stay pinned separately.
run_check "INVARIANT" rg -n '^theorem lockSet_lifecycleRetype_clearedKey_write_mem' SeLe4n/Kernel/Concurrency/Locks/LockSetTransitions.lean
run_check "INVARIANT" rg -n '^theorem lockSet_lifecycleRetype_nonTarget_kinds' SeLe4n/Kernel/Concurrency/Locks/LockSetTransitions.lean
run_check "INVARIANT" rg -n '^theorem permittedKinds_lifecycleRetype_admits_every_kind' SeLe4n/Kernel/Concurrency/Locks/LockSetTransitions.lean
# PR #873 round 7: a frozen parked sender must carry its message — the state
# check alone let a `.blockedOnSend` head with no `pendingMessage` be dequeued,
# after which the receiver got `none` and the sender's provenance anyway.
run_check "INVARIANT" rg -n 'headTcb.pendingMessage.isSome' SeLe4n/Kernel/FrozenOps/Operations.lean
run_check "INVARIANT" rg -n 'frozenParkedSenderCarriesItsMessage' tests/FrozenOpsSuite.lean
# No receive declares a CSpace sink, and PR #873 round 8 corrected the reason:
# not "the live receive installs nothing" — it has installed since round 6 — but
# the standing scope decision that a CNode holds no tracked content
# (`senderTaintEdges_content_only`).  The three are pinned OUT because declaring
# them would hand an unrelated later downgrade an unsaturated predecessor; only
# a scope change that tracks capability provenance can restore them, on BOTH
# orderings at once.
run_negative_check "INVARIANT" rg -n 'theorem taintPropagation_queued_receive_to_cspace' SeLe4n/Kernel/InformationFlow/TaintPropagation.lean
run_negative_check "INVARIANT" rg -n 'theorem taintPropagation_cspace_taints_consumer' SeLe4n/Kernel/InformationFlow/TaintPropagation.lean
run_negative_check "INVARIANT" rg -n 'def parkedCarriesCaps' SeLe4n/Kernel/InformationFlow/TaintPropagation.lean
# The send-side Grant gate is NOT pinned here any more.  It lived inside
# `sendCarriesCaps`, which the content-derived cut deleted and which the negative
# check below pins out — so requiring its text in this file contradicted that
# check and could not pass.  The gate itself is unchanged; it is a property of
# the IPC transition, and this file no longer restates it.
# PR #873 round 8: the delete guard sees transfers IN FLIGHT, not only children.
# Between a blocking send and the unwrap that completes it the source slot has no
# CDT child yet, so a children-only guard permitted the delete, the slot was
# detached from its node, and the transferred copy landed under a parent no slot
# pointed at — unreachable by any revoke.
run_check "INVARIANT" rg -n '^def nodeHasPendingTransfer' SeLe4n/Kernel/Capability/Operations.lean
run_check "INVARIANT" rg -n '^def slotHasPendingTransfer' SeLe4n/Kernel/Capability/Operations.lean
run_check "INVARIANT" rg -n '^theorem cspaceDeleteSlot_refuses_pending_transfer' SeLe4n/Kernel/Capability/Operations.lean
run_check "INVARIANT" rg -n '^theorem cspaceDeleteSlot_refuses_existing_children' SeLe4n/Kernel/Capability/Operations.lean
run_check "INVARIANT" rg -n 'hasCdtChildren st addr \|\| slotHasPendingTransfer st addr' SeLe4n/Kernel/Capability/Operations.lean

# The derivation-parent predicate has two callers — the slot delete and the
# CNode retype — and they must read the same one, so both the factored
# predicate and each caller's use of it are pinned.
run_check "INVARIANT" rg -n '^def slotIsDerivationParent' SeLe4n/Kernel/Capability/Operations.lean
run_check "INVARIANT" rg -n '^def cnodeHasDerivationParentSlot' SeLe4n/Kernel/Capability/Operations.lean
run_check "INVARIANT" rg -n 'if slotIsDerivationParent st addr then' SeLe4n/Kernel/Capability/Operations.lean
run_check "INVARIANT" rg -n 'if cnodeHasDerivationParentSlot st target cn then' SeLe4n/Kernel/Lifecycle/Operations/CleanupPreservation.lean

# The guarantee those guards are the ergonomics for: the single creator of an
# `.ipcTransfer` edge declines when the source node has no slot, so no
# destroyer — present or future — can leave an unrevokable child behind.
run_check "INVARIANT" rg -n '^  \| sourceRevoked$' SeLe4n/Model/Object/Types.lean
run_check "INVARIANT" rg -n '^theorem ipcTransferSingleCap_installed_implies_live_source' SeLe4n/Kernel/Capability/Operations.lean
run_check "INVARIANT" rg -n '^theorem ipcTransferSingleCap_sourceRevoked_preserves_state' SeLe4n/Kernel/Capability/Operations.lean
# PR #873 round 18: that check asked whether the node still MAPPED to a slot, on
# the premise that every destroyer severs the mapping.  Delete, CNode retype and
# the descendant sweep do; the LOCAL sibling sweep does not -- `revokeTargetLocal`
# empties every sibling naming the revoked target while `revokeAndClearRefsState`
# deliberately preserves the CDT maps.  So the mapping outlived the capability, a
# transfer parked against a swept sibling installed, and nothing could revoke the
# copy afterwards: `cspaceRevokeCdt` on an empty slot fails at `cspaceLookupSlot`.
run_check "INVARIANT" rg -n '^def cdtNodeIsRevocable' SeLe4n/Kernel/Capability/Operations.lean
run_check "INVARIANT" rg -n 'match cdtNodeIsRevocable st srcNode with' SeLe4n/Kernel/Capability/Operations.lean
run_check "INVARIANT" rg -n '^theorem ipcTransferSingleCap_installed_implies_revocable_source' SeLe4n/Kernel/Capability/Operations.lean
# The condition is revocation's own precondition, not a second opinion about it:
# a change to what revocation requires breaks these rather than widening the check.
run_check "INVARIANT" rg -n '^theorem cspaceRevoke_ok_implies_slot_occupied' SeLe4n/Kernel/Capability/Operations.lean
run_check "INVARIANT" rg -n '^theorem cdtNodeIsRevocable_false_revoke_refuses' SeLe4n/Kernel/Capability/Operations.lean
# The mapping-only test must not come back at the install site.
run_negative_check "INVARIANT" rg -n 'match SystemState.lookupCdtSlotOfNode st srcNode with' SeLe4n/Kernel/Capability/Operations.lean
# The regression carries both load-bearing negatives: the mapping survives the
# sweep (so the old check would have passed) and the in-flight consumption does
# not reach a swept sibling (so this is a second hole, not the first restated).
run_check "INVARIANT" rg -n '^private def revokeSweptSiblingBlocksPendingTransfer' tests/OperationChainSuite.lean
run_check "INVARIANT" rg -n 'the CDT mapping outlived the capability' tests/OperationChainSuite.lean
run_check "INVARIANT" rg -n 'the consumption sweep did not reach it' tests/OperationChainSuite.lean
# NEGATIVE: the CNode retype arm must not go back to branching on the
# replacement's shape — both shapes destroy the old slots, so both must detach.
run_negative_check "INVARIANT" rg -n 'CNode → CNode: no CDT cleanup needed' SeLe4n/Kernel/Lifecycle/Operations/CleanupPreservation.lean
# The load-bearing negative: the parked source provably has NO CDT child, so the
# old guard would have permitted the delete and the new predicate is doing the work.
run_check "INVARIANT" rg -n 'chain12b: NEGATIVE . the parked source has no CDT child yet' tests/OperationChainSuite.lean
run_check "INVARIANT" rg -n 'chain12b: deleting the source of a parked transfer is REFUSED' tests/OperationChainSuite.lean
run_check "INVARIANT" rg -n 'chain12b: NEGATIVE . an unrelated slot in the same CNode still deletes' tests/OperationChainSuite.lean
# PR #873 review round 4: the flow fold reads every source from the PRE-state, so
# a transfer's root-to-root edge cannot chain into a root-to-subject edge within
# one commit.  The receiving subject is therefore sourced from the sender's root
# directly, or a courier's provenance never reaches a downgrading subject.
# …and the CSpace sinks are GATED on capabilities actually crossing.  Ungated,
# a plain message writes the sender's provenance into a CNode no capability
# reached, and — since a root now feeds the consuming subject — an unrelated
# later downgrade could name it as an UNSATURATED predecessor, which is exactly
# what `staleTaint_is_not_saturation` rules out.
run_negative_check "INVARIANT" rg -n '^def sendCarriesCaps' SeLe4n/Kernel/InformationFlow/TaintPropagation.lean
run_check "INVARIANT" rg -n 'NEGATIVE: a send declares no CSpace-root sink or source' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'NEGATIVE: no rendezvous declares a CSpace-root sink, caps or not' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'EVERY taint write key is write-locked by the send footprint' tests/SmpInformationFlowSuite.lean
# …a clear is FINAL within its commit: the final origination pass skips cleared
# keys, so a declassifying signal that delivers straight to a waiter cannot
# re-tag the transport it just emptied.
run_check "INVARIANT" rg -n '^theorem applySyscallTaint_cleared_empty' SeLe4n/Kernel/InformationFlow/TaintPropagation.lean
run_check "INVARIANT" rg -n 'a cleared object stays empty even when the commit recorded a downgrade' tests/SmpInformationFlowSuite.lean
# …and a BOUND delivery clears NOTHING.  `boundDeliveryTarget?` ignores
# `pendingBadge` and `notificationSignalBound` never writes the notification, so
# an unconditional clear discarded the provenance of a badge the object still
# holds — a MISSED chain, the direction a detector must never err in.
run_check "INVARIANT" rg -n '^def signalClearedNotification' SeLe4n/Kernel/InformationFlow/TaintPropagation.lean
run_check "INVARIANT" rg -n 'NEGATIVE: a bound delivery clears no notification taint' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'a waiter delivery still empties the notification' tests/SmpInformationFlowSuite.lean
# PR #873 review: the CONTENT-DERIVED transport model.  A transport's taint
# reflects the content it currently holds: an endpoint is not a sink at all (it
# buffers no content — the message is in the blocked sender's TCB, and the
# receiver reads the head sender directly), and a consumed notification is
# cleared.  Without this a reused endpoint links causally-unrelated messages —
# a false positive that is NOT saturation.
run_check "INVARIANT" rg -n '^def contentFlowClears' SeLe4n/Kernel/InformationFlow/TaintPropagation.lean
run_check "INVARIANT" rg -n '^theorem waitClearsNotificationTaint' SeLe4n/Kernel/InformationFlow/TaintPropagation.lean
run_check "INVARIANT" rg -n '^theorem taintPropagation_receive_from_sender' SeLe4n/Kernel/InformationFlow/TaintPropagation.lean
run_check "INVARIANT" rg -n 'NEGATIVE: the endpoint is not among the declared sinks at all' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'NEGATIVE: the endpoint itself carries no identity' tests/SmpInformationFlowSuite.lean
run_check "TRACE" rg -n 'transportUntouched=' tests/fixtures/smp_information_flow.expected
# …and the endpoint-proxy forms must not come back: they ARE the stale-transport
# false positive, so a regression that re-adds an endpoint sink or an
# endpoint-sourced receive would restore it.
run_negative_check "INVARIANT" rg -n 'theorem taintPropagation_send_to_endpoint' SeLe4n/Kernel/InformationFlow/TaintPropagation.lean
run_negative_check "INVARIANT" rg -n 'theorem taintPropagation_receive_from_endpoint' SeLe4n/Kernel/InformationFlow/TaintPropagation.lean
# PR #873 review: the tracked-content SCOPE, stated as a value and tied to the
# gate's own channel list, with the one deliberate exclusion (a capability badge
# is authority metadata, not payload) recorded as a theorem rather than prose.
run_check "INVARIANT" rg -n '^def contentTrackedFields' SeLe4n/Kernel/InformationFlow/TaintPropagation.lean
run_check "INVARIANT" rg -n '^theorem capabilityBadgeChannel_out_of_scope' SeLe4n/Kernel/InformationFlow/TaintPropagation.lean
run_check "BUILD" rg -n 'def check_scope_matches_lean' scripts/check_content_flow_coverage.py
# PR #873 review: the hot-path elision — a value-preserving join must not extend
# the table's closure chain, which ordinary untainted IPC would otherwise do on
# every edge.
run_check "INVARIANT" rg -n '^theorem joinAt_eq_of_join_eq' SeLe4n/Kernel/InformationFlow/Taint.lean
# SM9.D.9 (audit): the replyRecv REPLY leg — the steady-state server loop's
# second hop, which a receive-leg-only plan under-approximates (the unsafe
# direction for a detector).  The resolution mirrors `resolveReplyRecvReply`
# step for step, sharing `replyTaintEdges` with the `.reply` arm so the two
# cannot drift.
run_check "INVARIANT" rg -n '^def replyRecvReplyLegEdges' SeLe4n/Kernel/InformationFlow/TaintPropagation.lean
run_check "INVARIANT" rg -n '^theorem taintPropagation_replyRecv_reply_to_prevCaller' SeLe4n/Kernel/InformationFlow/TaintPropagation.lean
run_check "INVARIANT" rg -n 'the replyRecv plan names the reply object.s recorded caller as a sink' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'NEGATIVE: the receive-leg edges alone miss the recorded caller' tests/SmpInformationFlowSuite.lean
# SM9.D.14 (audit): the monitor's own inference direction — every read 1 ⇒ the
# view is causal — alongside the forward reconstruction.
run_check "INVARIANT" rg -n '^theorem declassificationChainCausal_of_pairwise' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
run_check "INVARIANT" rg -n '^theorem chainVerdict_all_ok_causal' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
# PR #873 review: the flow sources are SEEDED with this commit's own origination,
# so a syscall that both declassifies and delivers (`.declassifySignal`, whose
# second hop is an ordinary delivery) carries the fresh event's tag to the object
# the delivery reached.  Reading the raw pre-table there loses the successor —
# a MISSED chain, the direction a detector must never err in.
run_check "INVARIANT" rg -n 'applyOrigination \(planOriginationTags plan pre post\)' SeLe4n/Kernel/InformationFlow/TaintPropagation.lean
# SM9.D.17 (audit): the pre-existing cap-transfer footprint gap — the receiver's
# CSpace root, which `ipcUnwrapCaps` writes with no declared CNode write lock —
# as a registered domain (owner recorded in the inventory itself) with its
# violation witness and the honest §12.8 partition.
run_check "INVARIANT" rg -n 'capTransferReceiverCnode' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^theorem capTransfer_receiverCnode_write_undeclared' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n 'GAP .registered lock-inventory debt.: the receiver.s CSpace root is NOT write-locked' tests/SmpInformationFlowSuite.lean
# The carve-out is gone: with the cap-transfer sink deleted, the receiver's
# CSpace root is no longer a taint write key at all, so the send's coverage claim
# is unconditional.  The registered domain above still records the underlying
# footprint gap, which is a fact about `ipcUnwrapCaps`, not about taint.
run_check "INVARIANT" rg -n 'EVERY taint write key is write-locked by the send footprint' tests/SmpInformationFlowSuite.lean

# WS-SM SM9.D.17 (audit): the taint table's per-key realisation is a registered
# domain rather than a paragraph.  The footprints declare each taint key's own
# object lock while the model replaces the field whole, so key-local locking is
# sound only once the runtime stores per object — owed by the representation cut.
# Registered so that enabling fine locks has to delete the entry deliberately.
run_check "INVARIANT" rg -n 'taintTablePerKeyStore' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
# The owner string is pinned as *present*, not as a literal: spelling the
# workstream code here would put it in a non-documentation file, which the
# identifier-naming gate forbids.  That it is non-empty is checked properly, by
# the suite's `declaredFootprintUncoveredDomains.all (fun d => !d.2.isEmpty)`.
run_check "INVARIANT" rg -n '\(\.taintTablePerKeyStore, "' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
# SM9.D.7 (audit): the gate's direct-field-writer sweep — check (C) names only
# constants that USE the taint API; (C2) scans every definition for a direct
# write of `declassificationTaint` through the structure's constructor, in any
# spelling (PR #873 round 12 dropped the `{ st with .. }` test that a positional
# rebuild walked past), and the self-test asserts the sweep detects the one
# declared writer so blindness cannot pass.
run_check "BUILD" rg -n 'DECLARED_FIELD_WRITERS' scripts/check_content_flow_coverage.py
run_check "BUILD" rg -n 'CF_FIELD_WRITER' scripts/check_content_flow_coverage.py
run_check "BUILD" rg -n 'cfWritesField' scripts/check_content_flow_coverage.py
# The rule inventory records the NEW claim in place of the retired one; the
# count is unchanged, so the replacement is 1:1 rather than an addition.
run_check "INVARIANT" rg -n 'chainLinkageIsCausal' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
run_check "INVARIANT" rg -n '^theorem declassificationRules_count : DeclassificationRuleId.all.length = 12' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
# The RETIRED claim must not come back: SM8.C's `…_is_syntactic` asserted
# exactly what SM9.D falsifies, and its rule id with it.
run_negative_check "INVARIANT" rg -n 'declassificationChainLinked_is_syntactic' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean
run_negative_check "INVARIANT" rg -n 'chainLinkageIsSyntactic' SeLe4n/Kernel/InformationFlow/DeclassificationPerCore.lean

# SM9.D.17: the SERIALIZATION SUBJECT.  The taint table is keyed by `ObjId`, so
# — exactly as for `SystemState.objects`, whose per-key writes ride the
# object's own lock and never `objStoreLock` — the subject is the lock the
# transition already holds on the key.  Putting the level-0 singleton on the
# eight content-moving syscalls would serialise every IPC in the system against
# every other and blow the SM5.J tick budget the IPC fixtures pin, so the
# absence of that lock on the hot path is pinned NEGATIVELY.
run_check "INVARIANT" rg -n '^def taintWriteKeys' SeLe4n/Kernel/InformationFlow/TaintPropagation.lean
run_check "INVARIANT" rg -n '^theorem applySyscallTaint_frame_off_writeKeys' SeLe4n/Kernel/InformationFlow/TaintPropagation.lean

# The origination keys are serialised by their own object locks, not by the
# trail's state-level lock: `stateLevelLock` orders this transition against
# other state-level writers only, while an ordinary IPC writing the same taint
# key holds that key's lock and no state-level lock at all.
run_check "INVARIANT" rg -n '^theorem lockSet_declassify_originationKeys_write_mem' SeLe4n/Kernel/Concurrency/Locks/LockSetTransitions.lean
run_check "INVARIANT" rg -n 'targetLock : Option LockId' SeLe4n/Kernel/Concurrency/Locks/LockSetTransitions.lean
# The aggregate bound must quantify over the new member, or the resolved shape
# is silently unbounded at the defaulted `none` — the SM9.C notificationSignal defect.
run_check "INVARIANT" rg -n 'lockSet_declassify a b t\).size' SeLe4n/Kernel/Concurrency/Locks/Deadlock.lean

# Provenance follows content through the frozen operations, not only across the
# freeze itself — a snapshot that stopped propagating one operation later would
# report every recorded downgrade as causally unconnected.
run_check "INVARIANT" rg -n '^private def frozenTaintFlow' SeLe4n/Kernel/FrozenOps/Operations.lean
run_check "INVARIANT" rg -n '^private def frozenTaintClear' SeLe4n/Kernel/FrozenOps/Operations.lean
run_check "INVARIANT" rg -n 'signaller : SeLe4n\.ThreadId' SeLe4n/Kernel/FrozenOps/Operations.lean
# NEGATIVE: the replier is the content source of a frozen reply, so it must not
# go back to being an unused parameter.
run_negative_check "INVARIANT" rg -n 'frozenEndpointReply \(_replierId' SeLe4n/Kernel/FrozenOps/Operations.lean
run_check "INVARIANT" rg -n '^theorem taintWriteKeys_disjoint_updates_independent' SeLe4n/Kernel/InformationFlow/TaintPropagation.lean
run_check "INVARIANT" rg -n '^theorem taintWriteKeys_of_no_events' SeLe4n/Kernel/InformationFlow/TaintPropagation.lean
# Pinned positively at the send's base list, whose last member is the endpoint:
# appending the level-0 singleton here is exactly the regression, and it breaks
# this anchor.  (`stateLevelLock` still appears in the file — on the three
# footprints that write the audit TRAIL, whose `List` append does not
# decompose by key — so a file-wide negative would be wrong.)
run_check "INVARIANT" rg -n '^       \(endpointLock endpointObjId, .write\)\]\)$' SeLe4n/Kernel/Concurrency/Locks/LockSetTransitions.lean
run_check "INVARIANT" rg -n '^theorem taintWriteKeys_inert' SeLe4n/Kernel/InformationFlow/TaintPropagation.lean
# SM9.D.18: the propagation is framed to one field and visible to no observer,
# so every existing invariant argument and every NI result stands unchanged.
run_check "INVARIANT" rg -n '^theorem applySyscallTaint_frame' SeLe4n/Kernel/InformationFlow/TaintPropagation.lean
run_check "INVARIANT" rg -n '^theorem applySyscallTaint_preserves_projection' SeLe4n/Kernel/InformationFlow/TaintPropagation.lean
run_check "INVARIANT" rg -n '^theorem applySyscallTaint_confinedToCores_nil' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^theorem applySyscallTaint_preserves_onCore' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean
run_check "INVARIANT" rg -n '^theorem applySyscallTaint_preserves_proofLayerInvariantBundle' SeLe4n/Kernel/InformationFlow/FineLockFlow.lean

# SM9.D tests: the eight runtime groups, their load-bearing negatives, the
# surface anchors and the golden-fixture lines.
run_check "INVARIANT" rg -n 'NEGATIVE: a ninth identity saturates, and the top reports one nobody held' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'NEGATIVE: a domain-only detector fires on a causally unrelated pair' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'NEGATIVE: an object-adjacency detector MISSES the real chain' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'an ORDINARY delivery — no declassification edge — carried it to the next subject' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'NEGATIVE: a framed retype would keep them, and the stale tag is NOT a saturation' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'the content-moving footprints do NOT declare the coarse table lock' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'NEGATIVE: a disjoint plan leaves this plan.s keys literally unchanged' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'SCOPE: the residual over-approximation is saturation, and only that' tests/SmpInformationFlowSuite.lean
run_check "TRACE" rg -n 'taint classification: moving=' tests/fixtures/smp_information_flow.expected
run_check "TRACE" rg -n 'taint propagation: liveReceiverTagged=' tests/fixtures/smp_information_flow.expected
run_check "TRACE" rg -n 'causal chain: causal=' tests/fixtures/smp_information_flow.expected
run_check "TRACE" rg -n 'taint saturation: full=8' tests/fixtures/smp_information_flow.expected

# ============================================================================
# WS-SM SM9.E — tests + closure
# (plan SMP_DECLASSIFICATION_COMPLETION_PLAN.md §4 SM9.E.1 … SM9.E.6).
# ============================================================================
# SM9.E adds no transition and no module.  Its subject is the phase's own
# acceptance criteria, run end to end and pinned byte-for-byte: the epoch
# EXERCISED against surviving entries, the refusal seam covering BOTH
# declassifying syscalls at the dispatch boundary, and the two
# acceptance-scenario golden fixtures.  The two retirement negatives the plan
# lists under this sub-phase — SM9.B.10's `refusalIsUnrecorded` and SM9.D.15's
# `declassificationChainLinked_is_syntactic` — and the negative against a
# hardcoded `.declassify` seam filter landed with their sub-phases and stand
# in the SM9.B / SM9.D blocks above.

# SM9.E.2: the epoch exercised — the runtime group whose recording runs LIVE
# against a partially-drained trail with survivors present.
run_check "INVARIANT" rg -n '^  runPostDrainRecordingFreshnessChecks' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'the LIVE recording after it is stamped 3' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'NEGATIVE: the pre-epoch rule would have stamped it 2' tests/SmpInformationFlowSuite.lean
# SM9.E.2: the seam's boundary coverage, and the pinned refusal classes.  The
# two pre-existing dispatch-level checks exercise the checked entry's
# OUTERMOST refusal and now say so explicitly, so the class of refusal every
# dispatch-level check covers is part of its assertion.
run_check "INVARIANT" rg -n '^  runDeclassifyingSeamBoundaryChecks' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'the denied signal.s frame is exactly the receiver refusal.s error frame' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'the denied declassify at the same state is the POLICY.s refusal, recorded receiverless' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'NEGATIVE: neither refusal wrote the trail' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'the seam.s classification admits exactly the two declassifying syscalls' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'recorded.reason = KernelError.policyDenied' tests/SmpInformationFlowSuite.lean

# SM9.E.2a: the causal acceptance scenario landed with SM9.D; the closure pins
# its criterion lines — the causal chain, the lifecycle case, and the
# same-domain distinction only recorded snapshots can make.  PR #874 review:
# the chain's middle step and the whole lifecycle case run through the LIVE
# checked entry (whose taint seam is the behaviour under test), so a hand-built
# propagation edge in the acceptance fixtures is a refuted shape.
run_check "INVARIANT" rg -n 'hop 2.s recorded snapshot therefore names hop 1' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'syscallEntryChecked declassChainEntryLabeling' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'the live retype cleared the tainted object.s provenance' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'the lifecycle case: the downgrade from the replacement names nothing' tests/SmpInformationFlowSuite.lean
run_negative_check "INVARIANT" rg -n 'edges := ..sink := lowCurrent.toObjId, source := declassTargetA' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n 'NEGATIVE: two same-domain second hops are distinguished by their snapshots' tests/SmpInformationFlowSuite.lean

# SM9.E.3: the two golden fixtures, their hash companions, their in-suite
# byte-for-byte checks, and the acceptance values they pin.
run_check "TRACE" rg -n '^\[declassification-reader\]' tests/fixtures/declassification_reader.expected
run_check "TRACE" rg -n 'declassification_reader\.expected' tests/fixtures/declassification_reader.expected.sha256
run_check "TRACE" rg -n '^\[declassification-taint\]' tests/fixtures/declassification_taint.expected
run_check "TRACE" rg -n 'declassification_taint\.expected' tests/fixtures/declassification_taint.expected.sha256
run_check "INVARIANT" rg -n '^  runDeclassificationReaderFixtureCheck' tests/SmpInformationFlowSuite.lean
run_check "INVARIANT" rg -n '^  runDeclassificationTaintFixtureCheck' tests/SmpInformationFlowSuite.lean
run_check "TRACE" rg -n 'cliff fill: capacity=256 filled=256' tests/fixtures/declassification_reader.expected
run_check "TRACE" rg -n 'cliff recovery: postDrainRecords=1 freshTimestamp=256 wellFormed=true' tests/fixtures/declassification_reader.expected
run_check "TRACE" rg -n 'epoch survivors: survivorStamps=.1, 2. recordedStamp=3 survivorCollision=false' tests/fixtures/declassification_reader.expected
run_check "TRACE" rg -n 'seam boundary: signalReason=56 signalReceiver=1021 declassifyReason=14 recordingSyscalls=2' tests/fixtures/declassification_reader.expected
run_check "TRACE" rg -n 'causal verdicts: causal=true launders=true domainOnlyFalsePositive=true adjacencyFalseNegative=true snapshotsDistinguishSameDomain=true' tests/fixtures/declassification_taint.expected
run_check "TRACE" rg -n 'lifecycle: liveRetypeCleared=true replacementDeliveryClean=true replacementDowngradeNamesNothing=true' tests/fixtures/declassification_taint.expected
run_check "TRACE" rg -n 'monitor verdict: word=1 strippedWord=0' tests/fixtures/declassification_taint.expected

# SM9.E.4: the closure block in the surface-anchor suite — the four sub-phase
# headliners standing together, and the seam-coverage facts decided there.
run_check "INVARIANT" rg -n 'the four sub-phase headliners stand together' tests/SmpSurfaceAnchors.lean
run_check "INVARIANT" rg -n 'the epoch discipline and the seam.s coverage of both declassifying syscalls' tests/SmpSurfaceAnchors.lean

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
run_check "INVARIANT" rg -n '^\s*\| ipcMessageTooLarge' SeLe4n/Model/KernelError.lean
run_check "INVARIANT" rg -n '^\s*\| ipcMessageTooManyCaps' SeLe4n/Model/KernelError.lean
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
# WS-RA (RA.E.5): the bit-63 protocol is RETIRED — `encodeOk` / `encodeError`
# must not come back as definitions anywhere in the production tree (the
# retained hazard statement is `bit63Encoding_not_injective_on_badges`, which
# names them only in prose).  Errors ride the offset x1 label
# (`Architecture.errorFrame`); the value channel is full-width x0.
run_negative_check "INVARIANT" rg -n 'def encodeError' SeLe4n/Platform/FFI.lean
run_negative_check "INVARIANT" rg -n 'def encodeOk' SeLe4n/Platform/FFI.lean
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
# WS-RA: the vestigial `syscall_dispatch_inner` export is REMOVED (it was the
# last other speaker of the retired bit-63 protocol; no Rust source declared
# the symbol since v0.31.67).  Negative anchor so a dead export cannot return.
run_negative_check "INVARIANT" rg -n '@\[export syscall_dispatch_inner\]' SeLe4n/Platform/FFI.lean
# WS-SM SM6.A (v0.31.67): the cross-core SGI-firing dispatch entry
# `lean_syscall_dispatch_cross_core` (`SyscallDispatchEntry`) is PROMOTED to the
# production library (`SeLe4n.lean`) with its `PriorityInheritance.PerCore` +
# `Concurrency.Runtime` closure, and the Rust extern is flipped to it (line 993):
# the live syscall fires the diff-recovered cross-core `.reschedule` SGIs.
# (WS-RA removed the vestigial boot-pinned `syscall_dispatch_inner`.)
run_check "INVARIANT" rg -n '^@\[export lean_syscall_dispatch_cross_core\]' SeLe4n/Kernel/SyscallDispatchEntry.lean
run_check "INVARIANT" rg -n '^def suspendThreadInner' SeLe4n/Platform/FFI.lean
run_negative_check "INVARIANT" rg -n '^def syscallDispatchInner' SeLe4n/Platform/FFI.lean
# WS-RA: the convention model + the staging seam (RA.A / RA.B.1-B.2 / RA.B.5a).
run_check "INVARIANT" rg -n '^def syscallReturnShape' SeLe4n/Kernel/Architecture/SyscallReturn.lean
run_check "INVARIANT" rg -n '^theorem syscallReturnShape_value_returning' SeLe4n/Kernel/Architecture/SyscallReturn.lean
run_check "INVARIANT" rg -n '^theorem returnShape_list_gate_insufficient' SeLe4n/Kernel/Architecture/SyscallReturn.lean
run_check "INVARIANT" rg -n '^theorem errorLabel_never_zero' SeLe4n/Kernel/Architecture/SyscallReturn.lean
run_check "INVARIANT" rg -n '^theorem errorLabel_roundtrip' SeLe4n/Kernel/Architecture/SyscallReturn.lean
run_check "INVARIANT" rg -n '^theorem kernelErrorFitsLabel' SeLe4n/Kernel/Architecture/SyscallReturn.lean
run_check "INVARIANT" rg -n '^theorem bit63Encoding_not_injective_on_badges' SeLe4n/Kernel/Architecture/SyscallReturn.lean
run_check "INVARIANT" rg -n '^def syscallAbiVersion : Nat := 2' SeLe4n/Kernel/Architecture/SyscallReturn.lean
run_check "INVARIANT" rg -n '^def writeReturnFrameToTcb' SeLe4n/Kernel/Architecture/SyscallReturn.lean
run_check "INVARIANT" rg -n '^def readReturnFrame' SeLe4n/Kernel/Architecture/SyscallReturn.lean
run_check "INVARIANT" rg -n '^theorem readReturnFrame_writeReturnFrame' SeLe4n/Kernel/Architecture/SyscallReturn.lean
run_check "INVARIANT" rg -n '^def stageDeliveredMessage' SeLe4n/Kernel/Architecture/SyscallReturn.lean
# WS-RA RA.B.5b: the blocked-waiter staging seam — the Option-lifted stagers
# the unblocking arms compose, the plan-named theorem, and its unit dual.
run_check "INVARIANT" rg -n '^def stageWokenDelivery' SeLe4n/Kernel/Architecture/SyscallReturn.lean
run_check "INVARIANT" rg -n '^def stageWokenSendCompletion' SeLe4n/Kernel/Architecture/SyscallReturn.lean
run_check "INVARIANT" rg -n '^theorem stageWokenSendCompletion_stages_zero' SeLe4n/Kernel/Architecture/SyscallReturn.lean
run_check "INVARIANT" rg -n '^theorem blockedReturn_staged_in_waiter_frame' SeLe4n/Kernel/Architecture/SyscallReturn.lean
run_check "INVARIANT" rg -n '^theorem blockedUnitReturn_staged_in_sender_frame' SeLe4n/Kernel/Architecture/SyscallReturn.lean
run_check "INVARIANT" rg -n '^theorem stageWokenDelivery_preserves_projection' SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean
run_check "INVARIANT" rg -n '^theorem stageWokenSendCompletion_preserves_projection' SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean
# WS-RA RA.B.8: the per-arm shape-coherence family — the classification and
# the live dispatch arms cannot disagree (`.call` through the reply arm, §3.5).
run_check "INVARIANT" rg -n '^theorem dispatchArm_notificationWait_matches_returnShape' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n '^theorem dispatchArm_serviceQuery_matches_returnShape' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n '^theorem dispatchArm_receive_matches_returnShape' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n '^theorem dispatchArm_replyRecv_matches_returnShape' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n '^theorem dispatchArm_call_frame_delivered_by_reply' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n '^def syscallReturnOutcome' SeLe4n/Platform/FFI.lean
run_check "INVARIANT" rg -n '^theorem readReturnValue_eq_readReturnFrame_x0' SeLe4n/Platform/FFI.lean
run_check "INVARIANT" rg -n '^theorem writeReturnFrameToTcb_preserves_projection' SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean
run_check "INVARIANT" rg -n '^theorem stageDeliveredMessage_preserves_projection' SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean
run_check "INVARIANT" rg -n '^theorem syscallDispatchFromAbi_error_stages_no_frame' SeLe4n/Platform/FFI.lean
run_check "INVARIANT" rg -n 'ffi_syscall_return_frame' rust/sele4n-hal/src/ffi.rs
run_check "INVARIANT" rg -n 'pub const SYSCALL_ABI_VERSION: u64 = 2' rust/sele4n-types/src/lib.rs
# PR #866 review: the Blocked trap arm must poison the frame with the
# fail-closed blocked-resume sentinel until the context-restore seam
# installs a successor — a silent revert to the no-op arm re-opens the
# false-success decode of the caller's own stale request registers.
run_check "INVARIANT" rg -n 'pub const BLOCKED_RESUME_SENTINEL_LABEL' rust/sele4n-hal/src/svc_dispatch.rs
run_check "INVARIANT" rg -n 'pub fn blocked_resume_sentinel_regs' rust/sele4n-hal/src/svc_dispatch.rs
run_check "INVARIANT" rg -n 'blocked_resume_sentinel_regs' rust/sele4n-hal/src/trap.rs
run_check "INVARIANT" rg -n 'fn blocked_resume_sentinel_decodes_fail_closed' rust/sele4n-hal/src/svc_dispatch.rs
# PR #866 round-2: the return-frame mailbox and the kernel-entry bracket key
# on the TPIDR-derived LOGICAL core index (the boot-validated slot space the
# Lean dispatch's executingCore lives in) — the packed MPIDR value must not
# come back as an index (out-of-range on a second-cluster core: mailbox
# bounds abort + silently disabled shootdown self-service).
run_check "INVARIANT" rg -n 'per_cpu::current_core_id_from_tpidr' rust/sele4n-hal/src/svc_dispatch.rs
run_check "INVARIANT" rg -n 'per_cpu::current_core_id_from_tpidr' rust/sele4n-hal/src/ffi.rs
run_negative_check "INVARIANT" rg -n 'crate::cpu::current_core_id' rust/sele4n-hal/src/svc_dispatch.rs
run_negative_check "INVARIANT" rg -n 'crate::cpu::current_core_id' rust/sele4n-hal/src/ffi.rs
# PR #866 round-2: the staged extraCaps is the transfer summary's INSTALLED
# count, never the requested msg.caps.size.
run_check "INVARIANT" rg -n '^def installedCount' SeLe4n/Model/Object/Types.lean
run_check "INVARIANT" rg -n '^theorem returnMessageInfo_extraCaps_le_installed' SeLe4n/Kernel/Architecture/SyscallReturn.lean
run_negative_check "INVARIANT" rg -n 'extraCaps := min msg.caps.size' SeLe4n/Kernel/Architecture/SyscallReturn.lean
# PR #866 round-2: the query wrapper returns the typed ServiceId.
run_check "INVARIANT" rg -n 'pub fn service_query\(endpoint_cap: CPtr\) -> KernelResult<ServiceId>' rust/sele4n-sys/src/service.rs
# PR #866 round-3: the prefilter conformance sweep drives the REAL wrappers
# (host-capture mock trap) against the REAL HAL minima (dev-dep) — the
# hand-duplicated table that drifted twice must not come back, and the
# `.message`-shaped call wrapper carries the badge tuple like its siblings.
run_check "INVARIANT" rg -n 'pub mod host_capture' rust/sele4n-abi/src/trap.rs
run_check "INVARIANT" rg -n 'fn wrapper_lengths_clear_prefilter_minimums' rust/sele4n-abi/tests/conformance.rs
run_check "INVARIANT" rg -n 'host_capture::last_request' rust/sele4n-abi/tests/conformance.rs
run_check "INVARIANT" rg -n 'min_inline_args' rust/sele4n-abi/tests/conformance.rs
run_check "INVARIANT" rg -n 'pub fn endpoint_call\(dest: CPtr, msg: &IpcMessage\) -> KernelResult<\(Badge, SyscallResponse\)>' rust/sele4n-sys/src/ipc.rs
# PR #866 round-3: the three wrappers the ABI documented but never had —
# implemented so the sweep covers the whole canonical syscall surface.
run_check "INVARIANT" rg -n 'pub fn tcb_bind_notification' rust/sele4n-sys/src/tcb.rs
run_check "INVARIANT" rg -n 'pub fn tcb_unbind_notification' rust/sele4n-sys/src/tcb.rs
run_check "INVARIANT" rg -n 'pub fn mint_reply_cap' rust/sele4n-sys/src/cspace.rs
# The retired bit-63 theorems must not come back either.
run_negative_check "INVARIANT" rg -n 'theorem encodeError_high_bit_set' SeLe4n/Platform/FFI.lean
run_negative_check "INVARIANT" rg -n 'theorem encodeOk_high_bit_clear' SeLe4n/Platform/FFI.lean
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
# it.  (WS-RA removed the vestigial boot-pinned `syscall_dispatch_inner`.)
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
# WS-SM SM1.C.6 adds the secondary-core kernel entry
# (Kernel.SecondaryEntry.secondaryKernelMain — definitionally the
# per-core reschedule entry since the reschedule-receiver seam
# completion — with the seam-identity + body-shape marker theorems
# and the verified perCoreRescheduleStep it commits).
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
-- SM1.C.6 — Secondary-core kernel entry (closes SMP-C2 Lean side;
-- bring-up is definitionally the first reschedule on the onlined core)
#check @SeLe4n.Kernel.secondaryKernelMain
#check @SeLe4n.Kernel.secondaryKernelMain_eq_perCoreRescheduleEntry
#check @SeLe4n.Kernel.secondaryKernelMain_def
#check @SeLe4n.Kernel.perCoreRescheduleEntry
#check @SeLe4n.Kernel.perCoreRescheduleEntry_def
#check @SeLe4n.Kernel.perCoreRescheduleStep
#check @SeLe4n.Kernel.perCoreRescheduleStep_invalid_core
#check @SeLe4n.Kernel.perCoreRescheduleStep_ok
#check @SeLe4n.Kernel.perCoreRescheduleStep_error
#check @SeLe4n.Kernel.perCoreRescheduleStep_preserves_objects_invExt
#check @SeLe4n.Kernel.perCoreRescheduleStep_preserves_runQueue_wellFormed
#check @SeLe4n.Kernel.perCoreRescheduleStep_switches_current
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
#check @perCoreTimerTickStep_domain_error
#check @perCoreTimerTickStep_sgis_eq_tick
#check @perCoreTimerTickStep_preserves_objects_invExt
#check @perCoreTimerTickStep_ok_currentThreadValidOnCore
#check @tickClockedState
#check @tickClockedState_objects
#check @tickClockedState_scheduler
#check @tickClockedState_bootCore_timer
#check @tickClockedState_nonBoot
#check @scheduleDomainOnCore_preserves_currentThreadValidOnCore
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
