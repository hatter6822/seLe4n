#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck disable=SC1091
source "${SCRIPT_DIR}/test_lib.sh"

parse_common_args "$@"
cd "${REPO_ROOT}"

# Invariant bundle surface anchors (M1/M2/M3 composed entrypoints).
run_check "INVARIANT" rg -n '^(def|abbrev) schedulerInvariantBundle' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n '^def capabilityInvariantBundle' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n '^def m3IpcSeedInvariantBundle' SeLe4n/Kernel/API.lean

# M3 seed IPC preservation theorem anchors.
run_check "INVARIANT" rg -n '^theorem endpointSend_preserves_m3IpcSeedInvariantBundle' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n '^theorem endpointReceive_preserves_m3IpcSeedInvariantBundle' SeLe4n/Kernel/API.lean

# Bundle composition guard: M3 seed bundle must still compose scheduler + capability + IPC invariants.
run_check "INVARIANT" rg -n '^\s*schedulerInvariantBundle st ∧ capabilityInvariantBundle st ∧ ipcInvariant st' SeLe4n/Kernel/API.lean

# M3.5 step-1 state-model anchors must remain present.
run_check "INVARIANT" rg -n '^inductive ThreadIpcState' SeLe4n/Model/Object.lean
run_check "INVARIANT" rg -n '^\s*ipcState\s*:\s*ThreadIpcState' SeLe4n/Model/Object.lean
run_check "INVARIANT" rg -n '^\s*waitingReceiver\s*:\s*Option SeLe4n\.ThreadId' SeLe4n/Model/Object.lean
run_check "INVARIANT" rg -n '^def endpointQueueWellFormed' SeLe4n/Kernel/API.lean
run_check "INVARIANT" rg -n '^def endpointObjectValid' SeLe4n/Kernel/API.lean

# Active milestone docs should stay synchronized for both current and next slices.
run_check "DOC" rg -n 'M3\.5' README.md docs/SEL4_SPEC.md docs/DEVELOPMENT.md
run_check "DOC" rg -n 'M4' README.md docs/SEL4_SPEC.md docs/DEVELOPMENT.md

# Full-suite contract should continue to include Tier 3.
run_check "DOC" rg -n 'test_tier3_invariant_surface\.sh' scripts/test_full.sh

finalize_report
