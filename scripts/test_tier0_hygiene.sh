#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck disable=SC1091
source "${SCRIPT_DIR}/test_lib.sh"

parse_common_args "$@"
cd "${REPO_ROOT}"

# Scan for forbidden markers (axiom, sorry, TODO) in production proof surface.
# Lines annotated with a TPI-D* reference are explicitly tracked proof obligations
# and are excluded from this check (see AUDIT_v0.11.0_TRACKED_PROOF_ISSUES.md).
if command -v rg >/dev/null 2>&1; then
  run_check "HYGIENE" bash -lc 'if rg -n -w "axiom|sorry|TODO" SeLe4n Main.lean | grep -v "TPI-D[0-9]"; then echo "Forbidden markers found in tracked proof surface." >&2; exit 1; fi'
else
  log_section "HYGIENE" "ripgrep (rg) not found; using grep fallback for marker scan."
  run_check "HYGIENE" bash -lc 'if (find SeLe4n -name "*.lean" -print0; printf "Main.lean\0") | xargs -0 grep -nwE "axiom|sorry|TODO" | grep -v "TPI-D[0-9]"; then echo "Forbidden markers found in tracked proof surface." >&2; exit 1; fi'
fi


if command -v rg >/dev/null 2>&1; then
  run_check "HYGIENE" bash -lc 'if rg -n "SeLe4n\.Testing\.RuntimeContractFixtures|SeLe4n\.Testing\.runtimeContract(AcceptAll|DenyAll)" SeLe4n/Kernel; then echo "Test-only runtime contract fixtures leaked into production kernel modules (SeLe4n/Kernel)." >&2; exit 1; fi'
else
  run_check "HYGIENE" bash -lc 'if find SeLe4n/Kernel -name "*.lean" -print0 | xargs -0 grep -nE "SeLe4n\.Testing\.RuntimeContractFixtures|SeLe4n\.Testing\.runtimeContract(AcceptAll|DenyAll)"; then echo "Test-only runtime contract fixtures leaked into production kernel modules (SeLe4n/Kernel)." >&2; exit 1; fi'
fi

if command -v rg >/dev/null 2>&1; then
  run_check "HYGIENE" bash -lc 'if rg -n "abbrev (DomainId|Priority|Irq|Badge|ASID|VAddr|PAddr) := Nat" SeLe4n/Prelude.lean; then echo "WS-B4 regression: remaining scalar wrappers must stay structure-based." >&2; exit 1; fi'
else
  run_check "HYGIENE" bash -lc 'if grep -nE "abbrev (DomainId|Priority|Irq|Badge|ASID|VAddr|PAddr) := Nat" SeLe4n/Prelude.lean; then echo "WS-B4 regression: remaining scalar wrappers must stay structure-based." >&2; exit 1; fi'
fi

run_check "HYGIENE" "${SCRIPT_DIR}/test_docs_sync.sh"

if command -v shellcheck >/dev/null 2>&1; then
  run_check "HYGIENE" shellcheck scripts/*.sh
else
  log_section "HYGIENE" "shellcheck unavailable; optional shell lint not executed in this environment."
fi

finalize_report
