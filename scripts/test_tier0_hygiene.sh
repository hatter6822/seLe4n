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

# L-08 (WS-E1): spot-check theorem-body validation.
# Verify that sampled key preservation theorems have non-trivial proof bodies.
# A theorem is flagged if its body is only `:= by rfl`, `:= rfl`, or contains sorry.
THEOREM_CHECK_TARGETS=(
  "SeLe4n/Kernel/Scheduler/Operations/Preservation.lean"
  "SeLe4n/Kernel/Capability/Invariant/Preservation.lean"
  "SeLe4n/Kernel/IPC/Invariant/EndpointPreservation.lean"
  "SeLe4n/Kernel/IPC/Invariant/Structural.lean"
  "SeLe4n/Kernel/Lifecycle/Invariant.lean"
  "SeLe4n/Kernel/Service/Invariant/Acyclicity.lean"
  "SeLe4n/Kernel/Architecture/VSpaceInvariant.lean"
  "SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean"
  "SeLe4n/Kernel/InformationFlow/Invariant/Composition.lean"
)
if command -v python3 >/dev/null 2>&1; then
  run_check "HYGIENE" python3 "${SCRIPT_DIR}/check_proof_depth.py" "${THEOREM_CHECK_TARGETS[@]}"
else
  log_section "HYGIENE" "python3 not found; using regex fallback for L-08 theorem-body validation."
  L08_FAIL=0
  for target in "${THEOREM_CHECK_TARGETS[@]}"; do
    if [[ ! -f "${target}" ]]; then
      continue
    fi
    if command -v rg >/dev/null 2>&1; then
      if rg -n '\bsorry\b' "${target}" | grep -v 'TPI-D[0-9]' | grep -v '^--' | grep -v '/-' | head -5 | grep -q '.'; then
        log_section "HYGIENE" "L-08 FAIL: sorry found in ${target}"
        L08_FAIL=1
      fi
      if rg -n 'theorem.*preserves.*:=\s*(by\s+)?rfl\s*$' "${target}" | head -5 | grep -q '.'; then
        log_section "HYGIENE" "L-08 FAIL: trivial rfl-only preservation theorem in ${target}"
        L08_FAIL=1
      fi
    fi
  done
  if [[ "${L08_FAIL}" -eq 1 ]]; then
    record_failure "HYGIENE" "L-08: sorry or trivial rfl-only proof found in invariant proof surface (see details above)"
    if [[ "${CONTINUE_MODE}" -eq 0 ]]; then
      finalize_report
    fi
  else
    log_section "HYGIENE" "L-08: theorem-body spot-check passed for invariant proof surface."
  fi
fi

# L-08 supplemental: verify that SHA-pinned GitHub Actions have not regressed to tag-only refs.
if command -v rg >/dev/null 2>&1; then
  # shellcheck disable=SC2016
  run_check "HYGIENE" bash -lc 'if rg -n "uses: [a-zA-Z]+/[a-zA-Z-]+@v[0-9]" .github/workflows/ | rg -v "@[0-9a-f]{40}"; then echo "F-14 regression: GitHub Actions must be SHA-pinned (see docs/CI_POLICY.md)." >&2; exit 1; fi'
fi

if command -v shellcheck >/dev/null 2>&1; then
  run_check "HYGIENE" shellcheck scripts/*.sh
else
  log_section "HYGIENE" "shellcheck unavailable; optional shell lint not executed in this environment."
fi

# Website link protection: verify that all paths referenced by sele4n.org
# (hatter6822.github.io) still exist in the repository tree.  A failure here
# means a rename or deletion would produce 404s on the project website.
run_check "HYGIENE" "${SCRIPT_DIR}/check_website_links.sh"

# AH4-F: Version sync — validate all version-bearing files match lakefile.toml.
run_check "HYGIENE" "${SCRIPT_DIR}/check_version_sync.sh"

# AN10-D: AK7 cascade monotonicity gate. Reads docs/audits/AL0_baseline.txt
# and rejects regressions on any AK7 cascade metric (raw-match site count,
# typed-helper adoption, storeObjectKindChecked adoption, sentinel guard
# coverage, AN10 regression test count).
run_check "HYGIENE" "${SCRIPT_DIR}/ak7_cascade_check_monotonic.sh"

run_check "HYGIENE" python3 -m unittest scripts.tests.test_generate_codebase_map

# WS-I1/R-03: Scenario registry validation — every fixture ID must be in the registry and vice versa.
run_check "HYGIENE" python3 "${SCRIPT_DIR}/scenario_catalog.py" validate-registry \
  --extra-fixtures tests/fixtures/robin_hood_smoke.expected \
  tests/fixtures/two_phase_arch_smoke.expected

# AN4-A (H-02): enforce `SeLe4n.Kernel.Internal.lifecycleRetypeObject` consumer allowlist.
# The internal retype primitive bypasses `lifecyclePreRetypeCleanup` and
# `scrubObjectMemory`; production dispatch must use `lifecycleRetypeWithCleanup`.
# Any `.lean` file that references `Internal.lifecycleRetypeObject` or opens
# `SeLe4n.Kernel.Internal` must appear in `scripts/lifecycle_internal_allowlist.txt`.
run_check "HYGIENE" "${SCRIPT_DIR}/check_lifecycle_internal_allowlist.sh"

# AN7-A (H-14/PLT-M04): enforce that no consumer outside DeviceTree.lean itself
# references the deprecated legacy `findMemoryRegProperty` /
# `classifyMemoryRegion` Option-returning variants.  Callers must use the
# `Checked` variants that propagate DeviceTreeParseError / Option MemoryKind.
run_check "HYGIENE" "${SCRIPT_DIR}/check_devicetree_legacy_consumers.sh"

# AN7-B (H-15): audit every `physicalAddressWidth := N` binding so that
# platform-specific values are explicit and correct (RPi5 = 44, Sim = 52,
# defaults = 52; no `:= 48` VA/PA confusion anywhere).
run_check "HYGIENE" "${SCRIPT_DIR}/check_physical_address_width.sh"

# AN7-F (PLT-L): BCM2712 datasheet reference freshness marker.  Warns (not
# fatal) when the `BCM2712_DATASHEET_VERIFIED` marker in RPi5/Board.lean is
# older than one calendar year.
run_check "HYGIENE" "${SCRIPT_DIR}/check_bcm2712_freshness.sh"

finalize_report
