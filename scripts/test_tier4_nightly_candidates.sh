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

if [[ "${NIGHTLY_ENABLE_EXPERIMENTAL:-0}" != "1" ]]; then
  log_section "META" "Staged candidates: extended determinism seed probe + full suite replay + WS-SM SMP boot-check stub."
  log_section "META" "Note: basic determinism validation is now mandatory in Tier 2 (WS-I1/R-02)."
  # Two different things look alike here and must not be conflated.
  #
  # A *missing prerequisite* (no QEMU, no kernel image) is a gate that was
  # supposed to run and could not: that is NOT RUN, and it propagates.
  # NIGHTLY_ENABLE_EXPERIMENTAL is different — Tier 4 is an explicit opt-in
  # (`docs/gitbook/07-testing-and-ci.md`), so a caller who did not set it did
  # not ask for these gates, and `./scripts/test_nightly.sh` is the documented
  # PR-validation command in `.github/pull_request_template.md`.  Reporting NOT
  # RUN there would make the standard command exit non-zero for every
  # contributor.
  #
  # But a caller who sets SELE4N_REQUIRE_GATES=1 *is* asking for every gate to
  # have run, and answering that with a clean exit over a tier that never
  # started is the vacuous acceptance the skip status exists to prevent — it is
  # how `SELE4N_REQUIRE_GATES=1 ./scripts/test_nightly.sh` came to certify a
  # release having executed zero Tier-4 gates.  So strict mode fails here, and
  # default mode passes as documented.
  if [[ "${SELE4N_REQUIRE_GATES:-0}" -eq 1 ]]; then
    record_skip "META" \
      "Tier 4 candidates not enabled — SELE4N_REQUIRE_GATES=1 demands they run; set NIGHTLY_ENABLE_EXPERIMENTAL=1"
  else
    log_section "META" "Tier 4 candidates staged but not enabled (set NIGHTLY_ENABLE_EXPERIMENTAL=1 to run)."
  fi
  finalize_report
  # `finalize_report` RETURNS on a clean report — it only exits on a failure or
  # a skip — so without this the "not enabled" branch printed its report and
  # then fell through and ran the boot-check anyway, which is how a disabled
  # tier still exited 77.  Terminating here is what makes "not enabled" mean
  # nothing ran.
  exit 0
fi

# WS-SM SM0.T — Reserved tier-4 slot for the SMP boot-check evidence.
# At SM0 this is a SKIP-only stub; SM1.H..SM8.E populate the checks.
sm0t_sub_args=()
if [[ "${CONTINUE_MODE:-0}" -eq 1 ]]; then
  sm0t_sub_args+=("--continue")
fi
run_gate_check "META" "${SCRIPT_DIR}/test_tier4_smp_bootcheck.sh" "${sm0t_sub_args[@]}"

ensure_lake_available

ARTIFACT_DIR="tests/artifacts/nightly"
mkdir -p "${ARTIFACT_DIR}"

run_check "META" python3 "${SCRIPT_DIR}/scenario_catalog.py" validate
run_check "META" bash -lc "python3 '${SCRIPT_DIR}/scenario_catalog.py' nightly-seeds > '${ARTIFACT_DIR}/scenario_seeds.txt'"
run_check "META" bash -lc "if [[ ! -s '${ARTIFACT_DIR}/scenario_seeds.txt' ]] || ! rg -q '[0-9]' '${ARTIFACT_DIR}/scenario_seeds.txt'; then echo 'error: no nightly seeds found in scenario catalog' >&2; exit 1; fi"

run_check_with_timeout "TRACE" bash -lc 'lake exe sele4n > tests/artifacts/nightly/sele4n_run1.trace'
run_check_with_timeout "TRACE" bash -lc 'lake exe sele4n > tests/artifacts/nightly/sele4n_run2.trace'
run_check "TRACE" bash -lc 'diff -u tests/artifacts/nightly/sele4n_run1.trace tests/artifacts/nightly/sele4n_run2.trace > tests/artifacts/nightly/sele4n_determinism.diff'
# Q1 simplified the service interface: start/stop/restart lifecycle ops removed.
# Validate the Q1/Q2 service registry surface instead.
run_check "TRACE" rg -n 'register service success: true' tests/artifacts/nightly/sele4n_run1.trace
run_check "TRACE" rg -n 'duplicate register: SeLe4n.Model.KernelError.illegalState' tests/artifacts/nightly/sele4n_run1.trace
run_check "TRACE" rg -n 'service isolation api↔denied: true' tests/artifacts/nightly/sele4n_run1.trace
# shellcheck disable=SC2016
run_check_with_timeout "TRACE" bash -lc 'while read -r seed; do [[ -z "${seed}" ]] && continue; lake exe trace_sequence_probe "${seed}" 320 | tee "tests/artifacts/nightly/trace_sequence_probe_seed_${seed}.log"; done < tests/artifacts/nightly/scenario_seeds.txt'
# shellcheck disable=SC2016
run_check "TRACE" bash -lc 'printf "seed,steps\n" > tests/artifacts/nightly/trace_sequence_probe_manifest.csv; while read -r seed; do [[ -z "${seed}" ]] && continue; printf "%s,320\n" "${seed}" >> tests/artifacts/nightly/trace_sequence_probe_manifest.csv; done < tests/artifacts/nightly/scenario_seeds.txt'

finalize_report
