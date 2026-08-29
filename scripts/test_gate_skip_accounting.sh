#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
#
# Witness suite for the acceptance-gate skip accounting in test_lib.sh.
#
# The mechanism this pins: a sub-test that cannot run exits
# `SELE4N_SKIP_EXIT` and, invoked through `run_gate_check`, is recorded
# NOT RUN rather than PASS.  Before it existed, every tier-4 QEMU gate
# exited 0 when the emulator or the kernel image was absent, `run_check`
# scored that as PASS, and the tier printed "All checks passed" over
# fourteen gates that had never executed — so the phases those gates
# certify read as hardware-validated on a machine with no emulator.
#
# A regression here is silent by construction: the tier still exits 0 and
# still looks green.  That is precisely why the mechanism needs a witness
# rather than trust, in the same spirit as `test_code_view_wiring.sh`
# (the code-view routing) and `test_identifier_naming_gate.py`.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck disable=SC1091
source "${SCRIPT_DIR}/test_lib.sh"

parse_common_args "$@"
cd "${REPO_ROOT}"

log_section "META" "Gate skip-accounting witness"

WITNESS_FAILURES=0
witness() {
  local name="$1" expected="$2" actual="$3"
  if [[ "${expected}" == "${actual}" ]]; then
    echo "  PASS: ${name}"
  else
    echo "  FAIL: ${name} — expected '${expected}', got '${actual}'"
    WITNESS_FAILURES=$((WITNESS_FAILURES + 1))
  fi
}

TMP="$(mktemp -d)"
trap 'rm -rf "${TMP}"' EXIT

printf '#!/usr/bin/env bash\necho "[SKIP] witness: nothing to run"\nexit 77\n' > "${TMP}/skipper.sh"
printf '#!/usr/bin/env bash\necho "[PASS] witness"\nexit 0\n'                  > "${TMP}/passer.sh"
printf '#!/usr/bin/env bash\necho "[FAIL] witness"\nexit 1\n'                  > "${TMP}/failer.sh"
chmod +x "${TMP}"/*.sh

# Drive a tier through the real library in a child shell, so the witness
# exercises run_gate_check/finalize_report exactly as a tier does.
drive() {
  local script="$1" require="$2"
  SELE4N_REQUIRE_GATES="${require}" bash -c '
    source "$1/test_lib.sh"
    run_gate_check "META" "$2" || true
    finalize_report
  ' _ "${SCRIPT_DIR}" "${script}" 2>&1
}

# 1. A skipped gate is reported NOT RUN, never PASS.
out="$(drive "${TMP}/skipper.sh" 0 || true)"
witness "skip is recorded NOT RUN" \
  "yes" "$(grep -q 'SKIP (NOT RUN)' <<<"${out}" && echo yes || echo no)"
witness "skip is not scored PASS" \
  "yes" "$(grep -qE '^\[META\] PASS' <<<"${out}" && echo no || echo yes)"

# 2. The summary line never claims a clean run over an unexecuted gate.
witness "summary does not say 'All checks passed'" \
  "yes" "$(grep -q 'All checks passed' <<<"${out}" && echo no || echo yes)"
witness "summary names the incomplete coverage" \
  "yes" "$(grep -q 'DID NOT RUN' <<<"${out}" && echo yes || echo no)"

# 3. Strict mode promotes a skip to a hard failure.
rc=0; drive "${TMP}/skipper.sh" 1 >/dev/null 2>&1 || rc=$?
witness "SELE4N_REQUIRE_GATES=1 fails on a skipped gate" "1" "${rc}"

# 4. Real outcomes are unaffected: a pass still passes, a failure still fails.
rc=0; drive "${TMP}/passer.sh" 0 >/dev/null 2>&1 || rc=$?
witness "a passing gate still exits 0" "0" "${rc}"
out="$(drive "${TMP}/passer.sh" 0 || true)"
witness "a passing gate still reports All checks passed" \
  "yes" "$(grep -q 'All checks passed' <<<"${out}" && echo yes || echo no)"

rc=0; drive "${TMP}/failer.sh" 0 >/dev/null 2>&1 || rc=$?
witness "a failing gate still exits 1" "1" "${rc}"

# 5. The source-level guarantee: no QEMU sub-test may exit 0 out of a
#    [SKIP] branch.  This is what stops the original defect returning one
#    script at a time — the accounting above cannot help if the sub-test
#    reports success instead of the skip code.
stray=0
for f in scripts/test_qemu_*.sh; do
  # Walk each file; a bare `exit 0` reached from a [SKIP] echo block is
  # the regression.  Only echo/blank/comment lines may sit in between.
  if awk '
    /\[SKIP\]/            { armed = 1; next }
    armed && /^[[:space:]]*exit[[:space:]]+0[[:space:]]*$/ { found = 1; exit }
    armed && /^[[:space:]]*(echo|#)/ { next }
    armed && /^[[:space:]]*$/        { next }
    armed                            { armed = 0 }
    END { exit (found ? 0 : 1) }
  ' "${f}"; then
    echo "  FAIL: ${f} exits 0 from a [SKIP] branch (must exit \${SELE4N_SKIP_EXIT})"
    stray=$((stray + 1))
  fi
done
witness "no QEMU sub-test exits 0 from a [SKIP] branch" "0" "${stray}"

if [[ "${WITNESS_FAILURES}" -gt 0 ]]; then
  record_failure "META" "${WITNESS_FAILURES} gate skip-accounting witness(es) failed"
fi
log_section "META" "Gate skip-accounting witness complete."
finalize_report
