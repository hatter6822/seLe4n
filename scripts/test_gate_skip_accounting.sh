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

# 5. The source-level guarantee: no gate script may exit 0 out of a skip
#    branch.  This is what stops the original defect returning one script at
#    a time — the accounting above cannot help if the sub-test reports
#    success instead of the skip code.
#
#    Both skip idioms count.  Matching only the literal `[SKIP]` would miss
#    branches written with the shared logger (`log_section "META" "SKIP: …"`),
#    which is how the hardware gates spell it; a script converted to that
#    style would silently restore the defect while this suite stayed green.
#    The glob is `test_qemu*.sh` (not `test_qemu_*.sh`) plus the hardware
#    gates, because `test_qemu.sh` has no underscore and is a live gate.
stray=0
for f in scripts/test_qemu*.sh scripts/test_hw_*.sh; do
  [[ -e "${f}" ]] || continue
  if awk '
    /\[SKIP\]/                                   { armed = 1; next }
    /log_section[[:space:]]+"[A-Z]+"[[:space:]]+"SKIP/ { armed = 1; next }
    armed && /^[[:space:]]*exit[[:space:]]+0[[:space:]]*$/ { found = 1; exit }
    armed && /^[[:space:]]*(echo|log_section|#|tail|fi|\})/ { next }
    armed && /GITHUB_OUTPUT/                     { next }
    armed && /^[[:space:]]*$/                    { next }
    armed                                        { armed = 0 }
    END { exit (found ? 0 : 1) }
  ' "${f}"; then
    echo "  FAIL: ${f} exits 0 from a skip branch (must exit \${SELE4N_SKIP_EXIT})"
    stray=$((stray + 1))
  fi
done
witness "no gate script exits 0 from a skip branch" "0" "${stray}"

#    The complement, and the gap that hid a live defect: a skip that neither
#    exits nor records.  `test_hw_crosscheck.sh` announced "SKIP: devmem2 not
#    available", fell through to `finalize_report` with SKIP_COUNT at zero, and
#    was reported PASS by `test_hw_full.sh` — coverage the check above cannot
#    see, because there is no `exit 0` to find.  So require the converse:
#    every skip announcement is either emitted through `record_skip` (which
#    increments the counter) or followed by an exit carrying the skip status.
#    A bare `log_section`/`echo` skip that reaches the end of its branch is
#    the defect, whatever it prints.
fallthrough=0
for f in scripts/test_qemu*.sh scripts/test_hw_*.sh; do
  [[ -e "${f}" ]] || continue
  if awk '
    function indent(s,   n) { n = match(s, /[^ \t]/); return (n ? n - 1 : -1) }
    /record_skip/       { armed = 0; next }   # the accounted form needs no exit
    /^[[:space:]]*#/    { next }              # a comment about the idiom is not the idiom
    # An announcement arms the scan and remembers its own nesting level.
    !armed && (/\[SKIP\]/ || /log_section[[:space:]]+"[A-Z]+"[[:space:]]+"SKIP/) {
      armed = 1; at = NR; lvl = indent($0); next
    }
    armed && /exit[[:space:]]/ { armed = 0; next }   # left via exit: accounted
    armed && /^[[:space:]]*$/  { next }
    # Dedenting past the announcement means its branch closed with neither a
    # record_skip nor an exit — the announcement was cosmetic and the script
    # falls through to finalize_report with SKIP_COUNT still at zero.
    armed && indent($0) < lvl {
      print "    line " at ": skip announced but neither recorded nor exited"
      bad = 1; armed = 0
    }
    END { exit (bad ? 0 : 1) }
  ' "${f}"; then
    echo "  FAIL: ${f} announces a skip it does not record (use record_skip)"
    fallthrough=$((fallthrough + 1))
  fi
done
witness "no gate script announces a skip without recording it" "0" "${fallthrough}"

# 6. The skip status must survive the process boundary.  Tier scripts nest,
#    and a `finalize_report` that returned 0 on skips had each parent's
#    `run_check` record PASS — so the nightly still printed "All checks
#    passed" over fourteen gates that never ran.  Reporting NOT RUN inside
#    one script while the enclosing verdict stays clean is the same defect
#    one level up, which is why it gets its own witness.
rc=0; drive "${TMP}/skipper.sh" 0 >/dev/null 2>&1 || rc=$?
witness "a skipped gate exits the reserved skip status, not 0" "77" "${rc}"

# Its own counter: sharing `stray` with the check above made a source-level
# failure cascade into this one, reporting two defects where there is one.
unaware=0
for parent in scripts/test_tier4_nightly_candidates.sh scripts/test_nightly.sh; do
  # SC2016 is exactly the property under test: the pattern must match the
  # LITERAL text `${SCRIPT_DIR}` as it appears in the parent script's source.
  # Expanding it here would search for this process's own value and match
  # nothing, silently passing the witness.
  # shellcheck disable=SC2016
  if grep -q 'run_check "META" "${SCRIPT_DIR}/test_tier4' "${parent}"; then
    echo "  FAIL: ${parent} invokes a tier-4 runner with run_check (skip status is lost)"
    unaware=$((unaware + 1))
  fi
done
witness "nested tier runners are invoked skip-aware" "0" "${unaware}"

if [[ "${WITNESS_FAILURES}" -gt 0 ]]; then
  record_failure "META" "${WITNESS_FAILURES} gate skip-accounting witness(es) failed"
fi
log_section "META" "Gate skip-accounting witness complete."
finalize_report
