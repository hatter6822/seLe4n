#!/usr/bin/env bash
# Witness: surface anchors read CODE, and prose checks read prose.
#
# WS-SM SM8.B (PR #861 review round 43).
#
# `lean_code_view.py --self-test` pins the stripper.  This pins the *wiring* —
# that `run_check` actually routes a Lean scan through the stripped overlay —
# because the two fail differently and only one of them is visible.  A
# refactor of `test_lib.sh` that dropped `_run_with_view` would leave every
# anchor passing, the suite green, and 1500 checks quietly reading prose
# again: the exact state this change was made to leave behind.
#
# Both directions are checked, on a fixture built for the purpose:
#   * a symbol that exists ONLY in a comment must NOT satisfy `run_check`
#     (the fail-open that let an anchor pin a deleted theorem);
#   * that same symbol MUST satisfy `run_prose_check` (the opt-out has to
#     actually reach the real text, or the escape hatch is broken too);
#   * a symbol that exists in code must satisfy `run_check` (the stripper
#     must not be eating code, which would fail every anchor closed).

set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
cd "${REPO_ROOT}" || exit 1

# shellcheck source=/dev/null
source "${SCRIPT_DIR}/test_lib.sh"

FIXTURE_DIR="SeLe4n/Kernel"
FIXTURE="${FIXTURE_DIR}/CodeViewWiringWitness.lean"
# shellcheck disable=SC2317  # invoked by the EXIT trap below, not by name
cleanup() { rm -f "${REPO_ROOT}/${FIXTURE}" "${REPO_ROOT}/.lake/build/leancodeview/${FIXTURE}"; }
trap cleanup EXIT

cat > "${REPO_ROOT}/${FIXTURE}" <<'LEANEOF'
-- A fixture, written and deleted by scripts/test_code_view_wiring.sh.
-- `codeViewWitnessProseOnly` appears here in a comment and nowhere in code.
/-- Doc mentioning codeViewWitnessProseOnly so a raw grep would find it. -/
def codeViewWitnessInCode : Nat := 0
LEANEOF

# Drive the real helpers, with the accounting under this script's control.
# `run_check` calls `finalize_report` (which exits) on failure unless continue
# mode is on, and check 1 is *expected* to fail — so continue mode is set and
# the verdict is read off `FAILURE_COUNT` instead of the exit status.  Driving
# `run_check` itself rather than `_run_with_view` is the point: the routing
# decision has to be reached through the function the 1696 anchors call.
# shellcheck disable=SC2034  # read by run_check/finalize_report in test_lib.sh
CONTINUE_MODE=1
failures=0
note() { echo "[code-view-wiring] $*"; }

expect_recorded() {   # description, expected delta (0 = must pass, 1 = must fail)
  local what="$1" want="$2"; shift 2
  local before="${FAILURE_COUNT}"
  "$@" >/dev/null 2>&1 || true
  local got=$(( FAILURE_COUNT - before ))
  if [[ "${got}" -eq "${want}" ]]; then
    note "PASS: ${what}"
  else
    note "FAIL: ${what} (recorded ${got} failure(s), expected ${want})"
    failures=$((failures + 1))
  fi
}

# A comment-only symbol must NOT satisfy a code anchor.
expect_recorded "a comment cannot satisfy a code anchor" 1 \
  run_check "WIRING" rg -n 'codeViewWitnessProseOnly' "${FIXTURE}"

# ... but a prose check must still see it, or the opt-out is broken too.
expect_recorded "run_prose_check still reads the real text" 0 \
  run_prose_check "WIRING" rg -n 'codeViewWitnessProseOnly' "${FIXTURE}"

# ... and real code must still be found, or every anchor fails closed.
expect_recorded "code anchors still match code" 0 \
  run_check "WIRING" rg -n '^def codeViewWitnessInCode' "${FIXTURE}"

# The negative dual.  Routing negatives through the view would have made every
# anchor forbidding a *wording* vacuous — absent from a view with no comments
# in it, therefore passing forever.  A prose negative must still be able to
# fire on prose.
expect_recorded "run_prose_negative_check still fires on prose" 1 \
  run_prose_negative_check "WIRING" rg -n 'codeViewWitnessProseOnly' "${FIXTURE}"

# ... while a construct negative correctly ignores the comment that names it.
expect_recorded "run_negative_check ignores a comment-only mention" 0 \
  run_negative_check "WIRING" rg -n 'codeViewWitnessProseOnly' "${FIXTURE}"

if [[ "${failures}" -ne 0 ]]; then
  note "SELF-TEST FAILED (${failures})"
  exit 1
fi
note "SELF-TEST PASS (5 checks)"
exit 0
