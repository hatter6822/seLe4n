#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
#
# Enforce that the CodeQL `analyze` step is a blocking gate — that it carries
# no `continue-on-error`.
#
# WS-B10 originally masked this step, and that mask is why a real breakage
# went unseen: when PRs #858 and #859 ran a version-mismatched
# `init`/`analyze` pair, CodeQL died in a configuration error, code scanning
# received nothing, and the security job still reported **success**.  The only
# symptom was an unmergeable pull request with no failing check to point at.
# The flag was removed in v0.33.6 (docs/CI_POLICY.md §8); this gate keeps it
# from returning silently.
#
# `analyze` does not fail on findings — it fails on configuration and upload
# errors, which are exactly the conditions under which the repository's
# code-scanning merge requirement will otherwise hang.  Fork-origin pull
# requests never reach the step: the job's `if:` skips them.
#
# Gates read code, prose reads prose: YAML comments are stripped before
# matching, so the sentence explaining the rule cannot trip it.
#
# Usage:
#   check_codeql_analyze_blocking.sh              # scan the repository
#   check_codeql_analyze_blocking.sh --self-test  # prove the gate still bites
#
# Exits 0 when clean, 1 when the analyze step is masked.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

# Report every workflow whose `codeql-action/analyze` step block also carries
# `continue-on-error`.  Steps are delimited by their leading `- ` list marker,
# so the check is order-insensitive within a step: a mask written above the
# `uses:` line is caught just as a mask written below it.
masked_workflows() {
  local dir="$1"
  [[ -d "${dir}" ]] || return 0
  local f
  while IFS= read -r f; do
    awk '
      function flush() {
        if (block ~ /github\/codeql-action\/analyze@/ && block ~ /continue-on-error/) bad = 1
        block = ""
      }
      { line = $0; sub(/[ \t]*#.*$/, "", line) }        # strip YAML comments
      line ~ /^[ \t]*-[ \t]/ { flush() }                 # a new step begins
      { block = block "\n" line }
      END { flush(); exit bad ? 1 : 0 }
    ' "${f}" || echo "${f}"
  done < <(find "${dir}" -type f \( -name '*.yml' -o -name '*.yaml' \) | sort)
}

check_dir() {
  local masked
  masked="$(masked_workflows "$1")"
  if [[ -n "${masked}" ]]; then
    echo "CodeQL analyze gate FAIL: the analyze step is masked by continue-on-error in:" >&2
    printf '%s\n' "${masked}" | sed 's/^/  /' >&2
    echo "" >&2
    echo "  A masked analyze reports the job green while code scanning receives" >&2
    echo "  nothing, so a broken CodeQL is indistinguishable from a healthy one and" >&2
    echo "  only surfaces as an unmergeable pull request.  See docs/CI_POLICY.md §8." >&2
    return 1
  fi
  return 0
}

self_test() {
  local tmp status
  tmp="$(mktemp -d)"
  # shellcheck disable=SC2064
  trap "rm -rf '${tmp}'" RETURN

  local sha='5595ccaf912efad79be6eef63a5619ff05969be3'
  local blocking="${tmp}/blocking" masked_after="${tmp}/after" masked_before="${tmp}/before"
  mkdir -p "${blocking}" "${masked_after}" "${masked_before}"

  {
    echo "      # this step carries no continue-on-error (prose, must not trip)"
    echo "      - name: Run CodeQL analysis"
    echo "        uses: github/codeql-action/analyze@${sha} # v4.37.6"
  } > "${blocking}/w.yml"

  {
    echo "      - name: Run CodeQL analysis"
    echo "        uses: github/codeql-action/analyze@${sha} # v4.37.6"
    echo "        continue-on-error: true"
  } > "${masked_after}/w.yml"

  # Order-insensitivity: a mask written above the `uses:` line must also fail.
  {
    echo "      - name: Run CodeQL analysis"
    echo "        continue-on-error: true"
    echo "        uses: github/codeql-action/analyze@${sha} # v4.37.6"
  } > "${masked_before}/w.yml"

  status=0
  if ! check_dir "${blocking}" 2>/dev/null; then
    echo "SELF-TEST FAIL: a blocking analyze step was rejected (prose tripped the gate?)." >&2
    status=1
  fi
  if check_dir "${masked_after}" 2>/dev/null; then
    echo "SELF-TEST FAIL: continue-on-error below the uses: line was accepted." >&2
    status=1
  fi
  if check_dir "${masked_before}" 2>/dev/null; then
    echo "SELF-TEST FAIL: continue-on-error above the uses: line was accepted." >&2
    status=1
  fi

  if [[ "${status}" -eq 0 ]]; then
    echo "CodeQL analyze gate self-test: mask detected above and below the uses: line; prose ignored."
  fi
  return "${status}"
}

if [[ "${1:-}" == "--self-test" ]]; then
  self_test
  exit $?
fi

if ! check_dir "${REPO_ROOT}/.github/workflows"; then
  exit 1
fi
echo "CodeQL analyze gate: no continue-on-error on any codeql-action/analyze step."
exit 0
