#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
#
# Enforce that every `github/codeql-action/*` reference across
# `.github/workflows/` pins the SAME commit.
#
# Why this is a gate and not a convention: `codeql-action/init` stamps the
# configuration file it writes with its own action version, and
# `codeql-action/analyze` refuses to load a configuration stamped with a
# different one ("Loaded a configuration file for version 'X', but running
# version 'Y'").  A mismatched pair therefore ends the run as a CodeQL
# *configuration error*, whose post-step uploads a diagnostics-only "failed
# run" SARIF.  Code scanning rejects that SARIF, so the repository's
# code-scanning merge requirement never receives results for the head commit
# and reports "Code scanning is waiting for results from CodeQL for the
# commits ..." indefinitely — the pull request becomes permanently
# unmergeable, and a mismatch landed on `main` blocks every later PR.
#
# The failure is invisible in the Actions UI because the analyze step is
# `continue-on-error` per docs/CI_POLICY.md §8, so the job still reports
# success.  That is what makes a source-level gate the right enforcement
# point: it fails at Tier 0, before CodeQL ever runs.
#
# Parity is only meaningful over immutable refs, so each reference must also
# be a full 40-character lowercase commit SHA.  (The F-14 SHA-pinning scan in
# `test_tier0_hygiene.sh` does not reach sub-path actions such as
# `github/codeql-action/init`, whose owner/repo segment contains a `/`.)
#
# Usage:
#   check_codeql_action_pin_parity.sh              # scan the repository
#   check_codeql_action_pin_parity.sh --self-test  # verify the gate detects
#                                                  # a mismatch it must catch
#
# Exits 0 when clean, 1 on a mismatch, unpinned ref, or self-test failure.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

# Emit `file|line|sub-action|ref|version-comment` for every codeql-action
# `uses:` in the given directory.  The leading-`uses:` anchor keeps YAML
# comment lines (which start with `#`) out of the scan: prose that discusses
# a pin must never satisfy or trip it.
collect_pins() {
  local dir="$1"
  [[ -d "${dir}" ]] || return 0
  # `|| true`: grep exits 1 on no match, and under `pipefail` that would
  # abort the caller's assignment — a workflow tree with no CodeQL at all is
  # a clean state, not a violation.
  { grep -RnE '^[[:space:]]*-?[[:space:]]*uses:[[:space:]]*github/codeql-action/' \
      --include='*.yml' --include='*.yaml' "${dir}" 2>/dev/null || true; } \
    | awk -F: '
      {
        file = $1; lineno = $2;
        rest = substr($0, length(file) + length(lineno) + 3);
        marker = "github/codeql-action/";
        spec = substr(rest, index(rest, marker) + length(marker));
        at = index(spec, "@");
        if (at == 0) { sub_action = spec; tail = "" }
        else { sub_action = substr(spec, 1, at - 1); tail = substr(spec, at + 1) }
        sp = index(tail, " ");
        if (sp > 0) { ref = substr(tail, 1, sp - 1); comment = substr(tail, sp + 1) }
        else { ref = tail; comment = "" }
        gsub(/^[ \t]*#[ \t]*/, "", comment);
        gsub(/[ \t\r]+$/, "", comment);
        gsub(/[ \t\r]+$/, "", ref);
        print file "|" lineno "|" sub_action "|" ref "|" comment;
      }' \
    | sort
}

# Verdict for one directory. Prints diagnostics to stderr; returns non-zero
# on any violation.
check_dir() {
  local dir="$1"
  local pins refs comments unpinned
  pins="$(collect_pins "${dir}")"

  if [[ -z "${pins}" ]]; then
    return 0
  fi

  unpinned="$(printf '%s\n' "${pins}" | awk -F'|' '$4 !~ /^[0-9a-f]{40}$/')"
  if [[ -n "${unpinned}" ]]; then
    echo "CodeQL pin parity FAIL: codeql-action refs must be full 40-character commit SHAs." >&2
    printf '%s\n' "${unpinned}" | awk -F'|' '{ printf "  %s:%s  %s@%s\n", $1, $2, $3, $4 }' >&2
    return 1
  fi

  refs="$(printf '%s\n' "${pins}" | cut -d'|' -f4 | sort -u)"
  comments="$(printf '%s\n' "${pins}" | cut -d'|' -f5 | sort -u)"

  if [[ "$(printf '%s\n' "${refs}" | wc -l)" -ne 1 ]]; then
    echo "CodeQL pin parity FAIL: github/codeql-action/* references disagree." >&2
    echo "" >&2
    echo "  \`init\` stamps its config with its own version and \`analyze\` rejects a" >&2
    echo "  config from a different one, so a mismatched pair ends in a CodeQL" >&2
    echo "  configuration error and code scanning never receives results —" >&2
    echo "  leaving every affected pull request permanently unmergeable." >&2
    echo "" >&2
    printf '%s\n' "${pins}" | awk -F'|' '{ printf "  %s:%s  %s@%s  %s\n", $1, $2, $3, $4, $5 }' >&2
    echo "" >&2
    echo "  Bump every codeql-action reference to the same commit in one change." >&2
    return 1
  fi

  if [[ "$(printf '%s\n' "${comments}" | wc -l)" -ne 1 ]]; then
    echo "CodeQL pin parity FAIL: codeql-action refs share a commit but their" >&2
    echo "trailing version comments disagree (see docs/CI_POLICY.md §9)." >&2
    printf '%s\n' "${pins}" | awk -F'|' '{ printf "  %s:%s  %s@%s  # %s\n", $1, $2, $3, $4, $5 }' >&2
    return 1
  fi

  return 0
}

# A scanner that stops scanning fails silently, so prove it still catches the
# mismatch it exists to catch — and still passes a matched pair.
self_test() {
  local tmp status
  tmp="$(mktemp -d)"
  # shellcheck disable=SC2064
  trap "rm -rf '${tmp}'" RETURN

  local matched="${tmp}/matched" mismatched="${tmp}/mismatched"
  local tagged="${tmp}/tagged" none="${tmp}/none"
  mkdir -p "${matched}" "${mismatched}" "${tagged}" "${none}"

  echo "name: no codeql here" > "${none}/w.yml"

  local sha_a='5595ccaf912efad79be6eef63a5619ff05969be3'
  local sha_b='f205ea1c3313d32999d8d6a48b4f6530d4437b38'

  {
    echo "      - uses: github/codeql-action/init@${sha_a} # v4.37.6"
    echo "      - uses: github/codeql-action/analyze@${sha_a} # v4.37.6"
    echo "      # - uses: github/codeql-action/init@${sha_b} # v4.37.4 (prose, ignored)"
  } > "${matched}/w.yml"

  {
    echo "      - uses: github/codeql-action/init@${sha_a} # v4.37.6"
    echo "      - uses: github/codeql-action/analyze@${sha_b} # v4.37.4"
  } > "${mismatched}/w.yml"

  {
    echo "      - uses: github/codeql-action/init@v4"
    echo "      - uses: github/codeql-action/analyze@v4"
  } > "${tagged}/w.yml"

  status=0

  if ! check_dir "${matched}" 2>/dev/null; then
    echo "SELF-TEST FAIL: a matched pair was rejected." >&2
    status=1
  fi
  if [[ "$(collect_pins "${matched}" | wc -l)" -ne 2 ]]; then
    echo "SELF-TEST FAIL: the scan did not read exactly the two live pins" >&2
    echo "(a commented-out pin must not be collected)." >&2
    status=1
  fi
  if check_dir "${mismatched}" 2>/dev/null; then
    echo "SELF-TEST FAIL: a mismatched pair was accepted — the gate has lost its reach." >&2
    status=1
  fi
  if check_dir "${tagged}" 2>/dev/null; then
    echo "SELF-TEST FAIL: mutable tag refs were accepted." >&2
    status=1
  fi
  # A workflow tree with no CodeQL at all is clean, not a violation: `grep`
  # exits 1 on no match and under `pipefail` that once aborted the scan with
  # a bare exit 1 and no diagnostic.
  if ! check_dir "${none}" 2>/dev/null; then
    echo "SELF-TEST FAIL: a tree with no codeql-action references was rejected." >&2
    status=1
  fi

  if [[ "${status}" -eq 0 ]]; then
    echo "CodeQL pin parity self-test: gate detects mismatched, tagged, absent, and commented refs correctly."
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

pin_count="$(collect_pins "${REPO_ROOT}/.github/workflows" | wc -l | tr -d ' ')"
if [[ "${pin_count}" -eq 0 ]]; then
  echo "CodeQL pin parity: no github/codeql-action references in .github/workflows."
else
  echo "CodeQL pin parity: ${pin_count} github/codeql-action reference(s) agree on one pinned commit."
fi
exit 0
