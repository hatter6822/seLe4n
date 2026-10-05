#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
#
# Every remote `uses:` reference in `.github/workflows/` must name a full
# 40-hex commit SHA (docs/CI_POLICY.md §9, F-14).
#
# Each `uses:` value is resolved, not pattern-matched:
#   ./path                         a local action: exempt
#   docker://image@sha256:<64 hex> a container: the digest is required
#   owner/repo[/path]@ref          a remote action or reusable workflow: the
#                                  ref must be a full 40-hex commit SHA
# Anything else fails as a shape this check cannot classify.  That includes a
# line that mentions `uses:` outside a `uses:` key (a flow mapping, a key
# with no space after its colon), an empty value, an anchor or alias, and a
# ref that is a tag, a branch or a short SHA.  A `uses:` inside a YAML comment
# or inside another key's scalar value (a step `name:`) is not a reference.
#
# Lines are located with `rg`, or `grep -E` where `rg` is absent, over the
# `.yml`/`.yaml` files GitHub runs.  No scanner, a scanner error or a scan that
# finds no `uses:` at all fails: none of those is a clean tree.  Each finding
# is printed as `file:line: reason: value`.
#
# Usage:
#   check_actions_sha_pinned.sh [--root DIR]   scan DIR (default: repo root)
#   check_actions_sha_pinned.sh --self-test    prove the check still bites,
#                                              under every available scanner
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LOCATE='uses["'"'"']?[[:space:]]*:'
SHA_RE='^[0-9a-f]{40}$'
REMOTE_RE='^([[:alnum:]_.-]+)/([[:alnum:]_.-]+)(/[^@[:space:]]+)?@([^@[:space:]]+)$'
DOCKER_RE='^docker://[^@[:space:]]+@sha256:[0-9a-f]{64}$'
USES_KEY_RE='^(-[[:space:]]+)?(uses|"uses"|'"'"'uses'"'"')[[:space:]]*:([[:space:]]+(.*))?$'
OTHER_KEY_RE='^(-[[:space:]]+)?("?[[:alnum:]_.-]+"?)[[:space:]]*:([[:space:]]+(.*))?$'

# Set CODE to the part of $1 before a YAML comment.  A `#` opens a comment only
# outside quotes and at the start of the line or after whitespace.
code_part() {
  local s="$1" quote="" prev=" " ch i
  CODE="${s}"
  for ((i = 0; i < ${#s}; i++)); do
    ch="${s:i:1}"
    if [[ -n "${quote}" ]]; then
      [[ "${ch}" == "${quote}" ]] && quote=""
    elif [[ "${ch}" == '"' || "${ch}" == "'" ]]; then
      quote="${ch}"
    elif [[ "${ch}" == "#" && ( "${prev}" == " " || "${prev}" == $'\t' ) ]]; then
      CODE="${s:0:i}"
      return 0
    fi
    prev="${ch}"
  done
}

trim() {
  local s="$1"
  s="${s#"${s%%[![:space:]]*}"}"
  s="${s%"${s##*[![:space:]]}"}"
  printf '%s' "${s}"
}

# Classify one `uses:` value: set KIND, or set REASON and return 1.
classify_value() {
  local value="$1" first last
  if [[ ${#value} -ge 2 ]]; then
    first="${value:0:1}"
    last="${value: -1}"
    if [[ "${first}" == "${last}" && ( "${first}" == '"' || "${first}" == "'" ) ]]; then
      value="${value:1:${#value}-2}"
    fi
  fi
  if [[ -z "${value}" || "${value}" =~ [[:space:]\"\'] ]]; then
    REASON="cannot classify this \`uses:\` value"
    return 1
  fi
  case "${value}" in
    ./*) KIND=local; return 0 ;;
    docker://*)
      if [[ "${value}" =~ ${DOCKER_RE} ]]; then KIND=docker; return 0; fi
      REASON="docker image is not pinned to an @sha256: digest"
      return 1
      ;;
  esac
  if [[ ! "${value}" =~ ${REMOTE_RE} ]]; then
    REASON="cannot classify this \`uses:\` value as owner/repo[/path]@ref"
    return 1
  fi
  # Saved first: the test below overwrites BASH_REMATCH.
  local ref="${BASH_REMATCH[4]}"
  if [[ ! "${ref}" =~ ${SHA_RE} ]]; then
    REASON="ref \`${ref}\` is not a full 40-hex commit SHA"
    return 1
  fi
  KIND=remote
}

# Scan ROOT with SCANNER (rg or grep).  Findings go to stderr; returns 0 when
# every reference is pinned, 1 on a finding, 2 when the scan cannot run.
scan_tree() {
  local root="$1" scanner="$2" hits status=0
  local -a cmd
  case "${scanner}" in
    rg) cmd=(rg -n -H --no-heading --hidden --no-ignore -g '*.yml' -g '*.yaml' -e "${LOCATE}" -- .github/workflows) ;;
    grep) cmd=(grep -rnHE --include='*.yml' --include='*.yaml' -e "${LOCATE}" -- .github/workflows) ;;
    *) echo "F-14: unknown scanner '${scanner}'" >&2; return 2 ;;
  esac
  hits="$(cd "${root}" && "${cmd[@]}")" || status=$?
  if [[ "${status}" -gt 1 ]]; then
    echo "F-14: ${scanner} could not scan .github/workflows (exit ${status}), which is not a clean tree." >&2
    return 2
  fi
  if [[ -z "${hits}" ]]; then
    echo "F-14: ${scanner} found no \`uses:\` in .github/workflows, so nothing was checked." >&2
    return 2
  fi

  local hit loc text value findings=0 remote=0 local_n=0 docker=0
  while IFS= read -r hit; do
    if [[ ! "${hit}" =~ ^([^:]+:[0-9]+):(.*)$ ]]; then
      echo "F-14: cannot read the scanner's output line: ${hit}" >&2
      findings=$((findings + 1))
      continue
    fi
    loc="${BASH_REMATCH[1]}"
    text="${BASH_REMATCH[2]%$'\r'}"
    code_part "${text}"
    CODE="$(trim "${CODE}")"
    # A mention inside a comment is not a reference.
    [[ "${CODE}" =~ ${LOCATE} ]] || continue
    if [[ "${CODE}" =~ ${USES_KEY_RE} ]]; then
      value="$(trim "${BASH_REMATCH[4]}")"
      if classify_value "${value}"; then
        case "${KIND}" in
          remote) remote=$((remote + 1)) ;;
          local) local_n=$((local_n + 1)) ;;
          docker) docker=$((docker + 1)) ;;
        esac
        continue
      fi
      echo "${loc}: ${REASON}: ${value}" >&2
      findings=$((findings + 1))
      continue
    fi
    # `uses:` inside another key's plain value (a step `name:`) is text, but a
    # flow collection may hold a real `uses:` key, so it cannot be classified.
    if [[ "${CODE}" =~ ${OTHER_KEY_RE} ]]; then
      value="$(trim "${BASH_REMATCH[4]}")"
      if [[ "${value}" != "{"* && "${value}" != "["* ]]; then
        continue
      fi
    fi
    echo "${loc}: cannot classify this line: it mentions \`uses:\` outside a \`uses:\` key: ${CODE}" >&2
    findings=$((findings + 1))
  done <<< "${hits}"

  if [[ "${findings}" -gt 0 ]]; then
    echo "F-14 regression: ${findings} \`uses:\` reference(s) not pinned to a full commit SHA (see docs/CI_POLICY.md §9)." >&2
    return 1
  fi
  echo "F-14: ${remote} remote reference(s) pinned to a commit SHA, ${docker} docker digest(s), ${local_n} local action(s) (scanner: ${scanner})."
}

scanner_for_host() {
  if command -v rg >/dev/null 2>&1; then
    echo rg
  elif command -v grep >/dev/null 2>&1; then
    echo grep
  else
    return 1
  fi
}

# --------------------------------------------------------------------------
# Self-test.  Each case is one line, written as line 8 of a workflow whose
# line 7 is a pinned step, and is scanned under every scanner on the host.  A
# failing case must name `w.yml:8`, so a finding that loses its location fails
# the self-test too.
# --------------------------------------------------------------------------
SELF_SHA="0123456789abcdef0123456789abcdef01234567"
SELF_DIGEST="0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"

write_case() {
  local root="$1" line="$2"
  mkdir -p "${root}/.github/workflows"
  printf '%s\n' "name: t" "on: push" "jobs:" "  j:" "    runs-on: ubuntu-latest" \
    "    steps:" "      - uses: actions/checkout@${SELF_SHA} # v4" "      ${line}" \
    > "${root}/.github/workflows/w.yml"
}

self_test() {
  local -a scanners=() cases=(
    "0|a pinned sub-path action|- uses: github/codeql-action/init@${SELF_SHA} # v4.38.0"
    "0|a pinned owner and repo with digits|- uses: actions2/check-out9@${SELF_SHA}"
    "0|a quoted pinned reference|- uses: \"actions/checkout@${SELF_SHA}\""
    "0|a pinned reusable workflow|uses: octo-org/repo/.github/workflows/ci.yml@${SELF_SHA}"
    "0|a local action|- uses: ./.github/actions/local"
    "0|a docker image pinned to a digest|- uses: docker://alpine@sha256:${SELF_DIGEST}"
    "0|a reference inside a comment|# - uses: actions/checkout@v4"
    "0|uses: inside a step name|- name: Check uses: pinning"
    "1|an unpinned sub-path action|- uses: github/codeql-action/init@v3"
    "1|an owner with digits on a tag|- uses: actions2/checkout@v4"
    "1|a branch ref|- uses: actions/checkout@main"
    "1|a short SHA|- uses: actions/checkout@a1b2c3d"
    "1|a non-v tag|- uses: aquasecurity/trivy-action@0.36.0"
    "1|a quoted tag|- uses: \"actions/checkout@v4\""
    "1|a space before the colon|- uses : actions/checkout@v4"
    "1|a quoted key|- \"uses\": actions/checkout@v4"
    "1|a flow mapping|- {uses: actions/checkout@v4}"
    "1|a docker tag|- uses: docker://alpine:3.8"
    "1|a reusable workflow on a tag|uses: octo-org/repo/.github/workflows/ci.yml@v1"
    "1|an empty value|- uses:"
    "1|no ref at all|- uses: actions/checkout"
    "1|an expression|- uses: actions/checkout@\${{ github.sha }}"
    "1|an alias|- uses: *pinned"
    "1|no space after the colon|- uses:actions/checkout@v4"
  )
  command -v rg >/dev/null 2>&1 && scanners+=(rg)
  command -v grep >/dev/null 2>&1 && scanners+=(grep)
  if [[ "${#scanners[@]}" -eq 0 ]]; then
    echo "SELF-TEST FAIL: neither rg nor grep is on PATH." >&2
    return 1
  fi

  local tmp failures=0 checked=0 scanner entry want label line got out n=0
  tmp="$(mktemp -d)"
  # shellcheck disable=SC2064  # expand now: the path is fixed
  trap "rm -rf '${tmp}'" RETURN
  for scanner in "${scanners[@]}"; do
    for entry in "${cases[@]}"; do
      want="${entry%%|*}"; entry="${entry#*|}"
      label="${entry%%|*}"; line="${entry#*|}"
      n=$((n + 1))
      write_case "${tmp}/c${n}" "${line}"
      got=0
      out="$(scan_tree "${tmp}/c${n}" "${scanner}" 2>&1)" || got=$?
      checked=$((checked + 1))
      if [[ "${got}" -ne "${want}" ]]; then
        echo "SELF-TEST FAIL (${scanner}): ${label}: exit ${got}, expected ${want}: ${out}" >&2
        failures=$((failures + 1))
      elif [[ "${want}" -eq 1 && "${out}" != *"w.yml:8: "* ]]; then
        echo "SELF-TEST FAIL (${scanner}): ${label}: the finding does not name w.yml:8: ${out}" >&2
        failures=$((failures + 1))
      fi
    done
    # A scan that cannot run, or reads nothing, is not a clean tree.
    mkdir -p "${tmp}/none-${scanner}"
    got=0; scan_tree "${tmp}/none-${scanner}" "${scanner}" >/dev/null 2>&1 || got=$?
    [[ "${got}" -eq 2 ]] || { echo "SELF-TEST FAIL (${scanner}): a tree with no workflows directory exited ${got}, expected 2" >&2; failures=$((failures + 1)); }
    mkdir -p "${tmp}/empty-${scanner}/.github/workflows"
    printf 'name: t\non: push\n' > "${tmp}/empty-${scanner}/.github/workflows/w.yml"
    printf 'uses: actions/checkout@v4\n' > "${tmp}/empty-${scanner}/.github/workflows/notes.md"
    got=0; scan_tree "${tmp}/empty-${scanner}" "${scanner}" >/dev/null 2>&1 || got=$?
    [[ "${got}" -eq 2 ]] || { echo "SELF-TEST FAIL (${scanner}): workflows with no \`uses:\` (and a .md file that is not a workflow) exited ${got}, expected 2" >&2; failures=$((failures + 1)); }
    checked=$((checked + 2))
  done
  if [[ "${failures}" -gt 0 ]]; then
    echo "SELF-TEST FAILED: ${failures} of ${checked} case(s)." >&2
    return 1
  fi
  echo "SELF-TEST PASS: ${checked} case(s) under ${scanners[*]}."
}

main() {
  local root
  root="$(cd "${SCRIPT_DIR}/.." && pwd)"
  case "${1:-}" in
    --self-test) self_test; return $? ;;
    --root) root="$2" ;;
    "") ;;
    *) echo "usage: $0 [--root DIR | --self-test]" >&2; return 2 ;;
  esac
  local scanner
  if ! scanner="$(scanner_for_host)"; then
    echo "F-14: neither rg nor grep is on PATH, so the SHA-pinning scan cannot run." >&2
    return 2
  fi
  scan_tree "${root}" "${scanner}"
}

main "$@"
