#!/usr/bin/env bash
# Tier 0 hygiene: forbid workstream IDs, audit IDs, phase codes, and
# sub-task numbers in *declared identifiers*.
#
# CLAUDE.md ("Internal-first naming") requires every identifier to
# describe what it is, not which workstream produced it.  Prose is
# exempt -- docstrings, comments, commit messages, and CHANGELOG
# entries are legitimate places to cite a workstream ID -- so this gate
# inspects only the name in a declaration.
#
# Why the gate exists: the same finding recurred across four review
# rounds of PR #854, because each sweep was a hand-written grep whose
# pattern was narrower than the rule.  A prefix-only match missed
# `phase5_defaults_...`; an `fn`-only match missed statics and consts.
# A gate that runs on every push is the only thing that makes "zero"
# mean zero.
#
# Two surfaces, two policies:
#   Rust  -- hard zero.  Cleaned at v0.32.121; new violations fail.
#   Lean  -- ratchet.  CLAUDE.md grandfathers historical identifiers
#            ("stay as-is until touched by a workstream that can rename
#            them in the same commit"), so the count may fall but never
#            rise.  Lower the baseline when a workstream renames some.
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${REPO_ROOT}"

# Code classes: phase codes (phase5), workstream prefixes (sm1d_, an3b_,
# ak7), sub-task numbers (ws_q_, _p2_, step3, task4).
readonly CODE_CLASSES='phase[0-9]|\bsm[0-9]|_sm[0-9]|an[0-9]+[a-z]?_|ak[0-9]|ws_[a-z]_|_p[0-9]_|step[0-9]|task[0-9]'

readonly LEAN_BASELINE=127

rust_declared_identifiers() {
  grep -rhoE '^\s*(pub )?(async )?(unsafe )?(fn|const|static|struct|enum|trait|type|mod) [A-Za-z0-9_]+' \
    rust/*/src/*.rs rust/*/src/**/*.rs rust/*/build.rs 2>/dev/null \
    | awk '{print $NF}' | sort -u
}

lean_declared_identifiers() {
  grep -rhoE "^\s*(private |protected |@\[[a-z]+\] )*(theorem|def|lemma|abbrev|structure|inductive) [A-Za-z0-9_']+" \
    SeLe4n/ tests/ 2>/dev/null \
    | awk '{print $NF}' | sort -u
}

status=0

rust_hits="$(rust_declared_identifiers | grep -iE "${CODE_CLASSES}" || true)"
if [[ -n "${rust_hits}" ]]; then
  echo "FAIL: workstream/phase codes in Rust declared identifiers:" >&2
  while IFS= read -r hit; do
    echo "  ${hit}" >&2
  done <<< "${rust_hits}"
  echo "" >&2
  echo "Rename by subject (what it does), not by workstream." >&2
  echo "Cite the workstream in the docstring instead -- prose is exempt." >&2
  echo "Renaming an identifier build.rs or a gate script reads by name" >&2
  echo "also requires updating those references in the same commit." >&2
  status=1
else
  echo "PASS: Rust declared identifiers carry no workstream/phase codes."
fi

lean_count="$(lean_declared_identifiers | grep -icE "${CODE_CLASSES}" || true)"
if (( lean_count > LEAN_BASELINE )); then
  echo "FAIL: Lean identifiers carrying workstream/phase codes rose:" >&2
  echo "  baseline ${LEAN_BASELINE}, found ${lean_count}." >&2
  echo "Historical Lean identifiers are grandfathered, but new code must" >&2
  echo "comply from day one (CLAUDE.md, Internal-first naming)." >&2
  status=1
elif (( lean_count < LEAN_BASELINE )); then
  echo "PASS: Lean ratchet improved (${lean_count} < ${LEAN_BASELINE})."
  echo "NOTE: lower LEAN_BASELINE to ${lean_count} in $(basename "${BASH_SOURCE[0]}") to lock the gain in."
else
  echo "PASS: Lean ratchet holding at ${lean_count} grandfathered identifiers."
fi

exit "${status}"
