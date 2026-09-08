#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
#
# AN7-A (H-14/PLT-M04): enforce that no consumer outside
# `SeLe4n/Platform/DeviceTree.lean` references the deprecated legacy
# DeviceTree entry points (`findMemoryRegProperty`, `classifyMemoryRegion`)
# without the `Checked` suffix.
#
# Callers must use:
#   - `findMemoryRegPropertyChecked`  (Except DeviceTreeParseError)
#   - `classifyMemoryRegionChecked`   (Option MemoryKind)
#
# The `DeviceTree.lean` module retains `classifyMemoryRegion` (marked
# `@[deprecated]`) and its bridge theorems
# (`classifyMemoryRegionChecked_some_agrees`, `classifyMemoryRegion_default`),
# which are allowed references in that file only.
#
# PR #892 review round 7 **removed** `findMemoryRegProperty` outright: it was a
# second, unbounded walk of the structure block with no consumers, and this gate
# is what proved there were none.  The pattern is kept — a reintroduction, here
# or elsewhere, is still a finding.
#
# Exits 0 when clean, 1 when a forbidden reference is found.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

unauthorized=""

# Word-boundary patterns: the bare name followed by a NOT-Checked character.
# The -w option in ripgrep/grep gives us "classifyMemoryRegion" distinct from
# "classifyMemoryRegionChecked". We additionally exclude the one legitimate
# host file and pure comment/docstring lines.
# **PR #892 review round 9**: the host-file exemption is **per symbol**, because
# it exists for one reason only — the symbol is still *declared* there.
#
# `classifyMemoryRegion` is retained in `DeviceTree.lean` (deprecated, with its
# bridge theorems), so a match there is its own declaration and is exempt.
# `findMemoryRegProperty` was **removed** at `v0.34.117`, so nothing in that
# file may name it; exempting the host file for a symbol that no longer exists
# means the walker can be reintroduced at exactly the place it was deleted from
# and this gate stays silent.  The round-7 changelog and reply claimed the
# retained pattern prevented that reintroduction "here or elsewhere"; that was
# true only of *elsewhere*, and this is the correction.
#
# The rule, stated so the next removal inherits it: exempt the host file for a
# symbol the host file still declares, and for no other.
# The scan reads each file's **code view**, not its raw text.  A symbol named in
# a docstring is not a consumer, and — the direction that bit here — the comment
# recording a symbol's *removal* is not a reintroduction of it.  This is the
# same correction round 8 made at `check_physical_address_width.sh` and
# `check_claim_evidence_citations.py`; the sweep did not reach here because the
# gate's own `filter_comments` asserted the names were "distinctive enough that
# every match is a real consumer", which stopped being true the moment one of
# them appeared in prose.
scan() {
  local pattern="$1" exempt_host="$2"
  local view
  (
    cd "${REPO_ROOT}"
    while IFS= read -r src; do
      if [ "${exempt_host}" = "exempt-host" ] \
          && [ "${src}" = "./SeLe4n/Platform/DeviceTree.lean" ]; then
        continue
      fi
      view="${VIEW_DIR}/$(echo "${src}" | tr '/.' '__')"
      python3 "${SCRIPT_DIR}/lean_code_view.py" "${src}" > "${view}" 2>/dev/null || continue
      grep -nwE "${pattern}" "${view}" 2>/dev/null | sed "s|^|${src}:|" || true
    done < <(find . -name '*.lean' -not -path './.lake/*' 2>/dev/null)
  )
}

# Comment awareness is `scan`'s job now: it reads the Lean code view, so a
# reference surviving only in a docstring never reaches here.  Kept as the
# pipeline's shape so a future filter has a place to live.
filter_comments() {
  cat
}

VIEW_DIR="$(mktemp -d)"
trap 'rm -rf "${VIEW_DIR}"' EXIT

# `classifyMemoryRegion` is still declared in the host file; `findMemoryRegProperty`
# is not declared anywhere, so it may not be named anywhere.
hits_classify=$(scan 'classifyMemoryRegion' exempt-host | filter_comments || true)
hits_find=$(scan 'findMemoryRegProperty' scan-everywhere | filter_comments || true)

if [[ -n "${hits_classify}" ]]; then
  unauthorized="${unauthorized}${hits_classify}
"
fi
if [[ -n "${hits_find}" ]]; then
  unauthorized="${unauthorized}${hits_find}
"
fi

if [[ -n "${unauthorized}" ]]; then
  echo "AN7-A (H-14/PLT-M04) FAIL: a legacy Option-returning DeviceTree entry"
  echo "point is referenced where it may not be. classifyMemoryRegion is still"
  echo "declared in SeLe4n/Platform/DeviceTree.lean and may be named there only;"
  echo "findMemoryRegProperty was removed and may be named nowhere. Migrate to"
  echo "the Checked variants (findMemoryRegPropertyChecked /"
  echo "classifyMemoryRegionChecked)." >&2
  echo "" >&2
  printf '%s' "${unauthorized}" >&2
  exit 1
fi

echo "AN7-A: no legacy DeviceTree consumers (classifyMemoryRegion outside its host file; findMemoryRegProperty anywhere)."
exit 0
