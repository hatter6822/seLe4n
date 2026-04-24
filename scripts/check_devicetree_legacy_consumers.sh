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
# The `DeviceTree.lean` module retains both legacy definitions (marked
# `@[deprecated]`) and bridge theorems (`classifyMemoryRegionChecked_some_agrees`,
# `classifyMemoryRegion_default`), which are allowed references in that
# file only.
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
scan() {
  local pattern="$1"
  (
    cd "${REPO_ROOT}"
    if command -v rg >/dev/null 2>&1; then
      rg -n -w "${pattern}" --type-add 'lean:*.lean' -tlean . 2>/dev/null \
        | grep -v '^./SeLe4n/Platform/DeviceTree\.lean:' || true
    else
      find . -name '*.lean' \
        ! -path './SeLe4n/Platform/DeviceTree.lean' \
        -print0 \
        | xargs -0 grep -nwE "${pattern}" 2>/dev/null || true
    fi
  )
}

# Lines that are pure comments (`--` at column 1, or inside /-...-/ blocks)
# carry no semantic reference to the symbol; allow them.
filter_comments() {
  # Passthrough — we don't attempt comment-aware parsing here; the two
  # symbol names are distinctive enough that every match is a real consumer.
  # If a test suite references them in a docstring (`/-- foo -/`), we still
  # want to flag it so that the suite either migrates or documents intent.
  cat
}

hits_classify=$(scan 'classifyMemoryRegion' | filter_comments || true)
hits_find=$(scan 'findMemoryRegProperty' | filter_comments || true)

if [[ -n "${hits_classify}" ]]; then
  unauthorized="${unauthorized}${hits_classify}
"
fi
if [[ -n "${hits_find}" ]]; then
  unauthorized="${unauthorized}${hits_find}
"
fi

if [[ -n "${unauthorized}" ]]; then
  echo "AN7-A (H-14/PLT-M04) FAIL: legacy Option-returning DeviceTree entry"
  echo "points referenced outside SeLe4n/Platform/DeviceTree.lean. Migrate to"
  echo "the Checked variants (findMemoryRegPropertyChecked /"
  echo "classifyMemoryRegionChecked)." >&2
  echo "" >&2
  printf '%s' "${unauthorized}" >&2
  exit 1
fi

echo "AN7-A: no legacy DeviceTree consumers outside DeviceTree.lean."
exit 0
