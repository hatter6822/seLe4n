#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
cd "${REPO_ROOT}"

python3 "${SCRIPT_DIR}/generate_doc_navigation.py"

before_hashes="$(sha256sum docs/gitbook/README.md docs/gitbook/SUMMARY.md)"
python3 "${SCRIPT_DIR}/generate_doc_navigation.py" >/dev/null
after_hashes="$(sha256sum docs/gitbook/README.md docs/gitbook/SUMMARY.md)"
if [[ "${before_hashes}" != "${after_hashes}" ]]; then
  echo "Generated navigation files are not stable across repeated generation runs." >&2
  exit 1
fi

python3 "${SCRIPT_DIR}/check_markdown_links.py"

python3 "${SCRIPT_DIR}/generate_codebase_map.py" --pretty --check

# ──────────────────────────────────────────────────────────────────────
# Documentation-claim drift gates.
#
# `generate_codebase_map.py --check` above proves the map matches the tree.
# It does NOT prove anything downstream of the map was re-synced FROM it,
# and the three checks below close that gap.  Each guards a claim the
# project publishes but nothing previously enforced, and each had actually
# drifted when they were added:
#
#   1. README.md + SELE4N_SPEC.md headline metrics (production/test LoC,
#      proved-declaration count).  A stale map is caught; a fresh map that
#      nobody propagated was not — so regenerating the map and forgetting
#      the propagation silently published wrong numbers.
#   2. The "Known large files" list (docs/agent_guide/LARGE_FILES.md).  Its detector existed but
#      lived only in `sync_documentation_metrics.sh`, which is in no tier
#      and no workflow, so the "warning" it emits had never been seen.
#      Tolerant by design (see that script's header) so it is quiet about
#      the per-patch churn the `~N lines` approximation already signals.
#   3. The same figures where they are *translated*.  Eleven i18n READMEs
#      and four GitBook surfaces quoted them, the sync matrix said the
#      translations mirror the root README, and nothing propagated: the
#      locales published a `v0.33.101` snapshot against a `v0.34.x` tree.
#      Its self-test runs beside it because three of those languages
#      inflect the counted noun, so the sync emits translated text and a
#      scanner that stopped selecting the right form would fail silently
#      in a language no reader of this file need speak.
#   4. Source citations carrying line numbers (`Boot.lean:551`), which are
#      stale on the next edit above them.
#   5. AGENTS.md is a symlink to CLAUDE.md.  It used to be a byte-identical
#      mirror (only the *version line* was once checked, so any other
#      divergence was invisible to CI); a symlink makes divergence
#      impossible, and the check below pins the link in the git index.
# ──────────────────────────────────────────────────────────────────────

"${SCRIPT_DIR}/sync_readme_from_codebase_map.sh" --check

python3 "${SCRIPT_DIR}/sync_translated_metrics.py" --self-test
python3 "${SCRIPT_DIR}/sync_translated_metrics.py" --check

"${SCRIPT_DIR}/find_large_lean_files.sh" --check

# 5. Source citations must not carry line numbers.  See the script header:
#    511 such citations had accumulated, 178 verifiably pointing at unrelated
#    code and 3 past end-of-file, because a line number goes stale the moment
#    anything above it changes.  Fenced blocks (verbatim tool output) and
#    CHANGELOG.md (append-only history, quotes real diagnostics) are exempt.
python3 "${SCRIPT_DIR}/check_source_line_citations.py"

# The gate above has now shipped under-reaching twice in consecutive
# rounds — the orphaned `:NNN` its own cleanup sweep produced, then the
# GitHub `#L123` anchor spelling — and both times it printed PASS over
# documents holding exactly what it forbids.  This pins each spelling it
# must catch, and each one it must leave alone.
python3 "${SCRIPT_DIR}/test_source_line_citations_gate.py"

# AGENTS.md is a symlink to CLAUDE.md, so the two cannot diverge (it replaced a
# byte-identical mirror whose sync this check used to enforce).  What is checked
# is the RELATION, in the git index rather than the working tree: the entry is
# a symlink (mode 120000) and its target is exactly `CLAUDE.md`.  A regular file
# that merely contains the same text, or a symlink to anything else, fails --
# and so does a checkout with `core.symlinks=false`, where the working-tree file
# would be a one-line text file that only the index can tell apart.
agents_entry="$(git ls-files -s -- AGENTS.md)"
agents_mode="${agents_entry%% *}"
if [[ "${agents_mode}" != "120000" ]]; then
  echo "FAIL: AGENTS.md must be a symlink to CLAUDE.md in the git index (mode '${agents_mode:-absent}', want 120000)." >&2
  exit 1
fi
agents_target="$(git cat-file -p ":AGENTS.md")"
if [[ "${agents_target}" != "CLAUDE.md" ]]; then
  echo "FAIL: AGENTS.md is a symlink to '${agents_target}', not to CLAUDE.md." >&2
  exit 1
fi
if [[ -L AGENTS.md && "$(readlink AGENTS.md)" != "CLAUDE.md" ]]; then
  echo "FAIL: the working-tree AGENTS.md symlink points at '$(readlink AGENTS.md)', not CLAUDE.md." >&2
  exit 1
fi
echo "PASS: AGENTS.md is a symlink to CLAUDE.md."

# AC5-B / X-08 (retired): a GitBook content-hash drift check compared the
# H1/H2 headings of six canonical root documents against GitBook chapters that
# restated them.  Those restating chapters (25-31) were retired: the GitBook
# navigation now links the canonical documents directly, so there is no second
# copy left to drift, and a check keyed on files that no longer exist would
# pass vacuously.  See docs/DOCUMENTATION_SYNC_AND_COVERAGE_MATRIX.md section 0.

# Prefer an already-installed elan toolchain in non-login shells.
if [[ -f "${HOME}/.elan/env" ]]; then
  # shellcheck disable=SC1091
  source "${HOME}/.elan/env"
fi

# Keep docs-sync deterministic when possible by attempting Lean setup before the
# optional doc-gen4 probe. Setup remains best-effort by default so docs-sync can
# still validate navigation/link consistency on restricted/offline environments.
if ! command -v lake >/dev/null 2>&1; then
  if [[ "${DOCS_SYNC_SKIP_LEAN_SETUP:-0}" == "1" ]]; then
    echo "DOCS_SYNC_SKIP_LEAN_SETUP=1: skipping Lean setup; doc-gen4 probe disabled in this run."
  elif [[ -x "${SCRIPT_DIR}/setup_lean_env.sh" ]]; then
    echo "lake not found; attempting setup_lean_env.sh for docs-sync doc-gen4 probe"
    if "${SCRIPT_DIR}/setup_lean_env.sh"; then
      export PATH="${HOME}/.elan/bin:${PATH}"
    else
      if [[ "${DOCS_SYNC_REQUIRE_LEAN_SETUP:-0}" == "1" ]]; then
        echo "DOCS_SYNC_REQUIRE_LEAN_SETUP=1: setup_lean_env.sh failed; failing docs-sync." >&2
        exit 1
      fi
      echo "warning: setup_lean_env.sh failed; continuing docs-sync without doc-gen4 probe." >&2
    fi
  else
    echo "lake not available and setup_lean_env.sh is missing; skipping optional doc-gen4 invocation."
  fi
fi

if command -v lake >/dev/null 2>&1; then
  if lake exe doc-gen4 --help >/dev/null 2>&1; then
    lake exe doc-gen4 SeLe4n
  else
    echo "doc-gen4 executable not available in this environment; navigation/link automation still enforced."
  fi
else
  echo "lake not available in this environment; skipping optional doc-gen4 invocation."
fi
