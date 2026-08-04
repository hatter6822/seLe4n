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
#   2. The CLAUDE.md "Known large files" list.  Its detector existed but
#      lived only in `sync_documentation_metrics.sh`, which is in no tier
#      and no workflow, so the "warning" it emits had never been seen.
#      Tolerant by design (see that script's header) so it is quiet about
#      the per-patch churn the `~N lines` approximation already signals.
#   3. Source citations carrying line numbers (`Boot.lean:551`), which are
#      stale on the next edit above them.
#   4. CLAUDE.md ↔ AGENTS.md byte-identity.  Both files state the rule in
#      their own headers ("the two files must stay byte-identical apart
#      from this header"), and only the *version line* was checked, so any
#      other divergence was invisible to CI.
# ──────────────────────────────────────────────────────────────────────

"${SCRIPT_DIR}/sync_readme_from_codebase_map.sh" --check

"${SCRIPT_DIR}/find_large_lean_files.sh" --check

# 4. Source citations must not carry line numbers.  See the script header:
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

# CLAUDE.md and AGENTS.md differ only in their leading header block: each
# names itself in an H1 and points at the other in a blockquote.  The
# shared body begins at the first `##` section, `## What this project is`,
# and must be byte-identical from there on.
# The bodies are extracted to FILES, not shell variables (PR #854 review).
# Command substitution strips every trailing newline, so a variable
# comparison silently accepts bodies that differ in trailing blank lines or
# in whether the final newline is present — i.e. it accepts files that are
# not byte-identical, which is the one thing this gate claims to enforce.
mirror_anchor='## What this project is'
mirror_tmp="$(mktemp -d)"
trap 'rm -rf "${mirror_tmp}"' EXIT
awk -v a="${mirror_anchor}" 'index($0,a)==1{f=1} f' CLAUDE.md > "${mirror_tmp}/claude"
awk -v a="${mirror_anchor}" 'index($0,a)==1{f=1} f' AGENTS.md > "${mirror_tmp}/agents"

# The body comparison above starts AT the anchor, so everything above it
# was previously unchecked (PR #854 review): a divergent paragraph of
# instructions added to one mirror's header region passed the gate, even
# though the files were then not "byte-identical apart from this header".
# Both headers are fixed text that names the file and points at its
# mirror, so pin them verbatim.
awk -v a="${mirror_anchor}" 'index($0,a)==1{exit} {print}' CLAUDE.md > "${mirror_tmp}/claude_hdr"
awk -v a="${mirror_anchor}" 'index($0,a)==1{exit} {print}' AGENTS.md > "${mirror_tmp}/agents_hdr"
cat > "${mirror_tmp}/claude_hdr_want" <<'CLAUDE_HDR_EOF'
# CLAUDE.md — seLe4n project guidance

> A mirror of this file lives at `AGENTS.md` so that non-Claude coding
> agents (and any tool that follows the AGENTS.md convention) get the
> same project rules. If you edit one, edit the other in the same PR —
> the two files must stay byte-identical apart from this header.

CLAUDE_HDR_EOF
cat > "${mirror_tmp}/agents_hdr_want" <<'AGENTS_HDR_EOF'
# AGENTS.md — seLe4n project guidance

> This file mirrors `CLAUDE.md` so that non-Claude coding agents (and any
> tool that follows the AGENTS.md convention) get the same project rules.
> If you edit one, edit the other in the same PR — the two files must
> stay byte-identical apart from this header.

AGENTS_HDR_EOF
for m in claude agents; do
  if ! cmp -s "${mirror_tmp}/${m}_hdr" "${mirror_tmp}/${m}_hdr_want"; then
    echo "FAIL: the header block of ${m^^}.md is not the pinned text." >&2
    echo "      Only the header may differ between the mirrors, and its" >&2
    echo "      exact shape is fixed. Update the pin in this script if the" >&2
    echo "      header is intentionally reworded." >&2
    diff "${mirror_tmp}/${m}_hdr_want" "${mirror_tmp}/${m}_hdr" | head -20 >&2
    exit 1
  fi
done
if [[ ! -s "${mirror_tmp}/claude" || ! -s "${mirror_tmp}/agents" ]]; then
  echo "FAIL: could not locate the shared '${mirror_anchor}' heading in both \
CLAUDE.md and AGENTS.md; the mirror check would be vacuous." >&2
  exit 1
fi
if ! cmp -s "${mirror_tmp}/claude" "${mirror_tmp}/agents"; then
  echo "FAIL: CLAUDE.md and AGENTS.md have diverged below their header blocks." >&2
  echo "      Both files require byte-identical bodies (see their own headers)." >&2
  diff "${mirror_tmp}/claude" "${mirror_tmp}/agents" | head -40 >&2
  exit 1
fi
echo "PASS: CLAUDE.md and AGENTS.md bodies are byte-identical."

# ──────────────────────────────────────────────────────────────────────
# AC5-B / X-08: GitBook content-hash drift check
# Compare H1/H2 structural headings between canonical docs/ files and
# their GitBook chapter mirrors. Emits warnings (not hard failures) for
# header divergence, since GitBook chapters are summaries and may
# legitimately have fewer headings than canonical sources.
# ────────────────────────���────────────────────────��────────────────────
gitbook_drift_warnings=0
# Mapping: canonical → gitbook mirror (pairs with known canonical references)
declare -A CANONICAL_TO_GITBOOK=(
  ["docs/CLAIM_EVIDENCE_INDEX.md"]="docs/gitbook/31-claim-vs-evidence-index.md"
  ["docs/DOCUMENTATION_SYNC_AND_COVERAGE_MATRIX.md"]="docs/gitbook/25-documentation-sync-and-coverage-matrix.md"
  ["docs/DOCS_DEDUPLICATION_MAP.md"]="docs/gitbook/27-documentation-deduplication-map.md"
  ["docs/THREAT_MODEL.md"]="docs/gitbook/28-threat-model-and-security-hardening.md"
  ["docs/CI_TELEMETRY_BASELINE.md"]="docs/gitbook/29-ci-maturity-and-telemetry-baseline.md"
  ["docs/VSPACE_MEMORY_MODEL_ADR.md"]="docs/gitbook/26-ws-b1-vspace-memory-adr.md"
)

for canonical in "${!CANONICAL_TO_GITBOOK[@]}"; do
  gitbook="${CANONICAL_TO_GITBOOK[$canonical]}"
  if [[ -f "${REPO_ROOT}/${canonical}" ]] && [[ -f "${REPO_ROOT}/${gitbook}" ]]; then
    # Extract H1/H2 headings (lines starting with # or ##, not ###)
    canonical_headers=$(grep -E '^#{1,2} ' "${REPO_ROOT}/${canonical}" | head -20 | sha256sum | cut -d' ' -f1)
    gitbook_headers=$(grep -E '^#{1,2} ' "${REPO_ROOT}/${gitbook}" | head -20 | sha256sum | cut -d' ' -f1)
    if [[ "${canonical_headers}" != "${gitbook_headers}" ]]; then
      echo "warning: GitBook header drift detected: ${canonical} ↔ ${gitbook}" >&2
      gitbook_drift_warnings=$((gitbook_drift_warnings + 1))
    fi
  fi
done
if [[ ${gitbook_drift_warnings} -gt 0 ]]; then
  # AN11-E.5 (TST-M05): GitBook drift now fails hard.  Previously a warning,
  # which let GitBook chapters drift silently from their canonical sources.
  # If the drift is intentional (e.g., a deliberate divergence that the
  # mirror cannot reflect), update both files in lockstep so the H1/H2
  # header set hashes match.
  echo "error: ${gitbook_drift_warnings} GitBook chapter(s) have divergent H1/H2 headers from canonical sources." >&2
  echo "  Run: diff <(grep -E '^#{1,2} ' docs/FILE.md) <(grep -E '^#{1,2} ' docs/gitbook/CHAPTER.md) to inspect." >&2
  exit 1
fi

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
