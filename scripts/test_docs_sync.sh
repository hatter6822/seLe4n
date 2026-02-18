#!/usr/bin/env bash
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
