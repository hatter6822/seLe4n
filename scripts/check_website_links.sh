#!/usr/bin/env bash
# check_website_links.sh — verify that all paths referenced by the seLe4n
# project website (sele4n.org / hatter6822.github.io) still exist in the repo.
#
# The website's index.html contains links to source files, documentation,
# scripts, assets, and directories in this repository.  If any of those paths
# are renamed or deleted without updating the website, visitors will hit 404s.
#
# This script reads the manifest at scripts/website_link_manifest.txt and
# checks every listed path.  It is designed to be called from
# test_tier0_hygiene.sh (and therefore runs in every CI lane).
#
# Exit codes:
#   0  All paths present.
#   1  One or more paths missing — CI should fail.
#   2  Manifest file itself is missing (setup error).

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
MANIFEST="${SCRIPT_DIR}/website_link_manifest.txt"

if [[ ! -f "${MANIFEST}" ]]; then
  echo "ERROR: website link manifest not found at ${MANIFEST}" >&2
  exit 2
fi

missing=0
missing_paths=()

while IFS= read -r line; do
  # Skip comments and blank lines.
  [[ -z "${line}" || "${line}" =~ ^[[:space:]]*# ]] && continue

  # Strip inline comments and trailing whitespace.
  path="${line%%#*}"
  path="${path%"${path##*[![:space:]]}"}"
  [[ -z "${path}" ]] && continue

  target="${REPO_ROOT}/${path}"

  if [[ "${path}" == */ ]]; then
    # Directory entry.
    if [[ ! -d "${target}" ]]; then
      echo "MISSING directory: ${path}" >&2
      missing_paths+=("${path}")
      missing=$((missing + 1))
    fi
  else
    # File entry.
    if [[ ! -f "${target}" ]]; then
      echo "MISSING file: ${path}" >&2
      missing_paths+=("${path}")
      missing=$((missing + 1))
    fi
  fi
done < "${MANIFEST}"

if [[ "${missing}" -gt 0 ]]; then
  echo "" >&2
  echo "Website link protection: ${missing} path(s) referenced by sele4n.org are missing." >&2
  echo "Either restore the path(s), update the website (hatter6822.github.io), or" >&2
  echo "update scripts/website_link_manifest.txt if the change is intentional." >&2
  echo "" >&2
  echo "Missing paths:" >&2
  for p in "${missing_paths[@]}"; do
    echo "  - ${p}" >&2
  done
  exit 1
fi

echo "Website link protection: all paths present."
