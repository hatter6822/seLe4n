#!/usr/bin/env bash
# shellcheck disable=SC2154  # VERSION_SITE_* arrays are defined in the sourced manifest
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
#
# bump_version.sh — set the project version at EVERY version-bearing site.
#
# Usage:  ./scripts/bump_version.sh <new-version>      # e.g. 0.31.10
#
# Per CLAUDE.md, every PR bumps the patch version and updates ALL version
# locations (README.md, GitBook, i18n badges, the Rust crates, the spec,
# codebase_map.json, …).  Doing that by hand across ~26 sites is exactly the
# error this script prevents: it rewrites each site from the shared manifest
# (scripts/version_locations.sh) and then runs the sync verifier to prove the
# result is consistent.
#
# Each site is rewritten to the NEW version regardless of its current value,
# so this also repairs any pre-existing drift.  CHANGELOG.md is deliberately
# NOT touched — its version headers are historical prose; add a new
# `## v<new> — <summary>` entry by hand (this script reminds you).

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
cd "${REPO_ROOT}"

if [[ $# -ne 1 ]]; then
  echo "Usage: $0 <new-version>   (e.g. $0 0.31.10)" >&2
  exit 2
fi
NEW="$1"
if [[ ! "${NEW}" =~ ^[0-9]+\.[0-9]+\.[0-9]+$ ]]; then
  echo "ERROR: '${NEW}' is not a 3-component version (X.Y.Z)." >&2
  exit 2
fi

CURRENT=$(grep '^version' lakefile.toml | sed 's/.*"\(.*\)"/\1/')
echo "Bumping version: ${CURRENT:-<unknown>} -> ${NEW}"
if [[ "${NEW}" == "${CURRENT}" ]]; then
  echo "NOTE: new version equals current; running as a drift-repair pass."
fi

MANIFEST="${SCRIPT_DIR}/version_locations.sh"
if [[ ! -f "${MANIFEST}" ]]; then
  echo "ERROR: version-site manifest missing at ${MANIFEST}" >&2
  exit 2
fi
# shellcheck source=scripts/version_locations.sh
source "${MANIFEST}"

declare -A TOUCHED=()
for i in "${!VERSION_SITE_FILE[@]}"; do
  file="${VERSION_SITE_FILE[$i]}"
  label="${VERSION_SITE_LABEL[$i]}"
  if [[ ! -f "${file}" ]]; then
    echo "WARN: ${file} not found (skipped: ${label})" >&2
    continue
  fi
  sed_expr="${VERSION_SITE_SED[$i]//@NEW@/${NEW}}"
  tmp="$(mktemp)"
  sed -E "${sed_expr}" "${file}" > "${tmp}"
  if cmp -s "${file}" "${tmp}"; then
    rm -f "${tmp}"
  else
    # `cat >` rewrites in place, preserving the file's mode and inode.
    cat "${tmp}" > "${file}"
    rm -f "${tmp}"
    TOUCHED["${file}"]=1
    echo "  updated: ${label}"
  fi
done

echo ""
if [[ "${#TOUCHED[@]}" -eq 0 ]]; then
  echo "No files needed changes (already at ${NEW})."
else
  echo "Rewrote ${#TOUCHED[@]} file(s)."
fi

echo ""
echo "Verifying with check_version_sync.sh ..."
echo "---"
if "${SCRIPT_DIR}/check_version_sync.sh"; then
  echo "---"
  echo "Version bump to ${NEW} complete and verified."
  echo "REMINDER: add a '## v${NEW} — <summary>' entry at the top of CHANGELOG.md."
else
  echo "---"
  echo "ERROR: post-bump verification FAILED — inspect the mismatches above." >&2
  exit 1
fi
