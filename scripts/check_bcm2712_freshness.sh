#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
#
# AN7-F (PLT-L): BCM2712 datasheet reference freshness check.
#
# Parses the `BCM2712_DATASHEET_VERIFIED: YYYY-MM-DD` marker in
# `SeLe4n/Platform/RPi5/Board.lean` and warns (non-fatal) when the
# marker is more than one calendar year old.  The intent is to surface
# stale datasheet references at CI time without blocking releases — a
# maintainer can re-verify the constants against the latest Raspberry Pi
# Ltd documentation and bump the marker in a hygiene commit.
#
# Exit codes:
#   0 — marker present and within one year
#   1 — marker missing or malformed (hard failure)
#   0 with a WARNING — marker older than one year (advisory, not fatal)

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
BOARD_FILE="${REPO_ROOT}/SeLe4n/Platform/RPi5/Board.lean"

if [[ ! -f "${BOARD_FILE}" ]]; then
  echo "AN7-F ERROR: ${BOARD_FILE} missing." >&2
  exit 1
fi

marker=$(grep -oE 'BCM2712_DATASHEET_VERIFIED: [0-9]{4}-[0-9]{2}-[0-9]{2}' "${BOARD_FILE}" || true)
if [[ -z "${marker}" ]]; then
  echo "AN7-F ERROR: BCM2712_DATASHEET_VERIFIED marker missing in Board.lean." >&2
  exit 1
fi

marker_date="${marker##* }"
current_year=$(date -u +%Y)
marker_year="${marker_date%%-*}"
year_diff=$((current_year - marker_year))

if (( year_diff > 1 )); then
  echo "AN7-F WARNING: BCM2712 datasheet marker is ${year_diff} years old (${marker_date})." >&2
  echo "  Please re-verify BCM2712 constants against upstream Raspberry Pi Ltd" >&2
  echo "  documentation and bump the marker in Board.lean." >&2
fi

echo "AN7-F: BCM2712 datasheet marker present (${marker_date})."
exit 0
