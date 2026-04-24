#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck disable=SC1091
source "${SCRIPT_DIR}/test_lib.sh"

parse_common_args "$@"
cd "${REPO_ROOT}"

ensure_lake_available

run_check "BUILD" lake build

# AN7-D.7 (PLT-M07): force the seven staged platform-binding modules into
# the build graph.  Without this, regressions in modules not reached from
# `Main.lean` (e.g., the RPi5 boot VSpaceRoot AN7-D.2) would go undetected
# until a future workstream reaches them.  See `SeLe4n/Platform/Staged.lean`
# for the module list.
run_check "BUILD" lake build SeLe4n.Platform.Staged

finalize_report
