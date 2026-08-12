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

# WS-SM SM8.B: no live syscall arm may reach a boot-pinned scheduler primitive.
# PR #861 review rounds 10 and 12 found this defect three times, one syscall per
# round — `.tcbResume`, `.send`, `.tcbSetPriority`/`.tcbSetMCPriority` — each
# fixed on discovery, none found by a gate.  Running the check found four more
# (`.schedContextBind`, `.schedContextConfigure`, `.schedContextUnbind`, and the
# retype destroy path) that no review round had reached.
#
# It lives in Tier 1 rather than Tier 0 because round 29 moved detection to
# Lean's elaborated environment: it runs `lake env lean` over a probe, so it
# needs the build above.  That is also why it must come *after* both `lake
# build` calls — the probe imports `SeLe4n` and `SeLe4n.Platform.Staged`, and a
# staged per-core primitive is invisible without the second.
#
# The self-test runs first: it re-walks the pre-SMP operations and fails if the
# gate no longer detects them, so a gate that has lost its reach fails loudly
# instead of passing everything.
run_check "BUILD" "${SCRIPT_DIR}/check_live_arm_per_core_routing.py" --self-test
run_check "BUILD" "${SCRIPT_DIR}/check_live_arm_per_core_routing.py"

finalize_report
