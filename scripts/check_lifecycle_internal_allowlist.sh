#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
#
# AN4-A (H-02): enforce consumer allowlist for
# `SeLe4n.Kernel.Internal.lifecycleRetypeObject`.
#
# The internal retype primitive bypasses `lifecyclePreRetypeCleanup` and
# `scrubObjectMemory`; production dispatch MUST call `lifecycleRetypeWithCleanup`
# or `lifecycleRetypeDirectWithCleanup`. Any `.lean` file that references
# `Internal.lifecycleRetypeObject` directly, or opens `SeLe4n.Kernel.Internal`
# (or its `Internal` shorthand while inside `SeLe4n.Kernel`), must appear in
# `scripts/lifecycle_internal_allowlist.txt`.
#
# Run with `--check` (default) to fail-close on unauthorized consumers.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
ALLOWLIST="${REPO_ROOT}/scripts/lifecycle_internal_allowlist.txt"

if [[ ! -f "${ALLOWLIST}" ]]; then
    echo "AN4-A ERROR: allowlist ${ALLOWLIST} missing." >&2
    exit 1
fi

allowed=$(grep -vE "^[[:space:]]*(#|$)" "${ALLOWLIST}" | sort -u)

unauthorized=""

# Collect referenced .lean files, one per line, stripping leading ./ if any.
# Two signals trigger inclusion:
#   (1) a literal `SeLe4n.Kernel.Internal.lifecycleRetypeObject` token
#   (2) an `open SeLe4n.Kernel.Internal` / `open Internal` directive at the
#       start of a line (allowing leading whitespace).
while IFS= read -r file; do
    normalized="${file#./}"
    if [[ "${normalized}" == "scripts/lifecycle_internal_allowlist.txt" ]]; then
        continue
    fi
    if ! grep -Fxq "${normalized}" <<<"${allowed}"; then
        unauthorized+="${normalized}"$'\n'
    fi
done < <(
    {
        grep -rln "SeLe4n\.Kernel\.Internal\.lifecycleRetypeObject" \
            "${REPO_ROOT}/SeLe4n" "${REPO_ROOT}/tests" "${REPO_ROOT}/Main.lean" \
            --include="*.lean" 2>/dev/null || true
        grep -rlnE '^[[:space:]]*open[[:space:]]+(SeLe4n\.Kernel\.)?Internal[[:space:]]*$' \
            "${REPO_ROOT}/SeLe4n" "${REPO_ROOT}/tests" "${REPO_ROOT}/Main.lean" \
            --include="*.lean" 2>/dev/null || true
    } | sed "s|^${REPO_ROOT}/||" | sort -u
)

if [[ -n "${unauthorized}" ]]; then
    echo "AN4-A FAIL: unauthorized consumer(s) of SeLe4n.Kernel.Internal detected:" >&2
    printf '  %s\n' ${unauthorized} >&2
    cat >&2 <<'EOM'

Add the file to `scripts/lifecycle_internal_allowlist.txt` ONLY if it is
proof-chain infrastructure (theorem statement requires the internal def) or
test harness (direct exercise of the internal step for negative-branch
coverage). Production dispatch must call `lifecycleRetypeWithCleanup` or
`lifecycleRetypeDirectWithCleanup` instead.
EOM
    exit 1
fi

echo "AN4-A: Lifecycle internal consumer allowlist check PASSED."
