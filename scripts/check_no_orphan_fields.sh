#!/usr/bin/env bash
# scripts/check_no_orphan_fields.sh
#
# Per WS-RC R12.D (closes DEEP-ARCH-02 false positive structurally):
# every `*_fields : List StateField` definition must have at least one
# consumer somewhere in the SeLe4n tree (in-file or out-of-file).
#
# This detects truly dead metadata — defs that are declared but never
# referenced. File-local helpers (used only via fieldsDisjoint within
# the same file) pass the gate.
#
# The naive "out-of-file consumer required" interpretation would fail
# spuriously on the v0.30.11 tree (all 11 _fields defs have 0
# out-of-file consumers but 3-5 in-file consumers each via
# fieldsDisjoint calls). The relaxed gate matches the deep audit's
# intent: detect orphan metadata, not enforce export discipline.

set -euo pipefail
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
cd "$ROOT"

errors=0
TARGETS=(SeLe4n/Kernel/CrossSubsystem.lean)

for file in "${TARGETS[@]}"; do
    if [ ! -f "$file" ]; then
        echo "FAIL: $file does not exist"
        exit 1
    fi
    while IFS= read -r line; do
        name=$(echo "$line" | sed -E 's/^def ([A-Za-z_]+_fields).*/\1/')
        if [ -z "$name" ]; then continue; fi
        # Count ALL hits in SeLe4n tree, including the def line itself.
        # A live def contributes 1; we need at least 2 to mean "used".
        total_hits=$(grep -rn "\b${name}\b" SeLe4n/ | wc -l)
        if [ "$total_hits" -lt 2 ]; then
            echo "ERROR: '$name' is dead (only the def itself, 0 consumers)"
            errors=$((errors + 1))
        fi
    done < <(grep -E "^def [A-Za-z_]+_fields[[:space:]]*:" "$file")
done

if [ "$errors" -gt 0 ]; then
    echo "FAIL: $errors dead *_fields definition(s)"
    exit 1
fi
echo "OK: every *_fields definition is used (in-file or out-of-file)"
