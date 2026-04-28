#!/usr/bin/env bash
# scripts/check_production_staging_partition.sh
#
# Per WS-RC R12.B (closes DEEP-ARCH-01 false positive structurally):
# enforce the production/staged module partition.
#
# The gate runs three checks:
#
#   1. Compute the production set = transitive `^import SeLe4n.` closure
#      from `SeLe4n.lean` (the public library entry point).
#   2. Compute the staged set     = transitive closure from
#      `Platform/Staged.lean` (the build anchor that pulls staged-only
#      modules into CI).
#   3. Verify that `staged_only := staged_set \ production_set` matches
#      the human-maintained allowlist `staged_module_allowlist.txt`
#      EXACTLY.
#   4. Verify that no module carrying a `STATUS: staged` marker has
#      leaked into the production set.
#
# Failure produces a diff so a contributor can see what changed and
# update either the source markers or the allowlist (or both).

set -euo pipefail
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
cd "$ROOT"

ALLOWLIST="$SCRIPT_DIR/staged_module_allowlist.txt"
if [ ! -f "$ALLOWLIST" ]; then
    echo "FAIL: missing $ALLOWLIST"
    exit 1
fi

trace_imports() {
    local entry="$1"
    declare -A seen
    local queue=("$entry")
    while [ ${#queue[@]} -gt 0 ]; do
        local curr="${queue[0]}"
        queue=("${queue[@]:1}")
        if [ -n "${seen[$curr]:-}" ]; then continue; fi
        seen[$curr]=1
        local file="${curr//.//}.lean"
        if [ ! -f "$file" ]; then continue; fi
        local imp
        while IFS= read -r imp; do
            queue+=("$imp")
        done < <(grep -E "^import SeLe4n\." "$file" | awk '{print $2}')
    done
    for k in "${!seen[@]}"; do echo "$k"; done | sort -u
}

production_set="$(trace_imports SeLe4n)"
staged_set="$(trace_imports SeLe4n.Platform.Staged)"
staged_only="$(comm -23 <(echo "$staged_set") <(echo "$production_set"))"
allowed="$(grep -vE '^\s*(#|$)' "$ALLOWLIST" | awk '{print $1}' | sort -u)"

errors=0

# Check 1: staged_only must equal the allowlist exactly.
extras="$(comm -23 <(echo "$staged_only") <(echo "$allowed"))"
if [ -n "$extras" ]; then
    echo "ERROR: modules in staged_only but NOT in allowlist:"
    echo "$extras" | sed 's/^/    /'
    echo "  Add to $(basename "$ALLOWLIST") with rationale, OR"
    echo "  remove the import from Platform/Staged.lean."
    errors=$((errors + 1))
fi
missing="$(comm -13 <(echo "$staged_only") <(echo "$allowed"))"
if [ -n "$missing" ]; then
    echo "ERROR: modules in allowlist but NOT staged-only (entered production?):"
    echo "$missing" | sed 's/^/    /'
    echo "  Remove from $(basename "$ALLOWLIST"), OR"
    echo "  re-stage the module."
    errors=$((errors + 1))
fi

# Check 2: every "STATUS: staged" file must NOT be in production_set.
while IFS= read -r file; do
    if [ -z "$file" ]; then continue; fi
    mod="$(echo "$file" | sed 's|^\./||; s|\.lean$||; s|/|.|g')"
    if echo "$production_set" | grep -qx "$mod"; then
        echo "ERROR: $file has 'STATUS: staged' marker but is reachable from production"
        errors=$((errors + 1))
    fi
done < <(grep -rlE "^>?\s*\*\*STATUS: staged|^--\s*STATUS: staged" SeLe4n 2>/dev/null || true)

if [ "$errors" -gt 0 ]; then
    echo "FAIL: production/staged partition violation ($errors error(s))"
    exit 1
fi

staged_count=$(echo "$staged_only" | grep -c . || true)
echo "OK: production/staged partition consistent (${staged_count} staged-only modules verified against allowlist)"
