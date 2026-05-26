#!/usr/bin/env bash
# =============================================================================
# Pre-commit hook: Verify staged Lean modules compile and contain no sorry
#
# This hook prevents the exact failure mode from WS-N2/N3 where code was
# committed without ever compiling the specific module under development.
# The default `lake build` only compiles modules reachable from Main.lean
# and test executables — isolated modules (like RobinHood before kernel
# integration) silently pass even with broken proofs.
#
# What this hook does:
#   1. Finds all staged .lean files (new or modified)
#   2. Converts file paths to Lean module names
#   3. Runs `lake build <module>` for each
#   4. Checks for `sorry` in staged .lean content
#   5. Blocks the commit if any check fails
#
# To bypass in emergencies: git commit --no-verify
# (CLAUDE.md forbids agents from using --no-verify)
# =============================================================================

set -euo pipefail

# Ensure elan/lean are available
if [ -f "$HOME/.elan/env" ]; then
    # shellcheck source=/dev/null
    source "$HOME/.elan/env"
fi

# --- Version-sync check (CLAUDE.md: every PR bumps the patch version and
#     updates ALL version locations) ---
# Runs only when a version-bearing file is staged, so commits that touch no
# version site are never blocked.  The site list and verifier are shared via
# scripts/version_locations.sh + scripts/check_version_sync.sh (Tier 0 also
# runs the verifier).  This needs no Lean toolchain, so it precedes the lake
# check below.
PRE_COMMIT_REPO_ROOT="$(git rev-parse --show-toplevel 2>/dev/null || true)"
if [ -n "${PRE_COMMIT_REPO_ROOT}" ] \
   && [ -f "${PRE_COMMIT_REPO_ROOT}/scripts/version_locations.sh" ] \
   && [ -f "${PRE_COMMIT_REPO_ROOT}/scripts/check_version_sync.sh" ]; then
    # shellcheck source=scripts/version_locations.sh
    source "${PRE_COMMIT_REPO_ROOT}/scripts/version_locations.sh"
    mapfile -t STAGED_FOR_VERSION < <(git diff --cached --name-only --diff-filter=ACMR || true)
    VERSION_FILE_STAGED=0
    if [ "${#STAGED_FOR_VERSION[@]}" -gt 0 ]; then
        for _staged in "${STAGED_FOR_VERSION[@]}"; do
            # shellcheck disable=SC2154
            for _site in "${VERSION_SITE_FILE[@]}"; do
                if [ "${_staged}" = "${_site}" ]; then
                    VERSION_FILE_STAGED=1
                    break 2
                fi
            done
        done
    fi
    if [ "${VERSION_FILE_STAGED}" -eq 1 ]; then
        echo "pre-commit: version-bearing file staged — verifying version sync..."
        if ! "${PRE_COMMIT_REPO_ROOT}/scripts/check_version_sync.sh"; then
            echo ""
            echo "COMMIT BLOCKED: version locations are out of sync (see above)."
            echo "Sync every site with: ./scripts/bump_version.sh <version>"
            exit 1
        fi
    fi
fi

if ! command -v lake &>/dev/null; then
    echo "⚠ pre-commit: lake not found, skipping Lean build check"
    exit 0
fi

# AA2-C (H-5): Use bash array to avoid word-splitting on filenames with spaces.
mapfile -t STAGED_LEAN_FILES < <(git diff --cached --name-only --diff-filter=ACMR -- '*.lean' | grep -v '^\.lake/' || true)

if [ "${#STAGED_LEAN_FILES[@]}" -eq 0 ]; then
    exit 0
fi

echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "pre-commit: checking staged Lean modules"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

ERRORS=0

# Secure temp file for build output (M-NEW-12: eliminates symlink race with PID-based names)
BUILD_LOG="$(mktemp)"
trap 'rm -f "${BUILD_LOG}"' EXIT

# --- Check 1: No sorry in staged content ---
echo ""
echo "[1/2] Checking for sorry in staged Lean files..."

for file in "${STAGED_LEAN_FILES[@]}"; do
    # Check the staged content (not working tree) for sorry
    # Use git show :file to get staged version
    if git show ":$file" 2>/dev/null | grep -n '^\([^-].*\)\?\bsorry\b' | grep -v '^\([^-].*\)\?--.*sorry' | grep -v '^\([^-].*\)\?/-' | grep -qv '^\([^-].*\)\?".*sorry'; then
        # More precise check: exclude comments and strings
        SORRY_LINES=$(git show ":$file" 2>/dev/null | grep -n '\bsorry\b' | grep -v '\-\-.*sorry' | grep -v '".*sorry.*"' | grep -v "doc comment" || true)
        if [ -n "$SORRY_LINES" ]; then
            echo "  ERROR: sorry found in $file:"
            echo "$SORRY_LINES" | head -5 | sed 's/^/    /'
            ERRORS=$((ERRORS + 1))
        fi
    fi
done

if [ $ERRORS -eq 0 ]; then
    echo "  OK: no sorry found"
fi

# --- Check 2: Build each modified module ---
echo ""
echo "[2/2] Building staged Lean modules..."

BUILD_ERRORS=0
MODULES_CHECKED=0

for file in "${STAGED_LEAN_FILES[@]}"; do
    # Skip test files and non-source files
    case "$file" in
        tests/*|.lake/*|scripts/*) continue ;;
    esac

    # Convert file path to module name
    # SeLe4n/Kernel/RobinHood/Bridge.lean -> SeLe4n.Kernel.RobinHood.Bridge
    # Main.lean -> Main
    MODULE=$(echo "$file" | sed 's/\.lean$//' | tr '/' '.')

    if [ -z "$MODULE" ]; then
        continue
    fi

    MODULES_CHECKED=$((MODULES_CHECKED + 1))
    echo "  Building $MODULE ..."

    # Build with timeout (5 minutes per module)
    if ! timeout 300 lake build "$MODULE" > "${BUILD_LOG}" 2>&1; then
        BUILD_ERRORS=$((BUILD_ERRORS + 1))
        ERROR_COUNT=$(grep -c "^error:" "${BUILD_LOG}" 2>/dev/null || echo "?")
        echo "  FAILED: $MODULE ($ERROR_COUNT errors)"
        grep "^error:" "${BUILD_LOG}" 2>/dev/null | head -5 | sed 's/^/    /'
        if [ "$ERROR_COUNT" != "?" ] && [ "$ERROR_COUNT" -gt 5 ]; then
            echo "    ... and $((ERROR_COUNT - 5)) more"
        fi
    else
        echo "  OK: $MODULE"
    fi
done

if [ $MODULES_CHECKED -eq 0 ]; then
    echo "  (no source modules to build)"
fi

# --- Summary ---
echo ""
TOTAL_ERRORS=$((ERRORS + BUILD_ERRORS))
if [ $TOTAL_ERRORS -gt 0 ]; then
    echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
    echo "COMMIT BLOCKED: $TOTAL_ERRORS problem(s) found"
    echo ""
    if [ $ERRORS -gt 0 ]; then
        echo "  - $ERRORS file(s) contain sorry"
    fi
    if [ $BUILD_ERRORS -gt 0 ]; then
        echo "  - $BUILD_ERRORS module(s) failed to build"
    fi
    echo ""
    echo "Fix the errors above before committing."
    echo "Emergency bypass: git commit --no-verify"
    echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
    exit 1
fi

echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "pre-commit: all checks passed ($MODULES_CHECKED modules built)"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
exit 0
