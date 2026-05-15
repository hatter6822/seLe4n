#!/usr/bin/env bash
# test_rust.sh — Rust syscall wrapper build + test + conformance
#
# Q8-D: Validates that all sele4n Rust crates build and pass tests.
# Integrated into test_smoke.sh as a Tier 2 gate.
#
# R8-C (I-M03): Explicit skip warnings + proper error propagation from cargo.
#
# WS-RH RH-H: Extended to cover the host-runtime crate (sele4n-host).
# The workspace test step (--all) already discovers the new crate;
# the explicit scaffold-suite step below pins coverage so a future
# CI lane that filters the workspace cannot accidentally drop the
# host-runtime integration tests.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
RUST_DIR="$PROJECT_ROOT/rust"

echo "=== Rust Syscall Wrappers (Q8) ==="
echo ""

# R8-C (I-M03): Explicit cargo availability check with CI warning annotation.
# AE6-C (T-F17): Log the skip explicitly so CI dashboards surface it.
if ! command -v cargo &> /dev/null; then
    echo "::warning::Rust tests SKIPPED — cargo not found in PATH"
    echo "[SKIP] cargo not found — Rust tests SKIPPED"
    echo "       Install Rust via: curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh"
    echo ""
    echo "       To ensure Rust tests run in CI, add a rustup install step"
    echo "       to .github/workflows/lean_action_ci.yml"
    # Propagate skip status to CI output variables when available.
    if [ -n "${GITHUB_OUTPUT:-}" ]; then
        echo "RUST_TESTS_SKIPPED=true" >> "$GITHUB_OUTPUT"
    fi
    exit 0
fi

# Check if rust directory exists
if [ ! -d "$RUST_DIR" ]; then
    echo "[FAIL] rust/ directory not found"
    exit 1
fi

cd "$RUST_DIR"

# R8-C (I-M03): Capture cargo output to temp file so we can show tail on success
# and full output on failure. Exit codes are checked directly, not through pipe.

run_cargo_step() {
    local step_label="$1"
    shift
    local log
    log="$(mktemp)"
    if "$@" > "$log" 2>&1; then
        tail -5 "$log"
        echo "      ✓ ${step_label}"
        rm -f "$log"
        return 0
    else
        local rc=$?
        cat "$log"
        echo ""
        echo "      ✗ ${step_label} FAILED (exit code ${rc})"
        rm -f "$log"
        return "$rc"
    fi
}

echo "[1/4] Building all crates (host target)..."
run_cargo_step "Build succeeded" cargo build --all
echo ""

echo "[2/4] Running unit tests..."
run_cargo_step "Unit tests passed" cargo test --all --features std
echo ""

echo "[3/4] Running conformance tests (RUST-XVAL-001..014)..."
run_cargo_step "Conformance tests passed" cargo test -p sele4n-abi --features std --test conformance
echo ""

# WS-RH RH-H: explicit coverage of the host-runtime scaffold integration
# tests.  The workspace --all of step 2 already runs them, but pinning
# the package + test name catches the regression where a future CI
# lane filters the workspace and silently drops host-runtime coverage.
echo "[4/4] Running host-runtime scaffold integration tests (WS-RH RH-H)..."
run_cargo_step "Host-runtime scaffold tests passed" cargo test -p sele4n-host --test scaffold
echo ""

echo "=== All Rust tests passed ==="
