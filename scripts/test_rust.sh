#!/usr/bin/env bash
# test_rust.sh — Rust syscall wrapper build + test + conformance
#
# Q8-D: Validates that all three sele4n Rust crates build and pass tests.
# Integrated into test_smoke.sh as a Tier 2 gate.
#
# R8-C (I-M03): Explicit skip warnings + proper error propagation from cargo.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
RUST_DIR="$PROJECT_ROOT/rust"

echo "=== Rust Syscall Wrappers (Q8) ==="
echo ""

# R8-C (I-M03): Explicit cargo availability check with CI warning annotation.
if ! command -v cargo &> /dev/null; then
    echo "::warning::Rust tests SKIPPED — cargo not found in PATH"
    echo "[SKIP] cargo not found — Rust tests SKIPPED"
    echo "       Install Rust via: curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh"
    echo ""
    echo "       To ensure Rust tests run in CI, add a rustup install step"
    echo "       to .github/workflows/lean_action_ci.yml"
    exit 0
fi

# Check if rust directory exists
if [ ! -d "$RUST_DIR" ]; then
    echo "[FAIL] rust/ directory not found"
    exit 1
fi

cd "$RUST_DIR"

# R8-C (I-M03): Use pipefail (already set) and capture cargo exit codes properly.
# Redirect output to temp files so we can show tails on success and full output on failure.

echo "[1/3] Building all crates (host target)..."
if cargo build --all 2>&1 | tail -5; then
    echo "      ✓ Build succeeded"
else
    echo ""
    echo "      ✗ Build FAILED (see output above)"
    exit 1
fi
echo ""

echo "[2/3] Running unit tests..."
if cargo test --all --features std 2>&1 | tail -20; then
    echo "      ✓ Unit tests passed"
else
    echo ""
    echo "      ✗ Unit tests FAILED (see output above)"
    exit 1
fi
echo ""

echo "[3/3] Running conformance tests (RUST-XVAL-001..014)..."
if cargo test -p sele4n-abi --features std --test conformance 2>&1 | tail -25; then
    echo "      ✓ Conformance tests passed"
else
    echo ""
    echo "      ✗ Conformance tests FAILED (see output above)"
    exit 1
fi
echo ""

echo "=== All Rust tests passed ==="
