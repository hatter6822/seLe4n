#!/usr/bin/env bash
# test_rust.sh — Rust syscall wrapper build + test + conformance
#
# Q8-D: Validates that all three sele4n Rust crates build and pass tests.
# Integrated into test_smoke.sh as a Tier 2 gate.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
RUST_DIR="$PROJECT_ROOT/rust"

echo "=== Rust Syscall Wrappers (Q8) ==="
echo ""

# Check if cargo is available
if ! command -v cargo &> /dev/null; then
    echo "[SKIP] cargo not found — skipping Rust tests"
    echo "       Install Rust via: curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh"
    exit 0
fi

# Check if rust directory exists
if [ ! -d "$RUST_DIR" ]; then
    echo "[FAIL] rust/ directory not found"
    exit 1
fi

cd "$RUST_DIR"

echo "[1/3] Building all crates (host target)..."
cargo build --all 2>&1 | tail -5
echo "      ✓ Build succeeded"
echo ""

echo "[2/3] Running unit tests..."
cargo test --all --features std 2>&1 | tail -20
echo "      ✓ Unit tests passed"
echo ""

echo "[3/3] Running conformance tests (RUST-XVAL-001..014)..."
cargo test -p sele4n-abi --features std --test conformance 2>&1 | tail -25
echo "      ✓ Conformance tests passed"
echo ""

echo "=== All Rust tests passed ==="
