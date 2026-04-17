#!/usr/bin/env bash
# AK4-G: End-to-end ABI round-trip integration test.
#
# Runs `lake exe abi_roundtrip_suite`, which simulates the Rust-side
# `sele4n-abi` encoder (including IPC-buffer overflow merge) and verifies
# that every 5-arg syscall decodes successfully via the Lean kernel's
# `decodeSyscallArgsFromState`.
#
# Hooked into `test_full.sh`. Added in v0.29.6 (WS-AK / Phase AK4).

set -euo pipefail

# shellcheck disable=SC1091
source "$(dirname "$0")/_common.sh" 2>/dev/null || true

ROOT_DIR="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT_DIR"

# Ensure the Lean toolchain is available.
if [ -f "$HOME/.elan/env" ]; then
    # shellcheck disable=SC1091
    source "$HOME/.elan/env"
fi

echo "[test_abi_roundtrip] Building abi_roundtrip_suite..."
lake build abi_roundtrip_suite >/dev/null

echo "[test_abi_roundtrip] Running AbiRoundtripSuite..."
lake exe abi_roundtrip_suite

echo "[test_abi_roundtrip] PASS"
