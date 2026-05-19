#!/usr/bin/env bash
# SPDX-License-Identifier: GPL-3.0-or-later
#
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
#
# WS-SM SM2.D.5 cross-language symmetry gate.
#
# Verifies that the Lean side (`SeLe4n/Platform/FFI.lean`) and the Rust
# side (`rust/sele4n-hal/src/ffi.rs` and `lock_bridge.rs`) agree on the
# SM2.D verified-lock FFI symbol list.  Run from Tier-1; the build.rs
# scanner enforces the Rust-side presence and this script enforces the
# Lean ↔ Rust agreement.
#
# Symmetric to `rust/sele4n-hal/build.rs::scan_lock_bridge_rs_intact`
# and `scan_ffi_rs_exposes_lock_ffi_exports`: those check the Rust
# side in isolation; this script cross-checks that every Lean
# `@[extern "ffi_*"]` declaration has a matching Rust
# `#[no_mangle] pub extern "C"` export.
#
# Exit codes:
#   0 — both sides agree on the FFI surface.
#   1 — Lean declares an FFI symbol the Rust side doesn't export.
#   2 — Rust exports an FFI symbol the Lean side doesn't declare.
#   3 — SM2 theorem count mismatch between Lean inventory and Rust constant.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

FFI_LEAN="${REPO_ROOT}/SeLe4n/Platform/FFI.lean"
FFI_RUST="${REPO_ROOT}/rust/sele4n-hal/src/ffi.rs"
LOCK_BRIDGE_RUST="${REPO_ROOT}/rust/sele4n-hal/src/lock_bridge.rs"
LOCK_PRIMITIVES_LEAN="${REPO_ROOT}/SeLe4n/Kernel/Concurrency/LockPrimitives.lean"

if [[ ! -r "${FFI_LEAN}" ]]; then
  echo "ERROR: cannot read ${FFI_LEAN}" >&2
  exit 1
fi
if [[ ! -r "${FFI_RUST}" ]]; then
  echo "ERROR: cannot read ${FFI_RUST}" >&2
  exit 1
fi
if [[ ! -r "${LOCK_BRIDGE_RUST}" ]]; then
  echo "ERROR: cannot read ${LOCK_BRIDGE_RUST}" >&2
  exit 1
fi
if [[ ! -r "${LOCK_PRIMITIVES_LEAN}" ]]; then
  echo "ERROR: cannot read ${LOCK_PRIMITIVES_LEAN}" >&2
  exit 1
fi

echo "WS-SM SM2.D.5 — cross-language FFI symmetry check"
echo "================================================="

# The list of required FFI symbols (the SM2.D bridge surface).
# A symbol appears here if it is part of the SM2.D contract.
# Keep alphabetised to make diffs reviewable.
EXPECTED_SYMBOLS=(
  "ffi_rw_lock_acquire_read"
  "ffi_rw_lock_acquire_read_count"
  "ffi_rw_lock_acquire_write"
  "ffi_rw_lock_acquire_write_count"
  "ffi_rw_lock_release_read"
  "ffi_rw_lock_release_read_count"
  "ffi_rw_lock_release_write"
  "ffi_rw_lock_release_write_count"
  "ffi_rw_lock_snapshot"
  "ffi_rw_lock_static_handle"
  "ffi_ticket_lock_acquire"
  "ffi_ticket_lock_acquire_count"
  "ffi_ticket_lock_peek_holder"
  "ffi_ticket_lock_release"
  "ffi_ticket_lock_release_count"
  "ffi_ticket_lock_static_handle"
)

failures=0

# Check 1: Every expected symbol is declared on the Lean side.
echo
echo "[1/4] Verifying Lean @[extern] declarations..."
for sym in "${EXPECTED_SYMBOLS[@]}"; do
  if ! grep -q "@\[extern \"${sym}\"\]" "${FFI_LEAN}"; then
    echo "  MISSING Lean @[extern]: ${sym}" >&2
    failures=$((failures + 1))
  fi
done

# Check 2: Every expected symbol is exported on the Rust side
# (in ffi.rs as a `#[no_mangle] pub extern "C"` function).
echo "[2/4] Verifying Rust #[no_mangle] pub extern \"C\" fn exports..."
for sym in "${EXPECTED_SYMBOLS[@]}"; do
  if ! grep -q "pub extern \"C\" fn ${sym}(" "${FFI_RUST}"; then
    echo "  MISSING Rust export: ${sym}" >&2
    failures=$((failures + 1))
  fi
done

# Check 3: Every Rust export has a corresponding helper in lock_bridge.rs.
# The helper name is the FFI symbol with the `ffi_` prefix stripped.
echo "[3/4] Verifying Rust lock_bridge.rs helpers..."
for sym in "${EXPECTED_SYMBOLS[@]}"; do
  helper="${sym#ffi_}"
  if ! grep -q "pub fn ${helper}(" "${LOCK_BRIDGE_RUST}"; then
    echo "  MISSING lock_bridge helper: ${helper} (for FFI symbol ${sym})" >&2
    failures=$((failures + 1))
  fi
done

# Check 4: Lean and Rust agree on the SM2 theorem count.
echo "[4/4] Verifying SM2 theorem count agreement..."

# Lean: `theorem lockPrimitives_count : lockPrimitives.length = 22`
# The literal "= 22" appears on the same line as the theorem statement;
# we extract the integer after the final `=` (PCRE lookbehind).
lean_count=$(grep -oP '^theorem lockPrimitives_count\s*:\s*lockPrimitives\.length\s*=\s*\K\d+' "${LOCK_PRIMITIVES_LEAN}" || echo "0")
# Rust: `pub const SM2_THEOREM_COUNT: usize = 22;`
rust_count=$(grep -oP 'pub const SM2_THEOREM_COUNT:\s*usize\s*=\s*\K\d+' "${LOCK_BRIDGE_RUST}" || echo "0")

if [[ "${lean_count}" != "${rust_count}" ]]; then
  echo "  MISMATCH: Lean lockPrimitives_count = ${lean_count}, Rust SM2_THEOREM_COUNT = ${rust_count}" >&2
  failures=$((failures + 1))
elif [[ "${lean_count}" == "0" ]]; then
  echo "  ERROR: could not extract SM2 theorem count from either side" >&2
  failures=$((failures + 1))
else
  echo "  OK: both sides report SM2 theorem count = ${lean_count}"
fi

# Check 5: Detect orphan Rust exports — every `ffi_(ticket_lock|rw_lock)_*`
# in ffi.rs must be in EXPECTED_SYMBOLS.
echo
echo "[bonus] Checking for orphan Rust lock FFI exports..."
mapfile -t actual_rust_symbols < <(
  grep -oP 'pub extern "C" fn \Kffi_(ticket|rw)_lock_[a-z_]+' "${FFI_RUST}" | sort -u
)
for actual in "${actual_rust_symbols[@]}"; do
  found=0
  for expected in "${EXPECTED_SYMBOLS[@]}"; do
    if [[ "${actual}" == "${expected}" ]]; then
      found=1
      break
    fi
  done
  if [[ ${found} -eq 0 ]]; then
    echo "  ORPHAN Rust export: ${actual} (not in EXPECTED_SYMBOLS)" >&2
    failures=$((failures + 1))
  fi
done

echo
if [[ ${failures} -eq 0 ]]; then
  echo "OK: SM2.D FFI surface is symmetric (${#EXPECTED_SYMBOLS[@]} symbols verified)."
  exit 0
else
  echo "FAIL: ${failures} SM2.D FFI symmetry violation(s)." >&2
  exit 1
fi
