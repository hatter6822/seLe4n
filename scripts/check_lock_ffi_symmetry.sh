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
# Since PR #890 review round 5 the gate also holds each symbol's
# **signature** across the two sides (check 7): the parameter types in
# order and the return type, read from the Lean `@[extern]` declaration's
# type and the Rust `pub extern "C" fn` signature and mapped through the
# one type table below.  Names alone are a presence check: the round that
# added a mode argument to `ffi_rw_lock_enqueue` and a return value to
# `ffi_rw_lock_cancel` would have passed every name check with the two
# sides calling one symbol at two arities, which links and then reads a
# garbage register.
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
  "ffi_rw_lock_cancel"
  "ffi_rw_lock_cancel_count"
  "ffi_rw_lock_complete_read"
  "ffi_rw_lock_complete_write"
  "ffi_rw_lock_enqueue"
  "ffi_rw_lock_is_served"
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
echo "[1/7] Verifying Lean @[extern] declarations..."
for sym in "${EXPECTED_SYMBOLS[@]}"; do
  if ! grep -q "@\[extern \"${sym}\"\]" "${FFI_LEAN}"; then
    echo "  MISSING Lean @[extern]: ${sym}" >&2
    failures=$((failures + 1))
  fi
done

# Check 2: Every expected symbol is exported on the Rust side
# (in ffi.rs as a `#[no_mangle] pub extern "C"` function).
echo "[2/7] Verifying Rust #[no_mangle] pub extern \"C\" fn exports..."
for sym in "${EXPECTED_SYMBOLS[@]}"; do
  if ! grep -q "pub extern \"C\" fn ${sym}(" "${FFI_RUST}"; then
    echo "  MISSING Rust export: ${sym}" >&2
    failures=$((failures + 1))
  fi
done

# Check 3: Every Rust export has a corresponding helper in lock_bridge.rs.
# The helper name is the FFI symbol with the `ffi_` prefix stripped.
echo "[3/7] Verifying Rust lock_bridge.rs helpers..."
for sym in "${EXPECTED_SYMBOLS[@]}"; do
  helper="${sym#ffi_}"
  if ! grep -q "pub fn ${helper}(" "${LOCK_BRIDGE_RUST}"; then
    echo "  MISSING lock_bridge helper: ${helper} (for FFI symbol ${sym})" >&2
    failures=$((failures + 1))
  fi
done

# Check 4: Lean and Rust agree on the SM2 theorem count.
echo "[4/7] Verifying SM2 theorem count agreement..."

# Lean: `theorem lockPrimitives_count : lockPrimitives.length = 30`
# The literal "= 25" appears on the same line as the theorem statement;
# we extract the integer after the final `=` (PCRE lookbehind).
lean_count=$(grep -oP '^theorem lockPrimitives_count\s*:\s*lockPrimitives\.length\s*=\s*\K\d+' "${LOCK_PRIMITIVES_LEAN}" || echo "0")
# Rust: `pub const LOCK_THEOREM_COUNT: usize = 28;`
rust_count=$(grep -oP 'pub const LOCK_THEOREM_COUNT:\s*usize\s*=\s*\K\d+' "${LOCK_BRIDGE_RUST}" || echo "0")

if [[ "${lean_count}" != "${rust_count}" ]]; then
  echo "  MISMATCH: Lean lockPrimitives_count = ${lean_count}, Rust LOCK_THEOREM_COUNT = ${rust_count}" >&2
  failures=$((failures + 1))
elif [[ "${lean_count}" == "0" ]]; then
  echo "  ERROR: could not extract SM2 theorem count from either side" >&2
  failures=$((failures + 1))
else
  echo "  OK: both sides report SM2 theorem count = ${lean_count}"
fi

# Check 5: Detect orphan Rust exports — every `ffi_(ticket_lock|rw_lock)_*`
# in ffi.rs must be in EXPECTED_SYMBOLS.  Catches the case where an
# FFI export was added on the Rust side but the EXPECTED_SYMBOLS list
# (and thus the Lean @[extern] declarations) was not updated.
echo
echo "[5/7] Checking for orphan Rust lock FFI exports..."
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

# Check 6: Detect orphan Lean @[extern] declarations — every
# `@[extern "ffi_(ticket_lock|rw_lock)_*"]` in Platform/FFI.lean must
# be in EXPECTED_SYMBOLS.  Catches the case where a Lean declaration
# was added without the corresponding Rust export.
echo
echo "[6/7] Checking for orphan Lean @[extern] declarations..."
mapfile -t actual_lean_symbols < <(
  grep -oP '@\[extern "\Kffi_(ticket|rw)_lock_[a-z_]+(?=")' "${FFI_LEAN}" | sort -u
)
for actual in "${actual_lean_symbols[@]}"; do
  found=0
  for expected in "${EXPECTED_SYMBOLS[@]}"; do
    if [[ "${actual}" == "${expected}" ]]; then
      found=1
      break
    fi
  done
  if [[ ${found} -eq 0 ]]; then
    echo "  ORPHAN Lean @[extern]: ${actual} (not in EXPECTED_SYMBOLS)" >&2
    failures=$((failures + 1))
  fi
done

# Check 7 (PR #890 review round 5): every symbol's signature agrees.
#
# The Lean side: the type of the `opaque` declaration that follows the
# `@[extern "<sym>"]` attribute — `(a : T₁) → (b : T₂) → BaseIO R` — read
# with the file flattened onto one line, so a declaration wrapped across
# lines is read whole.  The Rust side: the parameter list and return type
# of `pub extern "C" fn <sym>(…) -> R {`, read the same way.  Each Rust
# type is mapped to its Lean spelling through one table; a type the table
# does not know fails the check rather than passing it, since an unmapped
# type is a comparison nobody made.
echo
echo "[7/7] Verifying parameter and return types agree per symbol..."
lean_flat="$(tr '\n' ' ' < "${FFI_LEAN}")"
rust_flat="$(tr '\n' ' ' < "${FFI_RUST}")"

# Rust ABI spelling → Lean spelling.  Extend here when a new width is
# bound; the check refuses anything not listed.
map_rust_type() {
  case "$1" in
    u64) echo "UInt64" ;;
    u32) echo "UInt32" ;;
    u8) echo "UInt8" ;;
    bool) echo "Bool" ;;
    '()' | '') echo "Unit" ;;
    *) echo "UNMAPPED($1)" ;;
  esac
}

for sym in "${EXPECTED_SYMBOLS[@]}"; do
  # Lean: the declaration's type, up to and including its `BaseIO R`.
  lean_type="$(printf '%s' "${lean_flat}" \
    | grep -oP '@\[extern "'"${sym}"'"\]\s*opaque\s+\w+\s*:\s*\K.*?BaseIO\s+\w+' | head -1 || true)"
  if [[ -z "${lean_type}" ]]; then
    echo "  UNREADABLE Lean type for ${sym}" >&2
    failures=$((failures + 1))
    continue
  fi
  mapfile -t lean_params < <(printf '%s' "${lean_type}" | grep -oP '\(\s*\w+\s*:\s*\K\w+' || true)
  lean_ret="$(printf '%s' "${lean_type}" | grep -oP 'BaseIO\s+\K\w+' | tail -1)"

  # Rust: the parameter list and the return type of the export.
  rust_sig="$(printf '%s' "${rust_flat}" \
    | grep -oP 'pub extern "C" fn '"${sym}"'\s*\(\K[^)]*\)\s*(->\s*[^{]+)?(?=\{)' | head -1 || true)"
  if [[ -z "${rust_sig}" ]]; then
    echo "  UNREADABLE Rust signature for ${sym}" >&2
    failures=$((failures + 1))
    continue
  fi
  rust_param_list="${rust_sig%%)*}"
  mapfile -t rust_params_raw < <(printf '%s' "${rust_param_list}" | grep -oP ':\s*\K[[:alnum:]_()]+' || true)
  rust_ret_raw="$(printf '%s' "${rust_sig}" | grep -oP -- '->\s*\K[[:alnum:]_()]+' | head -1 || true)"

  rust_params=()
  for raw in "${rust_params_raw[@]}"; do
    rust_params+=("$(map_rust_type "${raw}")")
  done
  rust_ret="$(map_rust_type "${rust_ret_raw}")"

  if [[ "${lean_params[*]-}" != "${rust_params[*]-}" || "${lean_ret}" != "${rust_ret}" ]]; then
    echo "  SIGNATURE MISMATCH for ${sym}:" >&2
    echo "    Lean: (${lean_params[*]-}) -> ${lean_ret}" >&2
    echo "    Rust: (${rust_params[*]-}) -> ${rust_ret}" >&2
    failures=$((failures + 1))
  fi
done

echo
if [[ ${failures} -eq 0 ]]; then
  echo "OK: SM2.D FFI surface is symmetric (${#EXPECTED_SYMBOLS[@]} symbols verified, signatures included)."
  exit 0
else
  echo "FAIL: ${failures} SM2.D FFI symmetry violation(s)." >&2
  exit 1
fi
