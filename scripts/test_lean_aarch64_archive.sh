#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
# test_lean_aarch64_archive.sh — WS-BP BP1: the kernel's Lean object code for
# the hardware target.
#
# Builds `libsele4n.a` — the C Lean emits for `SeLe4n.lean`'s import closure,
# compiled freestanding for `aarch64-unknown-none` with the soft-float ABI —
# and then decides the kernel-entry reconciliation on it as well as on the
# host archive, so a HAL `extern "C"` the image's archive does not define is a
# failure here rather than at BP5's first link.
#
# The builder does its own checking (the closure against Lake and the staged
# allowlist, the allocator configuration, one initializer per module, the
# stdlib against the toolchain's own objects, and no FP/SIMD register
# operand); see its module docs.  `--require-cross` makes an absent cross
# archive a failure instead of a narrower check.
#
# Needs the Lean toolchain (`setup_lean_env.sh`) and rustup's `llvm-tools`
# component (listed in `rust/rust-toolchain.toml`), which supplies the
# `llvm-nm` and `llvm-objdump` the builder reads object code with.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
cd "${PROJECT_ROOT}"

if [[ -f "${HOME}/.elan/env" ]]; then
  # shellcheck disable=SC1091
  source "${HOME}/.elan/env"
fi

echo "[1/3] Host static archive (the reconciliation's other half)"
lake build SeLe4n:static

echo "[2/3] Cross archive"
python3 "${SCRIPT_DIR}/build_lean_aarch64_archive.py"

echo "[3/3] Kernel-entry reconciliation over both archives"
python3 "${SCRIPT_DIR}/check_kernel_entry_exports.py" --require-cross

echo "Lean aarch64 archive: built, checked and reconciled."
