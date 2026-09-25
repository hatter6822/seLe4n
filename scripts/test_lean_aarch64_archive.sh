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
# WS-BP BP5.2: then the kernel image itself.  `sele4n-kernel` built with
# `hw_target` links this archive and the roots script the builder writes
# beside it (`rust/sele4n-hal/build.rs`), with `--gc-sections` rooted at the
# library initializer and every production `@[export]` -- the link the
# builder's step [7/8] proved needs nothing the runtime does not define.
# `check_kernel_image.py --lean-kernel` checks the image and that every root
# is its text, and the FP/SIMD gate disassembles it: the target's
# `compiler_builtins` is not FP-free, so only the linked image decides which
# of its members the kernel carries.  The stale image is removed first, so
# the checks read this run's link.
#
# WS-BP BP5.3: and last, the Raspberry Pi 5 boot files cut from that image --
# `kernel8.img` and `config.txt`, written to .lake/build/rpi5-image and checked
# against the image by `scripts/build_rpi5_image.sh`, which (WS-BP BP5.4) ends
# by publishing the image's size and section map (`scripts/kernel_image_report.py`)
# to the CI step summary and `kernel-image-report.json`.
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

CROSS_TARGET="aarch64-unknown-none-softfloat"
IMAGE_BIN="sele4n-kernel"
ARCHIVE_DIR="${PROJECT_ROOT}/.lake/build/${CROSS_TARGET}"

echo "[1/5] Host static archive (the reconciliation's other half)"
lake build SeLe4n:static

echo "[2/5] Cross archive"
python3 "${SCRIPT_DIR}/build_lean_aarch64_archive.py"

echo "[3/5] Kernel-entry reconciliation over both archives"
python3 "${SCRIPT_DIR}/check_kernel_entry_exports.py" --require-cross

echo "[4/5] The kernel image, linked with the Lean kernel, and checked"
cd "${PROJECT_ROOT}/rust"
rm -f "target/${CROSS_TARGET}/release/${IMAGE_BIN}"
cargo build --release --target "${CROSS_TARGET}" -p sele4n-hal \
    --features hw_target,kernel_image --bin "${IMAGE_BIN}"
python3 "${PROJECT_ROOT}/scripts/check_kernel_image.py" \
    --lean-kernel "${ARCHIVE_DIR}/libsele4n.roots.ld" \
    target/"${CROSS_TARGET}"/release/"${IMAGE_BIN}"
python3 "${PROJECT_ROOT}/scripts/check_fp_simd_free_objects.py" \
    target/"${CROSS_TARGET}"/release/"${IMAGE_BIN}"

echo "[5/5] The Raspberry Pi 5 boot files, cut from that image and checked"
"${PROJECT_ROOT}/scripts/build_rpi5_image.sh" \
    target/"${CROSS_TARGET}"/release/"${IMAGE_BIN}" "${PROJECT_ROOT}/.lake/build/rpi5-image"

echo "Lean aarch64 archive: built, checked and reconciled; the kernel image links it and is packaged."
