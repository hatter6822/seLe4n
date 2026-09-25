#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
# build_rpi5_image.sh — WS-BP BP5.3: the Raspberry Pi 5 boot files.
#
# Writes `kernel8.img` (the kernel image's loaded bytes, as the firmware loads
# them) and `config.txt` (which pins the firmware's load address to the image's
# entry and the device tree to the window `link.ld` places it in), and checks
# both against the image they were cut from.  This is the deliverable the
# release cut's `SM10.1.1` names.
#
# The image must be the Lean-linked release image the archive lane builds
# (`scripts/test_lean_aarch64_archive.sh`, which runs this script as its last
# step).  It is checked as such first -- `check_kernel_image.py --lean-kernel`
# over the roots the image link read -- so a HAL-only image, or one the last
# archive build did not link, is refused rather than packaged.
#
#   scripts/build_rpi5_image.sh [<sele4n-kernel ELF> [<out dir>]]
#
# WS-BP BP5.4: the last step publishes the image's size and section map
# (`kernel_image_report.py`): Markdown on stdout and, in a GitHub Actions run,
# appended to the step summary; JSON beside the boot files, which the CI job
# uploads.  It runs after the packager so the size it reports is the size of
# the `kernel8.img` just checked, and it refuses one that is not the image.
#
# Defaults: the release image under rust/target, and .lake/build/rpi5-image.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

CROSS_TARGET="aarch64-unknown-none-softfloat"
ELF="${1:-${PROJECT_ROOT}/rust/target/${CROSS_TARGET}/release/sele4n-kernel}"
OUT_DIR="${2:-${PROJECT_ROOT}/.lake/build/rpi5-image}"
ROOTS="${PROJECT_ROOT}/.lake/build/${CROSS_TARGET}/libsele4n.roots.ld"

if [[ $# -gt 2 ]]; then
  echo "usage: $0 [<sele4n-kernel ELF> [<out dir>]]" >&2
  exit 2
fi
if [[ ! -f "${ELF}" ]]; then
  echo "build_rpi5_image: no kernel image at ${ELF}; run scripts/test_lean_aarch64_archive.sh" >&2
  exit 1
fi

python3 "${SCRIPT_DIR}/check_kernel_image.py" --lean-kernel "${ROOTS}" "${ELF}"
python3 "${SCRIPT_DIR}/rpi5_boot_files.py" package "${ELF}" "${OUT_DIR}"
python3 "${SCRIPT_DIR}/kernel_image_report.py" "${ELF}" "${OUT_DIR}"
