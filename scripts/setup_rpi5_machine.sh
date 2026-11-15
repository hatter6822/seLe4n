#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
#
# WS-PM PM1: the emulated Raspberry Pi 5 the boot lanes run the board image on.
#
# QEMU ships no BCM2712 machine.  hatter6822/rpi5_machine is an out-of-tree
# QEMU whose `raspi5b` machine models the Raspberry Pi 5 Model B: four
# Cortex-A76 PEs numbered in Aff1, the GIC-400, UART10, the 54 MHz generic
# timer, EL2 entry with PSCI over SMC, and the firmware's device tree.  This
# script builds it at the commit pinned below, once, into
# `.lake/rpi5-machine/<commit>/`, and prints the emulator's path.  A build at
# the pin that already finished is reused; any other directory under
# `.lake/rpi5-machine/` is another pin's and is left alone.
#
#   ./scripts/setup_rpi5_machine.sh            # build if need be; print the path
#   ./scripts/setup_rpi5_machine.sh --print    # print the path a build would have
#
# The pin moves only by an edit here, in its own PR, so every boot reading a
# PR reports was taken on the machine that PR names.
#
# Build dependencies (Debian/Ubuntu): build-essential ninja-build python3-venv
# libglib2.0-dev libpixman-1-dev libfdt-dev pkg-config git.

set -euo pipefail

RPI5_MACHINE_REPO="https://github.com/hatter6822/rpi5_machine"
RPI5_MACHINE_COMMIT="1d46342eecfc1be3f4ba172a83ecd73e54837811"

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
MACHINE_ROOT="${REPO_ROOT}/.lake/rpi5-machine/${RPI5_MACHINE_COMMIT}"
SOURCE_DIR="${MACHINE_ROOT}/src"
MACHINE_BIN="${MACHINE_ROOT}/qemu-system-aarch64"

if [[ "${1:-}" == "--print" ]]; then
    echo "${MACHINE_BIN}"
    exit 0
elif [[ $# -gt 0 ]]; then
    echo "setup_rpi5_machine.sh: unknown argument: $1" >&2
    exit 2
fi

# The binary is written last, after the build passed, so its presence means a
# finished build at this pin.
if [[ -x "${MACHINE_BIN}" ]]; then
    echo "${MACHINE_BIN}"
    exit 0
fi

log() { echo "[setup_rpi5_machine] $*" >&2; }

mkdir -p "${MACHINE_ROOT}"
if [[ ! -d "${SOURCE_DIR}/.git" ]]; then
    rm -rf "${SOURCE_DIR}"
    git init -q "${SOURCE_DIR}"
    git -C "${SOURCE_DIR}" remote add origin "${RPI5_MACHINE_REPO}"
fi
log "fetching ${RPI5_MACHINE_REPO} at ${RPI5_MACHINE_COMMIT}"
git -C "${SOURCE_DIR}" fetch -q --depth 1 origin "${RPI5_MACHINE_COMMIT}"
git -C "${SOURCE_DIR}" checkout -q --detach FETCH_HEAD
actual=$(git -C "${SOURCE_DIR}" rev-parse HEAD)
if [[ "${actual}" != "${RPI5_MACHINE_COMMIT}" ]]; then
    log "fetched ${actual}, not the pinned ${RPI5_MACHINE_COMMIT}"
    exit 1
fi

log "building (make setup build; about fifteen minutes on four cores, once per pin)"
make -C "${SOURCE_DIR}" setup >&2
make -C "${SOURCE_DIR}" -j"$(nproc)" build >&2

cp "${SOURCE_DIR}/build/qemu-system-aarch64" "${MACHINE_BIN}.partial"
strip "${MACHINE_BIN}.partial" 2>/dev/null || true
if ! "${MACHINE_BIN}.partial" -machine help | grep -q '^raspi5b '; then
    log "the built emulator offers no raspi5b machine"
    exit 1
fi
mv "${MACHINE_BIN}.partial" "${MACHINE_BIN}"
echo "${MACHINE_BIN}"
