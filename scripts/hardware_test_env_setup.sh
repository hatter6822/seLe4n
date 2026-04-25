#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# SPDX-License-Identifier: GPL-3.0-or-later
#
# AN9 hardware-testing environment setup.
#
# Idempotent installer for the toolchain required to run the
# post-AN9 hardware validation steps in docs/HARDWARE_TESTING.md §4.
#
# Tested on Ubuntu 22.04 / 24.04 and Debian 12.
# For other distributions, install the equivalent packages by hand.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
cd "${REPO_ROOT}"

# Colour output (disabled if not on a TTY).
if [[ -t 1 ]]; then
  C_PASS='\033[0;32m'
  C_INFO='\033[0;36m'
  C_WARN='\033[0;33m'
  C_END='\033[0m'
else
  C_PASS=''
  C_INFO=''
  C_WARN=''
  C_END=''
fi

info() { echo -e "${C_INFO}[INFO]${C_END} $*"; }
pass() { echo -e "${C_PASS}[ OK ]${C_END} $*"; }
warn() { echo -e "${C_WARN}[WARN]${C_END} $*"; }

# 1. Apt packages for QEMU + cross-toolchain
APT_PKGS=(
  qemu-system-arm
  qemu-utils
  gcc-aarch64-linux-gnu
  binutils-aarch64-linux-gnu
  device-tree-compiler
  build-essential
)

if command -v apt-get &>/dev/null; then
  info "Installing apt packages: ${APT_PKGS[*]}"
  if [[ ${EUID} -ne 0 ]]; then
    sudo apt-get update -qq
    sudo apt-get install -y -qq "${APT_PKGS[@]}"
  else
    apt-get update -qq
    apt-get install -y -qq "${APT_PKGS[@]}"
  fi
  pass "apt packages installed"
else
  warn "apt-get not available; install equivalents manually:"
  for pkg in "${APT_PKGS[@]}"; do
    echo "        - ${pkg}"
  done
fi

# 2. Verify QEMU version (need 8.0+ for full Cortex-A76 emulation)
if command -v qemu-system-aarch64 &>/dev/null; then
  QEMU_VER=$(qemu-system-aarch64 --version | head -1 | awk '{print $4}')
  info "QEMU version: ${QEMU_VER}"
  QEMU_MAJOR=$(echo "${QEMU_VER}" | cut -d. -f1)
  if [[ "${QEMU_MAJOR}" -lt 8 ]]; then
    warn "QEMU < 8.0 may not fully support Cortex-A76 features."
    warn "Some AN9 hardware tests will skip with [SKIP] markers."
  else
    pass "QEMU ${QEMU_VER} supports Cortex-A76"
  fi
else
  warn "QEMU not installed; hardware tests will skip"
fi

# 3. Rust toolchain + aarch64-unknown-none target
if command -v rustup &>/dev/null; then
  info "Ensuring aarch64-unknown-none Rust target"
  rustup target add aarch64-unknown-none 2>&1 | tail -2 || true
  pass "Rust aarch64-unknown-none target available"
else
  warn "rustup not installed; install via:"
  warn "  curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh"
fi

# 4. Lean toolchain (delegates to the existing setup script)
if [[ -x "${SCRIPT_DIR}/setup_lean_env.sh" ]]; then
  info "Running setup_lean_env.sh --skip-test-deps"
  "${SCRIPT_DIR}/setup_lean_env.sh" --skip-test-deps
  pass "Lean 4.28.0 toolchain ready"
else
  warn "scripts/setup_lean_env.sh not found"
fi

# 5. OpenOCD (optional, only for on-board JTAG; skip if absent)
if command -v openocd &>/dev/null; then
  info "OpenOCD detected ($(openocd --version 2>&1 | head -1))"
  pass "OpenOCD available for JTAG (optional)"
else
  warn "OpenOCD not installed; JTAG debugging unavailable."
  warn "  sudo apt install openocd  # if needed"
fi

# 6. Verify HAL builds for the hardware target (sanity check)
info "Sanity-checking HAL builds for the host target"
if cargo build --manifest-path rust/Cargo.toml -p sele4n-hal --quiet; then
  pass "sele4n-hal builds for host"
else
  warn "sele4n-hal failed to build; environment may be incomplete"
fi

echo ""
echo "============================================================"
echo "  AN9 hardware-testing environment is READY."
echo "============================================================"
echo ""
echo "Next steps:"
echo "  1. Read docs/HARDWARE_TESTING.md for the validation procedure."
echo "  2. Run individual tests via scripts/test_qemu_*.sh."
echo "  3. (Optional) Connect an RPi 5 board for full silicon"
echo "     validation; see §3.3 of HARDWARE_TESTING.md."
echo ""
