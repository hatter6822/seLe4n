#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
ELAN_HOME_DEFAULT="${HOME}/.elan"
ELAN_ENV_FILE="${ELAN_HOME:-$ELAN_HOME_DEFAULT}/env"
LEAN_TOOLCHAIN_FILE="${ROOT_DIR}/lean-toolchain"
ELAN_INSTALLER_URL="https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh"
# WS-B9 hardening anchor: update intentionally when bumping trusted elan installer revision.
ELAN_INSTALLER_SHA256="4bacca9502cb89736fe63d2685abc2947cfbf34dc87673504f1bb4c43eda9264"

APT_UPDATE_DONE=0

run_pkg_install() {
  if command -v sudo >/dev/null 2>&1; then
    sudo "$@"
  else
    "$@"
  fi
}

apt_update_once() {
  if [ "${APT_UPDATE_DONE}" -eq 0 ]; then
    if ! run_pkg_install apt-get update; then
      echo "[setup] apt-get update failed; retrying with primary sources only (ignoring sourceparts)" >&2
      run_pkg_install apt-get update \
        -o Dir::Etc::sourceparts="-" \
        -o APT::Get::List-Cleanup="0"
    fi
    APT_UPDATE_DONE=1
  fi
}

compute_sha256() {
  local target_file="$1"
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "${target_file}" | awk '{print $1}'
  elif command -v shasum >/dev/null 2>&1; then
    shasum -a 256 "${target_file}" | awk '{print $1}'
  else
    echo "error: neither sha256sum nor shasum is available for installer verification" >&2
    exit 1
  fi
}

ensure_shellcheck() {
  if command -v shellcheck >/dev/null 2>&1; then
    return 0
  fi

  echo "[setup] shellcheck not found; attempting to install"

  if command -v apt-get >/dev/null 2>&1; then
    apt_update_once
    run_pkg_install env DEBIAN_FRONTEND=noninteractive apt-get install -y shellcheck
  elif command -v dnf >/dev/null 2>&1; then
    run_pkg_install dnf install -y ShellCheck
  elif command -v yum >/dev/null 2>&1; then
    run_pkg_install yum install -y epel-release
    run_pkg_install yum install -y ShellCheck
  elif command -v pacman >/dev/null 2>&1; then
    run_pkg_install pacman -Sy --noconfirm shellcheck
  elif command -v brew >/dev/null 2>&1; then
    brew install shellcheck
  else
    echo "error: shellcheck is required, but no supported package manager (apt, dnf, yum, pacman, brew) was found" >&2
    exit 1
  fi

  if ! command -v shellcheck >/dev/null 2>&1; then
    echo "error: shellcheck installation failed" >&2
    exit 1
  fi
}

ensure_ripgrep() {
  if command -v rg >/dev/null 2>&1; then
    return 0
  fi

  echo "[setup] ripgrep (rg) not found; attempting to install"

  if command -v apt-get >/dev/null 2>&1; then
    apt_update_once
    run_pkg_install env DEBIAN_FRONTEND=noninteractive apt-get install -y ripgrep
  elif command -v dnf >/dev/null 2>&1; then
    run_pkg_install dnf install -y ripgrep
  elif command -v yum >/dev/null 2>&1; then
    run_pkg_install yum install -y epel-release
    run_pkg_install yum install -y ripgrep
  elif command -v pacman >/dev/null 2>&1; then
    run_pkg_install pacman -Sy --noconfirm ripgrep
  elif command -v brew >/dev/null 2>&1; then
    brew install ripgrep
  else
    echo "error: ripgrep (rg) is required, but no supported package manager (apt, dnf, yum, pacman, brew) was found" >&2
    exit 1
  fi

  if ! command -v rg >/dev/null 2>&1; then
    echo "error: ripgrep (rg) installation failed" >&2
    exit 1
  fi
}

if ! command -v curl >/dev/null 2>&1; then
  echo "error: curl is required to install elan" >&2
  exit 1
fi

if [ ! -f "${LEAN_TOOLCHAIN_FILE}" ]; then
  echo "error: lean-toolchain not found at ${LEAN_TOOLCHAIN_FILE}" >&2
  exit 1
fi

ensure_shellcheck
ensure_ripgrep

# If elan was previously installed with --no-modify-path, load it before probing.
if [ -f "${ELAN_ENV_FILE}" ]; then
  # shellcheck disable=SC1090
  source "${ELAN_ENV_FILE}"
fi

if ! command -v elan >/dev/null 2>&1; then
  echo "[setup] elan not found; installing to ${ELAN_HOME:-$ELAN_HOME_DEFAULT}"
  elan_installer="$(mktemp)"
  trap 'rm -f "${elan_installer}"' EXIT
  curl -fsSL "${ELAN_INSTALLER_URL}" -o "${elan_installer}"

  installer_sha256="$(compute_sha256 "${elan_installer}")"
  if [ "${installer_sha256}" != "${ELAN_INSTALLER_SHA256}" ]; then
    echo "error: elan installer checksum verification failed" >&2
    echo "  expected: ${ELAN_INSTALLER_SHA256}" >&2
    echo "  actual:   ${installer_sha256}" >&2
    exit 1
  fi

  sh "${elan_installer}" -y --no-modify-path
  rm -f "${elan_installer}"
  trap - EXIT
fi

if [ -f "${ELAN_ENV_FILE}" ]; then
  # shellcheck disable=SC1090
  source "${ELAN_ENV_FILE}"
else
  echo "error: unable to find elan env file at ${ELAN_ENV_FILE}" >&2
  exit 1
fi

TOOLCHAIN="$(tr -d '\n\r' < "${LEAN_TOOLCHAIN_FILE}")"
if [ -z "${TOOLCHAIN}" ]; then
  echo "error: ${LEAN_TOOLCHAIN_FILE} is empty" >&2
  exit 1
fi

echo "[setup] ensuring Lean toolchain ${TOOLCHAIN} is installed"
if ! elan toolchain list | tr -d '\r' | grep -Fxq "${TOOLCHAIN}"; then
  elan toolchain install "${TOOLCHAIN}" >/dev/null
else
  echo "[setup] Lean toolchain ${TOOLCHAIN} is already installed"
fi
elan default "${TOOLCHAIN}" >/dev/null

if ! command -v lake >/dev/null 2>&1; then
  echo "error: lake is still not on PATH after elan setup" >&2
  exit 1
fi

echo "[setup] Lean environment is ready"
echo "[setup] lake version: $(lake --version)"

echo "[setup] next steps:"
echo "  source \"${ELAN_ENV_FILE}\""
echo "  lake build"

if [ "${1:-}" = "--build" ]; then
  echo "[setup] running lake build"
  (cd "${ROOT_DIR}" && lake build)
fi
