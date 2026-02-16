#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
ELAN_HOME_DEFAULT="${HOME}/.elan"
ELAN_ENV_FILE="${ELAN_HOME:-$ELAN_HOME_DEFAULT}/env"
LEAN_TOOLCHAIN_FILE="${ROOT_DIR}/lean-toolchain"

ensure_shellcheck() {
  if command -v shellcheck >/dev/null 2>&1; then
    return 0
  fi

  echo "[setup] shellcheck not found; attempting to install"

  run_pkg_install() {
    if command -v sudo >/dev/null 2>&1; then
      sudo "$@"
    else
      "$@"
    fi
  }

  if command -v apt-get >/dev/null 2>&1; then
    if ! run_pkg_install env DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends shellcheck; then
      echo "[setup] shellcheck install without apt index refresh failed; running apt-get update and retrying"
      if ! run_pkg_install apt-get update; then
        echo "[setup] warning: apt-get update failed (often due to optional or blocked third-party repositories); retrying shellcheck install with existing indexes"
      fi
      run_pkg_install env DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends shellcheck
    fi
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

if ! command -v curl >/dev/null 2>&1; then
  echo "error: curl is required to install elan" >&2
  exit 1
fi

if [ ! -f "${LEAN_TOOLCHAIN_FILE}" ]; then
  echo "error: lean-toolchain not found at ${LEAN_TOOLCHAIN_FILE}" >&2
  exit 1
fi

ensure_shellcheck

if ! command -v elan >/dev/null 2>&1; then
  echo "[setup] elan not found; installing to ${ELAN_HOME:-$ELAN_HOME_DEFAULT}"
  curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf \
    | sh -s -- -y --no-modify-path
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
elan toolchain install "${TOOLCHAIN}" >/dev/null
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
