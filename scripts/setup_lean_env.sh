#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
ELAN_HOME_DEFAULT="${HOME}/.elan"
ELAN_ENV_FILE="${ELAN_HOME:-$ELAN_HOME_DEFAULT}/env"
LEAN_TOOLCHAIN_FILE="${ROOT_DIR}/lean-toolchain"

if ! command -v curl >/dev/null 2>&1; then
  echo "error: curl is required to install elan" >&2
  exit 1
fi

if [ ! -f "${LEAN_TOOLCHAIN_FILE}" ]; then
  echo "error: lean-toolchain not found at ${LEAN_TOOLCHAIN_FILE}" >&2
  exit 1
fi

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
