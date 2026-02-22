#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
QUIET=0
for arg in "$@"; do
  case "${arg}" in
    --quiet|-q) QUIET=1 ;;
  esac
done
log() { if [ "${QUIET}" -eq 0 ]; then echo "$@"; fi; }
ELAN_HOME_DEFAULT="${HOME}/.elan"
ELAN_ENV_FILE="${ELAN_HOME:-$ELAN_HOME_DEFAULT}/env"
LEAN_TOOLCHAIN_FILE="${ROOT_DIR}/lean-toolchain"
ELAN_INSTALLER_URL="https://raw.githubusercontent.com/leanprover/elan/87f5ec2f5627dd3df16b346733147412c3ddeef1/elan-init.sh"
# WS-B9 hardening anchor: commit-pinned installer URL + hash must be updated together intentionally.
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
      if ! run_pkg_install apt-get update \
        -o Dir::Etc::sourceparts="-" \
        -o APT::Get::List-Cleanup="0"; then
        echo "[setup] warning: apt-get update failed; package installs may not succeed" >&2
      fi
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

  log "[setup] shellcheck not found; attempting to install"

  if command -v apt-get >/dev/null 2>&1; then
    apt_update_once
    run_pkg_install env DEBIAN_FRONTEND=noninteractive apt-get install -y shellcheck || true
  elif command -v dnf >/dev/null 2>&1; then
    run_pkg_install dnf install -y ShellCheck || true
  elif command -v yum >/dev/null 2>&1; then
    { run_pkg_install yum install -y epel-release && \
    run_pkg_install yum install -y ShellCheck; } || true
  elif command -v pacman >/dev/null 2>&1; then
    run_pkg_install pacman -Sy --noconfirm shellcheck || true
  elif command -v brew >/dev/null 2>&1; then
    brew install shellcheck || true
  fi

  if ! command -v shellcheck >/dev/null 2>&1; then
    log "[setup] warning: shellcheck is unavailable; shell linting will be skipped"
  fi
}

ensure_ripgrep() {
  if command -v rg >/dev/null 2>&1; then
    return 0
  fi

  log "[setup] ripgrep (rg) not found; attempting to install"

  if command -v apt-get >/dev/null 2>&1; then
    apt_update_once
    run_pkg_install env DEBIAN_FRONTEND=noninteractive apt-get install -y ripgrep || true
  elif command -v dnf >/dev/null 2>&1; then
    run_pkg_install dnf install -y ripgrep || true
  elif command -v yum >/dev/null 2>&1; then
    { run_pkg_install yum install -y epel-release && \
    run_pkg_install yum install -y ripgrep; } || true
  elif command -v pacman >/dev/null 2>&1; then
    run_pkg_install pacman -Sy --noconfirm ripgrep || true
  elif command -v brew >/dev/null 2>&1; then
    brew install ripgrep || true
  fi

  if ! command -v rg >/dev/null 2>&1; then
    log "[setup] warning: ripgrep (rg) is unavailable; tests will use grep fallback"
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

ELAN_HOME_DIR="${ELAN_HOME:-$ELAN_HOME_DEFAULT}"

TOOLCHAIN="$(tr -d '\n\r' < "${LEAN_TOOLCHAIN_FILE}")"
if [ -z "${TOOLCHAIN}" ]; then
  echo "error: ${LEAN_TOOLCHAIN_FILE} is empty" >&2
  exit 1
fi

# Parse toolchain spec "org/repo:tag" into components for download URLs.
TOOLCHAIN_ORG="$(echo "${TOOLCHAIN}" | cut -d/ -f1)"
TOOLCHAIN_REPO="$(echo "${TOOLCHAIN}" | cut -d/ -f2 | cut -d: -f1)"
TOOLCHAIN_TAG="$(echo "${TOOLCHAIN}" | cut -d: -f2)"
# elan normalises "org/repo:tag" → "org-repo-tag" for directory names.
TOOLCHAIN_DIR_NAME="$(echo "${TOOLCHAIN}" | sed 's|/|-|g; s|:|-|g')"

# Detect architecture for download URL.
detect_arch_suffix() {
  local arch
  arch="$(uname -m)"
  case "${arch}" in
    x86_64|amd64)  echo "" ;;       # default is x86_64 (no suffix)
    aarch64|arm64) echo "_aarch64" ;;
    *) echo "error: unsupported architecture '${arch}'" >&2; exit 1 ;;
  esac
}

# Write the elan env file if it does not already exist.
ensure_elan_env_file() {
  if [ -f "${ELAN_ENV_FILE}" ]; then
    return 0
  fi
  mkdir -p "$(dirname "${ELAN_ENV_FILE}")"
  cat > "${ELAN_ENV_FILE}" << 'ENVEOF'
#!/bin/sh
# elan shell setup
case ":${PATH}:" in
    *:"${HOME}/.elan/bin":*)
        ;;
    *)
        export PATH="${HOME}/.elan/bin:${PATH}"
        ;;
esac
ENVEOF
}

# Ensure zstd is available for extracting Lean toolchain archives.
ensure_zstd() {
  if command -v zstd >/dev/null 2>&1; then
    return 0
  fi
  log "[setup] zstd not found; attempting to install"
  if command -v apt-get >/dev/null 2>&1; then
    apt_update_once
    run_pkg_install env DEBIAN_FRONTEND=noninteractive apt-get install -y zstd || true
  elif command -v dnf >/dev/null 2>&1; then
    run_pkg_install dnf install -y zstd || true
  elif command -v brew >/dev/null 2>&1; then
    brew install zstd || true
  fi
  if ! command -v zstd >/dev/null 2>&1; then
    return 1
  fi
}

# Fallback: manually download and install elan + Lean toolchain using curl.
# This bypasses elan's internal HTTP client which may fail in proxied
# environments (e.g. Claude Code web sessions behind an egress gateway).
manual_curl_install() {
  log "[setup] elan's network client failed; falling back to manual curl-based install"

  local elan_bin_dir="${ELAN_HOME_DIR}/bin"
  local toolchain_dir="${ELAN_HOME_DIR}/toolchains/${TOOLCHAIN_DIR_NAME}"

  # --- Install elan binary ---
  if [ ! -x "${elan_bin_dir}/elan" ]; then
    log "[setup] downloading elan binary via curl"
    local arch_name
    case "$(uname -m)" in
      x86_64|amd64)   arch_name="x86_64-unknown-linux-gnu" ;;
      aarch64|arm64)   arch_name="aarch64-unknown-linux-gnu" ;;
      *) echo "error: unsupported architecture for elan download: $(uname -m)" >&2; exit 1 ;;
    esac
    local elan_tar
    elan_tar="$(mktemp)"
    trap 'rm -f "${elan_tar}"' EXIT
    curl -fsSL "https://github.com/leanprover/elan/releases/latest/download/elan-${arch_name}.tar.gz" -o "${elan_tar}"
    mkdir -p "${elan_bin_dir}"
    tar -xzf "${elan_tar}" -C "${elan_bin_dir}/"
    chmod +x "${elan_bin_dir}/elan-init"
    rm -f "${elan_tar}"
    trap - EXIT
    log "[setup] elan binary installed to ${elan_bin_dir}"
  fi

  # --- Write env and settings files ---
  ensure_elan_env_file

  cat > "${ELAN_HOME_DIR}/settings.toml" << SETTINGSEOF
version = "12"
default_toolchain = "${TOOLCHAIN_DIR_NAME}"
SETTINGSEOF

  # --- Install Lean toolchain ---
  if [ ! -d "${toolchain_dir}/bin" ]; then
    log "[setup] downloading Lean toolchain ${TOOLCHAIN} via curl"
    local arch_suffix
    arch_suffix="$(detect_arch_suffix)"
    local version_number="${TOOLCHAIN_TAG#v}"
    local lean_archive_name="lean-${version_number}-linux${arch_suffix}"

    if ensure_zstd; then
      local lean_tar
      lean_tar="$(mktemp)"
      trap 'rm -f "${lean_tar}"' EXIT
      curl -fsSL "https://github.com/${TOOLCHAIN_ORG}/${TOOLCHAIN_REPO}/releases/download/${TOOLCHAIN_TAG}/${lean_archive_name}.tar.zst" -o "${lean_tar}"
      mkdir -p "${ELAN_HOME_DIR}/toolchains"
      local lean_extracted
      lean_extracted="$(mktemp)"
      rm -f "${lean_extracted}"
      lean_extracted="${lean_extracted}.tar"
      zstd -d "${lean_tar}" -o "${lean_extracted}"
      tar -xf "${lean_extracted}" -C "${ELAN_HOME_DIR}/toolchains/"
      rm -f "${lean_tar}" "${lean_extracted}"
      trap - EXIT
    else
      log "[setup] zstd unavailable; downloading zip archive instead"
      local lean_zip
      lean_zip="$(mktemp)"
      trap 'rm -f "${lean_zip}"' EXIT
      curl -fsSL "https://github.com/${TOOLCHAIN_ORG}/${TOOLCHAIN_REPO}/releases/download/${TOOLCHAIN_TAG}/${lean_archive_name}.zip" -o "${lean_zip}"
      mkdir -p "${ELAN_HOME_DIR}/toolchains"
      unzip -qo "${lean_zip}" -d "${ELAN_HOME_DIR}/toolchains/"
      rm -f "${lean_zip}"
      trap - EXIT
    fi

    # Rename extracted directory to match elan's naming convention.
    local extracted_dir="${ELAN_HOME_DIR}/toolchains/${lean_archive_name}"
    if [ -d "${extracted_dir}" ] && [ "${extracted_dir}" != "${toolchain_dir}" ]; then
      mv "${extracted_dir}" "${toolchain_dir}"
    fi

    log "[setup] Lean toolchain installed to ${toolchain_dir}"
  else
    log "[setup] Lean toolchain already present at ${toolchain_dir}"
  fi

  # --- Register toolchain with elan via symlink ---
  # shellcheck disable=SC1090
  source "${ELAN_ENV_FILE}"
  if command -v elan >/dev/null 2>&1; then
    elan toolchain link "${TOOLCHAIN}" "${toolchain_dir}" 2>/dev/null || true
    elan default "${TOOLCHAIN}" 2>/dev/null || true
  fi

  # Create update-hashes to prevent elan from trying to re-download.
  mkdir -p "${ELAN_HOME_DIR}/update-hashes"
  echo "manual-install" > "${ELAN_HOME_DIR}/update-hashes/${TOOLCHAIN_DIR_NAME}"
}

# -------- Main installation flow --------

# If elan was previously installed with --no-modify-path, load it before probing.
if [ -f "${ELAN_ENV_FILE}" ]; then
  # shellcheck disable=SC1090
  source "${ELAN_ENV_FILE}"
fi

ELAN_INSTALL_FAILED=0

if ! command -v elan >/dev/null 2>&1; then
  log "[setup] elan not found; installing to ${ELAN_HOME_DIR}"
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

  if ! sh "${elan_installer}" -y --no-modify-path; then
    echo "[setup] elan-init.sh failed (likely network/proxy issue)" >&2
    ELAN_INSTALL_FAILED=1
  fi
  rm -f "${elan_installer}"
  trap - EXIT
fi

# If elan standard install failed, fall back to manual curl-based install.
if [ "${ELAN_INSTALL_FAILED}" -eq 1 ]; then
  manual_curl_install
fi

ensure_elan_env_file

if [ -f "${ELAN_ENV_FILE}" ]; then
  # shellcheck disable=SC1090
  source "${ELAN_ENV_FILE}"
fi

# If elan is available and the toolchain isn't set up yet, try the standard path.
if command -v elan >/dev/null 2>&1; then
  log "[setup] ensuring Lean toolchain ${TOOLCHAIN} is installed"
  if ! elan toolchain list | tr -d '\r' | grep -Fq "${TOOLCHAIN}"; then
    if ! elan toolchain install "${TOOLCHAIN}" 2>/dev/null; then
      echo "[setup] elan toolchain install failed; trying manual install" >&2
      manual_curl_install
      # Re-source after manual install
      # shellcheck disable=SC1090
      source "${ELAN_ENV_FILE}"
    fi
  else
    log "[setup] Lean toolchain ${TOOLCHAIN} is already installed"
  fi
  elan default "${TOOLCHAIN}" 2>/dev/null || true
fi

if ! command -v lake >/dev/null 2>&1; then
  # Last resort: try manual install if we haven't already.
  manual_curl_install
  # shellcheck disable=SC1090
  source "${ELAN_ENV_FILE}"
fi

if ! command -v lake >/dev/null 2>&1; then
  echo "error: lake is still not on PATH after setup" >&2
  exit 1
fi

log "[setup] Lean environment is ready"
log "[setup] lake version: $(lake --version)"

if [ "${QUIET}" -eq 0 ]; then
  echo "[setup] next steps:"
  echo "  source \"${ELAN_ENV_FILE}\""
  echo "  lake build"
fi

BUILD_REQUESTED=0
for arg in "$@"; do
  case "${arg}" in
    --build) BUILD_REQUESTED=1 ;;
  esac
done

if [ "${BUILD_REQUESTED}" -eq 1 ]; then
  log "[setup] running lake build"
  (cd "${ROOT_DIR}" && lake build)
fi
