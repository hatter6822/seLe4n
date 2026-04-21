#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
QUIET=0
BUILD_REQUESTED=0
SKIP_TEST_DEPS=0
for arg in "$@"; do
  case "${arg}" in
    --quiet|-q) QUIET=1 ;;
    --build) BUILD_REQUESTED=1 ;;
    --skip-test-deps) SKIP_TEST_DEPS=1 ;;
  esac
done
log() { if [ "${QUIET}" -eq 0 ]; then echo "$@"; fi; }

# Elapsed-time helper for performance diagnostics.
SETUP_START_TIME="${EPOCHREALTIME:-$(date +%s)}"
log_elapsed() {
  local now="${EPOCHREALTIME:-$(date +%s)}"
  local elapsed
  # Use bc for fractional seconds if available, otherwise integer diff.
  if command -v bc >/dev/null 2>&1; then
    elapsed="$(echo "${now} - ${SETUP_START_TIME}" | bc)"
  else
    elapsed="$(( ${now%.*} - ${SETUP_START_TIME%.*} ))"
  fi
  log "[setup +${elapsed}s] $*"
}

ELAN_HOME_DEFAULT="${HOME}/.elan"
ELAN_HOME_DIR="${ELAN_HOME:-$ELAN_HOME_DEFAULT}"
ELAN_ENV_FILE="${ELAN_HOME_DIR}/env"
LEAN_TOOLCHAIN_FILE="${ROOT_DIR}/lean-toolchain"
ELAN_INSTALLER_URL="https://raw.githubusercontent.com/leanprover/elan/87f5ec2f5627dd3df16b346733147412c3ddeef1/elan-init.sh"
# WS-B9 hardening anchor: commit-pinned installer URL + hash must be updated together intentionally.
ELAN_INSTALLER_SHA256="4bacca9502cb89736fe63d2685abc2947cfbf34dc87673504f1bb4c43eda9264"

# AA2-B (H-4): Rust toolchain version pinned in CI via dtolnay/rust-toolchain action.
# This variable documents the pinned version for consistency with the Lean toolchain
# SHA-pinning above. Update this when bumping the Rust version in
# .github/workflows/lean_action_ci.yml (the `toolchain:` field).
# shellcheck disable=SC2034  # documentation-only variable, not consumed by this script
RUST_TOOLCHAIN_VERSION="1.82.0"

# R8-A (I-M01): Pin elan binary release version for direct download path.
# Replaces /releases/latest/ with a specific tag to prevent silent upgrades.
# SHA-256 hashes for the elan binary tarballs — update these together with the version.
ELAN_BINARY_VERSION="v4.2.1"
# To regenerate hashes after version bump:
#   curl -fsSL "https://github.com/leanprover/elan/releases/download/${ELAN_BINARY_VERSION}/elan-x86_64-unknown-linux-gnu.tar.gz" | sha256sum
#   curl -fsSL "https://github.com/leanprover/elan/releases/download/${ELAN_BINARY_VERSION}/elan-aarch64-unknown-linux-gnu.tar.gz" | sha256sum
ELAN_BINARY_SHA256_X86="4e717523217af592fa2d7b9c479410a31816c065d66ccbf0c2149337cfec0f5c"
ELAN_BINARY_SHA256_ARM="bb78726ace6a912c7122a389018bcd69d9122ce04659800101392f7db380d3b3"

# M-NEW-13: SHA-256 hashes for the Lean toolchain archives (v4.28.0).
# Update these when bumping TOOLCHAIN_TAG in lean-toolchain.
# To regenerate:
#   curl -fsSL "https://github.com/leanprover/lean4/releases/download/v4.28.0/lean-4.28.0-linux.tar.zst" | sha256sum
#   curl -fsSL "https://github.com/leanprover/lean4/releases/download/v4.28.0/lean-4.28.0-linux_aarch64.tar.zst" | sha256sum
#   curl -fsSL "https://github.com/leanprover/lean4/releases/download/v4.28.0/lean-4.28.0-linux.zip" | sha256sum
#   curl -fsSL "https://github.com/leanprover/lean4/releases/download/v4.28.0/lean-4.28.0-linux_aarch64.zip" | sha256sum
LEAN_TOOLCHAIN_SHA256_ZST_X86="ceb3a3f844f7aebf63245e2b51c28d5b0ed38942c19f93cf3febd520302160bd"
LEAN_TOOLCHAIN_SHA256_ZST_ARM="c865801261c747d4f15d08beca9abc20aca907904abbb284de25a37f4b4558bc"
LEAN_TOOLCHAIN_SHA256_ZIP_X86="b02b74bb23e93e5b05f03f51ad06274814337d107718a02b6f89dc4db1387416"
LEAN_TOOLCHAIN_SHA256_ZIP_ARM="c608141afb645c7faa3845cc5dc503890ae329a82359f9bf37358d1fab499f81"

# -------- Parse toolchain spec early (needed by fast-path) --------
if [ ! -f "${LEAN_TOOLCHAIN_FILE}" ]; then
  echo "error: lean-toolchain not found at ${LEAN_TOOLCHAIN_FILE}" >&2
  exit 1
fi
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

# -------- Fast-path: skip setup if everything is already ready --------
# This avoids all package-manager and network operations on repeat sessions.
fast_path_ready() {
  # Source elan env if available (single source point for fast-path check).
  if [ -f "${ELAN_ENV_FILE}" ]; then
    # shellcheck disable=SC1090
    source "${ELAN_ENV_FILE}"
  fi
  # Check 1: lake must be on PATH.
  command -v lake >/dev/null 2>&1 || return 1
  # Check 2: toolchain directory must exist with bin/lean.
  local tc_dir="${ELAN_HOME_DIR}/toolchains/${TOOLCHAIN_DIR_NAME}"
  [ -x "${tc_dir}/bin/lean" ] || return 1
  # Check 3: CRT startup files must be present (linker sanity).
  [ -f "${tc_dir}/lib/crti.o" ] || return 1
  return 0
}

if fast_path_ready; then
  log_elapsed "Lean environment already configured (fast-path)"
  # AN1-B.2 (audit C-03): ensure the pre-commit hook is installed on every
  # setup, not only on fresh clones. The installer is idempotent; it silently
  # skips non-git worktrees and returns non-zero (with an actionable message)
  # if a diverging hook is present. We surface that message to the user but
  # do not fail setup — CI's `install_git_hooks.sh --check` step is the
  # enforcement gate.
  if ! "${ROOT_DIR}/scripts/install_git_hooks.sh"; then
    log "[setup] WARNING: install_git_hooks.sh reported an issue (see message above)."
  fi
  if [ "${BUILD_REQUESTED}" -eq 1 ]; then
    log_elapsed "running lake build"
    (cd "${ROOT_DIR}" && lake build)
  fi
  exit 0
fi

log_elapsed "full environment setup required"

# -------- Prerequisite check --------
if ! command -v curl >/dev/null 2>&1; then
  echo "error: curl is required to install elan" >&2
  exit 1
fi

# -------- Package management helpers --------
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

# M-NEW-13: Verify SHA-256 of downloaded Lean toolchain archive.
# Usage: verify_toolchain_sha256 <file> <format>
#   format: "zst" or "zip"
# Aborts with error on mismatch. Skips verification if expected hash is empty
# (allows graceful handling of unknown toolchain versions).
verify_toolchain_sha256() {
  local target_file="$1"
  local format="$2"
  local expected_sha=""

  case "$(uname -m)" in
    x86_64|amd64)
      if [ "${format}" = "zst" ]; then
        expected_sha="${LEAN_TOOLCHAIN_SHA256_ZST_X86}"
      else
        expected_sha="${LEAN_TOOLCHAIN_SHA256_ZIP_X86}"
      fi
      ;;
    aarch64|arm64)
      if [ "${format}" = "zst" ]; then
        expected_sha="${LEAN_TOOLCHAIN_SHA256_ZST_ARM}"
      else
        expected_sha="${LEAN_TOOLCHAIN_SHA256_ZIP_ARM}"
      fi
      ;;
  esac

  # AA2-D (M-7): Fail-closed on unrecognized architectures — do not silently
  # skip hash verification, as this would allow unverified toolchain binaries.
  if [ -z "${expected_sha}" ]; then
    echo "error: no SHA-256 hash configured for architecture $(uname -m); aborting" >&2
    echo "  Add the appropriate hash to the LEAN_TOOLCHAIN_SHA256_* variables" >&2
    echo "  in scripts/setup_lean_env.sh before installing on this platform." >&2
    return 1
  fi

  local actual_sha
  actual_sha="$(compute_sha256 "${target_file}")"
  if [ "${actual_sha}" != "${expected_sha}" ]; then
    echo "error: Lean toolchain checksum verification failed" >&2
    echo "  archive: ${target_file}" >&2
    echo "  format:  ${format}" >&2
    echo "  expected: ${expected_sha}" >&2
    echo "  actual:   ${actual_sha}" >&2
    echo "" >&2
    echo "  This may indicate a corrupted download or a supply-chain attack." >&2
    echo "  If you intentionally upgraded the toolchain, update the" >&2
    echo "  LEAN_TOOLCHAIN_SHA256_* variables in this script." >&2
    rm -f "${target_file}"
    exit 1
  fi
  log_elapsed "toolchain SHA-256 verified (${format})"
}

# -------- Batched dependency installation --------
# Collect all missing packages and install in a single transaction.
# With --skip-test-deps, only install build-critical packages.
# IMPORTANT: apt-get update is extremely slow in environments with unreachable
# package sources (DNS resolution timeouts for docker, PPA, etc.). We avoid
# calling it on the critical path. zstd is nice-to-have (smaller download)
# but not required — the toolchain also ships as .zip.
install_missing_packages() {
  local missing_apt=()
  local missing_any=0

  # Shell-checker and ripgrep are only needed for test/lint — skip during build-only setup.
  if [ "${SKIP_TEST_DEPS}" -eq 0 ]; then
    if ! command -v shellcheck >/dev/null 2>&1; then
      missing_apt+=("shellcheck")
      missing_any=1
    fi
    if ! command -v rg >/dev/null 2>&1; then
      missing_apt+=("ripgrep")
      missing_any=1
    fi
  fi

  # zstd: try a quick install without apt-get update first (from local cache).
  # If that fails, skip it — the toolchain download will fall back to .zip.
  if ! command -v zstd >/dev/null 2>&1; then
    if command -v apt-get >/dev/null 2>&1; then
      # Try install from cached package index (no update). Timeout after 5s.
      if timeout 5 bash -c 'sudo DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends zstd 2>/dev/null' >/dev/null 2>&1; then
        log_elapsed "zstd installed from cache"
      else
        log_elapsed "zstd not in cache; will use zip fallback for toolchain download"
      fi
    fi
  fi

  if [ "${missing_any}" -eq 0 ]; then
    return 0
  fi

  # Non-critical packages: install in background so they don't block setup.
  if [ "${SKIP_TEST_DEPS}" -eq 1 ]; then
    return 0
  fi

  log_elapsed "installing test dependencies in background: ${missing_apt[*]}"
  (
    if command -v apt-get >/dev/null 2>&1; then
      apt_update_once
      run_pkg_install env DEBIAN_FRONTEND=noninteractive apt-get install -y "${missing_apt[@]}" || true
    elif command -v dnf >/dev/null 2>&1; then
      local dnf_pkgs=()
      for pkg in "${missing_apt[@]}"; do
        case "${pkg}" in
          shellcheck) dnf_pkgs+=("ShellCheck") ;;
          *) dnf_pkgs+=("${pkg}") ;;
        esac
      done
      run_pkg_install dnf install -y "${dnf_pkgs[@]}" || true
    elif command -v yum >/dev/null 2>&1; then
      run_pkg_install yum install -y epel-release 2>/dev/null || true
      local yum_pkgs=()
      for pkg in "${missing_apt[@]}"; do
        case "${pkg}" in
          shellcheck) yum_pkgs+=("ShellCheck") ;;
          *) yum_pkgs+=("${pkg}") ;;
        esac
      done
      run_pkg_install yum install -y "${yum_pkgs[@]}" || true
    elif command -v pacman >/dev/null 2>&1; then
      run_pkg_install pacman -Sy --noconfirm "${missing_apt[@]}" || true
    elif command -v brew >/dev/null 2>&1; then
      for pkg in "${missing_apt[@]}"; do
        brew install "${pkg}" || true
      done
    fi
  ) &
  PKG_BG_PID=$!
}

PKG_BG_PID=""
install_missing_packages

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

# Direct-install: download elan binary + Lean toolchain using curl.
# This bypasses elan's internal HTTP client which may fail in proxied
# environments (e.g. Claude Code web sessions behind an egress gateway).
# Optimized to download elan and toolchain in parallel where possible.
manual_curl_install() {
  log_elapsed "manual curl-based install starting"

  local elan_bin_dir="${ELAN_HOME_DIR}/bin"
  local toolchain_dir="${ELAN_HOME_DIR}/toolchains/${TOOLCHAIN_DIR_NAME}"
  local arch_suffix
  arch_suffix="$(detect_arch_suffix)"
  local version_number="${TOOLCHAIN_TAG#v}"
  local lean_archive_name="lean-${version_number}-linux${arch_suffix}"

  mkdir -p "${elan_bin_dir}" "${ELAN_HOME_DIR}/toolchains"

  # --- Write env and settings files early (no network needed) ---
  ensure_elan_env_file

  cat > "${ELAN_HOME_DIR}/settings.toml" << SETTINGSEOF
version = "12"
default_toolchain = "${TOOLCHAIN_DIR_NAME}"
SETTINGSEOF

  # --- Download elan binary in background while toolchain downloads ---
  # R8-A (I-M01): Version-pinned URL with SHA-256 verification.
  local elan_bg_pid=""
  if [ ! -x "${elan_bin_dir}/elan" ]; then
    (
      local arch_name expected_sha
      case "$(uname -m)" in
        x86_64|amd64)
          arch_name="x86_64-unknown-linux-gnu"
          expected_sha="${ELAN_BINARY_SHA256_X86}"
          ;;
        aarch64|arm64)
          arch_name="aarch64-unknown-linux-gnu"
          expected_sha="${ELAN_BINARY_SHA256_ARM}"
          ;;
        *) exit 1 ;;
      esac
      local elan_tar
      elan_tar="$(mktemp)"
      curl -fsSL "https://github.com/leanprover/elan/releases/download/${ELAN_BINARY_VERSION}/elan-${arch_name}.tar.gz" -o "${elan_tar}"

      # Verify SHA-256 hash of downloaded binary.
      local actual_sha
      actual_sha="$(compute_sha256 "${elan_tar}")"
      if [ "${actual_sha}" != "${expected_sha}" ]; then
        echo "error: elan binary checksum verification failed" >&2
        echo "  expected: ${expected_sha}" >&2
        echo "  actual:   ${actual_sha}" >&2
        rm -f "${elan_tar}"
        exit 1
      fi

      tar -xzf "${elan_tar}" -C "${elan_bin_dir}/" \
        && chmod +x "${elan_bin_dir}/elan-init"
      rm -f "${elan_tar}"
    ) &
    elan_bg_pid=$!
  fi

  # --- Install Lean toolchain (foreground — this is the critical path) ---
  if [ ! -d "${toolchain_dir}/bin" ]; then
    log_elapsed "downloading Lean toolchain ${TOOLCHAIN}"

    if command -v zstd >/dev/null 2>&1; then
      local lean_tar
      lean_tar="$(mktemp)"
      trap 'rm -f "${lean_tar}"' EXIT
      curl -fsSL "https://github.com/${TOOLCHAIN_ORG}/${TOOLCHAIN_REPO}/releases/download/${TOOLCHAIN_TAG}/${lean_archive_name}.tar.zst" -o "${lean_tar}"
      verify_toolchain_sha256 "${lean_tar}" "zst"
      log_elapsed "extracting toolchain (zstd)"
      local lean_extracted
      lean_extracted="$(mktemp)"
      rm -f "${lean_extracted}"
      lean_extracted="${lean_extracted}.tar"
      zstd -d "${lean_tar}" -o "${lean_extracted}"
      tar -xf "${lean_extracted}" -C "${ELAN_HOME_DIR}/toolchains/"
      rm -f "${lean_tar}" "${lean_extracted}"
      trap - EXIT
    else
      log_elapsed "zstd unavailable; downloading zip archive instead"
      local lean_zip
      lean_zip="$(mktemp)"
      trap 'rm -f "${lean_zip}"' EXIT
      curl -fsSL "https://github.com/${TOOLCHAIN_ORG}/${TOOLCHAIN_REPO}/releases/download/${TOOLCHAIN_TAG}/${lean_archive_name}.zip" -o "${lean_zip}"
      verify_toolchain_sha256 "${lean_zip}" "zip"
      unzip -qo "${lean_zip}" -d "${ELAN_HOME_DIR}/toolchains/"
      rm -f "${lean_zip}"
      trap - EXIT
    fi

    # Rename extracted directory to match elan's naming convention.
    local extracted_dir="${ELAN_HOME_DIR}/toolchains/${lean_archive_name}"
    if [ -d "${extracted_dir}" ] && [ "${extracted_dir}" != "${toolchain_dir}" ]; then
      mv "${extracted_dir}" "${toolchain_dir}"
    fi

    log_elapsed "Lean toolchain installed to ${toolchain_dir}"
  else
    log_elapsed "Lean toolchain already present at ${toolchain_dir}"
  fi

  # --- Wait for elan background download if it was started ---
  if [ -n "${elan_bg_pid}" ]; then
    if wait "${elan_bg_pid}" 2>/dev/null; then
      log_elapsed "elan binary download complete (SHA-256 verified)"
    else
      log_elapsed "warning: elan binary download failed (SHA-256 mismatch or network error); toolchain symlinks will be used instead"
    fi
  fi

  # --- Create direct symlinks so lean/lake/leanc are on PATH immediately ---
  # This makes the toolchain usable even if elan has issues.
  for bin in lean lake leanc leanmake; do
    if [ -x "${toolchain_dir}/bin/${bin}" ] && [ ! -e "${elan_bin_dir}/${bin}" ]; then
      ln -sf "${toolchain_dir}/bin/${bin}" "${elan_bin_dir}/${bin}"
    fi
  done

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

# Source elan env once if it exists (single source point for main flow).
source_elan_env() {
  if [ -f "${ELAN_ENV_FILE}" ]; then
    # shellcheck disable=SC1090
    source "${ELAN_ENV_FILE}"
  fi
}

source_elan_env
TOOLCHAIN_FRESHLY_INSTALLED=0

# Direct-install strategy: skip the elan installer script entirely and go
# straight to manual_curl_install. This eliminates one network round-trip
# (elan-init.sh download + SHA verify + elan's own toolchain download) and
# replaces it with a single curl download of the toolchain archive.
# The elan installer is only used as a fallback if manual install fails.
local_tc_dir="${ELAN_HOME_DIR}/toolchains/${TOOLCHAIN_DIR_NAME}"
if [ ! -x "${local_tc_dir}/bin/lean" ]; then
  log_elapsed "installing Lean toolchain ${TOOLCHAIN} (direct download)"
  if manual_curl_install; then
    TOOLCHAIN_FRESHLY_INSTALLED=1
  else
    # Fallback: try the elan installer script.
    log_elapsed "direct install failed; falling back to elan installer"
    if ! command -v elan >/dev/null 2>&1; then
      log_elapsed "downloading elan installer"
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
        echo "error: both direct install and elan installer failed" >&2
        exit 1
      fi
      rm -f "${elan_installer}"
      trap - EXIT
    fi

    ensure_elan_env_file
    source_elan_env

    if command -v elan >/dev/null 2>&1 && [ ! -d "${local_tc_dir}/bin" ]; then
      log_elapsed "installing toolchain via elan"
      elan toolchain install "${TOOLCHAIN}" 2>/dev/null || true
    fi
    elan default "${TOOLCHAIN}" 2>/dev/null || true
    TOOLCHAIN_FRESHLY_INSTALLED=1
  fi
else
  log_elapsed "Lean toolchain ${TOOLCHAIN} is already installed"
fi

ensure_elan_env_file
source_elan_env

if ! command -v lake >/dev/null 2>&1; then
  echo "error: lake is still not on PATH after setup" >&2
  exit 1
fi

# -------- Linker sanity: verify CRT startup files exist (crti.o fix) --------
# Only verify on fresh installs — cached toolchains already passed this check.
# Lean's clang uses --sysroot to find crti.o/crt1.o inside the toolchain.
# If the toolchain extraction was incomplete, linking will fail with
# "ld: cannot find crti.o". Detect this early and attempt recovery.
if [ "${TOOLCHAIN_FRESHLY_INSTALLED}" -eq 1 ]; then
  verify_crt_files() {
    local tc_dir="${ELAN_HOME_DIR}/toolchains/${TOOLCHAIN_DIR_NAME}"
    local missing=0
    for crt_file in crti.o crt1.o Scrt1.o; do
      if [ ! -f "${tc_dir}/lib/${crt_file}" ]; then
        missing=1
        break
      fi
    done
    if [ "${missing}" -eq 1 ]; then
      echo "[setup] warning: CRT startup files missing from toolchain (crti.o linker fix)" >&2
      echo "[setup] re-downloading toolchain to restore linker prerequisites" >&2
      rm -rf "${tc_dir}"
      manual_curl_install
      source_elan_env
      for crt_file in crti.o crt1.o Scrt1.o; do
        if [ ! -f "${tc_dir}/lib/${crt_file}" ]; then
          echo "[setup] warning: ${crt_file} still missing after re-install; linking may fail" >&2
          if command -v apt-get >/dev/null 2>&1; then
            apt_update_once
            run_pkg_install env DEBIAN_FRONTEND=noninteractive apt-get install -y libc-dev 2>/dev/null || true
          fi
          return 1
        fi
      done
      log_elapsed "CRT files restored successfully"
    fi
    return 0
  }
  verify_crt_files
fi

# Wait for background package install if it was started (don't leave orphans).
if [ -n "${PKG_BG_PID}" ]; then
  wait "${PKG_BG_PID}" 2>/dev/null || true
fi

log_elapsed "Lean environment is ready"
log_elapsed "lake version: $(lake --version)"

# AN1-B.2 (audit C-03): install the pre-commit hook automatically so fresh
# clones are guarded on first setup. The installer is idempotent; it silently
# skips non-git worktrees (tarball extracts, read-only mirrors) and returns
# non-zero with an actionable message if a diverging hook is present. We
# surface that message to the user but do not fail setup — CI's
# `install_git_hooks.sh --check` step is the enforcement gate.
if ! "${ROOT_DIR}/scripts/install_git_hooks.sh"; then
  log "[setup] WARNING: install_git_hooks.sh reported an issue (see message above)."
fi

if [ "${QUIET}" -eq 0 ]; then
  echo "[setup] next steps:"
  echo "  source \"${ELAN_ENV_FILE}\""
  echo "  lake build"
fi

if [ "${BUILD_REQUESTED}" -eq 1 ]; then
  log_elapsed "running lake build"
  (cd "${ROOT_DIR}" && lake build)
fi
