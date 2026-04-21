#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
#
# install_git_hooks.sh — idempotent installer for seLe4n's git pre-commit hook.
#
# Closes C-03 from AUDIT_v0.30.6_COMPREHENSIVE.md per AN1-B in
# docs/audits/AUDIT_v0.30.6_WORKSTREAM_PLAN.md §4.
#
# The canonical source is scripts/pre-commit-lean-build.sh. Contributors used
# to run a manual `cp` per CLAUDE.md's install recipe, which did not protect
# CI-cloned checkouts nor fresh worktrees. This installer runs automatically
# from setup_lean_env.sh and the Lean Action CI workflow bootstrap so every
# checkout gets the hook.
#
# Modes:
#   (default)  install the hook if absent; no-op if already identical to the
#              canonical source; refuse with an actionable message if a
#              diverging hook is present.
#   --check    exit 0 iff the installed hook matches the canonical source
#              (used by CI as a guard: "did the installer run?"). Non-zero
#              exit with an actionable message otherwise.
#   --force    overwrite any existing hook, backing the prior contents up
#              to .git/hooks/pre-commit.backup-<timestamp>.
#
# Exit codes:
#   0  success (hook present and matches canonical source)
#   1  diverging hook present and --force not supplied (default mode), or
#      --check mode with a missing/diverging hook
#   2  canonical source missing, or non-git-repo without --check
#
# Environment:
#   The script skips with a non-fatal informational log and exits 0 when
#   run outside a git working tree (tarball extract, archive unpack, etc.)
#   so setup_lean_env.sh can invoke it unconditionally.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
CANONICAL_HOOK="${SCRIPT_DIR}/pre-commit-lean-build.sh"
HOOK_RELATIVE="../../scripts/pre-commit-lean-build.sh"

MODE="install"
for arg in "$@"; do
  case "${arg}" in
    --check) MODE="check" ;;
    --force) MODE="force" ;;
    --help|-h)
      sed -n '1,40p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'
      exit 0
      ;;
    *)
      echo "install_git_hooks.sh: unknown argument '${arg}'" >&2
      echo "  Use --check, --force, or no arguments." >&2
      exit 2
      ;;
  esac
done

log() {
  echo "[install_git_hooks] $*"
}

# Canonical source must exist. Even in --check mode we need to compare against it.
if [[ ! -f "${CANONICAL_HOOK}" ]]; then
  echo "ERROR: canonical hook source missing at ${CANONICAL_HOOK}" >&2
  exit 2
fi

# Non-git-repo guard. setup_lean_env.sh invokes us unconditionally, but tarball
# extracts and zip downloads do not have a .git directory. Skip quietly in that
# case — the installer is not relevant.
GIT_DIR_REL=""
if ! GIT_DIR_REL="$(git -C "${REPO_ROOT}" rev-parse --git-dir 2>/dev/null)"; then
  if [[ "${MODE}" == "check" ]]; then
    echo "ERROR: not a git repository at ${REPO_ROOT}; --check cannot verify hook installation" >&2
    exit 2
  fi
  log "not a git repository; skipping pre-commit hook install (safe no-op)"
  exit 0
fi

# Resolve absolute git-dir path.
if [[ "${GIT_DIR_REL}" = /* ]]; then
  GIT_DIR="${GIT_DIR_REL}"
else
  GIT_DIR="${REPO_ROOT}/${GIT_DIR_REL}"
fi

HOOKS_DIR="${GIT_DIR}/hooks"
HOOK_PATH="${HOOKS_DIR}/pre-commit"

mkdir -p "${HOOKS_DIR}"

# Determine canonical hook content hash for comparison with whatever is installed.
canonical_sha() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "${CANONICAL_HOOK}" | awk '{print $1}'
  elif command -v shasum >/dev/null 2>&1; then
    shasum -a 256 "${CANONICAL_HOOK}" | awk '{print $1}'
  else
    # No sha tool — fall back to byte-identity via cmp below. Echo empty so the
    # caller distinguishes the case and uses cmp instead.
    echo ""
  fi
}

installed_matches_canonical() {
  # Returns 0 iff ${HOOK_PATH} exists and has identical bytes to ${CANONICAL_HOOK}.
  # Resolves symlinks transparently (cmp follows them).
  if [[ ! -e "${HOOK_PATH}" ]]; then
    return 1
  fi
  if cmp -s "${HOOK_PATH}" "${CANONICAL_HOOK}"; then
    return 0
  fi
  return 1
}

install_hook() {
  # Prefer a symlink so future edits to pre-commit-lean-build.sh propagate
  # without a reinstall. Fall back to a copy for symlink-hostile filesystems
  # (Windows WSL w/ certain mounts, some NFS configurations).
  if ln -s "${HOOK_RELATIVE}" "${HOOK_PATH}" 2>/dev/null; then
    log "installed pre-commit hook as symlink → ${HOOK_RELATIVE}"
    return 0
  fi
  log "symlink failed; falling back to copy"
  cp "${CANONICAL_HOOK}" "${HOOK_PATH}"
  chmod +x "${HOOK_PATH}"
  log "installed pre-commit hook as copy of pre-commit-lean-build.sh"
}

case "${MODE}" in
  check)
    if installed_matches_canonical; then
      log "pre-commit hook is installed and matches canonical source"
      exit 0
    fi
    if [[ ! -e "${HOOK_PATH}" ]]; then
      echo "ERROR: pre-commit hook NOT installed at ${HOOK_PATH}" >&2
    else
      echo "ERROR: pre-commit hook at ${HOOK_PATH} diverges from canonical source" >&2
    fi
    echo "  Run ./scripts/install_git_hooks.sh (or --force to overwrite) to install it." >&2
    exit 1
    ;;
  force)
    if [[ -e "${HOOK_PATH}" || -L "${HOOK_PATH}" ]]; then
      BACKUP="${HOOK_PATH}.backup-$(date -u +%Y%m%dT%H%M%SZ)"
      mv "${HOOK_PATH}" "${BACKUP}"
      log "backed up diverging hook to ${BACKUP}"
    fi
    install_hook
    exit 0
    ;;
  install)
    if installed_matches_canonical; then
      log "pre-commit hook already installed (no-op)"
      exit 0
    fi
    if [[ -e "${HOOK_PATH}" || -L "${HOOK_PATH}" ]]; then
      echo "ERROR: a diverging pre-commit hook is already present at ${HOOK_PATH}" >&2
      echo "  Compare with scripts/pre-commit-lean-build.sh and integrate the desired logic," >&2
      echo "  or run ./scripts/install_git_hooks.sh --force to overwrite (the previous" >&2
      echo "  hook will be backed up to .git/hooks/pre-commit.backup-<timestamp>)." >&2
      exit 1
    fi
    install_hook
    exit 0
    ;;
esac
