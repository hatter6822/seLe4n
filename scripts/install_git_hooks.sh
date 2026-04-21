#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
#
# install_git_hooks.sh — idempotent installer for seLe4n git hooks
#
# WS-AN AN1-B (audit finding C-03): the prior convention required every
# contributor to run `cp scripts/pre-commit-lean-build.sh .git/hooks/pre-commit`
# manually. Fresh clones that skipped the step shipped code without the
# sorry/build guard. This installer is invoked automatically by
# `scripts/setup_lean_env.sh` and by the CI bootstrap so any checkout is
# covered.
#
# Default mode (no flags): install hook if absent; no-op if already installed
# and pointing at the canonical source; abort with an actionable message if a
# different hook is present (use --force to replace it).
#
# --check: return 0 when the hook is installed correctly, non-zero otherwise.
#          Intended for CI ("did the installer run?" guard).
# --force: overwrite any existing pre-commit hook after backing it up to
#          `.git/hooks/pre-commit.backup-<timestamp>`.
# --help:  print usage and exit 0.
#
# Exit codes:
#   0  hook is installed and matches the canonical source, or this is not a
#      git worktree (nothing to install; warn and skip).
#   1  hook is missing or differs from the canonical source (and --force was
#      not passed), or --check was requested and verification failed.
#   2  invalid invocation / setup error.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
SOURCE_HOOK="${SCRIPT_DIR}/pre-commit-lean-build.sh"
GIT_DIR="${REPO_ROOT}/.git"
HOOK_TARGET="${GIT_DIR}/hooks/pre-commit"

MODE="install"
for arg in "$@"; do
  case "${arg}" in
    --check) MODE="check" ;;
    --force) MODE="force" ;;
    --help|-h)
      sed -n '1,40p' "${BASH_SOURCE[0]}" | grep -E '^#' | sed 's/^# \{0,1\}//'
      exit 0
      ;;
    *)
      echo "ERROR: unknown argument '${arg}' (see --help)" >&2
      exit 2
      ;;
  esac
done

if [[ ! -f "${SOURCE_HOOK}" ]]; then
  echo "ERROR: canonical hook source missing: ${SOURCE_HOOK}" >&2
  exit 2
fi

# Handle non-git checkouts (tarball extracts, read-only mirrors, etc.).
if [[ ! -d "${GIT_DIR}" ]]; then
  if [[ "${MODE}" == "check" ]]; then
    echo "install_git_hooks: not a git worktree (${GIT_DIR} absent) — nothing to check"
    exit 0
  fi
  echo "install_git_hooks: not a git worktree (${GIT_DIR} absent) — skipping"
  exit 0
fi

mkdir -p "${GIT_DIR}/hooks"

# Symlink target is repo-relative so future updates to pre-commit-lean-build.sh
# propagate without re-running the installer.
REL_SOURCE="../../scripts/pre-commit-lean-build.sh"

hook_matches_canonical() {
  # Returns 0 iff the installed hook points at (symlink) or byte-identical to
  # (copy) the canonical script.
  if [[ -L "${HOOK_TARGET}" ]]; then
    local target
    target="$(readlink "${HOOK_TARGET}")"
    [[ "${target}" == "${REL_SOURCE}" || "${target}" == "${SOURCE_HOOK}" ]]
  elif [[ -f "${HOOK_TARGET}" ]]; then
    cmp -s "${HOOK_TARGET}" "${SOURCE_HOOK}"
  else
    return 1
  fi
}

case "${MODE}" in
  check)
    if hook_matches_canonical; then
      echo "install_git_hooks: pre-commit hook installed and matches canonical source"
      exit 0
    fi
    if [[ ! -e "${HOOK_TARGET}" ]]; then
      echo "install_git_hooks: ERROR pre-commit hook missing at ${HOOK_TARGET}" >&2
    else
      echo "install_git_hooks: ERROR pre-commit hook present but differs from canonical source" >&2
    fi
    echo "Run: ./scripts/install_git_hooks.sh (or --force to replace)" >&2
    exit 1
    ;;

  install|force)
    if hook_matches_canonical; then
      echo "install_git_hooks: pre-commit hook already installed (no-op)"
      exit 0
    fi

    if [[ -e "${HOOK_TARGET}" || -L "${HOOK_TARGET}" ]]; then
      if [[ "${MODE}" != "force" ]]; then
        echo "ERROR: a different pre-commit hook already exists at ${HOOK_TARGET}" >&2
        echo "Re-run with --force to back it up and replace." >&2
        exit 1
      fi
      local_backup="${HOOK_TARGET}.backup-$(date -u +%Y%m%d-%H%M%S)"
      mv "${HOOK_TARGET}" "${local_backup}"
      echo "install_git_hooks: backed up existing hook to ${local_backup}"
    fi

    if ln -s "${REL_SOURCE}" "${HOOK_TARGET}" 2>/dev/null; then
      echo "install_git_hooks: symlinked ${HOOK_TARGET} -> ${REL_SOURCE}"
    else
      # Filesystems that forbid symlinks (some Windows / container mounts)
      # fall back to a copy. Mark executable either way.
      cp "${SOURCE_HOOK}" "${HOOK_TARGET}"
      echo "install_git_hooks: copied ${SOURCE_HOOK} -> ${HOOK_TARGET} (symlink unavailable)"
    fi

    chmod +x "${HOOK_TARGET}"
    echo "install_git_hooks: pre-commit hook installed"
    exit 0
    ;;
esac
