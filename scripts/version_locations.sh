#!/usr/bin/env bash
# shellcheck disable=SC2034,SC2016  # arrays are read by sourcing scripts; backticks in the sed/grep patterns are intentional literals
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
#
# version_locations.sh — single source of truth for every "current version"
# declaration site in the seLe4n project.
#
# This file is *sourced* (never executed) by both:
#   * scripts/check_version_sync.sh  — verifies every site equals the
#     canonical version in lakefile.toml (Tier 0 CI gate + pre-commit).
#   * scripts/bump_version.sh        — rewrites every site to a new version.
#
# Keeping the site list in ONE place means the verifier and the bumper can
# never disagree about what "all version locations" means.  Per CLAUDE.md
# ("every PR bumps the patch version and updates all version locations,
# including README.md and gitbook"), adding a new version-bearing file is a
# one-line `_reg` registration here — both scripts pick it up automatically.
#
# DELIBERATELY NOT LISTED (these are historical prose, NOT current-version
# declarations, and must never be rewritten by a version bump):
#   * CHANGELOG.md version headers (`## vX.Y.Z — ...`) and body text.
#   * "LANDED at vX.Y.Z" / "Version bumped A → B" / "Version stays at X"
#     notes in CLAUDE.md, AGENTS.md, docs/WORKSTREAM_HISTORY.md,
#     docs/CLAIM_EVIDENCE_INDEX.md, and docs/planning/*.md.
#   * The Lean toolchain version (`Lean 4.28.0`) — tracked separately.
#   * Audit-document filenames (`AUDIT_v0.30.6_*`, `AUDIT_v0.30.11_*`).
#
# Each site is registered with `_reg FILE SED VERIFY LABEL [OCCURS]`:
#   FILE    repo-root-relative path.
#   SED     a `sed -E` program that SETS the version.  The literal token
#           @NEW@ is substituted with the new version at apply time.  The
#           version itself is matched by the group-free token
#           [0-9]+[.][0-9]+[.][0-9]+ so the only capture groups are the
#           anchoring prefix (\1) and suffix (\2).
#   VERIFY  a `grep -E` pattern proving the version is present AND correctly
#           anchored.  The literal token @VER@ is substituted with the
#           regex-escaped expected version at check time.  The sentinel
#           value __CARGO_LOCK__ selects a bespoke multi-crate verifier.
#   LABEL   human-readable description for diagnostics.
#   OCCURS  expected number of matching lines (default 1).

VERSION_SITE_FILE=()
VERSION_SITE_SED=()
VERSION_SITE_VERIFY=()
VERSION_SITE_LABEL=()
VERSION_SITE_OCCURS=()

_reg() {
  VERSION_SITE_FILE+=("$1")
  VERSION_SITE_SED+=("$2")
  VERSION_SITE_VERIFY+=("$3")
  VERSION_SITE_LABEL+=("$4")
  VERSION_SITE_OCCURS+=("${5:-1}")
}

# --- Canonical source -------------------------------------------------------
_reg 'lakefile.toml' \
     's/(^version = ")[0-9]+[.][0-9]+[.][0-9]+(")/\1@NEW@\2/' \
     '^version = "@VER@"' \
     'lakefile.toml package version (CANONICAL)'

# --- Rust workspace ---------------------------------------------------------
_reg 'rust/Cargo.toml' \
     's/(\(currently )[0-9]+[.][0-9]+[.][0-9]+(\))/\1@NEW@\2/' \
     '\(currently @VER@\)' \
     'rust/Cargo.toml lakefile-tracking comment'

_reg 'rust/Cargo.toml' \
     's/(^version = ")[0-9]+[.][0-9]+[.][0-9]+(")/\1@NEW@\2/' \
     '^version = "@VER@"' \
     'rust/Cargo.toml workspace package version'

_reg 'rust/Cargo.lock' \
     '/^name = "sele4n-/{n;s/(^version = ")[0-9]+[.][0-9]+[.][0-9]+(")/\1@NEW@\2/;}' \
     '__CARGO_LOCK__' \
     'rust/Cargo.lock sele4n-* crate versions' \
     4

_reg 'rust/sele4n-hal/src/boot.rs' \
     's/(KERNEL_VERSION[^"]*")[0-9]+[.][0-9]+[.][0-9]+(")/\1@NEW@\2/' \
     'KERNEL_VERSION[^"]*"@VER@"' \
     'rust/sele4n-hal/src/boot.rs KERNEL_VERSION const + pinning assert' \
     2

# --- Canonical docs ---------------------------------------------------------
_reg 'docs/spec/SELE4N_SPEC.md' \
     's/(\*\*Package version\*\* \| `)[0-9]+[.][0-9]+[.][0-9]+(`)/\1@NEW@\2/' \
     '\*\*Package version\*\* \| `@VER@`' \
     'docs/spec/SELE4N_SPEC.md Package version row'

_reg 'CLAUDE.md' \
     's/(Lake build system, version )[0-9]+[.][0-9]+[.][0-9]+/\1@NEW@/' \
     'Lake build system, version @VER@' \
     'CLAUDE.md canonical version line'

_reg 'AGENTS.md' \
     's/(Lake build system, version )[0-9]+[.][0-9]+[.][0-9]+/\1@NEW@/' \
     'Lake build system, version @VER@' \
     'AGENTS.md canonical version line (CLAUDE.md mirror)'

# --- Root README ------------------------------------------------------------
_reg 'README.md' \
     's/(version-)[0-9]+[.][0-9]+[.][0-9]+(-blue)/\1@NEW@\2/' \
     'version-@VER@-blue' \
     'README.md version badge'

_reg 'README.md' \
     's/(\*\*Version\*\* \| `)[0-9]+[.][0-9]+[.][0-9]+(`)/\1@NEW@\2/' \
     '\*\*Version\*\* \| `@VER@`' \
     'README.md Version table row'

# --- i18n README badges (all 10 locales carry the shields.io badge) ---------
for _lang in ar de es fr hi ja ko pt-BR ru zh-CN; do
  _reg "docs/i18n/${_lang}/README.md" \
       's/(version-)[0-9]+[.][0-9]+[.][0-9]+(-blue)/\1@NEW@\2/' \
       'version-@VER@-blue' \
       "docs/i18n/${_lang}/README.md version badge"
done
unset _lang

# --- i18n README Version table rows (only de + fr carry the metadata row) ---
_reg 'docs/i18n/de/README.md' \
     's/(\*\*Version\*\* \| `)[0-9]+[.][0-9]+[.][0-9]+(`)/\1@NEW@\2/' \
     '\*\*Version\*\* \| `@VER@`' \
     'docs/i18n/de/README.md Version table row'

_reg 'docs/i18n/fr/README.md' \
     's/(\*\*Version\*\* \| `)[0-9]+[.][0-9]+[.][0-9]+(`)/\1@NEW@\2/' \
     '\*\*Version\*\* \| `@VER@`' \
     'docs/i18n/fr/README.md Version table row'

# --- GitBook ----------------------------------------------------------------
_reg 'docs/gitbook/README.md' \
     's/(\*\*Version:\*\* )[0-9]+[.][0-9]+[.][0-9]+/\1@NEW@/' \
     '\*\*Version:\*\* @VER@' \
     'docs/gitbook/README.md Version header'

_reg 'docs/gitbook/navigation_manifest.json' \
     's/(\*\*Version:\*\* )[0-9]+[.][0-9]+[.][0-9]+/\1@NEW@/' \
     '\*\*Version:\*\* @VER@' \
     'docs/gitbook/navigation_manifest.json Version header'

_reg 'docs/gitbook/05-specification-and-roadmap.md' \
     's/(\| Version \| `)[0-9]+[.][0-9]+[.][0-9]+(`)/\1@NEW@\2/' \
     '\| Version \| `@VER@`' \
     'docs/gitbook/05-specification-and-roadmap.md Version row'

# --- Machine-readable codebase map ------------------------------------------
_reg 'docs/codebase_map.json' \
     's/("version": ")[0-9]+[.][0-9]+[.][0-9]+(")/\1@NEW@\2/' \
     '"version": "@VER@"' \
     'docs/codebase_map.json version field'
