#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
#
# The boundary layout test: the compiled Lean's `SeLe4n.RegisterFile`
# (35 `UInt64` fields) and `FpContext` (66) place field `i` at scalar offset
# `8 · i`, where the HAL reads and writes it — executed across the language
# boundary, in both directions, by `rust/sele4n-lean-boundary`.
#
# The test links the host Lean archives Lake builds (`SeLe4n:static`, the
# kernel; `SeLe4nBoundaryProbes:static`, the test-only exports of
# `SeLe4n/Testing/BoundaryProbes.lean`) and the toolchain's `libleanshared`,
# builds objects with the toolchain's own `lean.h` at the HAL's offsets, and
# asks the compiled Lean's `word` for each; and reads objects the compiled Lean
# built back at the same offsets.  A same-size permutation of the Lean
# structure that every proof survives fails it.
#
# This lane needs both toolchains and is run from `test_tier1_build.sh`, right
# after the host static archive it reads is built.  It never skips: a missing
# `cargo` or a missing archive is a failure here, and the crate's own test
# fails naming what is missing when it is built without the archives (as the
# Lean-less `cargo test --all` of `test_rust.sh` would, which is why that step
# excludes the crate and this one runs it).
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
cd "${PROJECT_ROOT}"

if [ -f "${HOME}/.elan/env" ]; then
    # shellcheck disable=SC1091
    source "${HOME}/.elan/env"
fi
for tool in lake lean cargo; do
    if ! command -v "${tool}" >/dev/null 2>&1; then
        echo "[FAIL] ${tool} not found on PATH — the boundary layout test needs the Lean and Rust toolchains"
        exit 1
    fi
done

echo "[1/3] The host Lean archives the test links"
lake build SeLe4n:static SeLe4nBoundaryProbes:static

LAKE_LIB_DIR="${PROJECT_ROOT}/.lake/build/lib"
for archive in libseLe4n_SeLe4n.a libseLe4n_SeLe4nBoundaryProbes.a; do
    if [ ! -f "${LAKE_LIB_DIR}/${archive}" ]; then
        echo "[FAIL] ${LAKE_LIB_DIR}/${archive} was not produced"
        exit 1
    fi
done
LEAN_LIBDIR="$(lean --print-libdir)"
export SELE4N_LAKE_LIB_DIR="${LAKE_LIB_DIR}"
export SELE4N_LEAN_LIBDIR="${LEAN_LIBDIR}"

echo "[2/3] The boundary layout test (rust/sele4n-lean-boundary)"
(cd rust && cargo test -p sele4n-lean-boundary)

echo "[3/3] The test crate's lint and format"
(cd rust && cargo clippy -p sele4n-lean-boundary --all-targets -- -D warnings)
(cd rust && cargo fmt -p sele4n-lean-boundary -- --check)

echo "Boundary layout: the compiled Lean places every word of both contexts where the HAL reads it."
