#!/usr/bin/env bash
# seLe4n  - A Lean Microkernel
# Copyright (C) 2026  Adam Hall
# This program comes with ABSOLUTELY NO WARRANTY.
# This is free software, and you are welcome to redistribute it
# under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
# test_aarch64_cross_build.sh — WS-RR RR1: aarch64 compile coverage gate.
#
# Builds `sele4n-hal` for `aarch64-unknown-none`, the bare-metal target
# the kernel is actually deployed on.  Before RR1 no aarch64 target was
# compiled anywhere in the tree or in CI, so every `#[cfg(target_arch =
# "aarch64")]` block, every `asm!` site and all three `.S` files had zero
# compile coverage — SM10.1 would have been the first thing to compile
# them, while also being the first thing to link and boot them.
#
# ## Why a build and not a check
#
# `cargo check` stops before code generation.  It never hands an `asm!`
# template to the assembler, so it cannot see an invalid operand, an
# unencodable immediate, or an instruction the target's feature set does
# not admit — which is exactly the class of defect this gate exists to
# catch.  RR1 found four of them (`TLBI *OS` requires FEAT_TLBIOS) that
# `cargo check` reported as clean.
#
# ## Why `--features hw_target`
#
# The feature is empty by default and guards the hardware-only paths —
# the Lean calls in `timer.rs`, `trap.rs` and `smp.rs`.  A build without
# it compiles none of the code this gate exists to cover, and a later
# regression in exactly those blocks would merge with the gate green.
#
# ## Why `cd rust/`
#
# `rust/rust-toolchain.toml` pins the toolchain AND lists the cross
# target, and rustup's directory override applies it only to commands
# run from `rust/` or below.  A `--manifest-path` invocation from the
# repository root silently selects the *default* toolchain, which has
# neither — the build then fails with "can't find crate for `core`",
# which reads as a source problem and is a working-directory one.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
RUST_DIR="$PROJECT_ROOT/rust"

CROSS_TARGET="aarch64-unknown-none"
CROSS_PKG="sele4n-hal"
CROSS_FEATURES="hw_target"

echo "=== aarch64 cross-compile coverage (WS-RR RR1) ==="
echo ""

if ! command -v cargo > /dev/null 2>&1; then
    echo "::warning::aarch64 cross build SKIPPED — cargo not found in PATH"
    echo "[SKIP] cargo not found — aarch64 cross build SKIPPED"
    echo "       Install Rust via ./scripts/setup_lean_env.sh"
    exit 0
fi

cd "$RUST_DIR"

# --------------------------------------------------------------------------
# [1/4] Target availability.
#
# `rust-toolchain.toml` lists the target, so rustup installs it on first
# use.  A pre-seeded CI image or an offline environment can still be
# missing it, so try once explicitly and fail with a usable message
# rather than letting rustc report a missing `core`.
# --------------------------------------------------------------------------
echo "[1/4] Ensuring the ${CROSS_TARGET} target is installed..."
if ! rustup target list --installed 2> /dev/null | grep -qx "${CROSS_TARGET}"; then
    echo "      target not installed; adding it"
    if ! rustup target add "${CROSS_TARGET}"; then
        echo "      ✗ FAILED — could not install the ${CROSS_TARGET} target."
        echo "        It is listed in rust/rust-toolchain.toml; if this is an"
        echo "        offline runner, pre-seed the target in the image."
        exit 1
    fi
fi
echo "      ✓ ${CROSS_TARGET} available"
echo ""

# --------------------------------------------------------------------------
# [2/4] The gate itself: a real build, debug and release.
#
# Both profiles are built because inline-asm register allocation and
# constraint checking depend on the optimisation level: an `asm!` block
# that satisfies the register allocator at `-O0` can fail to at `-O2`,
# and the deployed kernel is a release build.
# --------------------------------------------------------------------------
echo "[2/4] Building ${CROSS_PKG} for ${CROSS_TARGET} (debug + release)..."
# Discard any previous run's build-script output first.  Step [3/4] below
# asserts that `boot.S`, `vectors.S` and `trap.S` reached an archive; if a
# stale archive from an earlier run survived, that assertion would pass over
# a build that assembled nothing — the exact "green gate over zero coverage"
# shape this workstream exists to eliminate, reintroduced inside the check
# meant to prevent it.  Deleting the directory also re-runs `build.rs`, so
# its source scanners fire on every invocation rather than only on a cache
# miss.  The cost is seconds: the crate has no dependencies for this target.
for profile in debug release; do
    rm -rf "target/${CROSS_TARGET}/${profile}/build/${CROSS_PKG}-"*
done
cargo build --target "${CROSS_TARGET}" -p "${CROSS_PKG}" --features "${CROSS_FEATURES}"
cargo build --release --target "${CROSS_TARGET}" -p "${CROSS_PKG}" --features "${CROSS_FEATURES}"
echo "      ✓ debug and release cross builds succeeded"
echo ""

# --------------------------------------------------------------------------
# [3/4] The three .S files really assembled.
#
# `build.rs` only assembles when `CARGO_CFG_TARGET_ARCH == "aarch64"`.
# If that gate ever regressed, the build above would still pass while
# assembling nothing at all — a green gate over zero coverage, which is
# the failure shape this whole workstream exists to eliminate.  So the
# archive is inspected rather than assumed.
# --------------------------------------------------------------------------
echo "[3/4] Verifying boot.S / vectors.S / trap.S assembled..."
# Exactly one archive can exist now, since the directory was cleared above;
# `head -1` is defensive rather than a choice between candidates.
asm_archive="$(find "target/${CROSS_TARGET}/release/build" \
    -name 'libsele4n_hal_asm.a' -print 2> /dev/null | head -1)"
if [ -z "${asm_archive}" ]; then
    echo "      ✗ FAILED — no libsele4n_hal_asm.a produced for ${CROSS_TARGET}."
    echo "        build.rs assembles src/boot.S, src/vectors.S and src/trap.S"
    echo "        only when CARGO_CFG_TARGET_ARCH == aarch64.  A missing"
    echo "        archive means the assembly step was skipped and the .S"
    echo "        files have no compile coverage."
    exit 1
fi
# `ar t` is in binutils and llvm-tools alike; fall back to a byte scan of
# the archive's member headers if neither is present, so the check
# degrades to "the members are named" rather than to "skipped".
if command -v ar > /dev/null 2>&1; then
    members="$(ar t "${asm_archive}")"
else
    members="$(strings "${asm_archive}" 2> /dev/null || true)"
fi
for obj in boot vectors trap; do
    if ! printf '%s\n' "${members}" | grep -q -- "${obj}\.o"; then
        echo "      ✗ FAILED — ${obj}.o missing from ${asm_archive}"
        echo "        Members found:"
        printf '%s\n' "${members}" | sed 's/^/          /'
        exit 1
    fi
done
echo "      ✓ all three .S sources assembled into ${asm_archive##*/}"
echo ""

# --------------------------------------------------------------------------
# [4/4] Lints, on the cross target, denied.
#
# `scripts/test_rust.sh` runs clippy on the host, where every
# `#[cfg(target_arch = "aarch64")]` block is removed before the linter
# sees it.  The project's zero-warning claim therefore excluded the
# entire hardware surface until this step existed: RR1 found two rustc
# warnings and one clippy finding living in blocks the host lane cannot
# reach.
# --------------------------------------------------------------------------
echo "[4/4] Linting ${CROSS_PKG} on ${CROSS_TARGET} (clippy -D warnings)..."
if ! rustup component list --installed 2> /dev/null | grep -q '^clippy'; then
    echo "      ✗ FAILED — clippy component not installed."
    echo "        rust-toolchain.toml lists it; install with"
    echo "        'rustup component add clippy'."
    exit 1
fi
cargo clippy --target "${CROSS_TARGET}" -p "${CROSS_PKG}" \
    --features "${CROSS_FEATURES}" -- -D warnings
echo "      ✓ clippy is clean on ${CROSS_TARGET}"
echo ""

echo "=== aarch64 cross-compile coverage: PASS ==="
