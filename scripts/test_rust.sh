#!/usr/bin/env bash
# test_rust.sh — Rust syscall wrapper build + test + conformance
#
# Q8-D: Validates that all three sele4n Rust crates build and pass tests.
# Integrated into test_smoke.sh as a Tier 2 gate.
#
# R8-C (I-M03): Explicit skip warnings + proper error propagation from cargo.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
RUST_DIR="$PROJECT_ROOT/rust"

echo "=== Rust Syscall Wrappers (Q8) ==="
echo ""

# R8-C (I-M03): Explicit cargo availability check with CI warning annotation.
# AE6-C (T-F17): Log the skip explicitly so CI dashboards surface it.
if ! command -v cargo &> /dev/null; then
    echo "::warning::Rust tests SKIPPED — cargo not found in PATH"
    echo "[SKIP] cargo not found — Rust tests SKIPPED"
    echo "       Install Rust via: curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh"
    echo ""
    echo "       To ensure Rust tests run in CI, add a rustup install step"
    echo "       to .github/workflows/lean_action_ci.yml"
    # Propagate skip status to CI output variables when available.
    if [ -n "${GITHUB_OUTPUT:-}" ]; then
        echo "RUST_TESTS_SKIPPED=true" >> "$GITHUB_OUTPUT"
    fi
    exit 0
fi

# Check if rust directory exists
if [ ! -d "$RUST_DIR" ]; then
    echo "[FAIL] rust/ directory not found"
    exit 1
fi

cd "$RUST_DIR"

# R8-C (I-M03): Capture cargo output to temp file so we can show tail on success
# and full output on failure. Exit codes are checked directly, not through pipe.

# On success only the tail of the log is shown, so for a `cargo test` step the
# visible summary is whichever test binary happened to run last — for the
# workspace run that is a single-doctest crate, which reads as "1 test passed"
# for a run of over a thousand.  Aggregate the per-binary `test result:` lines
# so the reported count is the run's real coverage; a step with no such lines
# (build, fmt, clippy) keeps the plain tail.
summarise_cargo_test_log() {
    local log="$1"
    local passed failed ignored binaries
    binaries="$(grep -c '^test result:' "$log" || true)"
    # Spelled as an `if` rather than `[ … ] && return 1`: under `set -e` the
    # latter's exit status depends on which branch was taken, which is exactly
    # the kind of thing that works until it doesn't.
    if [ "${binaries}" -eq 0 ]; then
        return 1
    fi
    passed="$(awk '/^test result:/ {s += $4} END {print s + 0}' "$log")"
    failed="$(awk '/^test result:/ {s += $6} END {print s + 0}' "$log")"
    ignored="$(awk '/^test result:/ {s += $8} END {print s + 0}' "$log")"
    echo "      ${passed} passed, ${failed} failed, ${ignored} ignored" \
         "across ${binaries} test binaries"
    # An ignored test is a test that does not run — whether skipped by an
    # `#[ignore]` attribute or by an ```ignore doc-comment fence, which is not
    # even compiled and so rots silently.  The project's standing claim is that
    # it has none of either, so surface any rather than letting them hide
    # inside an otherwise-green summary.
    if [ "${ignored}" -ne 0 ]; then
        echo "::warning::${ignored} Rust test(s) were skipped (#[ignore] attribute or \`\`\`ignore doctest fence)"
    fi
    return 0
}

run_cargo_step() {
    local step_label="$1"
    shift
    local log
    log="$(mktemp)"
    if "$@" > "$log" 2>&1; then
        summarise_cargo_test_log "$log" || tail -5 "$log"
        echo "      ✓ ${step_label}"
        rm -f "$log"
        return 0
    else
        local rc=$?
        cat "$log"
        echo ""
        echo "      ✗ ${step_label} FAILED (exit code ${rc})"
        rm -f "$log"
        return "$rc"
    fi
}

echo "[1/5] Building all crates (host target)..."
run_cargo_step "Build succeeded" cargo build --all
echo ""

echo "[2/5] Running unit tests..."
run_cargo_step "Unit tests passed" cargo test --all --features std
echo ""

echo "[3/5] Running conformance tests (RUST-XVAL-001..014)..."
run_cargo_step "Conformance tests passed" cargo test -p sele4n-abi --features std --test conformance
echo ""

# ----------------------------------------------------------------------------
# Lint + format gates.
#
# `setup_lean_env.sh` has always installed the `clippy` and `rustfmt`
# components, and `rust-toolchain.toml` has always listed them — but nothing
# ever *ran* them, so "zero clippy warnings" and a consistent format were
# claims no gate enforced.  Formatting drifted to a 6 187-line diff across 53
# files before anyone noticed, and the clippy claim was true only because the
# toolchain pin had frozen clippy three years behind stable.  Both are gated
# here so neither can drift again.
#
# `--all-targets` covers tests and benches, not just the lib targets: a lint
# that fires only in test code is still a lint.  `-D warnings` makes clippy
# exit non-zero, since it reports findings as warnings by default and would
# otherwise pass this gate while printing them.
# ----------------------------------------------------------------------------

echo "[4/5] Checking formatting (cargo fmt --check)..."
run_cargo_step "Formatting is clean" cargo fmt --all --check
echo ""

echo "[5/5] Linting (cargo clippy --all-targets -D warnings)..."
run_cargo_step "Clippy is clean" cargo clippy --all-targets -- -D warnings
echo ""

echo "=== All Rust tests passed ==="
