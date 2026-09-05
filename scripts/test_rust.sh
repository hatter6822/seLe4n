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
# Set by `summarise_cargo_test_log`, read by `run_cargo_step`: the number of
# tests the step skipped.  A skipped test is not a passing test, and the project
# claims zero of them, so a non-zero count fails the gate rather than merely
# annotating it.
ignored_total=0

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
    ignored_total="${ignored}"
    echo "      ${passed} passed, ${failed} failed, ${ignored} ignored" \
         "across ${binaries} test binaries"
    # An ignored test is a test that does not run — whether skipped by an
    # `#[ignore]` attribute or by an ```ignore doc-comment fence, which is not
    # even compiled and so rots silently.  Report which ones, so the failure
    # below names the offenders rather than just counting them.
    if [ "${ignored}" -ne 0 ]; then
        grep -E '\.\.\. ignored$' "$log" | sed 's/^/        /' || true
    fi
    return 0
}

run_cargo_step() {
    local step_label="$1"
    shift
    local log
    log="$(mktemp)"
    if "$@" > "$log" 2>&1; then
        ignored_total=0
        summarise_cargo_test_log "$log" || tail -5 "$log"
        # Cargo exits 0 with tests skipped, so the gate has to reject them
        # itself or the repository's zero-ignored-tests invariant is a claim
        # nothing enforces.
        if [ "${ignored_total}" -ne 0 ]; then
            echo "::error::${ignored_total} Rust test(s) were skipped; this repository requires zero"
            echo ""
            echo "      ✗ FAILED — ${ignored_total} skipped test(s); this repository requires zero."
            echo "        Remove the \`#[ignore]\` attribute, or make the"
            echo "        \`\`\`ignore doctest fence compile (\`no_run\` still"
            echo "        type-checks it; a bare \`\`\`ignore never compiles)."
            rm -f "$log"
            return 1
        fi
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

# `--features host_tools` is load-bearing in both steps below.  WS-RR
# RR1.3 gave `src/bin/rw_lock_oracle.rs` — the Tier-5 correspondence
# oracle, a `std` host tool — a `required-features` gate, so that the
# bare-metal `aarch64-unknown-none` build does not try to compile it.
# A `required-features` target is not merely skipped from the build:
# `cargo test` does not run its `#[cfg(test)]` module either, so
# without the flag here the oracle's test module silently stops running and
# the step still reports a clean pass over one fewer binary.  That is
# the same shape as a skipped test, which this script already rejects,
# and `scripts/check_aarch64_cross_target.py` pins the flag.
echo "[1/5] Building all crates (host target)..."
run_cargo_step "Build succeeded" cargo build --all --features host_tools
echo ""

echo "[2/5] Running unit tests..."
run_cargo_step "Unit tests passed" cargo test --all --features std,host_tools
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
# otherwise pass this gate while printing them.  `--all-features` matches what
# the test steps above compile: every crate declares `default = []`, so without
# it the `#[cfg(feature = "std")]` code the tests exercise — `KernelError`'s
# `Display` impl among it — is never linted at all, and the zero-warning claim
# would exclude the configuration under test.  (`--features std` cannot be used
# workspace-wide: `sele4n-hal` has no such feature and cargo rejects it.)
# ----------------------------------------------------------------------------

echo "[4/5] Checking formatting (cargo fmt --check)..."
run_cargo_step "Formatting is clean" cargo fmt --all --check
echo ""

echo "[5/5] Linting (cargo clippy --all-targets --all-features -D warnings)..."
run_cargo_step "Clippy is clean" cargo clippy --all-targets --all-features -- -D warnings
echo ""

echo "=== All Rust tests passed ==="
