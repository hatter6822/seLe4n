#!/usr/bin/env bash
# SPDX-License-Identifier: GPL-3.0-or-later
#
# WS-SM SM2.C-defer D-6: Tier-5 cross-language correspondence harness driver.
#
# See docs/planning/SMP_RWLOCK_DEFERRED_COMPLETION_PLAN.md §5.6.
#
# For each generated op-sequence, feeds the same input to:
#   1. `lake exe rw_lock_oracle` (Lean oracle — folds applyOp over the
#      abstract spec, prints canonical post-state)
#   2. `cargo run --bin rw_lock_oracle` (Rust oracle — folds the bit-
#      packed state evolution, prints the same canonical post-state)
#
# Diffs the outputs; any mismatch is a test failure (and a regression
# signal that the abstract spec and the impl have diverged).
#
# No FFI link-discipline change (closes audit H-3): both binaries are
# independent processes communicating via stdin/stdout text only.

set -euo pipefail

REPO_ROOT="$(git -C "$(dirname "${BASH_SOURCE[0]}")/.." rev-parse --show-toplevel)"
cd "$REPO_ROOT"

# Default: 1000 op-sequences per gate run (configurable via env).
NUM_SEQUENCES="${TIER5_NUM_SEQUENCES:-1000}"

# Source the Lean toolchain so `lake` is on PATH.
if [ -f "$HOME/.elan/env" ]; then
    # shellcheck disable=SC1091
    source "$HOME/.elan/env"
fi

# Confirm both oracles are available.
if ! command -v lake >/dev/null 2>&1; then
    echo "tier5: SKIP — lake not in PATH"
    exit 0
fi

if ! command -v cargo >/dev/null 2>&1; then
    echo "tier5: SKIP — cargo not in PATH"
    exit 0
fi

echo "tier5: building Lean oracle..."
lake build rw_lock_oracle 2>&1 | tail -3

echo "tier5: building Rust oracle..."
# `--features host_tools` is required, not decorative: WS-RR RR1.3 gave
# the oracle a `required-features` gate so the bare-metal aarch64 build
# does not try to compile a `std` binary for `aarch64-unknown-none`.
# Without the flag cargo reports "target `rw_lock_oracle` … requires the
# features: `host_tools`" and builds nothing.
cargo build -p sele4n-hal --bin rw_lock_oracle \
    --manifest-path rust/sele4n-hal/Cargo.toml \
    --features host_tools \
    --release 2>&1 | tail -3

LEAN_ORACLE="$REPO_ROOT/.lake/build/bin/rw_lock_oracle"
RUST_ORACLE="$REPO_ROOT/rust/target/release/rw_lock_oracle"

if [ ! -x "$LEAN_ORACLE" ]; then
    echo "tier5: FAIL — Lean oracle binary missing at $LEAN_ORACLE"
    exit 1
fi
if [ ! -x "$RUST_ORACLE" ]; then
    echo "tier5: FAIL — Rust oracle binary missing at $RUST_ORACLE"
    exit 1
fi

# Deterministic op-sequence generator.  Generates `$NUM_SEQUENCES`
# pseudo-random sequences of length 0..16 over a **five**-letter alphabet
# across four cores, seeded by sequence index for reproducibility.
#
# WS-LC LC3.6: the fifth letter is `c`, the withdrawal.  Both the op
# selector and the core selector move with the alphabet — `seed % 5` and
# `seed / 5 % 4` — because leaving the divisor at 4 would select cores
# from a different stride than the ops and silently narrow the space the
# generator claims to cover.
#
# Plus structured edge cases (empty trace, single ops, mutex,
# reader-batching, sequential writer chain, and the withdrawal shapes) at
# the start.
generate_sequences() {
    # Edge cases (17 fixed sequences).
    echo ""                                            # empty
    echo "R0,"                                         # single reader
    echo "W0,"                                         # single writer
    echo "R0,r0,"                                      # acquire/release reader
    echo "W0,w0,"                                      # acquire/release writer
    echo "R0,R1,R2,R3,"                                # all readers acquire
    echo "R0,R1,R2,R3,r0,r1,r2,r3,"                    # all readers acquire/release
    echo "W0,R1,r1,w0,"                                # writer with queued reader
    echo "W0,W1,W2,W3,"                                # writer queue
    echo "R0,R1,W2,r0,r1,w2,"                          # mixed mode
    # WS-LC LC3.6 — the withdrawal shapes.
    echo "c0,"                                         # withdraw with no request
    echo "W0,c0,"                                      # a holder withdraws: no-op
    echo "W0,W1,c1,w0,"                                # mid-queue, skipped by the release
    echo "W0,W1,W2,c1,c2,w0,"                          # a run of tombstones
    echo "W0,W1,W2,c1,w0,w2,"                          # a live waiter behind a tombstone
    echo "W0,R1,R2,c1,w0,r2,"                          # a withdrawn reader in a batch
    echo "W0,W1,c1,W1,w0,w1,"                          # withdraw then re-enqueue

    # Pseudo-random sequences (deterministic seed via sequence index).
    local n
    for ((n=0; n<NUM_SEQUENCES-17; n++)); do
        local seq=""
        local len=$((n % 16 + 1))
        local i
        # Use $n + $i as a deterministic seed for the op selection.
        for ((i=0; i<len; i++)); do
            local seed=$((n * 17 + i * 31))
            local op_type=$((seed % 5))
            local core=$((seed / 5 % 4))
            case "$op_type" in
                0) seq="${seq}R${core}," ;;
                1) seq="${seq}r${core}," ;;
                2) seq="${seq}W${core}," ;;
                3) seq="${seq}w${core}," ;;
                4) seq="${seq}c${core}," ;;
            esac
        done
        echo "$seq"
    done
}

# Compare oracles on each sequence.  Use a temp file to track mismatches
# across the subshell boundary (the while-loop body runs in a subshell
# under the pipe).
MISMATCH_LOG="$(mktemp -t tier5-mismatches.XXXXXX)"
trap 'rm -f "$MISMATCH_LOG"' EXIT

generate_sequences | while IFS= read -r seq; do
    lean_out=$(echo "$seq" | "$LEAN_ORACLE" 2>/dev/null | tail -1)
    rust_out=$(echo "$seq" | "$RUST_ORACLE" 2>/dev/null)
    if [ "$lean_out" != "$rust_out" ]; then
        {
            echo "MISMATCH on sequence: $seq"
            echo "  lean: $lean_out"
            echo "  rust: $rust_out"
        } >> "$MISMATCH_LOG"
    fi
done

mismatches=$(wc -l < "$MISMATCH_LOG" 2>/dev/null || echo 0)
if [ "$mismatches" -gt 0 ]; then
    echo "tier5: FAIL — mismatches found:"
    head -30 "$MISMATCH_LOG"
    echo "tier5: total mismatch lines: $mismatches (across $NUM_SEQUENCES sequences)"
    exit 1
fi

echo "tier5: completed ($NUM_SEQUENCES sequences)"
echo "tier5: PASS — no mismatches between Lean and Rust oracles"
