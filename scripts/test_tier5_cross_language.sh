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
# A harness that cannot run reports NOT RUN — the reserved exit status
# `SELE4N_SKIP_EXIT`, which `run_gate_check` records as incomplete coverage —
# never PASS.  Exiting 0 here let `test_nightly.sh` count a run in which no
# oracle executed as a passed acceptance gate (PR #890 review).
if ! command -v lake >/dev/null 2>&1; then
    echo "tier5: SKIP (NOT RUN) — lake not in PATH"
    exit "${SELE4N_SKIP_EXIT:-77}"
fi

if ! command -v cargo >/dev/null 2>&1; then
    echo "tier5: SKIP (NOT RUN) — cargo not in PATH"
    exit "${SELE4N_SKIP_EXIT:-77}"
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
# pseudo-random sequences of length 1..16 over a **five**-letter alphabet
# across four cores, seeded by sequence index for reproducibility.
#
# WS-LC LC3.6: the fifth letter is `c`, the withdrawal.
#
# WS-LC closure audit: the op and the core are drawn from a linear
# congruential generator advanced once per op, not from an affine
# function of the position.  The previous generator took the op type as
# `(17n + 31i) % 5` and the core as `(17n + 31i) / 5 % 4`, and the two
# are arithmetically coupled: within a sequence the op type advances by
# one and the core by three per position, so a core that withdrew never
# requested again in the same trace.  Measured over the abstract spec,
# 983 sequences contained 207 effective withdrawals and **zero**
# re-acquisitions by a core that had withdrawn — the one shape the
# closure audit's fix is about, and the one that decides whether the
# Rust oracle excludes a trace.  The harness reported "0 excluded" and
# the figure meant nothing.  Decorrelated, the same budget yields ~120
# effective withdrawals and ~35 such re-acquisitions.
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
    echo "W0,W1,c1,w0,W1,w1,"                          # withdraw, retired by the release, re-enqueue

    # Pseudo-random sequences (deterministic seed via sequence index).
    local n
    for ((n=0; n<NUM_SEQUENCES-17; n++)); do
        local seq=""
        local len=$((n % 16 + 1))
        local i
        # Per-sequence seed: the index scrambled by the golden-ratio
        # multiplier, so neighbouring sequences do not share a prefix.
        local seed=$(( (n * 2654435761) % 2147483648 ))
        for ((i=0; i<len; i++)); do
            # One LCG step per op (glibc's constants, 31-bit state); the
            # op is read from the high bits and the core from the middle
            # bits, so the two selections are not functions of each other.
            seed=$(( (seed * 1103515245 + 12345) % 2147483648 ))
            local op_type=$(( (seed >> 16) % 5 ))
            local core=$(( (seed >> 8) % 4 ))
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

# WS-LC closure audit: traces a single thread cannot execute.
#
# `QueuedRwLock::enqueue` parks until the calling core's previous
# withdrawal has been retired by the core ahead of it — issuing a ticket
# over a published slot is how the deployed lock lost a withdrawal and
# stalled.  A trace that asks a core to acquire while its own withdrawal
# is still published therefore asks the Rust oracle's one thread to wait
# for a release only another thread could perform.  The Rust oracle
# reports such a trace as not sequentially executable (exit status 3)
# instead of guessing a linearisation; the Lean oracle folds the abstract
# spec, which has no notion of a slot, and prints a state.  The two
# outputs are not comparable on that trace, and the harness must neither
# call it a mismatch nor let it pass unseen: it is COUNTED, reported, and
# held under a ceiling, so a change that starts excluding many more
# traces than the withdrawal shapes account for fails loudly.
#
# The exclusion path is itself pinned by a shape that MUST be excluded:
# if the Rust oracle ever stops refusing it — say the slot wait is
# removed from `enqueue` — both oracles print the same abstract state and
# a silent pass would follow, which is the presence-check failure
# CLAUDE.md describes.  So the harness asserts the exit status.
EXCLUDED_SHAPES=(
    "W0,W1,c1,W1,"                                     # re-enqueue while the withdrawal is unclaimed
    "W0,R1,c1,R1,w0,"                                  # same for a reader
)
NOT_SEQUENTIAL_STATUS=3
# Ceiling on the excluded fraction of the generated sequences, in percent.
# Measured at 2% (20 of 1000) on the decorrelated generator below when the
# exclusion landed; the shape needs a queued core to withdraw and then
# request again before the core ahead of it moves, which bounds it well
# under this, so exceeding it means the Rust oracle is refusing something
# other than a parked issue.
EXCLUDED_CEILING_PERCENT="${TIER5_EXCLUDED_CEILING_PERCENT:-10}"

for seq in "${EXCLUDED_SHAPES[@]}"; do
    rc=0
    echo "$seq" | "$RUST_ORACLE" >/dev/null 2>&1 || rc=$?
    if [ "$rc" -ne "$NOT_SEQUENTIAL_STATUS" ]; then
        echo "tier5: FAIL — the Rust oracle must refuse '$seq' as not sequentially"
        echo "tier5:        executable (exit $NOT_SEQUENTIAL_STATUS); it exited $rc"
        exit 1
    fi
done

# Compare oracles on each sequence.  Use temp files to track mismatches
# and exclusions across the subshell boundary (the while-loop body runs
# in a subshell under the pipe).
MISMATCH_LOG="$(mktemp -t tier5-mismatches.XXXXXX)"
EXCLUDED_LOG="$(mktemp -t tier5-excluded.XXXXXX)"
trap 'rm -f "$MISMATCH_LOG" "$EXCLUDED_LOG"' EXIT

generate_sequences | while IFS= read -r seq; do
    lean_out=$(echo "$seq" | "$LEAN_ORACLE" 2>/dev/null | tail -1)
    rust_rc=0
    rust_out=$(echo "$seq" | "$RUST_ORACLE" 2>/dev/null) || rust_rc=$?
    if [ "$rust_rc" -eq "$NOT_SEQUENTIAL_STATUS" ]; then
        echo "$seq" >> "$EXCLUDED_LOG"
        continue
    fi
    if [ "$rust_rc" -ne 0 ] || [ "$lean_out" != "$rust_out" ]; then
        {
            echo "MISMATCH on sequence: $seq"
            echo "  lean: $lean_out"
            echo "  rust: $rust_out (exit $rust_rc)"
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

excluded=$(wc -l < "$EXCLUDED_LOG" 2>/dev/null || echo 0)
# Compared by cross-multiplication, never through an integer percentage: the
# percentage rounds DOWN, so 101..109 excluded of 1000 would read as 10% and
# pass a 10% ceiling they exceed (PR #890 review).
if [ $(( excluded * 100 )) -gt $(( EXCLUDED_CEILING_PERCENT * NUM_SEQUENCES )) ]; then
    echo "tier5: FAIL — $excluded of $NUM_SEQUENCES sequences were excluded as not"
    echo "tier5:        sequentially executable, above the ${EXCLUDED_CEILING_PERCENT}%"
    echo "tier5:        ceiling ($(( EXCLUDED_CEILING_PERCENT * NUM_SEQUENCES / 100 )) of"
    echo "tier5:        $NUM_SEQUENCES); first few:"
    head -10 "$EXCLUDED_LOG"
    exit 1
fi

echo "tier5: completed ($NUM_SEQUENCES sequences; $excluded excluded as not"
echo "tier5:            sequentially executable — a core re-acquiring while its"
echo "tier5:            own withdrawal is unclaimed, which parks on hardware)"
echo "tier5: PASS — no mismatches between Lean and Rust oracles"
