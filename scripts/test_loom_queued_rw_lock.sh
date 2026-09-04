#!/usr/bin/env bash
# SPDX-License-Identifier: GPL-3.0-or-later
#
# WS-RR RR6.20: exhaustive-interleaving gate for the deployed
# reader-writer lock.
#
# `docs/planning/SMP_RWLOCK_DEFERRED_COMPLETION_PLAN.md` §8 lists
# "`cfg(loom)` exhaustive-interleaving runs pass on op-sequences of
# length <= 4" as a D-5 acceptance gate.  Before WS-RR RR6.20 nothing
# ran: `queued_rw_lock.rs` imported `core::sync::atomic` directly, and
# loom only instruments its own atomic types, so a `loom::model` block
# around it would explore exactly one interleaving and report success.
#
# What makes this real:
#
#   * `queued_rw_lock.rs` selects `loom::sync::atomic` under `--cfg loom`
#     (and `core::sync::atomic` otherwise), so the model runs over the
#     *deployed* lock rather than a copy of it.
#   * `loom` is a `[target.'cfg(loom)'.dependencies]` entry, so no
#     ordinary build — host, test, clippy, or the bare-metal cross
#     build — resolves it at all.
#   * The models are two threads with one or two operations each, which
#     is where loom's exploration is exhaustive rather than bounded.
#
# The filter is deliberate: under `--cfg loom` the crate's *other*
# thread tests would drive loom atomics from real `std` threads, which
# loom rejects.  Only the `loom_model` module runs.
#
# WS-LC LC3.3/LC3.4 — the withdrawal models, and what makes them decisive
# ---------------------------------------------------------------------
#
# Four of the nine models cover `QueuedRwLock::cancel`.  They are not
# decorative: the *first* version of that function failed two of them,
# and the reported state was the one they are written to catch —
# `now_serving` one short of `next_ticket`, the withdrawal slot still
# published, the lock stalled with a tombstone at the head.  The cause
# was the store-buffer window between publishing a withdrawal and
# checking whether one is the head; the fix is a `SeqCst` fence on each
# side, and making the four accesses themselves `SeqCst` was tried first
# and was not enough.
#
# Decisiveness is proved by **relation-breaking** mutation, per
# CLAUDE.md: each of the three below keeps every token a presence check
# would look for and breaks only the relation, and each fails
# `mid_queue_withdrawal_is_skipped_by_the_core_ahead` and
# `withdrawal_races_pass_turn_from_both_sides`:
#
#   1. Keep the publish, and move it *after* the head check
#      (`let served_first = self.is_served(ticket);` above the store).
#   2. Keep the skip loop, and delete only the compare-exchange
#      arbitration (`slot.store(NO_WITHDRAWAL, ..); return true;`).
#   3. Keep both fence call sites, and delete the one at the top of
#      `claim_withdrawal_of`.
#
# Deleting the `cancel` call, or the loop, would of course also fail —
# and would prove nothing, because a presence check survives removal.

set -euo pipefail

REPO_ROOT="$(git -C "$(dirname "${BASH_SOURCE[0]}")/.." rev-parse --show-toplevel)"
cd "$REPO_ROOT/rust"

if ! command -v cargo >/dev/null 2>&1; then
    echo "loom: SKIP — cargo not in PATH"
    exit 0
fi

echo "loom: exploring interleavings of queued_rw_lock (deployed lock)..."
RUSTFLAGS="--cfg loom" LOOM_MAX_PREEMPTIONS="${LOOM_MAX_PREEMPTIONS:-3}" \
    cargo test -p sele4n-hal --lib queued_rw_lock::loom_model -- --test-threads=1

echo "loom: PASS — every explored interleaving upholds mutual exclusion,"
echo "loom:        writer-readers exclusion, reader concurrency and the"
echo "loom:        ticket-interval invariant."
