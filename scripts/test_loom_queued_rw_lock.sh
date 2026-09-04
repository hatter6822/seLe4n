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
# Six of the eleven models cover `QueuedRwLock::cancel`.  They are not
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
#
# WS-LC closure audit — the double withdrawal
# ---------------------------------------------
#
# The four models above withdraw at most once per core, and that is why
# none of them saw the stall the closure audit found: the withdrawal slot
# is one word per core, so a core that withdrew, re-enqueued and withdrew
# again while its first withdrawal was unclaimed overwrote the
# publication, and the release ahead of it then stopped `now_serving` on
# a ticket nobody held.  `enqueue` now parks until the slot is empty, and
# `double_withdrawal_by_one_core_does_not_strand_the_lock` is the model;
# `pending_withdrawal_refuses_the_non_blocking_attempt` covers the
# `try_*` path, whose refusal is a consequence of the CAS rather than a
# wait.  Their decisiveness mutation, in the same discipline:
#
#   4. Keep the slot load, the comparison and the park in
#      `await_withdrawal_retired`, and turn the `while` into an `if` —
#      one observation, then proceed regardless.  Every token survives;
#      the model fails with `now_serving` one short of `next_ticket` and
#      the slot still published.  (Moving the whole wait *after*
#      `take_ticket` is NOT a relation break — the wait still precedes
#      the second `cancel`, which is the write that overwrote — and the
#      model correctly passes it.)

set -euo pipefail

REPO_ROOT="$(git -C "$(dirname "${BASH_SOURCE[0]}")/.." rev-parse --show-toplevel)"
cd "$REPO_ROOT/rust"

# A gate that cannot run reports NOT RUN (`SELE4N_SKIP_EXIT`, recorded by
# `run_gate_check`), never PASS; invoked directly by a CI job, the status
# fails the job, which is the right answer to a runner without cargo.
if ! command -v cargo >/dev/null 2>&1; then
    echo "loom: SKIP (NOT RUN) — cargo not in PATH"
    exit "${SELE4N_SKIP_EXIT:-77}"
fi

# Exhaustive means UNBOUNDED (PR #890 review).  loom's `Builder` reads
# `LOOM_MAX_PREEMPTIONS` as its preemption bound and explores every
# interleaving when it is unset; the first cut pinned it at 3, which omits
# every schedule needing four or more preemptions — and the operations under
# test have many atomic and yield points, so a two-operation model does not
# imply a three-preemption bound.  Unbounded, the eleven models take ~35 s;
# bounded at 3 they took under a second.  The gate is the unbounded run.  A
# caller may still set `LOOM_MAX_PREEMPTIONS=n` in the environment for a
# quick local pass, and that pass is not the gate — say so when quoting it.
if [ -n "${LOOM_MAX_PREEMPTIONS:-}" ]; then
    echo "loom: WARNING — LOOM_MAX_PREEMPTIONS=${LOOM_MAX_PREEMPTIONS} bounds the"
    echo "loom:           exploration; this is a quick pass, not the exhaustive gate."
else
    echo "loom: exploring ALL interleavings of queued_rw_lock (deployed lock; unbounded)..."
fi
RUSTFLAGS="--cfg loom" \
    cargo test -p sele4n-hal --lib queued_rw_lock::loom_model -- --test-threads=1

echo "loom: PASS — every explored interleaving upholds mutual exclusion,"
echo "loom:        writer-readers exclusion, reader concurrency and the"
echo "loom:        ticket-interval invariant."
