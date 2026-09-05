#!/usr/bin/env bash
# SPDX-License-Identifier: GPL-3.0-or-later
#
# WS-RR RR6.21: miri gate for the deployed reader-writer lock.
#
# `docs/planning/SMP_RWLOCK_DEFERRED_COMPLETION_PLAN.md` §8 lists
# "`cargo +nightly miri test -p sele4n-hal --lib queued_rw_lock` passes
# with `-Zmiri-strict-provenance`" as a D-5 acceptance gate.  No job ran
# it before WS-RR RR6.21.
#
# What miri adds over the cross-thread stress tests: it interprets every
# atomic access, so it reports data races, invalid provenance and
# undefined behaviour that a native run can execute past.  The stress
# tests scale themselves down under `cfg(miri)` (`STRESS_ITER`), because
# miri's value is in the first few interleavings, not the ten-thousandth.
#
# Nightly-only: `miri` is a nightly component.  The script installs it
# on demand and, when neither is available, reports NOT RUN — the reserved
# exit status `SELE4N_SKIP_EXIT`, which `test_nightly.sh` records through
# `run_gate_check` as incomplete coverage rather than as a pass (PR #890
# review: exiting 0 let the nightly log "miri gate executed" over a run in
# which no miri test ran).  A developer without a nightly toolchain is not
# blocked; the report simply says the gate did not run.

set -euo pipefail

REPO_ROOT="$(git -C "$(dirname "${BASH_SOURCE[0]}")/.." rev-parse --show-toplevel)"
cd "$REPO_ROOT/rust"

if ! command -v rustup >/dev/null 2>&1; then
    echo "miri: SKIP (NOT RUN) — rustup not in PATH"
    exit "${SELE4N_SKIP_EXIT:-77}"
fi

if ! rustup toolchain list | grep -q '^nightly'; then
    echo "miri: installing the nightly toolchain..."
    rustup toolchain install nightly --profile minimal --component miri >/dev/null 2>&1 || {
        echo "miri: SKIP (NOT RUN) — nightly toolchain unavailable"
        exit "${SELE4N_SKIP_EXIT:-77}"
    }
fi

if ! cargo +nightly miri --version >/dev/null 2>&1; then
    rustup component add miri --toolchain nightly >/dev/null 2>&1 || {
        echo "miri: SKIP (NOT RUN) — miri component unavailable"
        exit "${SELE4N_SKIP_EXIT:-77}"
    }
fi

echo "miri: interpreting queued_rw_lock under strict provenance..."
MIRIFLAGS="-Zmiri-strict-provenance ${MIRIFLAGS:-}" \
    cargo +nightly miri test -p sele4n-hal --lib queued_rw_lock -- --test-threads=1

echo "miri: PASS — no undefined behaviour, data race or provenance"
echo "miri:        violation in the deployed lock."
