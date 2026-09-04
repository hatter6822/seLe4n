# Plan — Eliminate every panic and hang in the WS-SM multi-core work

> **Status**: LANDED — the SM2.E remediation shipped the queued MCS-RW
> lock (`rust/sele4n-hal/src/queued_rw_lock.rs`) and closed both
> documented failure classes (see the SM2.E entry in `CHANGELOG.md`).
> The only remaining `panic!` sites in `queued_rw_lock.rs` are the
> deliberate panic-injection tests (guard-Drop release coverage), and no
> "known flakiness under load" note survives in `rust/` or the plans.

## Table of contents

1. [Context](#1-context)
2. [Definition of done](#2-definition-of-done)
3. [Audit summary — what's broken vs what's fail-closed-by-design](#3-audit-summary--whats-broken-vs-whats-fail-closed-by-design)
4. [Workstream layout](#4-workstream-layout)
5. [Stream A — Land PR #790's queued_rw_lock fixes](#5-stream-a--land-pr-790s-queued_rw_lock-fixes)
6. [Stream B — Isolate and close the residual `release_write` panic](#6-stream-b--isolate-and-close-the-residual-release_write-panic)
7. [Stream C — Structural defenses + multi-core audit closure](#7-stream-c--structural-defenses--multi-core-audit-closure)
8. [Stream D — Verification + acceptance gate](#8-stream-d--verification--acceptance-gate)
9. [Files modified — full list](#9-files-modified--full-list)
10. [Risk register + rollback paths](#10-risk-register--rollback-paths)
11. [Out of scope](#11-out-of-scope)

---

## 1. Context

seLe4n is a verified microkernel. WS-SM (SM0..SM2.D landed at v0.31.9
plus SM2.E in flight as PR #790) introduces the entire multi-core
substrate: PSCI bring-up, per-CPU TPIDR_EL1, per-core MMU/GIC/timer
init, DTB cmdline, inter-PE TLBI broadcast, SGIs, per-core kprintln,
verified `TicketLock` + `RwLock` + queued MCS-RW lock, FFI bridge.

Two failure classes remain visible today, both confined to
`rust/sele4n-hal/src/queued_rw_lock.rs` (the SM2.C-defer D-5 queued
variant — the MCS-style FIFO-preserving reader-writer lock):

* **HANGS** — documented in CLAUDE.md and confirmed by PR #790 commit
  `98afa66d`: `queued_rw_lock::cross_thread_tests` deadlocks ~10 % per
  iteration under heavy host-side load. Root cause: a state-machine
  gap in the per-slot `parked` machine (no way to distinguish a
  just-reset slot from a waiting slot) that PR #790 closes via the
  four-state machine (NOT_IN_QUEUE / WAITING_READER /
  WAITING_WRITER / ADMITTED).
* **PANICS** — surfaced once PR #790 closes the hangs: a ~35 % rate
  of `release_write`'s `debug_assert!((_prev & WRITER_BIT) != 0)`
  firing in the new `cross_thread_state_invariant_no_writer_with_readers`
  test (PR #790 commit `c0dffac8` explicitly leaves this **unresolved**:
  "the exact trace has not yet been isolated").

A direct audit of every other multi-core surface (catalogued in §3
below) found zero residual broken sites. Every other `panic!` /
`loop {}` / `assert!` is either an intentional fail-closed halt
(unrecoverable hardware state, malformed FFI handle, unreachable
under documented post-boot invariants) or a defensive informative
`debug_assert!` on a property already proven structurally.

The goal of this plan: make `queued_rw_lock.rs` panic-free and
hang-free under unlimited stress, with every fix mathematically
justified against the SM2.A operational memory model and the
existing SM2.C wf-preservation theorems.

## 2. Definition of done

`v1.0.0-rc` is reached when **all** of these hold:

* `cargo test --workspace --release` passes 5 consecutive runs.
* `cross_thread_state_invariant_no_writer_with_readers` passes
  1000/1000 iterations (instead of the default 100). Zero panics,
  zero hangs.
* All 13 tests in `queued_rw_lock::cross_thread_tests` pass
  100/100 consecutive cargo invocations under
  `cargo test --workspace -- --test-threads=$(nproc)`.
* `RUSTFLAGS="-Z sanitizer=thread" cargo test --workspace
  --target x86_64-unknown-linux-gnu` passes with zero TSAN warnings
  (or warnings explicitly justified in test docstrings).
* Tier 0+1+2+3 green; Tier 4 SMP nightly green or SKIP-clean.
* `lockPrimitives` aggregator's NoDup-checked identifiers all
  resolve; `LockPrimitives.lean`'s count witness still holds (or
  grows by exactly the number of new substantive theorems Stream B
  introduces, with the corresponding `_count` re-pinned).  The
  witness read **22** when this plan was written and reads **25**
  at v0.34.49: WS-RR RR6 added the deployed queued lock's
  refinement and its FIFO-admission payoff, and split the R-10 row
  that had advertised a safety alias as writer liveness.
* CLAUDE.md flips the "occasionally deadlock under heavy host-side
  load" note for queued_rw_lock to "closed at vX.Y.Z".

## 3. Audit summary — what's broken vs what's fail-closed-by-design

A direct review of every `loop {}`, `panic!`, `assert!`, and
`debug_assert!` in the SMP surface classified each occurrence into
one of three groups.

### 3.1 Intentional final halts (NOT bugs — keep)

These park the calling core in the safest possible state with DAIF
masked, when continued execution would be unsafe. Each is documented
in its own docstring + audit-pass history. Listed for the
implementer so they aren't accidentally "fixed":

* `smp.rs` — invalid PSCI context_id (validator rejected).
* `smp.rs` — timer init failure on a secondary (fatal for that
  core's scheduler; primary + siblings remain alive).
* `smp.rs` — post-`lean_secondary_kernel_main` idle fallback
  (Lean returns unexpectedly).
* `trap.rs` — `handle_serror` (`-> !`; ARM ARM D1.13 says
  SErrors are unrecoverable).
* `psci.rs` — `system_off` non-conforming-firmware defensive
  spin (DEN0022D §5.1.9).
* `psci.rs` — `system_reset` non-conforming-firmware defensive
  spin (DEN0022D §5.1.10).
* `gic.rs` — `self_check_distributor` mismatch on aarch64
  non-test (broken interrupt routing).

### 3.2 Fail-closed FFI panics (NOT bugs — keep)

Unreachable from typed Lean callers; production-callable only via
the FFI ABI, where they correctly fail loudly.

* `lock_bridge.rs` × 15 — `panic!` on `decode_*_handle => None`.
  Lean-side smart constructors `mkTicketLockHandle` /
  `mkRwLockHandle` carry a structural `raw.toNat < pool_size`
  proof, making the panic unreachable from Lean.
* `gic.rs::send_sgi*` × 3 — `assert!(intid < MAX_SGI_INTID)`. Lean
  routes through `SgiKind.toIntid : Fin 16`, making the bound
  structural.
* `per_cpu.rs::per_cpu_slot_addr` / `per_cpu_stats.rs::*_count_for`
  — `assert!` on out-of-range `core_id`. Unreachable under
  post-`check_per_cpu_invariants` invariants.
* `Concurrency/Runtime.lean::currentCoreId:106` — `panic!` on
  out-of-range FFI return. Defensive against TPIDR_EL1 corruption;
  unreachable under post-boot invariants.

### 3.3 Genuinely broken (FIX — this is the plan)

* **`queued_rw_lock.rs`** — every other broken site we found, plus
  the residual `release_write` panic PR #790 leaves open.

## 4. Workstream layout

Four streams. **A → B → C** must run in order; **D** runs alongside
each.

* **Stream A** — Cherry-pick PR #790's `queued_rw_lock.rs` fixes
  into branch `claude/fix-multicore-issues-oSSxN`. Closes the
  documented hangs. Quick verification (§5.6). **Dependencies:
  none.**
* **Stream B** — Isolate the residual writer-readers exclusion
  panic via a compile-gated diagnostic ring buffer, then apply the
  correct fix (one of three candidates triangulated by the trace).
  **Dependencies: Stream A landed.**
* **Stream C** — Add build-script scanners, runtime invariant
  probes, and Lean surface anchors so the corrected protocol
  cannot silently regress. Update CLAUDE.md / SPEC / GitBook /
  CHANGELOG. **Dependencies: Stream B landed.**
* **Stream D** — Per-tier acceptance gates run on every push. The
  1000-iteration stress and TSAN runs gate the final cut.

## 5. Stream A — Land PR #790's queued_rw_lock fixes

PR #790 (`claude/review-lock-primitives-docs-umtsc`, three commits)
delivers a 10-change `queued_rw_lock.rs` rewrite. Cherry-pick the
file-level diff into the working branch, then re-land the
accompanying Lean + documentation deltas so the spec and the code
stay lockstep.

### 5.1 The ten protocol changes — what each closes, why each is sound

The ten protocol changes PR #790 landed, each closing a documented failure
class in `rust/sele4n-hal/src/queued_rw_lock.rs`:

| Change | What it closes |
|--------|----------------|
| Group A1 | four-state mode-encoded `parked` machine |
| Group A2 | stale-self tail detection |
| Group A3 | order of operations on enqueue |
| Group A4 | NONE-path self-admit spin with CAS-claim ordering |
| Group A5 | walk-past stale slots with `MAX_WAITERS` step bound |
| Group A6 | signal-on-every-release in `release_read` |
| Group A7 | cascade CAS-loop with WRITER_BIT precondition |
| Group A8 | NOT_IN_QUEUE vs ADMITTED disposition |
| Group A9 | writer admission via `state.CAS(0, WRITER_BIT)`, NEVER `fetch_or` |
| Group A10 | self-link `debug_assert!` defenses |

### 5.2 Cherry-pick mechanics

The PR's 16 changed files split cleanly into "code" (correctness)
and "documentation" (lockstep with code). Land all 16 in one PR
on `claude/fix-multicore-issues-oSSxN`. Commit ordering:

* Commit A.1: code changes — `rust/sele4n-hal/src/queued_rw_lock.rs`
  only. After this commit, the hangs are closed; the residual
  panic is now reproducible.
* Commit A.2: Lean documentation hub —
  `SeLe4n/Kernel/Concurrency/Locks/Refinement.lean` (new) +
  `SeLe4n/Platform/Staged.lean` +
  `scripts/staged_module_allowlist.txt` +
  `scripts/test_tier3_invariant_surface.sh`. Pulls in the
  refinement-methodology hub.
* Commit A.3: MemoryModel + LockPrimitives —
  `SeLe4n/Kernel/Concurrency/MemoryModel.lean` (ARM ARM citation
  map expansion), `SeLe4n/Kernel/Concurrency/LockPrimitives.lean`
  (decision-rationale block + hardware-discipline limits).
* Commit A.4: spec + GitBook + project documentation —
  `docs/spec/SELE4N_SPEC.md` §10, `docs/gitbook/16-verified-lock-primitives.md`
  (new), `docs/gitbook/{SUMMARY.md, navigation_manifest.json,
  README.md}`, `docs/REGISTERED_DEBT.md`,
  `docs/codebase_map.json`, `CHANGELOG.md`, `README.md`.

### 5.3 Acceptance after Stream A

After commit A.1, run the following to confirm the hangs are
closed and the residual panic is the only remaining failure mode:

```bash
# Smoke test — fast sanity.
./scripts/test_smoke.sh

# Targeted stress — 100 consecutive cargo runs of queued_rw_lock
# cross-thread tests.  Expectations:
#   PASS: hang rate = 0%.
#   PARTIAL: panic in cross_thread_state_invariant_no_writer_with_readers
#            at ~35% (this is Stream B's input).
for i in $(seq 1 100); do
    timeout 60 cargo test --release \
        --package sele4n-hal queued_rw_lock::cross_thread_tests \
        2>&1 | tail -5
done | tee /tmp/stream-a-stress.log
grep -c "test result: ok"  /tmp/stream-a-stress.log
grep -c "panicked at"      /tmp/stream-a-stress.log
grep -c "test running over" /tmp/stream-a-stress.log  # must be 0
```

If hang rate > 0%, Stream A is not complete — re-audit the
cherry-pick.

## 6. Stream B — Isolate and close the residual `release_write` panic

This is the substantive new engineering. PR #790 explicitly defers
this. Phase 1 of Stream B builds a focused diagnostic; Phase 2
analyses the captured trace; Phase 3 applies the correct fix; Phase
4 mathematically justifies it; Phase 5 stresses to zero failures.

### 6.1 Failure shape

`release_write`'s `debug_assert!((_prev & WRITER_BIT) != 0)` fires
in `cross_thread_state_invariant_no_writer_with_readers` at ~35 %
per 100-iteration run. Translated: the WRITER_BIT was cleared by
SOMETHING between this writer's admit and its release.

The ONLY code path that clears WRITER_BIT is `release_write`'s
own `state.fetch_and(READER_MASK, AcqRel)`. So:

* Either ANOTHER writer's `release_write` cleared it (two writers
  held simultaneously — mutex violation), or
* The signal-walk undo path
  `state.CAS(WRITER_BIT, 0)` cleared it (we set the bit on behalf
  of a writer, then undid because parked CAS failed, but failed
  to leave the bit set under the writer that DID get admitted).

Both shapes are testable.

### 6.2–6.6 Hypothesis triage, diagnostics and fix (closed)

Stream B isolated the residual `release_write` panic and closed it.  The
hypothesis triage, the diagnostic ring buffer and the trace analysis were
apparatus for that investigation, not reusable design: the outcome is in
[`CHANGELOG.md`](../../CHANGELOG.md) at the SM2.E cuts, and the protocol the
fix settled on is what `queued_rw_lock.rs` implements today.

### 6.7 Proof obligation

Whichever fix(es) land, append the following proof obligations to
`SeLe4n/Kernel/Concurrency/Locks/RwLockRefinement.lean` (the F-02
aggregator). The Lean spec must remain a sound refinement of the
post-fix Rust impl.

1. **Reachable-state set invariant**: every state value reachable
   from `state = 0` via the Rust impl's operations is in
   `{0} ∪ {1..=READER_MASK} ∪ {WRITER_BIT}`. Express as a Lean
   predicate over `RwLockConcrete.state : UInt64` and prove by
   induction on the operation sequence.

   ```lean
   def QueuedRwLockReachableState (s : UInt64) : Prop :=
     s = 0
     ∨ (1 ≤ s.toNat ∧ s.toNat ≤ READER_MASK.toNat)
     ∨ s = WRITER_BIT

   theorem queued_rw_lock_reachable_state_invariant
     (ops : List ConcreteOp) (s : UInt64)
     (h : s = (foldl applyConcrete .unheld ops).state) :
       QueuedRwLockReachableState s := by
     induction ops with
     | nil => left; rfl
     | cons op rest ih => ...

*Landed. What each cut changed, and what its review rounds found, is in
[`CHANGELOG.md`](../../CHANGELOG.md) under the versions above.*

### 6.8 Stress regression

After the fix lands, run the headline test 1000 times **plus**
under ThreadSanitizer:

```bash
# Headline stress — 1000 iterations.
ITER_OVERRIDE=1000 \
    cargo test --release --package sele4n-hal \
    cross_thread_state_invariant_no_writer_with_readers \
    -- --nocapture --test-threads=$(nproc)

# Repeat 5 times.  Expectation: zero panics, zero hangs.
for i in 1 2 3 4 5; do
    ITER_OVERRIDE=1000 cargo test --release \
        --package sele4n-hal queued_rw_lock::cross_thread_tests \
        2>&1 | tail -10
done

# TSAN run.  Expectation: zero data-race reports.
RUSTFLAGS="-Z sanitizer=thread" \
    cargo test --workspace \
    --target x86_64-unknown-linux-gnu queued_rw_lock 2>&1 \
    | tee /tmp/tsan.log
grep -c "WARNING: ThreadSanitizer" /tmp/tsan.log  # must be 0
```

Acceptance: every run passes; TSAN silent (or each warning is
explicitly justified in a docstring as a sound usage of relaxed
ordering).

## 7. Stream C — Structural defenses + multi-core audit closure

Lock down the protocol so the corrected shape cannot silently
regress.

### 7.1 Build-script regression scanners

Add ONE new scanner (`scan_queued_rw_lock_protocol_intact`) to
`rust/sele4n-hal/build.rs` covering three contractual patterns.
The scanner follows the pattern of the existing 11 scanners (e.g.,
`scan_gic_rs_send_sgi_emits_dsb_ish` at SM1.F.8).

*(Planning note: this section originally proposed three separate
scanners — `_tristate_intact`, `_stale_self_intact`,
`_writer_admit_via_cas_intact`.  Consolidated to one scanner with
three internal checks for clarity and to match the as-built
implementation.)*

#### 7.1.1 Four-state parked machine pattern

Grep `queued_rw_lock.rs` for the literal presence of:

* `pub const PARKED_NOT_IN_QUEUE: u8`
* `pub const PARKED_WAITING_READER: u8`
* `pub const PARKED_WAITING_WRITER: u8`
* `pub const PARKED_ADMITTED: u8`

Fail with diagnostic "WS-SM SM2.E protocol regression: four-state
parked machine removed" if any pattern is missing.  The four-state
form (with WAITING_READER vs WAITING_WRITER distinction) is
essential to close the stale-mode-read race; a regression to
three states (collapsing READER+WRITER) re-opens the residual
writer-readers exclusion panic.

#### 7.1.2 `scan_queued_rw_lock_stale_self_intact`

Grep for `if raw_prev_tail == core_id` occurring **at least twice**
in the file (one occurrence per acquire path: `acquire_read` and
`acquire_write`).

Fail if count != 2.

#### 7.1.3 `scan_queued_rw_lock_writer_admit_via_cas_intact`

Grep for the FORBIDDEN pattern
`self.state.fetch_or(WRITER_BIT` inside `signal_next_waiter`'s body
(extract the function body via simple brace counting).

Fail if the pattern is found anywhere in the function. The CAS form
`state.compare_exchange(0, WRITER_BIT` MUST be the only writer-bit
setter in signal.

#### 7.1.4 (Stream B-conditional) — apply-fix scanners

If §6.6 applied F1, add a scanner pinning the revert-via-CAS shape:

* Grep for the FORBIDDEN pattern `slot.parked.store(PARKED_WAITING`
  inside `acquire_read` and `acquire_write`'s NONE-path self-admit
  spin (excluding the legitimate publication store BEFORE the
  predecessor link).

If §6.6 applied F2, add a scanner pinning the assert-undo-success
shape:

* Grep for `debug_assert!(undo_result.is_ok()` inside the writer
  undo path of `signal_next_waiter` and `cascade_admit_readers`.

### 7.2 Runtime invariant probes

Add a `#[cfg(debug_assertions)]` post-RMW check in every state-
mutating method on `QueuedRwLock`. The probe asserts:

```rust
#[cfg(debug_assertions)]
fn check_reachable_state(s: u64) {
    let reader_count = s & READER_MASK;
    let writer_held  = (s & WRITER_BIT) != 0;
    debug_assert!(
        !(writer_held && reader_count > 0),
        "WS-SM SM2.E invariant violated: writer+readers coexist (state=0x{:x})",
        s,
    );
}
```

Invocation: after every `self.state.compare_exchange(...)`,
`self.state.fetch_add(...)`, `self.state.fetch_sub(...)`,
`self.state.fetch_and(...)` site, call
`check_reachable_state(returned_value)`.

Release builds optimise this out (no runtime cost in production).
Debug builds catch the invariant violation at the EXACT point of
corruption — the source of every WRITER_BIT-clearing surprise in
`release_write`.

### 7.3 Lean surface anchors

Add to `scripts/test_tier3_invariant_surface.sh`:

* `#check @SeLe4n.Kernel.Concurrency.Locks.refinementMethodologyMarker`
* `#check @SeLe4n.Kernel.Concurrency.Locks.refinementMethodology_covers_sm2_inventory`
* `#check @SeLe4n.Kernel.Concurrency.Locks.rust_ticketLock_refines_lean`
* `#check @SeLe4n.Kernel.Concurrency.Locks.rust_rwLock_refines_lean`
* (Stream B-conditional) `#check @queued_rw_lock_reachable_state_invariant`
* (Stream B-conditional) `#check @queued_rw_lock_parked_admit_unique`

Each `#check` ensures a downstream rename / removal of the named
theorem fails the build immediately, not at some far-future Lean
elaboration.

### 7.4 `lockPrimitives` aggregator updates

If Stream B adds new substantive theorems (e.g., the two new
obligation theorems in §6.7), append them to
`SeLe4n/Kernel/Concurrency/LockPrimitives.lean`'s `lockPrimitives :
List LockPrimitiveTheorem` under the appropriate category:

* `queued_rw_lock_reachable_state_invariant` → `.rwLock` category.
* `queued_rw_lock_parked_admit_unique` → `.rwLock` category.

Update the `_count` size witness:
`lockPrimitives.length = 22 + N` where `N` is the number of new
theorems. The corresponding Rust constant
`LOCK_THEOREM_COUNT` (in `rust/sele4n-hal/src/lock_bridge.rs`) bumps
in lockstep — `scripts/check_lock_ffi_symmetry.sh` enforces the
agreement.

### 7.5 Documentation lockstep

Files to update with the post-fix protocol:

* `CLAUDE.md` — Active workstream section's SM2.D-defer note: flip
  the "occasionally deadlock under heavy host-side load" line to
  "closed at vX.Y.Z; see Stream B closure in WS-SM SM2.E".
* `docs/spec/SELE4N_SPEC.md` §10.4 (RwLock spec) — add a "Hardware
  discipline limits" entry describing the CAS-revert discipline if
  F1 landed, or the assert-undo discipline if F2 landed.
* `docs/gitbook/16-verified-lock-primitives.md` — same edit
  mirrored.
* `docs/REGISTERED_DEBT.md` — append the Stream B closure entry
  under WS-SM SM2.E with the version it landed at.
* `docs/codebase_map.json` — regenerate.
* `CHANGELOG.md` — append a `v0.31.10 — WS-SM SM2.E closure +
  queued_rw_lock panic-free guarantee` entry.

### 7.6 Audit closure — other multi-core surfaces

Document explicitly that the §3.1 / §3.2 categories above are
*intentional* (not bugs). Add a short docstring to each of the
following functions pinning the design intent (so a future audit
does not flag them as findings to remediate):

* `smp.rs::rust_secondary_main` post-validator halt loop:
  "**WS-SM SM1.C audit-pass-2**: intentional final halt; documented
  in CLAUDE.md §3.1."
* `smp.rs::rust_secondary_main` post-timer-init halt loop: same.
* `smp.rs::rust_secondary_main` idle fallback: same.
* `trap.rs::handle_serror`: "**ARM ARM D1.13**: SErrors are
  unrecoverable; intentional `-> !` halt."
* `psci.rs::system_off` / `system_reset` spin-park: pre-existing
  docstrings cover this; verify present.
* `gic.rs::self_check_distributor`: pre-existing docstring;
  verify present.
* `lock_bridge.rs::*::panic!` sites (15 occurrences): each
  already has a "Panics if ..." in its docstring; verify present
  and accurate.

No code changes — documentation reinforcement only.

## 8. Stream D — Verification + acceptance gate

Run on every push to `claude/fix-multicore-issues-oSSxN`. Final
landing requires a green run of all tiers AND the headline stress.

### 8.1 Tier-by-tier gate

```bash
# Tier 0 — hygiene
./scripts/test_tier0_hygiene.sh
# Includes: check_lock_ffi_symmetry.sh (Lean ↔ Rust FFI symmetry),
#           check_website_links.sh, check_version_sync.sh,
#           check_no_session_urls.sh.

# Tier 1 — build
./scripts/test_fast.sh
# Lean: every module elaborates, zero new sorry/axiom.
# Rust: zero clippy warnings under -D warnings.

# Tier 2 — negative + runtime
./scripts/test_smoke.sh
# Includes all Lean SmpFoundationsSuite, MemoryModelSuite,
# TicketLockSuite, LockBridgeSuite, SmpSurfaceAnchors,
# RwLockSuite, RwLockDeferredSuite runtime assertions.

# Tier 3 — invariant surface
./scripts/test_full.sh
# Every #check in test_tier3_invariant_surface.sh resolves.

# Tier 4 — SMP nightly (gated)
NIGHTLY_ENABLE_EXPERIMENTAL=1 ./scripts/test_nightly.sh
# Includes QEMU -smp 4 bringup, -smp 2 minimal, SGI round-trip.
# SKIP-clean when QEMU absent.
```

### 8.2 Headline stress — `cross_thread_state_invariant_no_writer_with_readers`

```bash
# Run 1000 iterations × 5 invocations.
for i in 1 2 3 4 5; do
    echo "=== Invocation $i ==="
    ITER_OVERRIDE=1000 \
        cargo test --release --package sele4n-hal \
        cross_thread_state_invariant_no_writer_with_readers \
        -- --nocapture --test-threads=$(nproc) 2>&1 \
        | tail -5
done

# Expected output for each invocation:
#   test result: ok. 1 passed; 0 failed; 0 ignored
#
# Any panic, any hang, any timeout: FAIL.
```

### 8.3 Full `queued_rw_lock` cross-thread suite — 100 consecutive invocations

```bash
for i in $(seq 1 100); do
    timeout 120 cargo test --release --package sele4n-hal \
        queued_rw_lock::cross_thread_tests 2>&1 \
        | grep "test result" | tail -1
done | tee /tmp/full-stress.log

# Acceptance: every line says "13 passed; 0 failed; 0 ignored"
grep -v "13 passed; 0 failed; 0 ignored" /tmp/full-stress.log
# Expected output: empty.
```

### 8.4 ThreadSanitizer

```bash
RUSTFLAGS="-Z sanitizer=thread" \
    cargo +nightly test --workspace \
    --target x86_64-unknown-linux-gnu 2>&1 \
    | tee /tmp/tsan-full.log

# Acceptance: zero WARNING lines.
grep -c "WARNING: ThreadSanitizer" /tmp/tsan-full.log
# Expected: 0.

# If any warning fires, the docstring of the affected lock method
# MUST explicitly justify the relaxed ordering, OR the ordering
# must be promoted to AcqRel.
```

### 8.5 Verification matrix

Cross-reference each acceptance criterion against the stream that
delivers it:

| Criterion | Delivered by | Verified by |
|-----------|--------------|-------------|
| Hangs closed | Stream A (Group A1, A2, A3, A4, A5, A8) | §8.3 |
| Cascade WRITER_BIT race closed | Stream A (Group A7) | §7.2 (runtime probe) + §8.2 |
| Writer admit via CAS | Stream A (Group A9) | §7.1.3 (scanner) |
| `cross_thread_state_invariant_*` passes | Stream B | §8.2 |
| Memory model invariants preserved | Stream B (§6.7 proof) | Tier 3 + `lockPrimitives_count` re-pin |
| No silent regression | Stream C (scanners + probes + anchors) | Tier 0 + Tier 3 |
| Documentation lockstep | Stream C (§7.5) | manual review |
| TSAN clean | Streams A+B combined | §8.4 |

## 9. Files modified — full list

### 9.1 Correctness-critical (Stream A + B)

* `rust/sele4n-hal/src/queued_rw_lock.rs` — Stream A's ten protocol
  fixes + Stream B's residual-panic fix + Stream C's runtime probes
  + (feature-gated) diagnostic ring buffer.
* `rust/sele4n-hal/build.rs` — three new build-script scanners
  (§7.1) plus any Stream-B-conditional scanner (§7.1.4).
* `rust/sele4n-hal/Cargo.toml` — declare the `lock_trace` feature
  (off by default).

### 9.2 Lean spec (Stream A + B)

* `SeLe4n/Kernel/Concurrency/MemoryModel.lean` — ARM ARM citation
  map expansion (Stream A).
* `SeLe4n/Kernel/Concurrency/Locks/Refinement.lean` (new, 294 LoC)
  — methodology hub (Stream A).
* `SeLe4n/Kernel/Concurrency/Locks/RwLockRefinement.lean` —
  Stream B's two new proof obligations (§6.7).
* `SeLe4n/Kernel/Concurrency/LockPrimitives.lean` —
  decision-rationale block (Stream A) + new aggregator entries
  (Stream B).
* `SeLe4n/Platform/Staged.lean` — register `Refinement.lean`
  (Stream A).

### 9.3 Test infrastructure + tier wiring

* `scripts/staged_module_allowlist.txt` — append `Refinement.lean`.
* `scripts/test_tier3_invariant_surface.sh` — new `#check`s
  (§7.3).
* `scripts/check_lock_ffi_symmetry.sh` — implicit update if
  `LOCK_THEOREM_COUNT` changes.

### 9.4 Documentation (Stream A + Stream C closure)

* `docs/spec/SELE4N_SPEC.md` §10.
* `docs/gitbook/16-verified-lock-primitives.md` (new).
* `docs/gitbook/SUMMARY.md`, `docs/gitbook/navigation_manifest.json`,
  `docs/gitbook/README.md`.
* `docs/REGISTERED_DEBT.md`.
* `docs/codebase_map.json` (regenerate).
* `CHANGELOG.md`.
* `README.md`.
* `CLAUDE.md` — flip the SM2.D-defer "occasionally deadlock" note.

### 9.5 Audit-closure docstring touch-ups (Stream C §7.6)

* `rust/sele4n-hal/src/smp.rs` — three docstring additions.
* `rust/sele4n-hal/src/trap.rs` — one docstring addition.

## 10. Risk register + rollback paths

### 10.1 Risk: Stream B fix re-introduces a different race

**Indicator**: TSAN warning post-fix, or 1000-iteration stress
shows < 100 % pass rate.

**Mitigation**: the trace diagnostic from §6.3 is left in the
codebase (feature-gated). If a regression surfaces, re-enable the
feature and capture another trace.

**Rollback**: revert the Stream B commit (preserving Stream A's
hang fixes). The codebase is back to the documented "~35 % panic
under stress on host; moot on hardware with real WFE" state of
PR #790's third commit. CLAUDE.md is updated to reflect.

### 10.2 Risk: build-script scanner false positive

**Indicator**: `cargo build` fails with a scanner diagnostic on a
legitimate refactor.

**Mitigation**: each scanner's pattern is a literal string — refactors
that preserve the SEMANTIC contract but rename a variable can trip
it. Resolution: update the scanner's expected literal in the same
commit as the rename.

**Rollback**: temporarily comment out the scanner with a TODO
linking to the resolution PR; never silently weaken a scanner's
pattern to match inferior code (per CLAUDE.md's
implement-the-improvement rule).

### 10.3 Risk: 1000-iteration stress too slow for CI

**Indicator**: stress run exceeds CI's 60-minute timeout.

**Mitigation**: the 1000-iteration variant is gated behind
`ITER_OVERRIDE=1000`. Default CI runs the 100-iteration variant.
The 1000-iteration variant runs nightly via
`NIGHTLY_ENABLE_EXPERIMENTAL=1`.

**Rollback**: none required — the default test budget is preserved.

### 10.4 Risk: Stream B diagnostic discovers H3 (unenumerated)

**Indicator**: the captured trace does not match H1 or H2 patterns.

**Mitigation**: this IS what the diagnostic is for. The
implementer captures the trace, derives the minimal reproducer,
proposes a fix candidate, and runs it through the same stress.
Budget: 2-3 days of iteration on hard problems. If the bug
proves intractable, see §10.5.

### 10.5 Risk: Stream B fix proves intractable within budget

**Indicator**: after multiple fix attempts, the stress test still
shows a non-zero panic rate, AND TSAN doesn't surface a clear
ordering-bug root cause.

**Mitigation**: the conservative fallback is to mark the
`queued_rw_lock.rs` variant as "host-test-only" / "SM3-prerequisite"
and exclude its cross-thread tests from the default test run:

```rust
#[cfg(all(test, feature = "queued_rw_lock_stress"))]
mod cross_thread_tests { ... }
```

The simple `rw_lock.rs` static-pool variant remains the production
path; the queued variant is fully verified at SM3 when its first
consumer (per-object locks) materialises. CLAUDE.md flips the
"closed" note to "deferred to SM3".

This fallback **is acceptable** because:
* No production kernel path consumes `queued_rw_lock.rs` at v1.0.0;
* The hardware target (RPi5 with real WFE) does not reproduce the
  host-side flake;
* The non-queued `rw_lock.rs` is panic-free and hang-free under
  the same stress.

The fallback is NOT preferred — Stream B's first-resort goal is
the full fix. The fallback exists only to avoid blocking v1.0.0 on
an intractable race.

## 11. Out of scope

* SM3+ per-object locks (the verified primitives' first consumer);
  this plan delivers the 100 %-clean SM2 substrate.
* QEMU SMP integration test (SM1.H.5 SGI round-trip) wiring Lean-
  side handler registration — requires SM5 per-core scheduler state.
* The documented FIFO divergence in `rw_lock.rs` vs the Lean spec
  (`rwLock_fifo_admission_temporal`) — formally captured in F-02's
  divergence note; the queued variant is the FIFO-preserving choice
  for kernel paths that need strict FIFO at SM3+.
* PSCI conduit parameterisation (HVC vs SMC) — RPi5 is HVC-only;
  post-1.0 work.
* Multi-cluster TLBI / cache-broadcast tuning — RPi5 is
  single-cluster; the OS variants are pre-positioned but unused at
  v1.0.0.
* Reachability-closure form of the refinement F-theorems — the
  per-step preservation form is sufficient for every SM3+
  consumer; full reachability closure is a post-1.0 hardening
  candidate per `Locks/Refinement.lean`'s methodology doc.
