# Plan — Eliminate every panic and hang in the WS-SM multi-core work

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
  iteration under heavy host-side load. Root cause: a tristate gap in
  the per-slot `parked` machine that PR #790 closes.
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
  resolve; `LockPrimitives.lean`'s 22-theorem count witness still
  holds (or grows by exactly the number of new substantive theorems
  Stream B introduces, with the corresponding `_count` re-pinned).
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

* `smp.rs:543` — invalid PSCI context_id (validator rejected).
* `smp.rs:617` — timer init failure on a secondary (fatal for that
  core's scheduler; primary + siblings remain alive).
* `smp.rs:674` — post-`lean_secondary_kernel_main` idle fallback
  (Lean returns unexpectedly).
* `trap.rs:467` — `handle_serror` (`-> !`; ARM ARM D1.13 says
  SErrors are unrecoverable).
* `psci.rs:526` — `system_off` non-conforming-firmware defensive
  spin (DEN0022D §5.1.9).
* `psci.rs:578` — `system_reset` non-conforming-firmware defensive
  spin (DEN0022D §5.1.10).
* `gic.rs:478` — `self_check_distributor` mismatch on aarch64
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

Group these into three semantic categories. Each entry below names
the change, identifies the failure mode it closes, and points at
the SM2.A invariant it preserves.

#### Group A1 — tristate `parked` machine

Replace `parked: AtomicBool` with `parked: AtomicU8` carrying one
of three documented values:

```rust
pub const PARKED_NOT_IN_QUEUE: u8 = 0; // slot reset, owner mid-enqueue
pub const PARKED_WAITING:      u8 = 1; // owner published, eligible
pub const PARKED_ADMITTED:     u8 = 2; // terminal; owner is holder
```

* **Closes**: cascade-vs-signal ghost-`+1` race where a 2-state
  `bool` cannot distinguish a just-reset slot from a waiting slot,
  so cascade/signal CAS WAITING→ADMITTED admits both real waiters
  and reset slots, producing accumulating ghost state.
* **Soundness**: every parked transition observed by an admitter
  is `WAITING → ADMITTED`. Reset transitions are owner-only and
  Relaxed-ordered before the WAITING publish. The CAS direction
  makes the admission unique per (slot, iteration).
* **Test pin**: `parked_tristate_constants_distinct` (new) asserts
  the three constants are pairwise distinct.

#### Group A2 — stale-self tail detection

In both `acquire_read` and `acquire_write`, after
`let raw_prev_tail = self.tail.swap(core_id, AcqRel);`, add:

```rust
let prev_tail = if raw_prev_tail == core_id {
    NONE_SENTINEL
} else {
    raw_prev_tail
};
```

* **Closes**: the self-link deadlock. Cascade does not update
  `tail`. When all cascade-admitted readers release, the last
  release's `signal_next_waiter` walks toward tail and tries to
  CAS-clear it; if the owner's re-enqueue races ahead, it observes
  the stale tail = own core_id, then sets `slot[me].next.store(me)`,
  creating a self-link that the park loop never exits.
* **Soundness**: only the calling core could have set tail to its
  own id (one slot per core). Treating it as
  `NONE_SENTINEL` means "the queue is effectively empty from my
  perspective" — the prior iteration's queue position is already
  consumed by the cascade chain.

#### Group A3 — order of operations on enqueue

Change the chained-enqueue path to store WAITING BEFORE linking
the predecessor:

```rust
slot.parked.store(PARKED_WAITING, Release);                 // step 2a
self.slots[prev_tail as usize].next.store(core_id, Release); // step 2b
```

* **Closes**: the publication-window race where the predecessor's
  signal observes `slot[prev].next.store(me, Release)` via an
  `Acquire`-load and then CAS-claims `slot[me].parked`. With the
  reversed order, signal could see the link before our WAITING
  store landed; the CAS fails on NOT_IN_QUEUE; signal walks past;
  we are orphaned.
* **Soundness**: the publication chain
  `slot[prev].next.store(me, Release) →
   signal's next.load(Acquire) →
   slot[me].parked.load(Acquire)`
  forms a transitive happens-before per ARM ARM B2.3.7. The
  WAITING store before the link store ensures the
  happens-before edge sees a publish-eligible parked value.

#### Group A4 — NONE-path self-admit spin with CAS-claim ordering

In `acquire_read` and `acquire_write`'s NONE-path, when the initial
`try_admit_as_*` fails (state already contended), spin in a
self-admit loop that CAS-claims parked before mutating state:

```rust
// Already past `try_admit_as_*` (which returned false).
slot.parked.store(PARKED_WAITING, Release);
loop {
    if slot.parked.load(Acquire) == PARKED_ADMITTED {
        // Some other admitter beat us; their state-update is in.
        // For readers: still cascade-admit our successors.
        self.cascade_admit_readers(core_id);  // reader only
        return;
    }
    if slot.parked.compare_exchange(
        PARKED_WAITING, PARKED_ADMITTED, AcqRel, Acquire
    ).is_ok() {
        // We claimed the slot transition; now do the state update.
        // For reader: CAS-loop reader admission with WRITER_BIT check.
        // For writer: state.CAS(0, WRITER_BIT).
        // If state update FAILS, revert parked to WAITING and continue.
        // (See §6.5 hypothesis H1 — the revert is the candidate
        //  remaining-panic root cause; Stream B fixes it.)
    }
    crate::cpu::wfe_bounded(crate::cpu::WFE_DEFAULT_TIMEOUT_TICKS);
}
```

* **Closes**: NONE-path orphan. Without this loop, a NONE-path
  acquirer whose `try_admit_as_*` fails has no predecessor to
  signal it; it would block forever.
* **CAS-claim before state update**: ensures exactly one path
  admits. A concurrent signal targeting this slot via a stale
  chain link would either lose the CAS (sees PARKED_ADMITTED
  from our claim) or win it (sees PARKED_WAITING, advances), but
  never both increment state.
* **Soundness**: state update happens under a CAS-claimed parked,
  giving exclusive admit rights for this iteration.

#### Group A5 — walk-past stale slots with `MAX_WAITERS` step bound

In `signal_next_waiter`, replace the original "find the one
successor and signal it" with a bounded walk:

```rust
let mut current = releaser_core_id;
for _walk_step in 0..MAX_WAITERS {
    let next = self.slots[current as usize].next.load(Acquire);
    // ... case analysis on (next == NONE_SENTINEL) and tail CAS ...
    // ... case analysis on next_mode (READ vs WRITE) ...
    // ... CAS-claim parked; on Ok continue (reader) or return
    //     (writer); on Err(NOT_IN_QUEUE) undo state and return;
    //     on Err(ADMITTED) walk past (set current = next).
}
debug_assert!(false, "signal_next_waiter: walk exceeded MAX_WAITERS");
```

Symmetric bound in `cascade_admit_readers`.

* **Closes**: chain stalls. A writer chained behind a cascade-admitted
  reader needed some other release's signal walk to traverse through
  that reader and find the writer. The walk-past-stale lets every
  release process the chain forward to the next live waiter (or to
  tail cleanup).
* **`MAX_WAITERS` step bound**: defends against any future
  regression that re-introduces a self-link or longer cycle. A
  well-formed chain has at most `MAX_WAITERS` distinct slots
  (one per core) — surpassing this bound is a logic error.
* **Soundness**: bound is structural in `MAX_WAITERS`, which is
  pinned by compile-time `const _: () = assert!(MAX_WAITERS == 4)`.

#### Group A6 — signal-on-every-release in `release_read`

Change `release_read`:

```rust
let prev = self.state.fetch_sub(1, AcqRel);
debug_assert!((prev & WRITER_BIT) == 0, "release_read with writer bit");
// PRE: signal only when prev_readers == 1.  POST: always signal.
self.signal_next_waiter(core_id);
crate::cpu::sev();
```

* **Closes**: dangling tail (a non-last release leaves tail pointing
  at us; a future enqueuer chains behind us; our next iteration's
  reset clears our `next`, orphaning them) and chain stall (a
  writer chained behind cascade-admitted readers stalls).
* **Soundness**: `signal_next_waiter` is idempotent-safe — it walks
  the chain and only admits slots in `PARKED_WAITING`; ADMITTED
  slots are walked past; NOT_IN_QUEUE returns. Calling it on
  every release adds at most O(MAX_WAITERS) work per release,
  which is structural.

#### Group A7 — cascade CAS-loop with WRITER_BIT precondition

In `cascade_admit_readers`, replace `state.fetch_add(1, AcqRel)`
with a CAS loop:

```rust
loop {
    let cur = self.state.load(Acquire);
    if (cur & WRITER_BIT) != 0 { return; }
    let reader_count = cur & READER_MASK;
    if reader_count >= READER_MASK { return; } // saturation guard
    if self.state.compare_exchange(
        cur, cur + 1, AcqRel, Acquire
    ).is_ok() { break; }
    core::hint::spin_loop();
}
// Then attempt parked CAS WAITING → ADMITTED.
// On Err: undo via fetch_sub(1, AcqRel); on Ok: continue.
```

* **Closes**:
  - (a) reader-during-writer admission (cascade's `fetch_add` did
    NOT check WRITER_BIT, so a writer admitted between cascade's
    pre-check and `fetch_add` produces state =
    `WRITER_BIT | reader_bits` — direct mutex violation).
  - (b) WRITER_BIT underflow on undo (cascade's `fetch_add`
    succeeded, then all readers released, then a NONE-path writer
    admitted (state = WRITER_BIT), then cascade's parked CAS
    failed, then undo `fetch_sub(1)` decremented WRITER_BIT —
    underflowing into `0x7FFF...` — corrupting both bit fields).
* **Soundness**: the CAS-loop's WRITER_BIT-clear precondition makes
  the admission atomic under writer-clear. The undo `fetch_sub(1)`
  is safe because state currently contains our +1 contribution; any
  concurrent writer's `state.CAS(0, WRITER_BIT)` failed (state != 0).

#### Group A8 — NOT_IN_QUEUE vs ADMITTED disposition

In `signal_next_waiter`'s admission walk, on parked CAS failure
distinguish the two errors:

```rust
match next_slot.parked.compare_exchange(
    PARKED_WAITING, PARKED_ADMITTED, AcqRel, Acquire,
) {
    Ok(_)  => { /* admitted; continue (reader) or return (writer) */ }
    Err(observed) => {
        // Undo state (reader fetch_sub, or writer state.CAS(WRITER_BIT, 0))
        if observed == PARKED_NOT_IN_QUEUE {
            // Stale chain link from a prior iteration.  Slot owner
            // is mid-reset; the real iter-K+1 predecessor's release
            // will admit them.  RETURN (do not walk past).
            return;
        }
        // observed == PARKED_ADMITTED: another path already admitted.
        // Walk past.
        current = next;
    }
}
```

* **Closes**: the orphan-waiter hang. Pre-fix code walked past
  regardless of the parked observed value, allowing `tail.CAS(_,
  NONE_SENTINEL)` to clear a tail that still had a waiting waiter
  downstream — orphaning them. PR #790 commit `c0dffac8` benchmarks
  this fix at 10% → 0% hang rate.
* **Soundness**: NOT_IN_QUEUE means the slot's owner is between
  `reset()` (Relaxed-stores NOT_IN_QUEUE) and `parked.store(WAITING,
  Release)`. The chain link `slot[Z].next = us` is from a previous
  iteration; the real iter-K+1 enqueue published a new
  `slot[realPrev].next.store(us)` after `parked.store(WAITING)`,
  so the real predecessor's release will signal us correctly.

#### Group A9 — writer admission via `state.CAS(0, WRITER_BIT)`, NEVER `fetch_or`

In `signal_next_waiter`'s writer-mode branch, use
`state.CAS(0, WRITER_BIT)` instead of
`state.fetch_or(WRITER_BIT, ...)`.

```rust
let writer_state_set = self.state.compare_exchange(
    0, WRITER_BIT, AcqRel, Acquire,
).is_ok();
if !writer_state_set {
    // Reader bits set; writer cannot be admitted now.  Return
    // without walking past — the writer stays parked in the chain,
    // a future signal (when state reaches 0) admits them.
    return;
}
```

* **Closes**: writer-readers coexistence. `fetch_or(WRITER_BIT)`
  unconditionally sets the bit even when reader bits are set,
  producing `WRITER_BIT | reader_bits` — direct mutex violation.
* **Soundness**: CAS(0, WRITER_BIT) succeeds only when state is
  exactly 0 — a witness of "no holders, no readers". The lock
  invariant is preserved.

#### Group A10 — self-link `debug_assert!` defenses

In both `cascade_admit_readers` and `signal_next_waiter`:

```rust
debug_assert!(next != current,
    "signal_next_waiter: self-referential next pointer at slot {}",
    current);
if next == current { return; }
```

* **Closes**: future regression detection. Combined with A2
  (stale-self tail detection), self-links are unreachable. The
  assertion surfaces any future regression that breaks the invariant
  at test time rather than silently looping.

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
  README.md}`, `docs/WORKSTREAM_HISTORY.md`,
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

### 6.2 Hypotheses

Concretely enumerate the candidate root causes the audit can construct
from the existing protocol after the Group A1..A10 fixes have landed.
Stream B's diagnostic must rule out two, leaving the third — or
identify a fourth not enumerated here.

#### Hypothesis H1 — NONE-path self-admit spin's parked-revert race

In `acquire_write`'s NONE-path self-admit spin (per Group A4), the
order is:

```text
spin {
  if parked == ADMITTED → return.
  CAS-claim parked WAITING → ADMITTED.
  if claimed:
    state.CAS(0, WRITER_BIT).
    if state-CAS failed: parked.store(WAITING).  ← race here
}
```

The `parked.store(WAITING)` on the revert is a STORE, not a CAS. A
concurrent signal-walk arriving via a stale chain link could:

1. Observe `parked == ADMITTED` (during the brief window between our
   CAS-claim and the state-CAS-revert).
2. Skip the parked-CAS (already ADMITTED), increment state for us
   (treating us as an admitted reader), and continue the walk.
3. Then our `parked.store(WAITING)` clobbers our own ADMITTED back
   to WAITING, but signal already credited us with a reader_count
   increment — and the next admit path treats us as a fresh
   waiter, double-admitting.

Net: two state updates for a single slot — eventual writer-readers
coexistence at some downstream admission.

**Fix candidate F1**: replace the revert STORE with a CAS:

```rust
let revert = slot.parked.compare_exchange(
    PARKED_ADMITTED, PARKED_WAITING, AcqRel, Acquire);
match revert {
    Ok(_)  => {} // CAS succeeded; signal hadn't yet observed our ADMITTED.
    Err(PARKED_NOT_IN_QUEUE) => unreachable!(),
    Err(PARKED_WAITING) => {
        // Another path already reverted us; retry the spin.
    }
    // Err(PARKED_ADMITTED) can't happen — we're CASing AWAY from ADMITTED.
}
// In both Ok and Err(PARKED_WAITING), spin again.
```

But — see §6.5 — F1 may itself create a subtler asymmetry between
reader and writer NONE-paths. Validate against the trace before
committing.

#### Hypothesis H2 — signal-walk writer undo silent failure

In `signal_next_waiter`'s writer branch (per Group A8), on parked
CAS failure, the undo is:

```rust
let _ = self.state.compare_exchange(
    WRITER_BIT, 0, AcqRel, Acquire);
```

The `let _ =` silently discards the failure. If the CAS fails (state
isn't exactly WRITER_BIT — e.g., reader bits set by some other
concurrent admit), the writer bit stays set without a corresponding
holder. The next writer admitted via a different path then holds
atop a phantom writer; both writers' `release_write` calls then race
on the bit, and one of them sees `_prev & WRITER_BIT == 0`.

**Fix candidate F2**: assert the undo succeeded (panic on failure)
via `debug_assert!`, AND re-derive the correct state-machine for
the undo:

```rust
let undo = self.state.compare_exchange(
    WRITER_BIT, 0, AcqRel, Acquire);
match undo {
    Ok(_) => {} // Expected.
    Err(observed) => {
        // CAN this happen?  Between our state.CAS(0, WRITER_BIT) success
        // and our parked.CAS failure, what mutations could land?
        //   - Another release_write: impossible (it would only fire on
        //     a writer holding, but the only writer is the one we just
        //     admitted via state.CAS; their parked is mid-admit).
        //   - A reader admit: impossible (try_admit_as_reader checks
        //     WRITER_BIT and returns false).
        //   - Another signal walk: would observe state != 0 and not
        //     touch WRITER_BIT.
        // So undo must succeed.  If it doesn't, the protocol is broken
        // — surface immediately.
        debug_assert!(false,
            "writer undo failed: state was 0x{:x}, expected WRITER_BIT", observed);
    }
}
```

#### Hypothesis H3 — unenumerated path

The audit may have missed an interaction. The diagnostic ring buffer
(§6.3) captures every state-RMW + parked transition; if the trace
shows a WRITER_BIT-clearing event not consistent with H1 or H2, the
implementer identifies the new shape and constructs the corresponding
fix.

### 6.3 Diagnostic ring buffer — design

Add a compile-gated diagnostic to `queued_rw_lock.rs`:

```rust
#[cfg(feature = "lock_trace")]
mod trace {
    use core::sync::atomic::{AtomicU32, AtomicU64, Ordering};

    /// Ring buffer size. 4096 events × 8B = 32 KiB.  Production
    /// builds (no `lock_trace` feature) link this out entirely.
    const RING_SIZE: usize = 4096;

    /// Packed event: 8 bytes.
    /// bits 60..63 (4 bits): core_id (0..3)
    /// bits 56..59 (4 bits): op_tag (see OP_* below)
    /// bits 32..55 (24 bits): state_before low 24 bits
    /// bits  8..31 (24 bits): state_after  low 24 bits
    /// bits  4..7  (4 bits): parked_before
    /// bits  0..3  (4 bits): parked_after
    pub const OP_ACQUIRE_READ_ENTER:     u8 = 0;
    pub const OP_ACQUIRE_WRITE_ENTER:    u8 = 1;
    pub const OP_TAIL_SWAP:              u8 = 2;
    pub const OP_TRY_ADMIT_READER:       u8 = 3;
    pub const OP_TRY_ADMIT_WRITER:       u8 = 4;
    pub const OP_NONE_SELF_ADMIT_CLAIM:  u8 = 5;
    pub const OP_NONE_SELF_ADMIT_STATE:  u8 = 6;
    pub const OP_NONE_SELF_ADMIT_REVERT: u8 = 7;
    pub const OP_CASCADE_STATE_CAS:      u8 = 8;
    pub const OP_CASCADE_PARKED_CAS:     u8 = 9;
    pub const OP_CASCADE_UNDO:           u8 = 10;
    pub const OP_SIGNAL_STATE_CAS:       u8 = 11;
    pub const OP_SIGNAL_PARKED_CAS:      u8 = 12;
    pub const OP_SIGNAL_UNDO:            u8 = 13;
    pub const OP_RELEASE_READ:           u8 = 14;
    pub const OP_RELEASE_WRITE:          u8 = 15;

    static RING: [AtomicU64; RING_SIZE] =
        [const { AtomicU64::new(0) }; RING_SIZE];
    static HEAD: AtomicU32 = AtomicU32::new(0);

    #[inline]
    pub fn record(core_id: u8, op_tag: u8,
                  state_before: u64, state_after: u64,
                  parked_before: u8, parked_after: u8) {
        let packed: u64 =
            ((core_id as u64 & 0xF) << 60)
          | ((op_tag  as u64 & 0xF) << 56)
          | ((state_before & 0xFF_FFFF) << 32)
          | ((state_after  & 0xFF_FFFF) << 8)
          | ((parked_before as u64 & 0xF) << 4)
          | ((parked_after  as u64 & 0xF));
        let idx = (HEAD.fetch_add(1, Ordering::Relaxed) as usize) % RING_SIZE;
        RING[idx].store(packed, Ordering::Relaxed);
    }

    /// Dump the last N events to stderr.  Called from the panic
    /// hook on `release_write`'s debug_assert failure.
    pub fn dump_last(n: usize) {
        // ... pretty-print with op_tag → name mapping ...
    }
}

#[cfg(not(feature = "lock_trace"))]
mod trace {
    pub fn record(_core_id: u8, _op_tag: u8,
                  _state_before: u64, _state_after: u64,
                  _parked_before: u8, _parked_after: u8) {}
    pub fn dump_last(_n: usize) {}
}
```

Instrument every state-RMW and parked-transition site with a
`trace::record(...)` call. The trace cost in production builds is
zero (the function body is empty and gets DCEd by LLVM).

### 6.4 Diagnostic test variant

Add a new test `cross_thread_state_invariant_no_writer_with_readers_traced`
gated on `#[cfg(feature = "lock_trace")]`. Same shape as the
existing test, but on `debug_assert` failure (caught via
`std::panic::set_hook`), the hook calls `trace::dump_last(200)`
to stderr BEFORE the standard panic propagates.

Run:

```bash
cargo test --release --features lock_trace \
    cross_thread_state_invariant_no_writer_with_readers_traced \
    -- --nocapture --test-threads=1 \
    --include-ignored 2>&1 | tee /tmp/lock-trace.log

# Repeat until at least 3 failures captured.  The ~35% rate means
# 3-5 runs.
```

### 6.5 Trace analysis — triangulation

From each captured trace, extract:

1. **The panicking writer's admit path**: backwards from the
   `OP_RELEASE_WRITE` event with `state_before` lacking WRITER_BIT,
   find the matching admit event for that core_id. One of:
   `OP_TRY_ADMIT_WRITER` (Ok), `OP_NONE_SELF_ADMIT_STATE` (Ok), or
   `OP_SIGNAL_STATE_CAS` (Ok).
2. **The WRITER_BIT-clearing event**: between the admit and the
   release, find the event with `state_before & WRITER_BIT != 0`
   and `state_after & WRITER_BIT == 0`. This is the culprit.
3. **The concurrent admit**: another `OP_*_ADMIT_*` (Ok) event in
   the same window — if present, identifies the second writer.

Map the culprit event to a hypothesis:

* `OP_NONE_SELF_ADMIT_REVERT` clearing WRITER_BIT, with no
  corresponding `OP_NONE_SELF_ADMIT_STATE` success → H1
  (parked-revert race; the revert pre-emptively claimed admission
  via signal's stale chain link).
* `OP_SIGNAL_UNDO` event with `state_before & READER_MASK != 0` →
  H2 (signal undo silently succeeded against a state that already
  had reader bits — the writer bit was already cleared by someone
  else, but we tried to clear it again).
* `OP_RELEASE_WRITE` from a different core_id between our admit
  and our release → two writers somehow co-admitted; trace the
  second writer's admit path to find the unenumerated H3.

### 6.6 Fix application

Apply the fix candidate matching the identified hypothesis:

#### If H1 confirmed — apply F1 (revert via CAS)

In `acquire_write`'s NONE-path self-admit spin, replace
`slot.parked.store(PARKED_WAITING, Release)` (the revert after a
failed `state.CAS(0, WRITER_BIT)`) with:

```rust
// Revert via CAS.  Two acceptable observed values:
//   - PARKED_ADMITTED: our CAS-claim from step 2 is intact; revert
//     it back to WAITING for the next spin iteration.
//   - PARKED_WAITING: signal has already reverted us; nothing to do.
//   - PARKED_NOT_IN_QUEUE: unreachable (only reset() stores it).
match slot.parked.compare_exchange(
    PARKED_ADMITTED, PARKED_WAITING, AcqRel, Acquire,
) {
    Ok(_) => {}
    Err(PARKED_WAITING) => {}
    Err(PARKED_NOT_IN_QUEUE) => debug_assert!(false,
        "NOT_IN_QUEUE during writer self-admit revert"),
    Err(_) => debug_assert!(false, "unexpected parked observed"),
}
```

Apply the symmetric fix in `acquire_read`'s NONE-path.

#### If H2 confirmed — apply F2 (assert undo success)

In both `cascade_admit_readers` and `signal_next_waiter` undo
paths, replace silent `let _ = ...CAS...` with explicit assert:

```rust
let undo_result = self.state.compare_exchange(
    WRITER_BIT, 0, AcqRel, Acquire,
);
debug_assert!(undo_result.is_ok(),
    "writer admit undo failed: state was 0x{:x}",
    undo_result.unwrap_err());
```

In release builds the assert is a no-op; in debug builds (cargo
test) it surfaces the underlying invariant violation immediately,
producing a much cleaner trace than the 100ms-downstream
`release_write` panic.

If the assert ever fires, the protocol has a deeper bug —
fall back to H3.

#### If H3 (unenumerated) — derive and fix

The trace pattern uniquely identifies a code path the audit
missed. Write the smallest reproducer (a 2-thread test with the
same interleaving), add a fix candidate with the same care as
A1..A10, run a 1000-iteration stress to confirm. Update the
relevant SM2.C invariants if the protocol shape changed.

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
   ```

   This is the formal expression of "no `WRITER_BIT | reader_bits`
   state is reachable".

2. **Parked transition uniqueness**: for each (slot, iteration),
   at most one observer transitions parked from WAITING to ADMITTED.

   ```lean
   theorem queued_rw_lock_parked_admit_unique
     (trace : List MemoryEvent)
     (h_wf : MemoryTrace.wellFormed trace)
     (h_target : MemoryEvent.loc = parkedOf slot) :
       (trace.filter (fun e =>
          e.isWrite ∧ ...))
         .length ≤ 1 := by ...
   ```

   This is the formal expression of the CAS-claim discipline.

3. **Writer-readers exclusion preservation** (already in SM2.C as
   `rwLock_writer_readers_exclusion`): re-verify that the new
   refinement bridge carries through. The proof reduces to
   `state ≠ WRITER_BIT | k` for any positive `k`, which follows
   directly from obligation (1).

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

Add three new scanners to `rust/sele4n-hal/build.rs`. Each follows
the pattern of the existing 11 scanners (e.g.,
`scan_gic_rs_send_sgi_emits_dsb_ish` at SM1.F.8).

#### 7.1.1 `scan_queued_rw_lock_tristate_intact`

Grep `queued_rw_lock.rs` for the literal presence of:

* `pub const PARKED_NOT_IN_QUEUE: u8 = 0;`
* `pub const PARKED_WAITING: u8 = 1;`
* `pub const PARKED_ADMITTED: u8 = 2;`
* `parked: AtomicU8,` (within the `struct WaiterSlot` block).

Fail with diagnostic "WS-SM SM2.E protocol regression: tristate
parked machine removed" if any pattern is missing.

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
`SM2_THEOREM_COUNT` (in `rust/sele4n-hal/src/lock_bridge.rs`) bumps
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
* `docs/WORKSTREAM_HISTORY.md` — append the Stream B closure entry
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
  `SM2_THEOREM_COUNT` changes.

### 9.4 Documentation (Stream A + Stream C closure)

* `docs/spec/SELE4N_SPEC.md` §10.
* `docs/gitbook/16-verified-lock-primitives.md` (new).
* `docs/gitbook/SUMMARY.md`, `docs/gitbook/navigation_manifest.json`,
  `docs/gitbook/README.md`.
* `docs/WORKSTREAM_HISTORY.md`.
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
